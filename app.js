/*!
 * Braille Studio — image → Unicode Braille  (engine v2)
 *
 * Pipeline (every stage is memoised, so moving one slider only re-runs what comes after it):
 *   crop → detail-preserving downscale → tone (levels / clarity / contrast) → ink (polarity + alpha)
 *   → sharpen → quantise (error diffusion / ordered / threshold / edges) → refine (dot-by-dot search,
 *   structure-aware for small pictures) → pack to ⠿
 *
 * The engine part has no DOM dependency; the UI part only starts when a document exists.
 */
(function (root) {
  "use strict";

  /* ───────────────────────────── constants ───────────────────────────── */
  var MAX_SRC = 1024;        // longest side kept in memory after loading
  var MAX_ROWS = 800;        // safety cap for very tall images
  var ASPECT = 2;            // braille cell height / width (monospace)
  var REFINE_LIMIT = 700000; // skip the refine pass above this many dots
  var STRUCT_LIMIT = 9000;   // structure-aware refine is slower, so only small pictures (where every dot counts) use it
  var BAYER = [
     0, 32,  8, 40,  2, 34, 10, 42, 48, 16, 56, 24, 50, 18, 58, 26,
    12, 44,  4, 36, 14, 46,  6, 38, 60, 28, 52, 20, 62, 30, 54, 22,
     3, 35, 11, 43,  1, 33,  9, 41, 51, 19, 59, 27, 49, 17, 57, 25,
    15, 47,  7, 39, 13, 45,  5, 37, 63, 31, 55, 23, 61, 29, 53, 21
  ];
  var MODE_ALIAS = { standard: "smart", dither: "floyd" };   // names used by the older markup
  var MODE_LABEL = { smart: "Smart", floyd: "Floyd–Steinberg", atkinson: "Atkinson", ordered: "Ordered", threshold: "Threshold", edges: "Edges" };
  var srcSeq = 0;

  /* ───────────────────────────── small helpers ───────────────────────────── */
  function clamp255(a) {
    for (var i = 0, n = a.length; i < n; i++) { var v = a[i]; a[i] = v < 0 ? 0 : v > 255 ? 255 : v; }
  }
  function clampInt(v, lo, hi) { v = Math.round(+v); return v < lo ? lo : v > hi ? hi : v; }
  function pct(hist, total, p) {
    var t = total * p, s = 0;
    for (var i = 0; i < 256; i++) { s += hist[i]; if (s >= t) return i; }
    return 255;
  }

  /* Running-sum box blur (edge-clamped, O(n)). */
  function boxBlur(src, w, h, r) {
    var n = src.length, tmp = new Float32Array(n), out = new Float32Array(n);
    var inv = 1 / (2 * r + 1), x, y, k, o, acc, a, b;
    for (y = 0; y < h; y++) {
      o = y * w; acc = 0;
      for (k = -r; k <= r; k++) acc += src[o + (k < 0 ? 0 : k >= w ? w - 1 : k)];
      for (x = 0; x < w; x++) {
        tmp[o + x] = acc * inv;
        a = x + r + 1; b = x - r;
        acc += src[o + (a >= w ? w - 1 : a)] - src[o + (b < 0 ? 0 : b)];
      }
    }
    for (x = 0; x < w; x++) {
      acc = 0;
      for (k = -r; k <= r; k++) acc += tmp[(k < 0 ? 0 : k >= h ? h - 1 : k) * w + x];
      for (y = 0; y < h; y++) {
        out[y * w + x] = acc * inv;
        a = y + r + 1; b = y - r;
        acc += tmp[(a >= h ? h - 1 : a) * w + x] - tmp[(b < 0 ? 0 : b) * w + x];
      }
    }
    return out;
  }

  /* Alpha-aware blur: transparent pixels do not leak into the subject. */
  function blurWeighted(L, A, w, h, r) {
    var n = L.length, P = new Float32Array(n), W = new Float32Array(n), i, al;
    for (i = 0; i < n; i++) { al = A[i] > 1 ? 1 : A[i]; P[i] = L[i] * al; W[i] = al; }
    P = boxBlur(boxBlur(P, w, h, r), w, h, r);
    W = boxBlur(boxBlur(W, w, h, r), w, h, r);
    var out = new Float32Array(n);
    for (i = 0; i < n; i++) out[i] = W[i] > 1e-4 ? P[i] / W[i] : L[i];
    return out;
  }

  /* ───────────────────────────── source preparation ───────────────────────────── */
  /** rgba: Uint8ClampedArray (w*h*4). Keeps luminance + "subject coverage" (alpha) as floats.
   *  A plain single-colour background is treated like transparency, so only the subject gets ink. */
  function makeSource(rgba, w, h) {
    var n = w * h, lum = new Float32Array(n), alpha = new Float32Array(n), minA = 255, i, p, a;
    for (i = 0, p = 0; i < n; i++, p += 4) {
      a = rgba[p + 3];
      alpha[i] = a / 255;
      lum[i] = 0.2126 * rgba[p] + 0.7152 * rgba[p + 1] + 0.0722 * rgba[p + 2];
      if (a < minA) minA = a;
    }
    var kind = "none", bgL = 0, bg;
    if (minA < 250) {
      kind = "alpha";
    } else {
      alpha.fill(1);
      bg = borderColor(rgba, w, h);
      if (bg) {
        cutout(rgba, w, h, bg, alpha);
        if (isFlatCutout(lum, alpha, n)) { kind = "uniform"; bgL = 0.2126 * bg[0] + 0.7152 * bg[1] + 0.0722 * bg[2]; }
        else alpha.fill(1);                       // textured picture, not a flat backdrop → keep everything
      }
    }
    var sum = 0, cnt = 0;
    for (i = 0; i < n; i++) if (alpha[i] > 0.5) { sum += lum[i]; cnt++; }
    var mean = cnt ? sum / cnt : 128;
    // which way round reads best: dots = bright things (default) or dots = dark things on a light page
    var invert = kind === "uniform" ? mean < bgL : kind === "alpha" ? mean < 90 : false;
    return { id: ++srcSeq, w: w, h: h, lum: lum, alpha: alpha, bounds: boundsOf(alpha, w, h), kind: kind, meanL: mean, autoInvert: invert };
  }

  var BG_TOL = 28;
  function median(a) { var s = Float32Array.from(a).sort(); return s[s.length >> 1]; }
  /* colour of the picture's border when (almost) all of it is one flat colour, else null */
  function borderColor(rgba, w, h) {
    var R = [], G = [], B = [], x, y, i;
    function ring(px, py) { var p = (py * w + px) * 4; R.push(rgba[p]); G.push(rgba[p + 1]); B.push(rgba[p + 2]); }
    for (x = 0; x < w; x++) { ring(x, 0); ring(x, h - 1); }
    for (y = 1; y < h - 1; y++) { ring(0, y); ring(w - 1, y); }
    var mr = median(R), mg = median(G), mb = median(B), ok = 0;
    for (i = 0; i < R.length; i++) {
      if (Math.abs(R[i] - mr) <= BG_TOL && Math.abs(G[i] - mg) <= BG_TOL && Math.abs(B[i] - mb) <= BG_TOL) ok++;
    }
    return ok / R.length >= 0.96 ? [mr, mg, mb] : null;
  }
  /* flood-fill the background from the border; those pixels become fully transparent */
  function cutout(rgba, w, h, bg, alpha) {
    var n = w * h, seen = new Uint8Array(n), stack = new Int32Array(n), sp = 0, i, x, y, p, j;
    function near(k) {
      var q = k * 4;
      return Math.abs(rgba[q] - bg[0]) <= BG_TOL && Math.abs(rgba[q + 1] - bg[1]) <= BG_TOL && Math.abs(rgba[q + 2] - bg[2]) <= BG_TOL;
    }
    function push(k) { if (!seen[k] && near(k)) { seen[k] = 1; stack[sp++] = k; } }
    for (x = 0; x < w; x++) { push(x); push((h - 1) * w + x); }
    for (y = 1; y < h - 1; y++) { push(y * w); push(y * w + w - 1); }
    while (sp) {
      i = stack[--sp]; alpha[i] = 0; x = i % w; y = (i - x) / w;
      if (x > 0) push(i - 1);
      if (x < w - 1) push(i + 1);
      if (y > 0) push(i - w);
      if (y < h - 1) push(i + w);
    }
  }
  /* the removed area must really be flat (no texture), otherwise it is part of the picture */
  function isFlatCutout(lum, alpha, n) {
    var cnt = 0, sum = 0, sq = 0, i, v;
    for (i = 0; i < n; i++) if (alpha[i] === 0) { v = lum[i]; cnt++; sum += v; sq += v * v; }
    if (cnt < 0.02 * n) return false;                 // nothing worth cutting out
    var m = sum / cnt;
    return Math.sqrt(Math.max(0, sq / cnt - m * m)) < 4;
  }
  /* bounding box of the subject, with a little breathing room; whole picture if that is not worth cropping */
  function boundsOf(alpha, w, h) {
    var x0 = w, y0 = h, x1 = -1, y1 = -1, x, y, o;
    for (y = 0; y < h; y++) {
      o = y * w;
      for (x = 0; x < w; x++) {
        if (alpha[o + x] > 0.06) {
          if (x < x0) x0 = x;
          if (x > x1) x1 = x;
          if (y < y0) y0 = y;
          y1 = y;
        }
      }
    }
    var full = { x0: 0, y0: 0, x1: w, y1: h };
    if (x1 < 0) return full;
    x1++; y1++;
    var pad = Math.max(1, Math.round(0.02 * Math.min(x1 - x0, y1 - y0)));
    x0 = Math.max(0, x0 - pad); y0 = Math.max(0, y0 - pad); x1 = Math.min(w, x1 + pad); y1 = Math.min(h, y1 + pad);
    if (x1 - x0 < 8 || y1 - y0 < 8 || (x1 - x0) * (y1 - y0) >= 0.97 * w * h) return full;
    return { x0: x0, y0: y0, x1: x1, y1: y1 };
  }

  /* ───────────────────────────── stage 1: downscale to the dot grid ───────────────────────────── */
  /* Area average guided by a detail-preserving weight (small bright/dark features survive).
     lambda = 0 → plain area average, → 1 → strong detail emphasis. */
  function gridSample(src, crop, pw, ph, lambda) {
    var sw = src.w, lum = src.lum, alpha = src.alpha;
    var cw = crop.x1 - crop.x0, ch = crop.y1 - crop.y0, n = pw * ph;
    var L = new Float32Array(n), A = new Float32Array(n), x, y, i, k;

    if (cw / pw < 2 || ch / ph < 2) {                      // little or no reduction → bilinear
      for (y = 0; y < ph; y++) {
        var fy = crop.y0 + (y + 0.5) * ch / ph - 0.5, y0 = Math.floor(fy), ty = fy - y0, y1 = y0 + 1;
        y0 = y0 < crop.y0 ? crop.y0 : y0 >= crop.y1 ? crop.y1 - 1 : y0;
        y1 = y1 < crop.y0 ? crop.y0 : y1 >= crop.y1 ? crop.y1 - 1 : y1;
        for (x = 0; x < pw; x++) {
          var fx = crop.x0 + (x + 0.5) * cw / pw - 0.5, x0 = Math.floor(fx), tx = fx - x0, x1 = x0 + 1;
          x0 = x0 < crop.x0 ? crop.x0 : x0 >= crop.x1 ? crop.x1 - 1 : x0;
          x1 = x1 < crop.x0 ? crop.x0 : x1 >= crop.x1 ? crop.x1 - 1 : x1;
          var i00 = y0 * sw + x0, i10 = y0 * sw + x1, i01 = y1 * sw + x0, i11 = y1 * sw + x1;
          var w00 = (1 - tx) * (1 - ty), w10 = tx * (1 - ty), w01 = (1 - tx) * ty, w11 = tx * ty;
          var a00 = alpha[i00] * w00, a10 = alpha[i10] * w10, a01 = alpha[i01] * w01, a11 = alpha[i11] * w11;
          var sa = a00 + a10 + a01 + a11;
          var sp = a00 * lum[i00] + a10 * lum[i10] + a01 * lum[i01] + a11 * lum[i11];
          k = y * pw + x;
          A[k] = sa;
          L[k] = sa > 1e-4 ? sp / sa : 0;
        }
      }
      return { L: L, A: A };
    }

    var cellX = new Int32Array(cw), cellY = new Int32Array(ch);
    for (x = 0; x < cw; x++) { k = Math.floor(x * pw / cw); cellX[x] = k >= pw ? pw - 1 : k; }
    for (y = 0; y < ch; y++) { k = Math.floor(y * ph / ch); cellY[y] = k >= ph ? ph - 1 : k; }
    var sA = new Float64Array(n), sP = new Float64Array(n), cnt = new Float64Array(n), a, l, row, cy;
    for (y = 0; y < ch; y++) {
      row = (crop.y0 + y) * sw + crop.x0; cy = cellY[y] * pw;
      for (x = 0; x < cw; x++) {
        i = row + x; k = cy + cellX[x]; a = alpha[i];
        sA[k] += a; sP[k] += a * lum[i]; cnt[k] += 1;
      }
    }
    var M = new Float32Array(n);
    for (k = 0; k < n; k++) { M[k] = sA[k] > 1e-6 ? sP[k] / sA[k] : 0; A[k] = cnt[k] ? sA[k] / cnt[k] : 0; }

    if (lambda > 0.01) {                                   // detail-preserving second pass
      var lut = new Float32Array(256), d;
      for (d = 0; d < 256; d++) lut[d] = Math.pow(d + 1, lambda);
      var sW = new Float64Array(n), sPW = new Float64Array(n), wt;
      for (y = 0; y < ch; y++) {
        row = (crop.y0 + y) * sw + crop.x0; cy = cellY[y] * pw;
        for (x = 0; x < cw; x++) {
          i = row + x; k = cy + cellX[x]; l = lum[i];
          d = l - M[k]; if (d < 0) d = -d;
          wt = lut[d > 255 ? 255 : d | 0] * alpha[i];
          sW[k] += wt; sPW[k] += wt * l;
        }
      }
      for (k = 0; k < n; k++) L[k] = sW[k] > 1e-9 ? sPW[k] / sW[k] : M[k];
    } else {
      L.set(M);
    }
    return { L: L, A: A };
  }

  /* ───────────────────────────── stage 2: tone ───────────────────────────── */
  function autoLevels(L, A, n) {
    var hist = new Uint32Array(256), cnt = 0, i, v;
    for (i = 0; i < n; i++) {
      if (A[i] > 0.5) { v = L[i]; v = v < 0 ? 0 : v > 255 ? 255 : v | 0; hist[v]++; cnt++; }
    }
    if (cnt < 8) return;
    var lo = pct(hist, cnt, 0.01), hi = pct(hist, cnt, 0.99);
    if (hi - lo < 12) return;
    var mid = (lo + hi) / 2, s = Math.min(255 / (hi - lo), 4), med = pct(hist, cnt, 0.5);
    for (i = 0; i < n; i++) L[i] = (L[i] - mid) * s + 127.5;
    clamp255(L);
    // gentle auto-exposure: pull a very dark / very bright picture towards the middle
    var m = ((med - mid) * s + 127.5) / 255;
    if (m < 0.02) m = 0.02; else if (m > 0.98) m = 0.98;
    if (Math.abs(m - 0.5) > 0.1) {
      var g = Math.pow(Math.log(0.5) / Math.log(m), 0.6);
      g = g < 0.55 ? 0.55 : g > 1.8 ? 1.8 : g;
      for (i = 0; i < n; i++) L[i] = 255 * Math.pow(L[i] / 255, g);
    }
  }

  function toneStage(g, w, h, o, clarity, punch) {
    var n = w * h, L = Float32Array.from(g.L), A = g.A, i;
    if (o.levels) autoLevels(L, A, n);
    if (clarity > 0.01) {                                   // local contrast ("clarity")
      var r = Math.min(24, Math.max(2, Math.round(Math.min(w, h) * 0.1)));
      var bl = blurWeighted(L, A, w, h, r);
      for (i = 0; i < n; i++) L[i] += clarity * (L[i] - bl[i]);
      clamp255(L);
    }
    if (o.contrast || o.brightness) {
      var f = Math.pow(4, o.contrast / 100), b = o.brightness * 1.28;
      for (i = 0; i < n; i++) L[i] = (L[i] - 128) * f + 128 + b;
    }
    clamp255(L);
    if (punch > 0.01) {                                     // S-curve: fewer muddy mid-tones, cleaner shapes
      for (i = 0; i < n; i++) {
        var x = L[i] / 255, y = x + punch * (x * x * (3 - 2 * x) - x);
        L[i] = 255 * (y < 0 ? 0 : y > 1 ? 1 : y);
      }
    }
    return L;
  }

  /* ───────────────────────────── stage 3: ink ───────────────────────────── */
  /* t = how much "ink" (lit dot) each pixel wants. Transparent pixels never get ink. */
  function inkStage(L, A, n, invert) {
    var t = new Float32Array(n), i, a, v;
    for (i = 0; i < n; i++) {
      a = A[i] > 1 ? 1 : A[i];
      v = invert ? 255 - L[i] : L[i];
      t[i] = v * a;
    }
    return t;
  }

  /* ───────────────────────────── stage 4: sharpen ───────────────────────────── */
  function sharpen(t, w, h, amt) {
    if (amt <= 0.001) return t;
    var b = boxBlur(t, w, h, 1), out = new Float32Array(t.length), i;
    for (i = 0; i < out.length; i++) out[i] = t[i] + amt * (t[i] - b[i]);
    clamp255(out);
    return out;
  }

  /* ───────────────────────────── stage 5: quantise ───────────────────────────── */
  function floyd(t, w, h, thr) {
    var a = Float32Array.from(t), out = new Uint8Array(w * h), x, y, i, v, e, on, o, o2;
    for (y = 0; y < h; y++) {
      o = y * w; o2 = o + w;
      if ((y & 1) === 0) {
        for (x = 0; x < w; x++) {
          i = o + x; v = a[i]; on = v >= thr; e = v - (on ? 255 : 0); out[i] = on ? 1 : 0;
          if (x + 1 < w) a[i + 1] += e * 0.4375;
          if (y + 1 < h) {
            if (x > 0) a[o2 + x - 1] += e * 0.1875;
            a[o2 + x] += e * 0.3125;
            if (x + 1 < w) a[o2 + x + 1] += e * 0.0625;
          }
        }
      } else {
        for (x = w - 1; x >= 0; x--) {
          i = o + x; v = a[i]; on = v >= thr; e = v - (on ? 255 : 0); out[i] = on ? 1 : 0;
          if (x > 0) a[i - 1] += e * 0.4375;
          if (y + 1 < h) {
            if (x + 1 < w) a[o2 + x + 1] += e * 0.1875;
            a[o2 + x] += e * 0.3125;
            if (x > 0) a[o2 + x - 1] += e * 0.0625;
          }
        }
      }
    }
    return out;
  }

  function atkinson(t, w, h, thr) {
    var a = Float32Array.from(t), out = new Uint8Array(w * h), x, y, i, v, e, on;
    for (y = 0; y < h; y++) {
      for (x = 0; x < w; x++) {
        i = y * w + x; v = a[i]; on = v >= thr; e = (v - (on ? 255 : 0)) / 8; out[i] = on ? 1 : 0;
        if (x + 1 < w) a[i + 1] += e;
        if (x + 2 < w) a[i + 2] += e;
        if (y + 1 < h) {
          if (x > 0) a[i + w - 1] += e;
          a[i + w] += e;
          if (x + 1 < w) a[i + w + 1] += e;
        }
        if (y + 2 < h) a[i + 2 * w] += e;
      }
    }
    return out;
  }

  function ordered(t, w, h) {
    var out = new Uint8Array(w * h), x, y, i;
    for (y = 0; y < h; y++) {
      for (x = 0; x < w; x++) {
        i = y * w + x;
        out[i] = t[i] > (BAYER[((y & 7) << 3) | (x & 7)] + 0.5) * (255 / 64) ? 1 : 0;
      }
    }
    return out;
  }

  function otsu(t, A, n) {
    var hist = new Float64Array(256), tot = 0, i, v;
    for (i = 0; i < n; i++) {
      if (A[i] > 0.3) { v = t[i]; v = v < 0 ? 0 : v > 255 ? 255 : v | 0; hist[v]++; tot++; }
    }
    if (!tot) return 128;
    var sum = 0, sB = 0, wB = 0, best = -1, thr = 128, wF, mB, mF, between;
    for (i = 0; i < 256; i++) sum += i * hist[i];
    for (i = 0; i < 256; i++) {
      wB += hist[i]; if (!wB) continue;
      wF = tot - wB; if (!wF) break;
      sB += i * hist[i];
      mB = sB / wB; mF = (sum - sB) / wF;
      between = wB * wF * (mB - mF) * (mB - mF);
      if (between > best) { best = between; thr = i; }
    }
    return thr + 1;
  }

  function edgeBits(t, w, h, bias) {
    var n = w * h, m = new Float32Array(n), x, y, i, gx, gy;
    for (y = 1; y < h - 1; y++) {
      for (x = 1; x < w - 1; x++) {
        i = y * w + x;
        gx = -t[i - w - 1] - 2 * t[i - 1] - t[i + w - 1] + t[i - w + 1] + 2 * t[i + 1] + t[i + w + 1];
        gy = -t[i - w - 1] - 2 * t[i - w] - t[i - w + 1] + t[i + w - 1] + 2 * t[i + w] + t[i + w + 1];
        m[i] = Math.sqrt(gx * gx + gy * gy);
      }
    }
    var s = Float32Array.from(m).sort(), p = s[Math.floor(n * 0.985)] || 1;
    if (p < 1) p = 1;
    var sens = 0.3 - bias / 100 * 0.25;
    sens = sens < 0.05 ? 0.05 : sens > 0.9 ? 0.9 : sens;
    var out = new Uint8Array(n), cut = p * sens;
    for (i = 0; i < n; i++) out[i] = m[i] >= cut ? 1 : 0;
    return out;
  }

  /* ───────────────────────────── stage 6: refine (direct binary search) ─────────────────────────────
     Starting from an error-diffused result, flip single dots whenever that makes the picture, seen through a
     small blur (a stand-in for the eye), closer to the target. Gives crisper edges and cleaner tones. */
  var C1 = [1, 4, 6, 4, 1], G5 = C1;
  function refine(t, b, w, h) {
    var P = 2, W = w + 4, H = h + 4, n = W * H, x, y, i, j, k, dx, dy;
    var d = new Float32Array(n), bp = new Uint8Array(n);
    for (y = 0; y < h; y++) {
      for (x = 0; x < w; x++) {
        i = (y + P) * W + x + P; j = y * w + x;
        bp[i] = b[j]; d[i] = (b[j] ? 255 : 0) - t[j];
      }
    }
    var tmp = new Float32Array(n), q = new Float32Array(n);
    for (y = 0; y < H; y++) {
      for (x = 2; x < W - 2; x++) {
        i = y * W + x;
        tmp[i] = (d[i - 2] + 4 * d[i - 1] + 6 * d[i] + 4 * d[i + 1] + d[i + 2]) / 16;
      }
    }
    for (y = 2; y < H - 2; y++) {
      for (x = 0; x < W; x++) {
        i = y * W + x;
        q[i] = (tmp[i - 2 * W] + 4 * tmp[i - W] + 6 * tmp[i] + 4 * tmp[i + W] + tmp[i + 2 * W]) / 16;
      }
    }
    var cw = new Float32Array(25), off = new Int32Array(25), c0 = 36 / 256;
    for (dy = -2, k = 0; dy <= 2; dy++) {
      for (dx = -2; dx <= 2; dx++, k++) { cw[k] = C1[dy + 2] * C1[dx + 2] / 256; off[k] = dy * W + dx; }
    }
    var pass, changed, delta, dE, ys, ye, ystep, xs, xe, xstep;
    for (pass = 0; pass < 8; pass++) {
      changed = 0;
      if (pass & 1) { ys = h - 1; ye = -1; ystep = -1; xs = w - 1; xe = -1; xstep = -1; }
      else { ys = 0; ye = h; ystep = 1; xs = 0; xe = w; xstep = 1; }
      for (y = ys; y !== ye; y += ystep) {
        for (x = xs; x !== xe; x += xstep) {
          i = (y + P) * W + x + P;
          delta = bp[i] ? -255 : 255;
          dE = delta * (2 * q[i] + delta * c0);
          if (dE < -1) {
            bp[i] ^= 1; changed++;
            for (k = 0; k < 25; k++) q[i + off[k]] += delta * cw[k];
          }
        }
      }
      if (changed < n * 0.0005) break;
    }
    for (y = 0; y < h; y++) {
      for (x = 0; x < w; x++) b[y * w + x] = bp[(y + P) * W + x + P];
    }
    return b;
  }

  /* Structure-aware variant for small pictures. Same dot-by-dot search, but the score also contains a local
     structure term (contrast/structure part of SSIM over 5x5 windows, as in "Structure-aware halftoning",
     Pang et al., SIGGRAPH 2008): the blurred dots must follow the target's edges, lines and small features,
     not just its average tone. Cleaner outlines and fewer stray dots when only a few dozen dots are available. */
  var STRUCT_BETA = 1.5, SSIM_C2 = 58.5;
  function refineStructure(t, b0, w, h) {
    var P = 4, W = w + 2 * P, H = h + 2 * P, n = W * H, x, y, i, k, m, s, dx, dy;
    var bp = new Uint8Array(n), inside = new Uint8Array(n);
    var T = new Float64Array(n), U = new Float64Array(n), TB = new Float64Array(n);
    for (y = 0; y < h; y++) {
      for (x = 0; x < w; x++) { i = (y + P) * W + x + P; bp[i] = b0[y * w + x]; T[i] = t[y * w + x]; inside[i] = 1; }
    }
    // kernels: 3x3 "eye" blur, 5x5 statistics window, and the table mapping (changed pixel, window) -> slot in a 7x7 patch
    var h9 = new Float64Array(9), o9 = new Int32Array(9), g25 = new Float64Array(25), slot = new Int32Array(225), soff = new Int32Array(49);
    for (dy = -1, k = 0; dy <= 1; dy++) for (dx = -1; dx <= 1; dx++, k++) { h9[k] = (2 - Math.abs(dx)) * (2 - Math.abs(dy)) / 16; o9[k] = dy * W + dx; }
    for (dy = -2, m = 0; dy <= 2; dy++) for (dx = -2; dx <= 2; dx++, m++) g25[m] = G5[dx + 2] * G5[dy + 2] / 256;
    for (dy = -1, k = 0; dy <= 1; dy++) {
      for (dx = -1; dx <= 1; dx++, k++) {
        for (var wy = -2, mm = 0; wy <= 2; wy++) for (var wx = -2; wx <= 2; wx++, mm++) slot[k * 25 + mm] = (dy + wy + 3) * 7 + (dx + wx + 3);
      }
    }
    for (dy = 0, s = 0; dy < 7; dy++) for (dx = 0; dx < 7; dx++, s++) soff[s] = (dy - 3) * W + (dx - 3);

    for (y = 1; y < H - 1; y++) {
      for (x = 1; x < W - 1; x++) {
        var su = 0, st = 0;
        for (k = 0; k < 9; k++) { i = y * W + x + o9[k]; su += h9[k] * (bp[i] ? 255 : 0); st += h9[k] * T[i]; }
        U[y * W + x] = su; TB[y * W + x] = st;
      }
    }
    var A1 = new Float64Array(n), A2 = new Float64Array(n), A3 = new Float64Array(n), B1 = new Float64Array(n), B2 = new Float64Array(n), S0 = new Float64Array(n);
    var a1, a2, a3, b1, b2, ci, pi, j;
    for (y = P; y < P + h; y++) {
      for (x = P; x < P + w; x++) {
        a1 = a2 = a3 = b1 = b2 = 0;
        for (dy = -2, m = 0; dy <= 2; dy++) {
          for (dx = -2; dx <= 2; dx++, m++) {
            j = (y + dy) * W + x + dx;
            var u = U[j], tt = T[j], gw = g25[m];
            a1 += gw * u; a2 += gw * u * u; a3 += gw * u * tt; b1 += gw * tt; b2 += gw * tt * tt;
          }
        }
        i = y * W + x; A1[i] = a1; A2[i] = a2; A3[i] = a3; B1[i] = b1; B2[i] = b2;
        S0[i] = (2 * (a3 - a1 * b1) + SSIM_C2) / ((a2 - a1 * a1) + (b2 - b1 * b1) + SSIM_C2);
      }
    }
    var dA1 = new Float64Array(49), dA2 = new Float64Array(49), dA3 = new Float64Array(49), S1 = new Float64Array(49);
    var NORM = 1 / (255 * 255), pass, changed, delta, du, u0, tp, c1, dTone, dStruct, wgt, sl, sx, sy, ys, ye, ystep, xs, xe, xstep;
    for (pass = 0; pass < 6; pass++) {
      changed = 0;
      if (pass & 1) { ys = h - 1; ye = -1; ystep = -1; xs = w - 1; xe = -1; xstep = -1; }
      else { ys = 0; ye = h; ystep = 1; xs = 0; xe = w; xstep = 1; }
      for (sy = ys; sy !== ye; sy += ystep) {
        for (sx = xs; sx !== xe; sx += xstep) {
          ci = (sy + P) * W + sx + P;
          delta = bp[ci] ? -255 : 255;
          dA1.fill(0); dA2.fill(0); dA3.fill(0);
          dTone = 0;
          for (k = 0; k < 9; k++) {
            pi = ci + o9[k]; du = delta * h9[k]; u0 = U[pi]; tp = T[pi];
            dTone += du * (2 * (u0 - TB[pi]) + du);
            c1 = 2 * u0 * du + du * du;
            for (m = 0; m < 25; m++) {
              sl = slot[k * 25 + m]; wgt = g25[m];
              dA1[sl] += wgt * du; dA2[sl] += wgt * c1; dA3[sl] += wgt * du * tp;
            }
          }
          dStruct = 0;
          for (s = 0; s < 49; s++) {
            j = ci + soff[s];
            if (!inside[j]) continue;
            a1 = A1[j] + dA1[s]; a2 = A2[j] + dA2[s]; a3 = A3[j] + dA3[s]; b1 = B1[j]; b2 = B2[j];
            S1[s] = (2 * (a3 - a1 * b1) + SSIM_C2) / ((a2 - a1 * a1) + (b2 - b1 * b1) + SSIM_C2);
            dStruct += S0[j] - S1[s];
          }
          if (dTone * NORM + STRUCT_BETA * dStruct < -1e-4) {
            bp[ci] ^= 1; changed++;
            for (k = 0; k < 9; k++) U[ci + o9[k]] += delta * h9[k];
            for (s = 0; s < 49; s++) {
              j = ci + soff[s];
              if (!inside[j]) continue;
              A1[j] += dA1[s]; A2[j] += dA2[s]; A3[j] += dA3[s]; S0[j] = S1[s];
            }
          }
        }
      }
      if (!changed) break;
    }
    for (y = 0; y < h; y++) for (x = 0; x < w; x++) b0[y * w + x] = bp[(y + P) * W + x + P];
    return b0;
  }

  function quantize(t, A, w, h, mode, bias) {
    var n = w * h, i, thr, out, b;
    switch (mode) {
      case "threshold":
        thr = otsu(t, A, n) + bias; thr = thr < 8 ? 8 : thr > 247 ? 247 : thr;
        out = new Uint8Array(n);
        for (i = 0; i < n; i++) out[i] = t[i] >= thr ? 1 : 0;
        return out;
      case "edges":    return edgeBits(t, w, h, bias);
      case "ordered":  return ordered(t, w, h);
      case "atkinson": return atkinson(t, w, h, 128);
      case "floyd":    return floyd(t, w, h, 128);
      default:
        b = floyd(t, w, h, 128);
        if (n <= STRUCT_LIMIT) refineStructure(t, b, w, h);
        else if (n <= REFINE_LIMIT) refine(t, b, w, h);
        return b;
    }
  }

  /* ───────────────────────────── stage 7: pack into braille characters ───────────────────────────── */
  function pack(bits, pw, ph, fill) {
    var cols = pw >> 1, rows = ph >> 2, buf = new Uint16Array(cols), out = new Array(rows), cy, cx, i, m, base;
    for (cy = 0; cy < rows; cy++) {
      base = cy * 4 * pw;
      for (cx = 0; cx < cols; cx++) {
        i = base + cx * 2;
        m = bits[i] | (bits[i + pw] << 1) | (bits[i + 2 * pw] << 2) | (bits[i + 1] << 3) |
            (bits[i + 1 + pw] << 4) | (bits[i + 1 + 2 * pw] << 5) | (bits[i + 3 * pw] << 6) | (bits[i + 1 + 3 * pw] << 7);
        buf[cx] = (m === 0 && fill) ? 0x2804 : 0x2800 + m;
      }
      out[cy] = String.fromCharCode.apply(null, buf);
    }
    return out.join("\n");
  }

  /* ───────────────────────────── pipeline with per-stage cache ───────────────────────────── */
  function createPipeline() {
    var cache = {};
    function stage(name, key, fn) {
      var c = cache[name];
      if (c && c.key === key) return c.val;
      var v = fn();
      cache[name] = { key: key, val: v };
      return v;
    }
    return {
      run: function (src, o) {
        var cols = clampInt(o.width, 8, 400);
        var crop = o.trim ? src.bounds : { x0: 0, y0: 0, x1: src.w, y1: src.h };
        var cw = crop.x1 - crop.x0, ch = crop.y1 - crop.y0;
        var rows = Math.round(cols * ch / cw / ASPECT);
        if (rows > MAX_ROWS) { rows = MAX_ROWS; cols = Math.max(1, Math.floor(rows * ASPECT * cw / ch)); }   // very tall picture: keep its proportions
        rows = Math.max(1, rows);
        var pw = cols * 2, ph = rows * 4, n = pw * ph;
        var tiny = Math.max(0, Math.min(1, (120 - pw) / 72));            // 1 up to ~24 chars, fades out by ~60 chars
        var detail = Math.min(1, Math.max(0, Math.min(100, +o.detail)) / 100 * (1 + 0.5 * tiny));
        var sharpAmt = Math.min(1, Math.max(0, Math.min(100, +o.sharp)) / 100 * (1 + 0.67 * tiny)) * 2.2;
        var small = Math.max(0, Math.min(1, (240 - pw) / 180));          // 1 for tiny pictures, 0 from ~120 chars up
        var lambda = detail * 0.95;
        var clarity = detail * 0.9 * (1 + 0.8 * small) * (o.cmul == null ? 1 : o.cmul);
        var punch = o.punch != null ? o.punch : detail * (0.33 + 1.33 * small);
        var mode = MODE_ALIAS[o.mode] || o.mode || "smart";

        var k1 = src.id + "|" + crop.x0 + "," + crop.y0 + "," + crop.x1 + "," + crop.y1 + "|" + pw + "x" + ph + "|" + lambda.toFixed(3);
        var g = stage("grid", k1, function () { return gridSample(src, crop, pw, ph, lambda); });

        var k2 = k1 + "|" + (o.levels ? 1 : 0) + "|" + o.contrast + "|" + o.brightness + "|" + clarity.toFixed(3) + "|" + punch.toFixed(3);
        var tone = stage("tone", k2, function () { return toneStage(g, pw, ph, o, clarity, punch); });

        var k3 = k2 + "|" + (o.invert ? 1 : 0);
        var ink = stage("ink", k3, function () { return inkStage(tone, g.A, n, o.invert); });

        var k4 = k3 + "|" + sharpAmt.toFixed(3);
        var sh = stage("sharp", k4, function () { return sharpen(ink, pw, ph, sharpAmt); });

        var k5 = k4 + "|" + mode + "|" + o.thr;
        var bits = stage("bits", k5, function () { return quantize(sh, g.A, pw, ph, mode, o.thr); });

        var k6 = k5 + "|" + (o.fill ? 1 : 0);
        var text = stage("text", k6, function () { return pack(bits, pw, ph, o.fill); });

        return { text: text, cols: cols, rows: rows, chars: cols * rows + rows - 1, mode: mode, bits: bits, pw: pw, ph: ph };
      }
    };
  }

  var Engine = {
    MAX_SRC: MAX_SRC, MODE_ALIAS: MODE_ALIAS, MODE_LABEL: MODE_LABEL,
    makeSource: makeSource, createPipeline: createPipeline
  };
  root.BrailleEngine = Engine;
  if (typeof module === "object" && module.exports) module.exports = Engine;

  /* ═════════════════════════════════ UI ═════════════════════════════════ */
  if (typeof document === "undefined") return;

  var $ = function (s) { return document.querySelector(s); };
  var $$ = function (s) { return Array.prototype.slice.call(document.querySelectorAll(s)); };
  var on = function (t, ev, fn) { var e = typeof t === "string" ? $(t) : t; if (e) e.addEventListener(ev, fn); return e; };

  var pipe = createPipeline();
  var src = null, objUrl = null, raf = 0, toastTimer = 0, curCols = 80, curRows = 40;
  var activeChoice = $(".choice.active");
  var mode = activeChoice ? (MODE_ALIAS[activeChoice.dataset.mode] || activeChoice.dataset.mode) : "smart";

  var output = $("#output"), mini = $("#miniOutput"), stats = $("#stats"), miniStats = $("#miniStats");
  var fileInput = $("#fileInput"), drop = $("#dropZone"), preview = $("#preview"), toast = $("#toast");

  var SLIDERS = {
    width:      { input: "#widthRange", label: "#widthValue",      def: 80 },
    detail:     { input: "#detail",     label: "#detailValue",     def: 60 },
    sharpness:  { input: "#sharpness",  label: "#sharpnessValue",  def: 30 },
    contrast:   { input: "#contrast",   label: "#contrastValue",   def: 0 },
    brightness: { input: "#brightness", label: "#brightnessValue", def: 0 },
    threshold:  { input: "#threshold",  label: "#thresholdValue",  def: 0 }
  };
  function num(key) { var e = $(SLIDERS[key].input); return e ? +e.value : SLIDERS[key].def; }
  function chk(sel, def) { var e = $(sel); return e ? e.checked : def; }
  function labelFor(key, v) { return key === "threshold" && +v === 0 ? "Auto" : String(v); }

  function readOpts() {
    return {
      width: num("width"), detail: num("detail"), sharp: num("sharpness"), contrast: num("contrast"),
      brightness: num("brightness"), thr: num("threshold"), mode: mode,
      invert: chk("#invert", false), levels: chk("#autoLevels", true), trim: chk("#trim", true), fill: chk("#fillBlank", false)
    };
  }

  /* fit the monospace preview to its box so the whole picture is visible */
  var mctx = document.createElement("canvas").getContext("2d");
  function fit(pre, maxH) {
    if (!pre || !src || !pre.clientWidth) return;
    var cs = getComputedStyle(pre), avail = pre.clientWidth - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight);
    if (avail <= 0) return;
    mctx.font = "100px " + cs.fontFamily;
    var cw = mctx.measureText("\u28ff").width / 100 || 0.6;
    var lh = Math.max(1, 2 * cw);                          // a Braille cell is twice as tall as it is wide
    var size = avail / (curCols * cw) * 0.985;
    if (maxH) size = Math.min(size, (maxH - parseFloat(cs.paddingTop) - parseFloat(cs.paddingBottom)) / (curRows * lh));
    pre.style.lineHeight = String(lh);
    pre.style.fontSize = Math.max(2, Math.min(30, size)) + "px";
  }
  function fitAll() { fit(output); fit(mini, window.innerWidth <= 520 ? 190 : 240); }

  function schedule() {
    if (!src) return;
    cancelAnimationFrame(raf);
    raf = requestAnimationFrame(draw);
  }

  function draw() {
    if (!src) return;
    var o = readOpts(), r = pipe.run(src, o);
    curCols = r.cols; curRows = r.rows;
    var info = r.cols + " × " + r.rows + " · " + (MODE_LABEL[r.mode] || r.mode) + " · " + r.chars + " chars" +
               (r.chars > 2000 ? " · over Discord's 2000 limit" : "");
    if (output) { output.textContent = r.text; output.classList.toggle("light", o.invert); }
    if (mini) { mini.textContent = r.text; mini.classList.toggle("light", o.invert); }
    if (stats) stats.textContent = info;
    if (miniStats) miniStats.textContent = info;
    fitAll();
  }

  /* ───────────── loading images ───────────── */
  function decode(file) {
    if (window.createImageBitmap) {
      return createImageBitmap(file).then(function (b) { return { source: b, w: b.width, h: b.height }; }, fallback);
    }
    return fallback();
    function fallback() {
      return new Promise(function (resolve, reject) {
        var u = URL.createObjectURL(file), im = new Image();
        im.onload = function () { URL.revokeObjectURL(u); resolve({ source: im, w: im.naturalWidth, h: im.naturalHeight }); };
        im.onerror = function () { URL.revokeObjectURL(u); reject(new Error("decode")); };
        im.src = u;
      });
    }
  }

  function loadFile(f) {
    if (!f || !/^image\//.test(f.type)) return show("Choose an image file");
    decode(f).then(function (img) {
      var s = Math.min(1, MAX_SRC / Math.max(img.w, img.h));
      var w = Math.max(1, Math.round(img.w * s)), h = Math.max(1, Math.round(img.h * s));
      var c = document.createElement("canvas"); c.width = w; c.height = h;
      var x = c.getContext("2d", { willReadFrequently: true });
      x.imageSmoothingEnabled = true; x.imageSmoothingQuality = "high";
      x.drawImage(img.source, 0, 0, w, h);
      src = makeSource(x.getImageData(0, 0, w, h).data, w, h);

      if (objUrl) URL.revokeObjectURL(objUrl);
      objUrl = URL.createObjectURL(f);
      if (preview) preview.src = objUrl;
      var fn = $("#fileName"); if (fn) fn.textContent = f.name || "image";
      var pc = $("#previewCard"); if (pc) pc.classList.remove("hidden");

      // a plain light background would turn into a solid block of dots → draw the dark parts instead
      var inv = $("#invert");
      if (inv) {
        var want = !!src.autoInvert;
        if (inv.checked !== want) { inv.checked = want; show(want ? "Dark-on-light picture — Invert turned on" : "Invert turned off"); }
      }
      draw();
      var tab = $('[data-tab="output"]'); if (tab) tab.click();
    }).catch(function () { show("Couldn't read that image"); });
  }

  function clearAll() {
    src = null; cancelAnimationFrame(raf);
    if (fileInput) fileInput.value = "";
    var pc = $("#previewCard"); if (pc) pc.classList.add("hidden");
    var msg = "Your Braille output will appear here.";
    [output, mini].forEach(function (p) { if (p) { p.textContent = msg; p.style.fontSize = ""; p.classList.remove("light"); } });
    if (stats) stats.textContent = "Ready";
    if (miniStats) miniStats.textContent = "Ready";
    var tab = $('[data-tab="convert"]'); if (tab) tab.click();
  }

  /* ───────────── controls ───────────── */
  on("#browseBtn", "click", function () { fileInput.click(); });
  on("#replaceBtn", "click", function () { fileInput.click(); });
  on("#clearBtn", "click", clearAll);
  on("#backBtn", "click", function () { window.scrollTo({ top: 0, behavior: "smooth" }); });
  on(fileInput, "change", function (e) { loadFile(e.target.files[0]); });

  var dragDepth = 0;
  window.addEventListener("dragenter", function (e) { e.preventDefault(); dragDepth++; if (drop) drop.classList.add("drag"); });
  window.addEventListener("dragover", function (e) { e.preventDefault(); });
  window.addEventListener("dragleave", function () { dragDepth = Math.max(0, dragDepth - 1); if (!dragDepth && drop) drop.classList.remove("drag"); });
  window.addEventListener("drop", function (e) {
    e.preventDefault(); dragDepth = 0; if (drop) drop.classList.remove("drag");
    var f = e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files[0];
    if (f) loadFile(f);
  });
  window.addEventListener("paste", function (e) {
    var items = (e.clipboardData && e.clipboardData.files) || [];
    for (var i = 0; i < items.length; i++) if (/^image\//.test(items[i].type)) { loadFile(items[i]); break; }
  });
  window.addEventListener("resize", fitAll);

  Object.keys(SLIDERS).forEach(function (key) {
    var s = SLIDERS[key], el = $(s.input), lb = $(s.label);
    if (!el) return;
    if (lb) lb.textContent = labelFor(key, el.value);
    el.addEventListener("input", function () { if (lb) lb.textContent = labelFor(key, el.value); schedule(); });
  });
  ["#invert", "#autoLevels", "#trim", "#fillBlank"].forEach(function (sel) { on(sel, "change", schedule); });

  function syncMode() {
    var tb = $("#thresholdBox");
    if (tb) tb.classList.toggle("hidden", mode !== "threshold" && mode !== "edges");
  }
  $$(".choice").forEach(function (b) {
    b.addEventListener("click", function () {
      $$(".choice").forEach(function (x) { x.classList.remove("active"); });
      b.classList.add("active");
      mode = MODE_ALIAS[b.dataset.mode] || b.dataset.mode;
      syncMode(); schedule();
    });
  });
  syncMode();

  on("#resetBtn", "click", function () {
    Object.keys(SLIDERS).forEach(function (key) {
      var s = SLIDERS[key], el = $(s.input), lb = $(s.label);
      if (key === "width" || !el) return;
      el.value = s.def; if (lb) lb.textContent = labelFor(key, s.def);
    });
    var al = $("#autoLevels"); if (al) al.checked = true;
    var tr = $("#trim"); if (tr) tr.checked = true;
    schedule(); show("Adjustments reset");
  });

  $$(".tools-tab").forEach(function (b) {
    b.addEventListener("click", function () {
      $$(".tools-tab").forEach(function (x) { x.classList.remove("active"); });
      $$(".panel").forEach(function (x) { x.classList.remove("active"); });
      b.classList.add("active");
      var p = $('[data-panel="' + b.dataset.tab + '"]'); if (p) p.classList.add("active");
      fitAll();
    });
  });

  function copyText(t) {
    var fallback = function () {
      var ta = document.createElement("textarea");
      ta.value = t; ta.style.cssText = "position:fixed;opacity:0;top:0;left:0";
      document.body.appendChild(ta); ta.select();
      var ok = false; try { ok = document.execCommand("copy"); } catch (e) { /* ignore */ }
      ta.remove(); return ok;
    };
    if (navigator.clipboard && window.isSecureContext) {
      return navigator.clipboard.writeText(t).then(function () { return true; }, function () { return fallback(); });
    }
    return Promise.resolve(fallback());
  }
  on("#copyBtn", "click", function () {
    if (!src) return show("Choose an image first");
    copyText(output.textContent).then(function (ok) { show(ok ? "Braille copied" : "Couldn't copy — select the text manually"); });
  });
  on("#downloadBtn", "click", function () {
    if (!src) return show("Choose an image first");
    var b = new Blob([output.textContent], { type: "text/plain;charset=utf-8" }), u = URL.createObjectURL(b), a = document.createElement("a");
    a.href = u; a.download = "braille.txt"; document.body.appendChild(a); a.click(); a.remove();
    setTimeout(function () { URL.revokeObjectURL(u); }, 1000);
  });

  function show(s) {
    if (!toast) return;
    toast.textContent = s; toast.classList.add("show");
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { toast.classList.remove("show"); }, 1800);
  }
})(typeof globalThis !== "undefined" ? globalThis : typeof self !== "undefined" ? self : this);
