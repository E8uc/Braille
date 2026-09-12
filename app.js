const $=s=>document.querySelector(s), $$=s=>document.querySelectorAll(s);
let image=null,mode="standard";
const fileInput=$("#fileInput"),drop=$("#dropZone"),preview=$("#preview"),output=$("#output"),width=$("#widthRange"),widthValue=$("#widthValue"),invert=$("#invert"),stats=$("#stats"),toast=$("#toast");
$("#browseBtn").onclick=()=>fileInput.click();$("#replaceBtn").onclick=()=>fileInput.click();$("#newImageBtn").onclick=()=>fileInput.click();$("#clearBtn").onclick=clearAll;$("#backBtn").onclick=()=>window.scrollTo({top:0,behavior:"smooth"});
fileInput.onchange=e=>loadFile(e.target.files[0]);
["dragenter","dragover"].forEach(x=>drop.addEventListener(x,e=>{e.preventDefault();drop.classList.add("drag")}));
["dragleave","drop"].forEach(x=>drop.addEventListener(x,e=>{e.preventDefault();drop.classList.remove("drag")}));
drop.addEventListener("drop",e=>loadFile(e.dataTransfer.files[0]));
width.oninput=()=>{widthValue.textContent=width.value;if(image)render()};
invert.onchange=()=>{if(image)render()};
$$(".choice").forEach(b=>b.onclick=()=>{$$(".choice").forEach(x=>x.classList.remove("active"));b.classList.add("active");mode=b.dataset.mode;if(image)render()});
$$(".tools-tab").forEach(b=>b.onclick=()=>{$$(".tools-tab").forEach(x=>x.classList.remove("active"));$$(".panel").forEach(x=>x.classList.remove("active"));b.classList.add("active");$(`[data-panel="${b.dataset.tab}"]`).classList.add("active")});
$("#openSidebar").onclick=()=>{$("#sidebar").classList.add("open");$("#scrim").classList.add("open")};
$("#closeSidebar").onclick=$("#scrim").onclick=()=>{$("#sidebar").classList.remove("open");$("#scrim").classList.remove("open")};
$("#themeBtn").onclick=()=>show("Theme controls can be added here");
$("#copyBtn").onclick=async()=>{if(!image)return;await navigator.clipboard.writeText(output.textContent);show("Braille copied")};
$("#downloadBtn").onclick=()=>{if(!image)return;const b=new Blob([output.textContent],{type:"text/plain"}),u=URL.createObjectURL(b),a=document.createElement("a");a.href=u;a.download="braille.txt";a.click();URL.revokeObjectURL(u)};
function loadFile(f){if(!f||!f.type.startsWith("image/"))return show("Choose an image file");const r=new FileReader();r.onload=()=>{const im=new Image();im.onload=()=>{image=im;preview.src=r.result;$("#fileName").textContent=f.name;$("#previewCard").classList.remove("hidden");render();document.querySelector('[data-tab="output"]').click()};im.src=r.result};r.readAsDataURL(f)}
function gray(d){const a=new Float32Array(d.length/4);for(let i=0,p=0;i<d.length;i+=4,p++)a[p]=.2126*d[i]+.7152*d[i+1]+.0722*d[i+2];return a}
function dither(a,w,h){a=new Float32Array(a);const at=(x,y)=>y*w+x;for(let y=0;y<h;y++)for(let x=0;x<w;x++){let i=at(x,y),old=a[i],n=old<128?0:255,e=old-n;a[i]=n;if(x+1<w)a[at(x+1,y)]+=e*7/16;if(y+1<h&&x)a[at(x-1,y+1)]+=e*3/16;if(y+1<h)a[at(x,y+1)]+=e*5/16;if(y+1<h&&x+1<w)a[at(x+1,y+1)]+=e/16}return a}
const dots=[[0,0,1],[0,1,2],[0,2,4],[1,0,8],[1,1,16],[1,2,32],[0,3,64],[1,3,128]];
function render(){const w=+width.value, h=Math.max(1,Math.round(w*image.height/image.width/2)),pw=w*2,ph=h*4,c=document.createElement("canvas");c.width=pw;c.height=ph;const x=c.getContext("2d",{willReadFrequently:true});x.drawImage(image,0,0,pw,ph);let a=gray(x.getImageData(0,0,pw,ph).data);if(mode==="dither")a=dither(a,pw,ph);let s="";for(let y=0;y<ph;y+=4){for(let xx=0;xx<pw;xx+=2){let bits=0;for(const[dx,dy,bit]of dots){let on=(a[(y+dy)*pw+xx+dx]??255)<128;if(invert.checked)on=!on;if(on)bits|=bit}s+=String.fromCodePoint(0x2800+bits)}if(y+4<ph)s+="\n"}output.textContent=s;stats.textContent=`${w} × ${h} · ${mode}`}
function clearAll(){image=null;fileInput.value="";$("#previewCard").classList.add("hidden");output.textContent="Your Braille output will appear here.";stats.textContent="Ready";document.querySelector('[data-tab="convert"]').click()}
let timer;function show(s){toast.textContent=s;toast.classList.add("show");clearTimeout(timer);timer=setTimeout(()=>toast.classList.remove("show"),1600)}
