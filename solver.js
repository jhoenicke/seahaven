
var a;a||(a=typeof Module !== 'undefined' ? Module : {});var p={},q;for(q in a)a.hasOwnProperty(q)&&(p[q]=a[q]);function aa(b,c){throw c;}var r="",t;r=self.location.href;r=0!==r.indexOf("blob:")?r.substr(0,r.lastIndexOf("/")+1):"";t=function(b){var c=new XMLHttpRequest;c.open("GET",b,!1);c.responseType="arraybuffer";c.send(null);return new Uint8Array(c.response)};var u=a.printErr||console.warn.bind(console);for(q in p)p.hasOwnProperty(q)&&(a[q]=p[q]);p=null;a.quit&&(aa=a.quit);
function ba(b){v||(v={});v[b]||(v[b]=1,u(b))}var v,y;a.wasmBinary&&(y=a.wasmBinary);var noExitRuntime=a.noExitRuntime||!0;"object"!==typeof WebAssembly&&z("no native wasm support detected");var ca,A=!1,B;function C(b,c){b||z("Assertion failed: "+c)}var D,E,da,ea,fa=[],ha=[],ia=[],ja=[],la=!1;function ma(){var b=a.preRun.shift();fa.unshift(b)}var F=0,na=null,G=null;a.preloadedImages={};a.preloadedAudios={};
function z(b){if(a.onAbort)a.onAbort(b);u(b);A=!0;B=1;throw new WebAssembly.RuntimeError("abort("+b+"). Build with -s ASSERTIONS=1 for more info.");}function oa(){var b=H;return String.prototype.startsWith?b.startsWith("data:application/octet-stream;base64,"):0===b.indexOf("data:application/octet-stream;base64,")}var H="solver.wasm";if(!oa()){var pa=H;H=a.locateFile?a.locateFile(pa,r):r+pa}
function qa(){var b=H;try{if(b==H&&y)return new Uint8Array(y);if(t)return t(b);throw"both async and sync fetching of the wasm failed";}catch(c){z(c)}}function ra(){return y||"function"!==typeof fetch?Promise.resolve().then(function(){return qa()}):fetch(H,{credentials:"same-origin"}).then(function(b){if(!b.ok)throw"failed to load wasm binary file at '"+H+"'";return b.arrayBuffer()}).catch(function(){return qa()})}
function I(b){for(;0<b.length;){var c=b.shift();if("function"==typeof c)c(a);else{var f=c.s;"number"===typeof f?void 0===c.l?ea.get(f)():ea.get(f)(c.l):f(void 0===c.l?null:c.l)}}}
function sa(b,c){K=b;L=c;if(M)if(ta||(ta=!0),0==b)N=function(){var e=Math.max(0,ua+c-va())|0;setTimeout(O,e)};else if(1==b)N=function(){wa(O)};else if(2==b){if("undefined"===typeof setImmediate){var f=[];addEventListener("message",function(e){if("setimmediate"===e.data||"setimmediate"===e.data.target)e.stopPropagation(),f.shift()()},!0);setImmediate=function(e){f.push(e);void 0===a.setImmediates&&(a.setImmediates=[]);a.setImmediates.push(e);postMessage({target:"setimmediate"})}}N=function(){setImmediate(O)}}}
var va;va=function(){return performance.now()};
function xa(b){function c(){if(f<P){if(!noExitRuntime)try{var e=B;B=e;if(!noExitRuntime){if(a.onExit)a.onExit(e);A=!0}aa(e,new ya(e))}catch(d){if(!(d instanceof ya))throw d;}return!1}return!0}C(!M,"emscripten_set_main_loop: there can only be one main loop function at once: call emscripten_cancel_main_loop to cancel the previous one before setting a new one with different parameters.");M=b;var f=P;ta=!1;O=function(){if(!A)if(0<za.length){var e=Date.now(),d=za.shift();d.s(d.l);if(Q){var g=Q,h=0==g%
1?g-1:Math.floor(g);Q=d.C?h:(8*g+(h+.5))/9}console.log('main loop blocker "'+d.name+'" took '+(Date.now()-e)+" ms");a.setStatus&&(e=a.statusMessage||"Please wait...",d=Q,g=Aa.F,d?d<g?a.setStatus(e+" ("+(g-d)+"/"+g+")"):a.setStatus(e):a.setStatus(""));c()&&setTimeout(O,0)}else c()&&(Ba=Ba+1|0,1==K&&1<L&&0!=Ba%L?N():(0==K&&(ua=va()),A||a.preMainLoop&&!1===a.preMainLoop()||(Ca(b),a.postMainLoop&&a.postMainLoop()),c()&&("object"===typeof SDL&&SDL.audio&&SDL.audio.v&&SDL.audio.v(),N())))}}
function Ca(b){try{b()}catch(c){if(!(c instanceof ya)&&"unwind"!==c)throw c&&"object"===typeof c&&c.stack&&u("exception thrown: "+[c,c.stack]),c;}}var ta=!1,N=null,P=0,M=null,K=0,L=0,Ba=0,za=[],Aa={},ua,O,Q,R=!1,Da=!1,Ea=[];
function Fa(){function b(){Da=document.pointerLockElement===a.canvas||document.mozPointerLockElement===a.canvas||document.webkitPointerLockElement===a.canvas||document.msPointerLockElement===a.canvas}a.preloadPlugins||(a.preloadPlugins=[]);if(!Ga){Ga=!0;try{S=!0}catch(f){S=!1,console.log("warning: no blob constructor, cannot create blobs with mimetypes")}Ha="undefined"!=typeof MozBlobBuilder?MozBlobBuilder:"undefined"!=typeof WebKitBlobBuilder?WebKitBlobBuilder:S?null:console.log("warning: no BlobBuilder");
T="undefined"!=typeof window?window.URL?window.URL:window.webkitURL:void 0;a.o||"undefined"!==typeof T||(console.log("warning: Browser does not support creating object URLs. Built-in browser image decoding will not be available."),a.o=!0);a.preloadPlugins.push({canHandle:function(f){return!a.o&&/\.(jpg|jpeg|png|bmp)$/i.test(f)},handle:function(f,e,d,g){var h=null;if(S)try{h=new Blob([f],{type:Ia(e)}),h.size!==f.length&&(h=new Blob([(new Uint8Array(f)).buffer],{type:Ia(e)}))}catch(m){ba("Blob constructor present but fails: "+
m+"; falling back to blob builder")}h||(h=new Ha,h.append((new Uint8Array(f)).buffer),h=h.getBlob());var k=T.createObjectURL(h),l=new Image;l.onload=function(){C(l.complete,"Image "+e+" could not be decoded");var m=document.createElement("canvas");m.width=l.width;m.height=l.height;m.getContext("2d").drawImage(l,0,0);a.preloadedImages[e]=m;T.revokeObjectURL(k);d&&d(f)};l.onerror=function(){console.log("Image "+k+" could not be decoded");g&&g()};l.src=k}});a.preloadPlugins.push({canHandle:function(f){return!a.I&&
f.substr(-4)in{".ogg":1,".wav":1,".mp3":1}},handle:function(f,e,d,g){function h(n){l||(l=!0,a.preloadedAudios[e]=n,d&&d(f))}function k(){l||(l=!0,a.preloadedAudios[e]=new Audio,g&&g())}var l=!1;if(S){try{var m=new Blob([f],{type:Ia(e)})}catch(n){return k()}m=T.createObjectURL(m);var w=new Audio;w.addEventListener("canplaythrough",function(){h(w)},!1);w.onerror=function(){if(!l){console.log("warning: browser could not fully decode audio "+e+", trying slower base64 approach");for(var n="",J=0,x=0,ka=
0;ka<f.length;ka++)for(J=J<<8|f[ka],x+=8;6<=x;){var Pa=J>>x-6&63;x-=6;n+="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"[Pa]}2==x?(n+="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"[(J&3)<<4],n+="=="):4==x&&(n+="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"[(J&15)<<2],n+="=");w.src="data:audio/x-"+e.substr(-3)+";base64,"+n;h(w)}};w.src=m;Ja(function(){h(w)})}else return k()}});var c=a.canvas;c&&(c.requestPointerLock=c.requestPointerLock||c.mozRequestPointerLock||
c.webkitRequestPointerLock||c.msRequestPointerLock||function(){},c.exitPointerLock=document.exitPointerLock||document.mozExitPointerLock||document.webkitExitPointerLock||document.msExitPointerLock||function(){},c.exitPointerLock=c.exitPointerLock.bind(document),document.addEventListener("pointerlockchange",b,!1),document.addEventListener("mozpointerlockchange",b,!1),document.addEventListener("webkitpointerlockchange",b,!1),document.addEventListener("mspointerlockchange",b,!1),a.elementPointerLock&&
c.addEventListener("click",function(f){!Da&&a.canvas.requestPointerLock&&(a.canvas.requestPointerLock(),f.preventDefault())},!1))}}
function Ka(b,c,f,e){if(c&&a.m&&b==a.canvas)return a.m;var d;if(c){var g={antialias:!1,alpha:!1,G:1};if(e)for(var h in e)g[h]=e[h];if("undefined"!==typeof GL&&(d=GL.D(b,g)))var k=GL.getContext(d).B}else k=b.getContext("2d");if(!k)return null;f&&(c||C("undefined"===typeof GLctx,"cannot set in module if GLctx is used, but we are a non-GL context that would replace it"),a.m=k,c&&GL.H(d),a.J=c,Ea.forEach(function(l){l()}),Fa());return k}var La=!1,U=void 0,V=void 0;
function Ma(b,c){function f(){R=!1;var g=e.parentNode;(document.fullscreenElement||document.mozFullScreenElement||document.msFullscreenElement||document.webkitFullscreenElement||document.webkitCurrentFullScreenElement)===g?(e.exitFullscreen=Na,U&&e.requestPointerLock(),R=!0,V?("undefined"!=typeof SDL&&(E[SDL.screen>>2]=da[SDL.screen>>2]|8388608),W(a.canvas),Oa()):W(e)):(g.parentNode.insertBefore(e,g),g.parentNode.removeChild(g),V?("undefined"!=typeof SDL&&(E[SDL.screen>>2]=da[SDL.screen>>2]&-8388609),
W(a.canvas),Oa()):W(e));if(a.onFullScreen)a.onFullScreen(R);if(a.onFullscreen)a.onFullscreen(R)}U=b;V=c;"undefined"===typeof U&&(U=!0);"undefined"===typeof V&&(V=!1);var e=a.canvas;La||(La=!0,document.addEventListener("fullscreenchange",f,!1),document.addEventListener("mozfullscreenchange",f,!1),document.addEventListener("webkitfullscreenchange",f,!1),document.addEventListener("MSFullscreenChange",f,!1));var d=document.createElement("div");e.parentNode.insertBefore(d,e);d.appendChild(e);d.requestFullscreen=
d.requestFullscreen||d.mozRequestFullScreen||d.msRequestFullscreen||(d.webkitRequestFullscreen?function(){d.webkitRequestFullscreen(Element.ALLOW_KEYBOARD_INPUT)}:null)||(d.webkitRequestFullScreen?function(){d.webkitRequestFullScreen(Element.ALLOW_KEYBOARD_INPUT)}:null);d.requestFullscreen()}
function Na(){if(!R)return!1;(document.exitFullscreen||document.cancelFullScreen||document.mozCancelFullScreen||document.msExitFullscreen||document.webkitCancelFullScreen||function(){}).apply(document,[]);return!0}var X=0;function wa(b){if("function"===typeof requestAnimationFrame)requestAnimationFrame(b);else{var c=Date.now();if(0===X)X=c+1E3/60;else for(;c+2>=X;)X+=1E3/60;setTimeout(b,Math.max(X-c,0))}}function Ja(b){setTimeout(function(){Ca(b)},1E4)}
function Ia(b){return{jpg:"image/jpeg",jpeg:"image/jpeg",png:"image/png",bmp:"image/bmp",ogg:"audio/ogg",wav:"audio/wav",mp3:"audio/mpeg"}[b.substr(b.lastIndexOf(".")+1)]}var Qa=[];function Oa(){var b=a.canvas;Qa.forEach(function(c){c(b.width,b.height)})}
function W(b,c,f){c&&f?(b.A=c,b.u=f):(c=b.A,f=b.u);var e=c,d=f;a.forcedAspectRatio&&0<a.forcedAspectRatio&&(e/d<a.forcedAspectRatio?e=Math.round(d*a.forcedAspectRatio):d=Math.round(e/a.forcedAspectRatio));if((document.fullscreenElement||document.mozFullScreenElement||document.msFullscreenElement||document.webkitFullscreenElement||document.webkitCurrentFullScreenElement)===b.parentNode&&"undefined"!=typeof screen){var g=Math.min(screen.width/e,screen.height/d);e=Math.round(e*g);d=Math.round(d*g)}V?
(b.width!=e&&(b.width=e),b.height!=d&&(b.height=d),"undefined"!=typeof b.style&&(b.style.removeProperty("width"),b.style.removeProperty("height"))):(b.width!=c&&(b.width=c),b.height!=f&&(b.height=f),"undefined"!=typeof b.style&&(e!=c||d!=f?(b.style.setProperty("width",e+"px","important"),b.style.setProperty("height",d+"px","important")):(b.style.removeProperty("width"),b.style.removeProperty("height"))))}var Ga,S,Ha,T;a.requestFullscreen=function(b,c){Ma(b,c)};a.requestAnimationFrame=function(b){wa(b)};
a.setCanvasSize=function(b,c,f){W(a.canvas,b,c);f||Oa()};a.pauseMainLoop=function(){N=null;P++};a.resumeMainLoop=function(){P++;var b=K,c=L,f=M;M=null;xa(f);sa(b,c);N()};a.getUserMedia=function(){window.getUserMedia||(window.getUserMedia=navigator.getUserMedia||navigator.mozGetUserMedia);window.getUserMedia(void 0)};a.createContext=function(b,c,f,e){return Ka(b,c,f,e)};
var Sa={a:function(){z("OOM")},b:function(b,c){if(Y)throw"already responded with final response!";Y=!0;c={callbackId:Ra,finalResponse:!0,data:b?new Uint8Array(D.subarray(b,b+c)):0};b?postMessage(c,[c.data.buffer]):postMessage(c)},c:function(b,c){if(Y)throw"already responded with final response!";c={callbackId:Ra,finalResponse:!1,data:b?new Uint8Array(D.subarray(b,b+c)):0};b?postMessage(c,[c.data.buffer]):postMessage(c)}};
(function(){function b(d){a.asm=d.exports;ca=a.asm.d;d=ca.buffer;a.HEAP8=new Int8Array(d);a.HEAP16=new Int16Array(d);a.HEAP32=E=new Int32Array(d);a.HEAPU8=D=new Uint8Array(d);a.HEAPU16=new Uint16Array(d);a.HEAPU32=da=new Uint32Array(d);a.HEAPF32=new Float32Array(d);a.HEAPF64=new Float64Array(d);ea=a.asm.j;ha.unshift(a.asm.e);F--;a.monitorRunDependencies&&a.monitorRunDependencies(F);0==F&&(null!==na&&(clearInterval(na),na=null),G&&(d=G,G=null,d()))}function c(d){b(d.instance)}function f(d){return ra().then(function(g){return WebAssembly.instantiate(g,
e)}).then(d,function(g){u("failed to asynchronously prepare wasm: "+g);z(g)})}var e={a:Sa};F++;a.monitorRunDependencies&&a.monitorRunDependencies(F);if(a.instantiateWasm)try{return a.instantiateWasm(e,b)}catch(d){return u("Module.instantiateWasm callback failed with error: "+d),!1}(function(){return y||"function"!==typeof WebAssembly.instantiateStreaming||oa()||"function"!==typeof fetch?f(c):fetch(H,{credentials:"same-origin"}).then(function(d){return WebAssembly.instantiateStreaming(d,e).then(c,
function(g){u("wasm streaming compile failed: "+g);u("falling back to ArrayBuffer instantiation");return f(c)})})})();return{}})();a.___wasm_call_ctors=function(){return(a.___wasm_call_ctors=a.asm.e).apply(null,arguments)};a._initcard=function(){return(a._initcard=a.asm.f).apply(null,arguments)};a._solve=function(){return(a._solve=a.asm.g).apply(null,arguments)};
var Ta=a._malloc=function(){return(Ta=a._malloc=a.asm.h).apply(null,arguments)},Ua=a._free=function(){return(Ua=a._free=a.asm.i).apply(null,arguments)},Z;function ya(b){this.name="ExitStatus";this.message="Program terminated with exit("+b+")";this.status=b}G=function Va(){Z||Wa();Z||(G=Va)};
function Wa(){function b(){if(!Z&&(Z=!0,a.calledRun=!0,!A)){la=!0;I(ha);I(ia);if(a.onRuntimeInitialized)a.onRuntimeInitialized();if(a.postRun)for("function"==typeof a.postRun&&(a.postRun=[a.postRun]);a.postRun.length;){var c=a.postRun.shift();ja.unshift(c)}I(ja)}}if(!(0<F)){if(a.preRun)for("function"==typeof a.preRun&&(a.preRun=[a.preRun]);a.preRun.length;)ma();I(fa);0<F||(a.setStatus?(a.setStatus("Running..."),setTimeout(function(){setTimeout(function(){a.setStatus("")},1);b()},1)):b())}}a.run=Wa;
if(a.preInit)for("function"==typeof a.preInit&&(a.preInit=[a.preInit]);0<a.preInit.length;)a.preInit.pop()();Wa();var Y=!1,Ra=-1;
(function(){function b(){if(f&&la){var g=f;f=null;g.forEach(function(h){onmessage(h)})}}function c(){b();f&&setTimeout(c,100)}var f=null,e=0,d=0;onmessage=function(g){if(la){b();var h=a["_"+g.data.funcName];if(!h)throw"invalid worker function to call: "+g.data.funcName;var k=g.data.data;if(k){k.byteLength||(k=new Uint8Array(k));if(!e||d<k.length)e&&Ua(e),d=k.length,e=Ta(k.length);D.set(k,e)}Y=!1;Ra=g.data.callbackId;k?h(e,k.length):h(0,0)}else f||(f=[],setTimeout(c,100)),f.push(g)}})();
