/* Onfim PWA 0.5 — salva offline soltanto i file dell'app, NON gli appunti. */
const CACHE='onfim-shell-v0.5.0';
const FILES=['./','./index.html','./manifest.webmanifest','./favicon.png','./icon-192.png','./icon-512.png','./maskable-192.png','./maskable-512.png','./apple-touch-icon.png'];
const ROOT=new URL('./',self.location.href).pathname;
self.addEventListener('install',e=>{
  e.waitUntil(caches.open(CACHE).then(c=>c.addAll(FILES)).then(()=>self.skipWaiting()));
});
self.addEventListener('activate',e=>{
  e.waitUntil(caches.keys().then(keys=>Promise.all(keys.filter(k=>k.startsWith('onfim-shell-')&&k!==CACHE).map(k=>caches.delete(k)))).then(()=>self.clients.claim()));
});
self.addEventListener('fetch',e=>{
  if(e.request.method!=='GET')return;
  const url=new URL(e.request.url);
  if(url.origin!==self.location.origin||!url.pathname.startsWith(ROOT))return;
  if(e.request.mode==='navigate'){
    e.respondWith(fetch(e.request).then(res=>{
      if(res.ok){const cloned=res.clone();e.waitUntil(caches.open(CACHE).then(c=>c.put('./index.html',cloned)));}
      return res;
    }).catch(()=>caches.match('./index.html')));
    return;
  }
  e.respondWith(caches.match(e.request).then(hit=>hit||fetch(e.request)));
});
