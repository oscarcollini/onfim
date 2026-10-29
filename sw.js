/* onfim Lite 0.9.0 bozza interfaccia — cache solo dell'applicazione, mai degli appunti */
const CACHE='onfim-shell-lite-v0.9.0-promemoria-ricorrenze-3';
const ASSETS=['./index.html','./manifest.webmanifest','./favicon.png','./icon-192.png','./icon-512.png','./maskable-192.png','./maskable-512.png','./apple-touch-icon.png'];
const ROOT=new URL('./',self.location.href).pathname;
self.addEventListener('install',event=>{event.waitUntil(caches.open(CACHE).then(c=>c.addAll(ASSETS)).then(()=>self.skipWaiting()));});
self.addEventListener('activate',event=>{event.waitUntil(caches.keys().then(keys=>Promise.all(keys.filter(k=>k.startsWith('onfim-shell-')&&k!==CACHE).map(k=>caches.delete(k)))).then(()=>self.clients.claim()));});
self.addEventListener('fetch',event=>{
  if(event.request.method!=='GET')return;
  const url=new URL(event.request.url);
  if(url.origin!==self.location.origin||!url.pathname.startsWith(ROOT))return;
  if(url.pathname.endsWith('/manifest.webmanifest')){
    // Per i nuovi installatori la versione corrente del manifest deve prevalere sulla cache.
    event.respondWith(fetch(event.request).then(r=>r.ok?r:Promise.reject(new Error('manifest non disponibile')))
      .catch(()=>caches.match('./manifest.webmanifest')));
  }else if(event.request.mode==='navigate'){
    event.respondWith(fetch(event.request).then(response=>{
      if(response.ok && !url.search){const copy=response.clone();event.waitUntil(caches.open(CACHE).then(c=>c.put('./index.html',copy)));}
      return response;
    }).catch(()=>caches.match('./index.html')));
  }else{event.respondWith(caches.match(event.request).then(hit=>hit||fetch(event.request)));}
});
