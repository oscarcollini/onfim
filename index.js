
(()=>{'use strict';
const $=id=>document.getElementById(id);const DB='appunti-prototipo-v1',STORE='notes',SNAPSTORE='localSnapshots',VERSION='0.8.18.1';
const LAST_EXPORT_KEY='onfim-last-json-export-v06',LAST_CHANGE_KEY='onfim-last-data-change-v06',BACKUP_MAX_AGE_DAYS=7;let db=null,note=null,images=[],photoMarks=[],drawData='',drawn=false,pen='#202a34',erasing=false,painting=false,last=null,saveTimer=0,dirty=false,saving=Promise.resolve(),knownTags=[],unlocked=false,audioClips=[],recorder=null,audioFinalizing=false,audioStarting=false,micStream=null,audioPieces=[],audioTick=null,audioStarted=0,audioPausedAt=0,audioPauseTotal=0,readId=null,editorFrom='list',reminderTimers=new Map(),selectionRange=null,toastTimer=0;
let textHistory=[],textHistoryAt=0,textHistoryTimer=0,drawUndoHistory=[],drawRedoHistory=[],drawLoadGeneration=0;
function toast(msg){const el=$('toast');el.textContent=msg;el.classList.add('show');clearTimeout(toastTimer);toastTimer=setTimeout(()=>el.classList.remove('show'),2600);}
function database(){return new Promise((res,rej)=>{const r=indexedDB.open(DB,1);r.onupgradeneeded=()=>{if(!r.result.objectStoreNames.contains(STORE))r.result.createObjectStore(STORE,{keyPath:'id'});};r.onsuccess=()=>{db=r.result;res(db)};r.onerror=()=>rej(r.error);});}
function allNotes(){return new Promise((res,rej)=>{const r=db.transaction(STORE).objectStore(STORE).getAll();r.onsuccess=()=>res(r.result||[]);r.onerror=()=>rej(r.error);});}
function putNote(n){return new Promise((res,rej)=>{const tx=db.transaction(STORE,'readwrite');tx.objectStore(STORE).put(n);tx.oncomplete=()=>{recordDataChange();res();};tx.onerror=()=>rej(tx.error||new Error('Errore salvataggio'));tx.onabort=()=>rej(tx.error||new Error('Salvataggio annullato'));});}
function removeNote(id){return removeNotesBatch([id]);}
function removeNotesBatch(ids){return new Promise((res,rej)=>{const tx=db.transaction(STORE,'readwrite'),store=tx.objectStore(STORE);for(const id of ids)store.delete(id);tx.oncomplete=()=>{recordDataChange();res();};tx.onerror=()=>rej(tx.error||new Error('Errore eliminazione definitiva'));tx.onabort=()=>rej(tx.error||new Error('Eliminazione definitiva annullata'));});}
function putNotesBatch(notes){return new Promise((res,rej)=>{const tx=db.transaction(STORE,'readwrite'),store=tx.objectStore(STORE);for(const n of notes)store.put(n);tx.oncomplete=()=>{recordDataChange();res();};tx.onerror=()=>rej(tx.error||new Error('Errore aggiornamento sequenza'));tx.onabort=()=>rej(tx.error||new Error('Aggiornamento sequenza annullato'));});}
// Una catena e' un appunto radice con piu' note figlie. Solo le figlie
// hanno chainRoot e chainOrder; nessuna migrazione delle vecchie note.
function chainRootOf(n){return typeof n?.chainRoot==='string'&&n.chainRoot?n.chainRoot:n.id;}
function chainMembers(n,all){const rootId=chainRootOf(n),root=all.find(x=>x.id===rootId);if(!root||root.reserved!==n.reserved||!!root.deletedAt!==!!n.deletedAt)return [n];const followers=all.filter(x=>x.chainRoot===rootId&&x.id!==rootId&&x.reserved===root.reserved&&!!x.deletedAt===!!root.deletedAt).sort((a,b)=>(Number(a.chainOrder)||1)-(Number(b.chainOrder)||1)||(a.created||0)-(b.created||0));return [root,...followers];}
function groupRootFor(n,all){const root=all.find(x=>x.id===chainRootOf(n));return root&&root.reserved===n.reserved&&!!root.deletedAt===!!n.deletedAt?root:n;}
async function unlinkChildrenOf(rootId){const all=await allNotes(),children=all.filter(n=>n.chainRoot===rootId);if(children.length)await putNotesBatch(children.map(n=>{const x={...n};delete x.chainRoot;delete x.chainOrder;return x;}));}
// Spostamento reversibile: una nota composta va nel Cestino come insieme.
// La data e l'ID dell'operazione consentono un ripristino atomico delle parti.
async function safeDeleteNote(n){
  const all=await allNotes(),current=all.find(x=>x.id===n.id&&!x.deletedAt);
  if(!current)return false;
  const members=current.chainRoot?[current]:chainMembers(current,all);
  const now=Date.now(),batchId=uid();
  await putNotesBatch(members.map(x=>({...x,deletedAt:now,trashBatchId:batchId,updated:now})));
  return members.length;
}
function confirmMoveToTrash(count=1){return confirm(count>1?'Spostare nel Cestino questo appunto e tutte le '+count+' parti collegate? Potrai ripristinarle insieme.':'Spostare questo appunto nel Cestino? Potrai ripristinarlo.');}
// Una sola transazione per ripristinare, non lascia catene parziali.
async function restoreTrashBatch(group){
  const all=await allNotes(),ids=new Set(group.map(x=>x.id));
  const now=Date.now();
  const restored=group.map(x=>{const n={...x,updated:now};delete n.deletedAt;delete n.trashBatchId;
    if(n.chainRoot){const root=all.find(a=>a.id===n.chainRoot);if(!root||(!ids.has(root.id)&&!!root.deletedAt)||root?.reserved!==n.reserved){delete n.chainRoot;delete n.chainOrder;}}
    return n;
  });
  await putNotesBatch(restored);
}
// La cancellazione dal Cestino è invece definitiva.
async function emptyTrashNow(){const trash=(await allNotes()).filter(x=>x.deletedAt);if(trash.length)await removeNotesBatch(trash.map(x=>x.id));return trash.length;}


function confirmDeleteTwice(){return confirmMoveToTrash();}
function uid(){return typeof crypto!=='undefined'&&crypto.randomUUID?crypto.randomUUID():Date.now().toString(36)+'-'+Math.random().toString(36).slice(2)}
// Estrazione del testo con separatori reali fra paragrafi e voci dell'elenco.
// textContent da solo unisce #hashtag e la prima voce del successivo <ul>/<ol>.
function txt(html){
  const root=document.createElement('div');root.innerHTML=html||'';
  const blocks=new Set(['DIV','P','UL','OL','LI','BLOCKQUOTE']);
  let result='';
  function newline(){if(result&&!result.endsWith('\n'))result+='\n';}
  function visit(node){
    if(node.nodeType===3){result+=node.nodeValue;return;}
    if(node.nodeType!==1)return;
    if(node.tagName==='BR'){newline();return;}
    const block=blocks.has(node.tagName);
    if(block)newline();
    for(const child of node.childNodes)visit(child);
    if(block)newline();
  }
  for(const child of root.childNodes)visit(child);
  return result;
}
function safeText(t){return String(t||'').replace(/[\u0000-\u001f]/g,' ');}
// Un solo filtro per l'HTML delle note: conserva esclusivamente link web/email sicuri.
function onfimSafeLinkHref(raw){
  const value=String(raw||'').trim();
  if(/^https?:\/\//i.test(value)){
    try{const url=new URL(value);return /^(https?:)$/.test(url.protocol)&&url.hostname?url.href:'';}catch{return '';}
  }
  if(/^mailto:/i.test(value)){
    try{const address=decodeURIComponent(value.slice(7).split('?')[0]);
      return /^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}$/.test(address)&&!/[\s<>"'`]/.test(value)?value:'';
    }catch{return '';}
  }
  return '';
}
function sanitizeHTML(markup){
  const tpl=document.createElement('template');tpl.innerHTML=String(markup||'');
  const allowed=new Set(['B','STRONG','I','EM','U','S','STRIKE','DEL','CODE','SPAN','FONT','P','DIV','BR','UL','OL','LI','BLOCKQUOTE','A']);
  const forbidden=new Set(['SCRIPT','STYLE','IFRAME','OBJECT','SVG','MATH','IMG','VIDEO','AUDIO','INPUT','FORM']);
  const safeColor=/^(#[0-9a-f]{3,8}|rgba?\([\d\s,.%]+\)|[a-z]{3,20})$/i;
  function walk(parent){
    for(const el of [...parent.children]){
      if(forbidden.has(el.tagName)){el.remove();continue;}
      walk(el);
      if(!allowed.has(el.tagName)){el.replaceWith(...el.childNodes);continue;}
      const oldColor=el.getAttribute('color')||el.style.color,oldBackground=el.style.backgroundColor;
      const href=el.tagName==='A'?onfimSafeLinkHref(el.getAttribute('href')):'';
      for(const attr of [...el.attributes])el.removeAttribute(attr.name);
      if(oldColor&&safeColor.test(oldColor))el.style.color=oldColor;
      if(oldBackground&&safeColor.test(oldBackground))el.style.backgroundColor=oldBackground;
      if(el.tagName==='A'){if(href){el.setAttribute('href',href);el.setAttribute('target','_blank');el.setAttribute('rel','noopener noreferrer');}else el.replaceWith(...el.childNodes);}
    }
  }
  walk(tpl.content);return tpl.innerHTML;
}
// Link automatici solo nella lettura e nell'HTML condiviso: nell'editor il testo resta modificabile.
function onfimLinkifyHTML(markup){
  const root=document.createElement('div');root.innerHTML=String(markup||'');
  const walker=document.createTreeWalker(root,NodeFilter.SHOW_TEXT);
  const nodes=[];let node;
  while((node=walker.nextNode()))if(node.parentElement&&!node.parentElement.closest('a'))nodes.push(node);
  const pattern=/https?:\/\/[^\s<>"'`]+|@[0-9]{1,2}(?:\.[0-9]{1,6})?[NS],[0-9]{1,3}(?:\.[0-9]{1,6})?[EW]|[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}/gi;
  for(const textNode of nodes){
    const source=textNode.nodeValue;pattern.lastIndex=0;
    if(!pattern.test(source))continue;
    pattern.lastIndex=0;
    const out=document.createDocumentFragment();let from=0,match;
    while((match=pattern.exec(source))){
      if(match.index>from)out.append(document.createTextNode(source.slice(from,match.index)));
      const whole=match[0];let candidate=whole;
      // Non rendere parte del collegamento la punteggiatura di fine frase.
      while(/[.,;:!?\])]+$/.test(candidate)){
        const last=candidate.slice(-1);
        if(last===')'&&(candidate.match(/\(/g)||[]).length>=(candidate.match(/\)/g)||[]).length)break;
        if(last===']'&&(candidate.match(/\[/g)||[]).length>=(candidate.match(/\]/g)||[]).length)break;
        candidate=candidate.slice(0,-1);
      }
      const geo=onfimFindRefs(candidate,'point').find(r=>r.start===0&&r.end===candidate.length);
      const href=geo?'https://www.openstreetmap.org/?mlat='+geo.lat+'&mlon='+geo.lon+'#map=16/'+geo.lat+'/'+geo.lon:onfimSafeLinkHref(/^https?:\/\//i.test(candidate)?candidate:'mailto:'+candidate);
      if(candidate&&href){const link=document.createElement('a');link.href=href;link.target='_blank';link.rel='noopener noreferrer';link.textContent=candidate;if(geo){link.className='onfim-ref-location';link.title='Apri la posizione sulla mappa';}out.append(link);}
      else out.append(document.createTextNode(candidate));
      if(candidate.length<whole.length)out.append(document.createTextNode(whole.slice(candidate.length)));
      from=match.index+whole.length;
    }
    if(from<source.length)out.append(document.createTextNode(source.slice(from)));
    textNode.replaceWith(out);
  }
  return root.innerHTML;
}
function view(id){
  if(id!=='editView'){document.body.classList.remove('onfim-drawing','onfim-drawing-full');$('drawTab').classList.remove('expanded');$('expandDrawing').classList.remove('hidden');$('closeExpanded').classList.add('hidden');}
  else {document.body.classList.toggle('onfim-drawing',$('drawTab').classList.contains('shown'));}
  if(id!=='readView')document.querySelectorAll('#readView audio').forEach(a=>a.pause());
  if(id!=='editView')document.querySelectorAll('#audioGallery audio').forEach(a=>a.pause());
  const home=id==='listView';
  ['listView','readView','editView','settingsView','trashView'].forEach(x=>$(x).classList.toggle('show',x===id));
  $('addButton').classList.toggle('hidden',!home);
  $('topBrand').classList.toggle('hidden',!home);
  $('topBack').classList.toggle('hidden',home);
  $('topBarTitle').classList.toggle('hidden',home);
  $('topBarTitle').textContent=({readView:'Appunto',editView:'Modifica',settingsView:'Impostazioni',trashView:'Cestino'})[id]||'';
  $('settingsButton').classList.toggle('hidden',!home);
  window.scrollTo(0,0);
  if(id==='editView'&&$('drawTab').classList.contains('shown'))requestAnimationFrame(fitDrawingCanvas);
}
// Gli hashtag sono parte del testo: Unicode, senza distinzione fra maiuscole/minuscole.
// Le vecchie etichette restano leggibili e vengono trascritte nel testo quando la nota viene modificata.
function normalizedTag(v){return String(v||'').normalize('NFC').toLocaleLowerCase('it-IT');}
function extractHashtags(content){
  const text=String(content||'');
  // #🍸 #🏔️ #👩🏽‍💻 #🇮🇹; hyphens in text remain allowed.
  const pattern=/(^|[^\p{L}\p{N}_])#([\p{L}\p{N}_\p{Extended_Pictographic}\p{Regional_Indicator}\p{Emoji_Modifier}\uFE0E\uFE0F\u200D\u20E3-]+)/gu;
  return [...new Set([...text.matchAll(pattern)].map(m=>normalizedTag(m[2].replace(/^-+|-+$/g,''))).filter(Boolean))];
}
function onfimTagLabel(tag){return tag==='📆'||tag==='📍'?tag:'#'+tag;}
// Riferimenti @ riconoscibili anche nei vecchi backup: nessuna migrazione IndexedDB.
// Le date devono essere reali, le coordinate rispettare latitudine e longitudine.
const ONFIM_DATE_PATTERN=/(^|[^\p{L}\p{N}_@])@(\d{2})\/(\d{2})\/(\d{4})(?:-(\d{2}):(\d{2}))?(?![\d/:.\-])/gu;
const ONFIM_POINT_PATTERN=/(^|[^\p{L}\p{N}_@])@(\d{1,2}(?:\.\d{1,6})?)([NS]),(\d{1,3}(?:\.\d{1,6})?)([EW])(?![\p{L}\p{N}_.])/gu;
function onfimValidDate(d,m,y,h,mi){
 const day=Number(d),month=Number(m),year=Number(y);
 if(year<1||year>9999||month<1||month>12||day<1||day>31)return false;
 const max=new Date(Date.UTC(2000,month,0)).getUTCDate();
 const days=month===2?((year%4===0&&(year%100!==0||year%400===0))?29:28):max;
 return day<=days&&(h===undefined||(Number(h)<=23&&Number(mi)<=59));
}
function onfimPointFromMatch(m){
 const lat=Number(m[2])*(m[3]==='S'?-1:1),lon=Number(m[4])*(m[5]==='W'?-1:1);
 return Number.isFinite(lat)&&Math.abs(lat)<=90&&Number.isFinite(lon)&&Math.abs(lon)<=180?{lat,lon}:null;
}
function onfimFindRefs(text,kind){
 const result=[],pattern=kind==='date'?ONFIM_DATE_PATTERN:ONFIM_POINT_PATTERN;
 pattern.lastIndex=0;
 for(const m of String(text||'').matchAll(pattern)){
  if(kind==='date'&&!onfimValidDate(m[2],m[3],m[4],m[5],m[6]))continue;
  const point=kind==='point'?onfimPointFromMatch(m):null;
  if(kind==='point'&&!point)continue;
  const start=m.index+m[1].length;
  result.push({start,end:m.index+m[0].length,value:m[0].slice(m[1].length),...(point||{})});
 }
 return result;
}
function legacyTagSlug(t){const v=String(t||'').trim().normalize('NFC').replace(/^#+/,'').replace(/\s+/g,'_');return extractHashtags('#'+v)[0]||'';}
function noteTags(n){
 const body=txt(n.text||''),raw=extractHashtags(body).filter(t=>t!=='📆'&&t!=='📍');
 // Evita etichette automatiche "fantasma" in eventuali note fuse o importate.
 const old=(n.tags||[]).map(legacyTagSlug).filter(t=>t&&t!=='📆'&&t!=='📍');
 const special=[];
 if(onfimFindRefs(body,'date').length)special.push('📆');
 if(onfimFindRefs(body,'point').length)special.push('📍');
 return [...new Set([...raw,...old,...special])];
}
function htmlEscape(text){return String(text).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));}
function migratedText(n){
  const old=(n.tags||[]).map(legacyTagSlug).filter(t=>t&&t!=='📆'&&t!=='📍');
  const have=new Set(extractHashtags(txt(n.text||'')));
  const missing=[...new Set(old)].filter(t=>!have.has(t));
  if(!missing.length)return n.text||'';
  const line=missing.map(t=>'#'+t).join(' ');
  return String(n.text||'')+'<p>'+htmlEscape(line)+'</p>';
}
// Filtro temporaneo progressivo: più etichette restringono i risultati (AND).
const onfimActiveTags=new Set();
let onfimTagReturnView=null;
function onfimTagsOfGroup(g){return new Set(g.parts.flatMap(noteTags));}
function onfimGroupMatchesTagFilters(g){
  if(!onfimActiveTags.size)return true;
  const tags=onfimTagsOfGroup(g);
  return [...onfimActiveTags].every(t=>tags.has(t));
}
function onfimClearTagFilters(){
  onfimActiveTags.clear();
  if(onfimTagReturnView){smartActive=onfimTagReturnView.active;$('filter').value=onfimTagReturnView.filter;syncFilterPills();}
  onfimTagReturnView=null;
  void showTags().then(renderNotes);
}
function onfimToggleTagFilter(tag){
  if(onfimActiveTags.has(tag)){
    onfimActiveTags.delete(tag);
    if(!onfimActiveTags.size){onfimClearTagFilters();return;}
  }else{
    if(!onfimActiveTags.size)onfimTagReturnView={active:smartActive,filter:$('filter').value};
    onfimActiveTags.add(tag);
  }
  smartActive='all';$('filter').value='ordinary';syncFilterPills();
  void showTags().then(renderNotes);
}
function onfimRenderActiveTags(){
  const bar=$('onfimActiveTagBar'),list=$('onfimActiveTagItems');
  bar.classList.toggle('hidden',!onfimActiveTags.size);
  list.replaceChildren();
  for(const tag of onfimActiveTags){
    const b=document.createElement('button');b.type='button';b.className='onfim-active-tag';
    b.textContent=onfimTagLabel(tag)+' ×';b.title='Rimuovi filtro '+onfimTagLabel(tag);
    b.setAttribute('aria-label','Rimuovi filtro '+onfimTagLabel(tag));
    b.onclick=()=>onfimToggleTagFilter(tag);list.append(b);
  }
}
// Gli hashtag nella lettura avviano la ricerca progressiva; nessun pannello Filtri separato.
async function showTags(){
  const notes=await allNotes(),fil=$('filter').value,groups=new Map();
  for(const n of notes.filter(x=>!x.deletedAt&&(fil==='reserved'?!!x.reserved:!x.reserved)&&(!x.reserved||unlocked))){
    const root=groupRootFor(n,notes);
    if(fil==='favorites'&&root.favorite!==true)continue;
    if(!groups.has(root.id))groups.set(root.id,{root,parts:chainMembers(root,notes)});
  }
  const counts=new Map();
  for(const g of groups.values())for(const tag of onfimTagsOfGroup(g))counts.set(tag,(counts.get(tag)||0)+1);
  knownTags=[...counts.entries()].sort((a,b)=>b[1]-a[1]||a[0].localeCompare(b[0],'it')).map(x=>x[0]);
  onfimRenderActiveTags();
}
$('onfimActiveTagsClear').onclick=onfimClearTagFilters;
function previewAllowed(n){return !n.reserved||unlocked;}

 // Raccolte intelligenti: viste locali. Nessuna proprietà aggiunta alle note.
 const ONFIM_COLLECTIONS_KEY='onfim-smart-collections-v1',ONFIM_COLLECTIONS_LEGACY_KEY='onfim-standalone-smart-collections-v1';
 let smartCollections=[],smartActive='home';
 function onfimLoadCollections(){
  try{const raw=JSON.parse(localStorage.getItem(ONFIM_COLLECTIONS_KEY)||localStorage.getItem(ONFIM_COLLECTIONS_LEGACY_KEY)||'[]');
    smartCollections=Array.isArray(raw)?raw.filter(x=>x&&typeof x.id==='string'&&typeof x.name==='string'&&Array.isArray(x.tags))
      .slice(0,40).map(x=>({id:x.id.slice(0,70),name:x.name.slice(0,48),tags:[...new Set(x.tags.map(legacyTagSlug).filter(Boolean))].slice(0,30),hideHome:!!x.hideHome})).filter(x=>x.tags.length):[];
  }catch(e){smartCollections=[];console.warn('Raccolte non leggibili',e);}
 }
 function onfimCleanCollections(raw){return Array.isArray(raw)?raw.filter(c=>c&&typeof c.id==='string'&&typeof c.name==='string'&&Array.isArray(c.tags)).slice(0,40).map(c=>({id:c.id.slice(0,70),name:c.name.slice(0,48),tags:[...new Set(c.tags.map(legacyTagSlug).filter(Boolean))].slice(0,30),hideHome:!!c.hideHome})).filter(c=>c.tags.length):[];}
 function onfimSaveCollections(){localStorage.setItem(ONFIM_COLLECTIONS_KEY,JSON.stringify(smartCollections));recordDataChange();void onfimRenderCollections().then(renderNotes);}
 function onfimCollectionMatches(group,c){const tags=onfimTagsOfGroup(group);return c.tags.some(t=>tags.has(t));}
 function onfimCollectionHidden(group){return smartCollections.some(c=>c.hideHome&&onfimCollectionMatches(group,c));}
 async function onfimRenderCollections(){
  const host=$('smartCollectionTabs'),oldScroll=host.scrollLeft;host.replaceChildren();
  const all=await allNotes(),ordinary=new Map();
  for(const n of all.filter(x=>!x.deletedAt&&!x.reserved)){
    const root=groupRootFor(n,all);
    if(!ordinary.has(root.id))ordinary.set(root.id,{root,parts:chainMembers(root,all)});
  }
  const choices=[{id:'home',name:'Home'},...smartCollections.map(c=>({id:'c:'+c.id,name:c.name})),{id:'all',name:'Tutti'}];
  if(!choices.some(c=>c.id===smartActive))smartActive='home';
  for(const c of choices){
    const b=document.createElement('button');b.type='button';b.textContent=c.name;
    if(c.id.startsWith('c:')){const def=smartCollections.find(x=>x.id===c.id.slice(2));
      const count=[...ordinary.values()].filter(g=>onfimCollectionMatches(g,def)).length;
      b.textContent=c.name+' · '+count;
    }
    b.dataset.kind=c.id.startsWith('c:')?'collection':'main';
    b.setAttribute('aria-pressed',String(c.id===smartActive));
    b.onclick=()=>{onfimActiveTags.clear();onfimTagReturnView=null;smartActive=c.id;$('filter').value='ordinary';syncFilterPills();
      void showTags().then(onfimRenderCollections).then(renderNotes);};
    host.append(b);
  }
  host.scrollLeft=oldScroll;
 }
 function onfimParseCollectionTags(input){
   const tags=String(input||'').split(/[\s,;]+/u).map(t=>legacyTagSlug(t)).filter(Boolean);
   return [...new Set(tags)].slice(0,30);
 }
 function onfimCollectionsDialogRender(){
  const host=$('collectionsItems');host.replaceChildren();
  if(!smartCollections.length){const hint=document.createElement('p');hint.className='small';hint.textContent='Nessuna raccolta';host.append(hint);}
  const appendButton=(parent,label,callback,disabled=false,extraClass='')=>{
    const b=document.createElement('button');b.type='button';b.textContent=label;
    b.className=extraClass;b.disabled=disabled;b.onclick=callback;parent.append(b);return b;
  };
  smartCollections.forEach((c,i)=>{
    const item=document.createElement('section');item.className='smart-collection-item onfim-collection-compact';
    const head=document.createElement('div');head.className='smart-collection-item-head';
    const toggle=document.createElement('button');toggle.type='button';toggle.className='onfim-collection-toggle';
    toggle.setAttribute('aria-expanded','false');toggle.textContent=c.name+'  ▾';
    const controls=document.createElement('div');controls.className='onfim-collection-order';
    appendButton(controls,'↑',()=>onfimMoveCollection(i,-1),i===0).title='Sposta su';
    appendButton(controls,'↓',()=>onfimMoveCollection(i,1),i===smartCollections.length-1).title='Sposta giù';
    const count=document.createElement('small');count.className='onfim-collection-count';count.textContent='';head.append(toggle,count,controls);item.append(head);item.dataset.collectionId=c.id;
    const details=document.createElement('div');details.className='onfim-collection-details hidden';
    const tags=document.createElement('p');tags.textContent=c.tags.map(onfimTagLabel).join(' · ');
    const hide=document.createElement('label');hide.className='smart-hide-check';
    const checkbox=document.createElement('input');checkbox.type='checkbox';checkbox.checked=c.hideHome;
    checkbox.onchange=()=>{c.hideHome=checkbox.checked;onfimSaveCollections();};
    hide.append(checkbox,document.createTextNode('Nascondi dalla Home'));
    const actions=document.createElement('div');actions.className='smart-collection-item-actions';
    appendButton(actions,'Rinomina',()=>{const answer=prompt('Nome raccolta',c.name);if(answer===null)return;const value=answer.trim().slice(0,48);if(!value)return;c.name=value;onfimSaveCollections();onfimCollectionsDialogRender();});
    appendButton(actions,'Modifica hashtag',()=>{const answer=prompt('Hashtag della raccolta '+c.name+' (separati da spazio o virgola)',c.tags.map(onfimTagLabel).join(' '));if(answer===null)return;const parsed=onfimParseCollectionTags(answer);if(!parsed.length){toast('Inserisci almeno un hashtag');return;}c.tags=parsed;onfimSaveCollections();onfimCollectionsDialogRender();});
    appendButton(actions,'Elimina',()=>{if(!confirm('Eliminare la raccolta “'+c.name+'”? Le note non verranno eliminate.'))return;smartCollections=smartCollections.filter(x=>x.id!==c.id);if(smartActive==='c:'+c.id)smartActive='home';onfimSaveCollections();onfimCollectionsDialogRender();},false,'danger');
    details.append(tags,hide,actions);item.append(details);host.append(item);
    toggle.onclick=()=>{const open=details.classList.toggle('hidden');toggle.setAttribute('aria-expanded',String(!open));toggle.textContent=c.name+(open?'  ▾':'  ▴');};
  });
  void allNotes().then(notes=>{
    const groups=new Map();
    for(const n of notes.filter(x=>!x.deletedAt&&!x.reserved)){
      const root=groupRootFor(n,notes);
      if(!groups.has(root.id))groups.set(root.id,{root,parts:chainMembers(root,notes)});
    }
    for(const item of host.querySelectorAll('[data-collection-id]')){
      const c=smartCollections.find(x=>x.id===item.dataset.collectionId);
      if(c){const matches=[...groups.values()].filter(g=>onfimCollectionMatches(g,c)).length;
        item.querySelector('.onfim-collection-count').textContent=String(matches);}
    }
  }).catch(()=>{});
}
function onfimMoveCollection(i,step){
  const j=i+step;if(j<0||j>=smartCollections.length)return;
  [smartCollections[i],smartCollections[j]]=[smartCollections[j],smartCollections[i]];
  onfimSaveCollections();onfimCollectionsDialogRender();
}

 onfimLoadCollections();
 $('manageCollections').onclick=()=>{onfimCollectionsDialogRender();$('collectionsCreate').classList.add('hidden');$('collectionsDialog').showModal();};
 $('onfimNewCollection').onclick=()=>{const form=$('collectionsCreate');const opening=form.classList.contains('hidden');form.classList.toggle('hidden',!opening);if(opening)$('collectionName').focus();};
 $('collectionsClose').onclick=()=>$('collectionsDialog').close();
 $('collectionsCreate').onsubmit=e=>{e.preventDefault();if(smartCollections.length>=40){toast('Limite di 40 raccolte raggiunto');return;}const name=$('collectionName').value.trim().slice(0,48),tags=onfimParseCollectionTags($('collectionTags').value);if(!name||!tags.length){toast('Indica nome e almeno un hashtag');return;}
  smartCollections.push({id:uid(),name,tags,hideHome:$('collectionHideHome').checked});
  onfimSaveCollections();onfimCollectionsDialogRender();$('collectionsCreate').reset();$('collectionsCreate').classList.add('hidden');toast('Raccolta creata');};
let onfimNotesView=(localStorage.getItem('onfim-notes-view')==='list'?'list':'grid');
function onfimSyncViewButtons(){
  $('notesGridView').setAttribute('aria-pressed',String(onfimNotesView==='grid'));
  $('notesListView').setAttribute('aria-pressed',String(onfimNotesView==='list'));
}
async function renderNotes(){
  const all=await allNotes(),q=$('search').value.toLocaleLowerCase().trim(),fil=$('filter').value,order=$('sortOrder').value;
  await onfimRenderCollections();onfimRenderActiveTags();
  $('homeHeading').textContent=fil==='reserved'?'Archivio 🔒':fil==='favorites'?'Preferiti ⭐':smartActive==='all'?'Tutti gli appunti':smartActive==='home'?'I tuoi appunti':(smartCollections.find(x=>'c:'+x.id===smartActive)?.name||'Raccolta');
  $('smartCollectionsNav').classList.toggle('hidden',fil!=='ordinary');
  // Raggruppiamo PRIMA di filtrare: la ricerca in una parte deve trovare l'appunto composto.
  const groups=new Map();
  for(const n of all.filter(x=>!x.deletedAt&&(fil==='reserved'?!!x.reserved:!x.reserved))){
    const root=groupRootFor(n,all),key=root.id;
    if(!groups.has(key))groups.set(key,{root,parts:chainMembers(root,all)});
  }
  let a=[...groups.values()];
  if(fil==='favorites')a=a.filter(g=>g.root.favorite===true);
  if(fil==='ordinary'){
    if(smartActive==='home')a=a.filter(g=>q||g.root.pinned||!onfimCollectionHidden(g));
    else if(smartActive.startsWith('c:')){
      const c=smartCollections.find(x=>x.id===smartActive.slice(2));a=c?a.filter(g=>onfimCollectionMatches(g,c)):[];
    }
  }
  a=a.filter(onfimGroupMatchesTagFilters);
  a=a.filter(g=>!q||g.parts.some(n=>[n.title,txt(n.text),...noteTags(n),...(n.checklist||[]).map(x=>x?.text||''),...(n.linkedFiles||[]).map(x=>x?.name||''),...(n.audios||[]).map(x=>x?.name||'')].join(' ').toLocaleLowerCase().includes(q)));
  function moment(g,which){return Math.max(...g.parts.map(n=>Number(n[which])||0));}
  a.sort((x,y)=>order==='created-desc'?moment(y,'created')-moment(x,'created'):order==='created-asc'?moment(x,'created')-moment(y,'created'):order==='updated-asc'?moment(x,'updated')-moment(y,'updated'):order==='title-asc'?(x.root.title||'').localeCompare(y.root.title||''):order==='title-desc'?(y.root.title||'').localeCompare(x.root.title||''):moment(y,'updated')-moment(x,'updated'));
  a.sort((x,y)=>Number(!!y.root.pinned)-Number(!!x.root.pinned));
  $('noteCount').textContent=a.length+' '+(a.length===1?'appunto':'appunti');
  const host=$('noteList');host.replaceChildren();host.classList.toggle('list-layout',onfimNotesView==='list');onfimSyncViewButtons();
  if(!a.length){const empty=document.createElement('div');empty.className='empty';empty.innerHTML=fil==='reserved'?'<div class="empty-symbol">🔒</div><strong>Archivio vuoto</strong><span>Puoi spostare qui gli appunti dal menu ⋮.</span>':fil==='favorites'?'<div class="empty-symbol">⭐</div><strong>Nessun preferito</strong><span>Aggiungi una stella a un appunto dal menu ⋮.</span>':'<div class="empty-symbol">✎</div><strong>Nessun appunto</strong><span>Premi ＋ per crearne uno.</span>';host.append(empty);return;}
  const columns=Array.from({length:onfimNotesView==='list'?1:2},()=>document.createElement('div'));
  for(const col of columns){col.className='note-column';host.append(col);}
  for(let i=0;i<a.length;i++){
    const {root:n,parts}=a[i],allowed=previewAllowed(n),el=document.createElement('article'),count=parts.length;
    el.className='card';el.tabIndex=0;el.setAttribute('role','button');
    el.setAttribute('aria-label',allowed?'Leggi '+(n.title||'appunto senza titolo'):'Sblocca archivio');
    el.style.setProperty('--note-color',allowed?(n.color||'#fff'):'#e8ecef');
    const title=document.createElement('div');title.className='title';title.textContent=allowed?(n.title||'Senza titolo'):'🔒 Riservato';el.append(title);
    if(allowed&&count>1){const chain=document.createElement('div');chain.className='chain-summary';chain.textContent='▤ '+count+' parti collegate';el.append(chain);}
    const excerpt=document.createElement('div');excerpt.className='preview';
    const content=txt(n.text||'').trim();excerpt.textContent=allowed?(content||''):'Inserisci il PIN per leggere';
    if(excerpt.textContent)el.append(excerpt);
    if(allowed){const rows=parts.flatMap(x=>onfimNormalizeChecklist(x.checklist).filter(v=>v.text.trim()));
      if(rows.length){const summary=document.createElement('div');summary.className='chain-summary';
        summary.textContent='☑ '+rows.filter(x=>x.done).length+' / '+rows.length+' · checklist';el.append(summary);}
    }
    if(allowed){
      const picSource=parts.find(p=>(p.photos||[]).some(s=>typeof s==='string'&&s.startsWith('data:image/'))||(typeof p.drawing==='string'&&p.drawing.startsWith('data:image/')))||n;
      const picture=(picSource.photos||[]).find(s=>typeof s==='string'&&s.startsWith('data:image/'))||(typeof picSource.drawing==='string'&&picSource.drawing.startsWith('data:image/')?picSource.drawing:'');
      if(picture){const thumb=document.createElement('img');thumb.className='cardthumb'+(picture===picSource.drawing?' drawing':'');thumb.src=picture;thumb.alt=picture===picSource.drawing?'Disegno':'Fotografia';thumb.loading='lazy';el.append(thumb);
        if(picture!==picSource.drawing&&picSource.photoMarks?.length){const index=(picSource.photos||[]).indexOf(picture),overlay=picSource.photoMarks[index];if(typeof overlay==='string'&&overlay.startsWith('data:image/')){const composite=document.createElement('canvas'),context=composite.getContext('2d');const source=new Image(),paint=new Image();source.onload=()=>{composite.width=source.naturalWidth;composite.height=source.naturalHeight;context.drawImage(source,0,0);paint.onload=()=>{context.drawImage(paint,0,0,composite.width,composite.height);thumb.src=composite.toDataURL('image/jpeg',0.83);};paint.src=overlay;};source.src=picture;}}}
    }
    const meta=document.createElement('div');meta.className='meta';
    if(n.reserved){const b=document.createElement('span');b.className='chip';b.textContent='🔒';b.title='Archivio';meta.append(b);}
    if(allowed){const uniqueTags=[...new Set(parts.flatMap(noteTags))];for(const t of uniqueTags.slice(0,3)){
        const c=document.createElement('button');c.type='button';c.className='chip tag-filter-link';c.textContent=onfimTagLabel(t);
        c.title='Mostra appunti con '+onfimTagLabel(t);c.setAttribute('aria-label','Filtra per '+onfimTagLabel(t));
        c.onclick=e=>{e.stopPropagation();onfimToggleTagFilter(t);};
        meta.append(c);
      }
      if(uniqueTags.length>3){
        const remaining=uniqueTags.slice(3);
        const more=document.createElement('span');more.className='chip tag-overflow';
        more.textContent='+'+remaining.length;
        more.title='Altre etichette: '+remaining.map(onfimTagLabel).join(', ');
        more.setAttribute('aria-label',remaining.length+' altre etichette');
        meta.append(more);
      }
      const voiceCount=parts.reduce((sum,p)=>sum+(p.audios||[]).length,0);if(voiceCount){const voice=document.createElement('span');voice.className='chip';voice.textContent='🎙 '+voiceCount;meta.append(voice);}}
    if(allowed&&(n.favorite||n.pinned)){
      const status=document.createElement('span');status.className='card-status';
      if(n.pinned){const marker=document.createElement('span');marker.className='card-status-pin';marker.innerHTML=ONFIM_ICONS.pin;marker.title='Fissato in alto';marker.setAttribute('aria-label','Fissato in alto');status.append(marker);}
      if(n.favorite&&!n.reserved){const marker=document.createElement('span');marker.className='card-status-favorite';marker.innerHTML=ONFIM_ICONS.star;marker.title='Preferito';marker.setAttribute('aria-label','Preferito');status.append(marker);}
      meta.append(status);
    }
    if(meta.childNodes.length)el.append(meta);
    const menu=document.createElement('div');menu.className='card-menu';
    const quickReminder=document.createElement('button');
    quickReminder.type='button';quickReminder.className='card-quick-reminder';
    quickReminder.innerHTML='<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M18 8a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9"/><path d="M10 21h4"/></svg>';
    quickReminder.setAttribute('aria-label','Promemoria per '+(n.title||'appunto'));
    quickReminder.title='Promemoria';
    if(parts.some(onfimReminderActive))quickReminder.classList.add('has-reminder');else quickReminder.classList.add('hidden');
    quickReminder.onclick=async e=>{e.stopPropagation();closeCardMenus();await openReminderFor(n,true);};
    const more=document.createElement('button');more.type='button';more.className='card-more';more.setAttribute('aria-label','Opzioni per '+(n.title||'appunto'));more.setAttribute('aria-expanded','false');more.innerHTML=ONFIM_ICONS.more;
    const popup=document.createElement('div');popup.className='card-popup hidden';
    const editAction=document.createElement('button');editAction.type='button';editAction.innerHTML=ONFIM_ICONS.pencil+'<span>Modifica nota</span>';
    editAction.onclick=async e=>{e.stopPropagation();closeCardMenus();if(n.reserved&&!unlocked&&!await checkPin())return;const latest=(await allNotes()).find(x=>x.id===n.id&&!x.deletedAt);if(!latest){toast('Nota non disponibile');return;}editorFrom='list';editNote(latest);};
    popup.append(editAction);
    const del=document.createElement('button');del.type='button';del.innerHTML=ONFIM_ICONS.trash+'<span>'+(count>1?'Sposta appunto nel Cestino':'Sposta nel Cestino')+'</span>';del.className='danger';
    del.onclick=async(e)=>{e.stopPropagation();popup.classList.add('hidden');if(n.reserved&&!await checkPin())return;if(!confirmMoveToTrash(count))return;await safeDeleteNote(n);await reload();await scheduleReminders();toast('Spostato nel Cestino');};
    const move=document.createElement('button');move.type='button';move.innerHTML=(n.reserved?ONFIM_ICONS.restore:ONFIM_ICONS.archive)+'<span>'+(n.reserved?'Riporta negli appunti':'Sposta in Archivio')+'</span>';move.className='archive-option';
    move.onclick=async e=>{e.stopPropagation();popup.classList.add('hidden');if(!n.reserved&&!await checkPin())return;const now=Date.now(),updated=parts.map(p=>({...p,reserved:!n.reserved,updated:now}));await putNotesBatch(updated);await reload();toast(n.reserved?'Riportato negli appunti':'Spostato nell’Archivio');};
    if(!n.reserved){
      const star=document.createElement('button');star.type='button';star.innerHTML=ONFIM_ICONS.star+'<span>'+(n.favorite?'Rimuovi dai Preferiti':'Aggiungi ai Preferiti')+'</span>';
      star.onclick=async e=>{e.stopPropagation();popup.classList.add('hidden');const fresh=(await allNotes()).find(x=>x.id===n.id);if(!fresh)return;await putNote({...fresh,favorite:!fresh.favorite,updated:Date.now()});await reload();toast(fresh.favorite?'Rimosso dai Preferiti':'Aggiunto ai Preferiti');};
      /* star always visible on card */
    }
    const pinAction=document.createElement('button');pinAction.type='button';pinAction.innerHTML=ONFIM_ICONS.pin+'<span>'+(n.pinned?'Rimuovi da Fissati':'Fissa in alto')+'</span>';
    pinAction.onclick=async e=>{e.stopPropagation();closeCardMenus();const fresh=(await allNotes()).find(x=>x.id===n.id&&!x.deletedAt);if(!fresh)return;if(fresh.reserved&&!unlocked&&!await checkPin())return;await putNote({...fresh,pinned:!fresh.pinned});await reload();toast(fresh.pinned?'Non più fissato':'Fissato in alto');};
    /* pin always visible on card */
    const remindAction=document.createElement('button');remindAction.type='button';remindAction.innerHTML=ONFIM_ICONS.bell+'<span>Promemoria</span>';remindAction.onclick=async e=>{e.stopPropagation();closeCardMenus();if(n.reserved&&!unlocked&&!await checkPin())return;await openReminderFor(n,true);};
    const partAction=document.createElement('button');partAction.type='button';partAction.innerHTML=ONFIM_ICONS.plus+'<span>Aggiungi a un’altra nota</span>';partAction.onclick=async e=>{e.stopPropagation();closeCardMenus();if(n.reserved&&!unlocked&&!await checkPin())return;onfimAskPartFromCard(n.id);};
    const exportAction=document.createElement('button');exportAction.type='button';exportAction.innerHTML='<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8Z"/><path d="M14 2v6h6M8 13l-2 2 2 2m8-4 2 2-2 2m-3-5-2 6"/></svg>'+'<span>Condividi nota</span>';exportAction.onclick=e=>{e.stopPropagation();closeCardMenus();void onfimExportNote(n.id);};popup.append(partAction,exportAction,move,del);menu.append(more,popup);el.append(menu);
    const bar=document.createElement('div');bar.className='card-actionbar';
    function directAction(kind,label,isOn,handler){
      const b=document.createElement('button');b.type='button';b.className='card-direct-action';b.dataset.action=kind;
      b.setAttribute('aria-pressed',String(!!isOn));b.setAttribute('aria-label',label);b.title=label;b.innerHTML=ONFIM_ICONS[kind];
      b.addEventListener('click',async e=>{e.preventDefault();e.stopPropagation();closeCardMenus();if(b.disabled)return;b.disabled=true;try{await handler();}finally{if(b.isConnected)b.disabled=false;}});
      return b;
    }
    const hasReminder=parts.some(onfimReminderActive);
    const directPin=directAction('pin',n.pinned?'Rimuovi da Fissati':'Fissa in alto',n.pinned,async()=>{
      const all=await allNotes(),fresh=all.find(x=>x.id===n.id&&!x.deletedAt);if(!fresh)return;
      if(fresh.reserved&&!unlocked&&!await checkPin())return;
      await putNote({...fresh,pinned:!fresh.pinned,updated:Date.now()});await reload();
    });
    const directStar=directAction('star',n.favorite?'Rimuovi dai Preferiti':'Aggiungi ai Preferiti',n.favorite,async()=>{
      const all=await allNotes(),fresh=all.find(x=>x.id===n.id&&!x.deletedAt);if(!fresh||fresh.reserved)return;
      await putNote({...fresh,favorite:!fresh.favorite,updated:Date.now()});await reload();
    });
    if(n.reserved){directStar.disabled=true;directStar.title='Non disponibile nell’Archivio';}
    const directBell=directAction('bell','Promemoria',hasReminder,async()=>await openReminderFor(n,true));
    bar.append(directPin,directStar,directBell);el.append(bar);
    more.onclick=e=>{e.stopPropagation();const wasOpen=!popup.classList.contains('hidden');closeCardMenus();if(!wasOpen){popup.classList.remove('hidden');el.classList.add('menu-open');more.setAttribute('aria-expanded','true');}};
    const open=async()=>{if(n.reserved&&!await checkPin())return;await openRead(n);};
    el.addEventListener('click',e=>{if(e.target.closest('button'))return;void open();});
    el.addEventListener('keydown',e=>{if(e.target===el&&(e.key==='Enter'||e.key===' ')){e.preventDefault();void open();}});
    columns[i%columns.length].append(el);
  }
}

function emptyNote(){return{id:uid(),title:'',text:'',color:'#ffffff',tags:[],reminder:'',reminderRepeat:'none',reserved:false,favorite:false,pinned:false,photos:[],photoMarks:[],drawing:'',audios:[],linkedFiles:[],created:Date.now(),updated:Date.now()};}
function hasContent(n){return !!(n.title.trim()||txt(n.text).trim()||(n.photos||[]).length||n.drawing||(n.audios||[]).length||(n.linkedFiles||[]).length);}
// Salvataggio automatico: una breve pausa tra le modifiche, nessun pulsante Salva.
let editorHasStoredCopy=false;
function markDirty(){
 if(!note)return;
 dirty=true;
 $('saveState').textContent='Da salvare…';
 clearTimeout(saveTimer);
 const editorId=note.id;
 saveTimer=setTimeout(()=>{if(note?.id===editorId)void flushSave();},850);
}
function snapshot(){return{...note,title:$('noteTitle').value.trim(),text:sanitizeHTML($('noteBody').innerHTML),color:$('noteColor').value,tags:extractHashtags(txt($('noteBody').innerHTML)),reminder:$('reminder').value,reminderBase:$('reminder').value===note.reminder?(note.reminderBase||note.reminder):$('reminder').value,reminderRepeat:$('reminder').value?(note.reminderRepeat||'none'):'none',reserved:$('reserved').checked,photos:[...images],photoMarks:[...photoMarks],drawing:drawn?$('drawCanvas').toDataURL('image/png'):drawData,audios:[...audioClips],linkedFiles:[...onfimEditorLinks],updated:Date.now()};}
// Un'unica coda di scrittura: gli inserimenti successivi non possono essere
// sovrascritti da un salvataggio precedente ancora in esecuzione.
function flushSave(){
 clearTimeout(saveTimer);
 if(!note||!dirty)return saving;
 const snap=snapshot(),editorId=snap.id;
 // Non creare una scheda vuota per una nota appena aperta e mai compilata.
 // Se la nota esisteva gia', salvarne anche lo svuotamento intenzionale.
 if(!hasContent(snap)&&!editorHasStoredCopy){dirty=false;$('saveState').textContent='';return saving;}
 dirty=false;$('saveState').textContent='Salvataggio…';
 saving=saving.catch(()=>{}).then(async()=>{
  try{
   await putNote(snap);
   const allSaved=await allNotes(),rootId=chainRootOf(snap);
   const related=allSaved.filter(x=>!x.deletedAt&&(x.id===rootId||x.chainRoot===rootId)&&x.id!==snap.id&&x.reserved!==snap.reserved);
   if(related.length)await putNotesBatch(related.map(x=>({...x,reserved:snap.reserved,updated:Date.now()})));
   if(note?.id!==editorId)return;
   note=snap;editorHasStoredCopy=true;$('recoverNote').disabled=false;
   $('editorDates').textContent=noteDates(snap);
   if(snap.reserved&&unlocked&&$('filter').value!=='reserved'){$('filter').value='reserved';syncFilterPills();}
   else if(!snap.reserved&&$('filter').value==='reserved'){$('filter').value='ordinary';unlocked=false;syncFilterPills();}
   if(!dirty)$('saveState').textContent='Salvato';
   $('deleteNote').classList.remove('hidden');
   await showTags();scheduleReminders();
  }catch(e){
   if(note?.id!==editorId)return;
   dirty=true;
   $('saveState').textContent='Errore nel salvataggio: '+(e.message||e.name||'errore');
  }
 });
 return saving;
}
async function ensureEditorSaved(){
 // Anche i comandi di organizzazione aspettano le scritture pendenti.
 for(let i=0;i<3;i++){
  if(dirty)await flushSave();else await saving.catch(()=>{});
  if(!dirty)return true;
 }
 toast('Salvataggio non riuscito: la nota resta aperta.');return false;
}
async function leaveEditor(){
 if(isRecording()){toast('Ferma la registrazione prima di uscire.');chooseTab('photos');return;}
 if(!(await ensureEditorSaved()))return;
 clearTimeout(saveTimer);clearTimeout(textHistoryTimer);
 dirty=false;$('saveState').textContent='';
 note=null;editorHasStoredCopy=false;drawLoadGeneration++;
 // Undo e Redo riguardano soltanto la sessione appena chiusa.
 textHistory=[];textHistoryAt=0;updateTextUndoUI();
 if(editorFrom==='read'&&readId){
  const all=await allNotes(),root=all.find(n=>n.id===readId&&!n.deletedAt);
  if(root){await openRead(root);return;}
 }
 await reload();view('listView');
}
function updateDrawingMark(){const mark=$('drawingMark');mark.textContent=drawn||drawData?'✓':'';$('tabDraw').setAttribute('aria-label',drawn||drawData?'Disegno, contenuto presente':'Disegno');}
function updateTextMark(){const filled=!!txt($('noteBody').innerHTML).trim();$('textMark').textContent=filled?'✓':'';$('tabText').setAttribute('aria-label',filled?'Testo, contenuto presente':'Testo');}
function updateNoteColorButton(){const current=$('noteColor').value;$('currentColorDot').style.backgroundColor=current;for(const b of document.querySelectorAll('[data-note-color]')){b.classList.toggle('selected',b.dataset.noteColor.toLowerCase()===current.toLowerCase());b.setAttribute('aria-pressed',String(b.classList.contains('selected')));}}
function clearCanvas(){drawLoadGeneration++;const c=$('drawCanvas'),ctx=c.getContext('2d');ctx.clearRect(0,0,c.width,c.height);ctx.fillStyle='#ffffff';ctx.fillRect(0,0,c.width,c.height);drawn=false;drawData='';updateDrawingMark();}
function showDrawing(src){clearCanvas();drawUndoHistory=[];drawRedoHistory=[];refreshDrawUndo();if(!src)return;drawData=src;updateDrawingMark();const im=new Image();const thisNote=note?.id,token=drawLoadGeneration;im.onload=()=>{if(note?.id!==thisNote||token!==drawLoadGeneration)return;const c=$('drawCanvas'),ctx=c.getContext('2d');const ratio=im.naturalWidth/im.naturalHeight;const w=Math.min(c.width,c.height*ratio);const h=w/ratio;ctx.drawImage(im,0,0,w,h);};im.src=src;}
function drawingState(){const c=$('drawCanvas');return {png:c.toDataURL('image/png'),present:!!(drawn||drawData)};}
function refreshDrawUndo(){$('drawUndo').disabled=!drawUndoHistory.length;$('drawRedo').disabled=!drawRedoHistory.length;}
function saveDrawUndo(){drawUndoHistory.push(drawingState());if(drawUndoHistory.length>18)drawUndoHistory.shift();drawRedoHistory=[];refreshDrawUndo();}
function restoreDrawingState(state){drawLoadGeneration++;const token=drawLoadGeneration,im=new Image();im.onload=()=>{if(token!==drawLoadGeneration)return;const c=$('drawCanvas'),ctx=c.getContext('2d');ctx.clearRect(0,0,c.width,c.height);ctx.fillStyle='#fff';ctx.fillRect(0,0,c.width,c.height);ctx.drawImage(im,0,0,c.width,c.height);drawn=state.present;drawData=state.present?c.toDataURL('image/png'):'';updateDrawingMark();markDirty();};im.src=state.png;}
function stepDrawHistory(dir){const source=dir===-1?drawUndoHistory:drawRedoHistory,target=dir===-1?drawRedoHistory:drawUndoHistory;if(!source.length)return;target.push(drawingState());restoreDrawingState(source.pop());refreshDrawUndo();}
// Le clip restano locali, incluse nel backup JSON; mai inviate a server.
const MAX_AUDIO_BYTES=10*1024*1024;
function isRecording(){return audioStarting||audioFinalizing||(!!recorder&&recorder.state!=='inactive');}
function clockString(ms){const sec=Math.floor(Math.max(0,ms)/1000);return String(Math.floor(sec/60)).padStart(2,'0')+':'+String(sec%60).padStart(2,'0');}
function recordingUI(){const live=!!recorder&&recorder.state!=='inactive';$('audioStart').disabled=isRecording();$('audioRecord').disabled=isRecording();$('audioPause').disabled=!live;$('audioStop').disabled=!live;$('audioPause').textContent=live&&recorder.state==='paused'?'Riprendi':'Pausa';$('audioRecord').setAttribute('aria-label',audioFinalizing?'Elaborazione registrazione':live?'Registrazione in corso':'Avvia registrazione audio');}
function tickAudio(){const elapsed=(performance.now()-audioStarted-audioPauseTotal)-(recorder?.state==='paused'?(performance.now()-audioPausedAt):0);$('audioClock').textContent=clockString(elapsed);}
function stopMic(){if(micStream){micStream.getTracks().forEach(track=>track.stop());micStream=null;}if(audioTick){clearInterval(audioTick);audioTick=null;}}
function fileAsDataURL(file){return new Promise((resolve,reject)=>{const reader=new FileReader();reader.onload=()=>resolve(String(reader.result));reader.onerror=()=>reject(reader.error||new Error('Lettura audio fallita'));reader.readAsDataURL(file);});}
function buildAudioItem(a,editable=true){
 const line=document.createElement('div');line.className='audio-item';
 const label=document.createElement('strong');label.textContent=a.name||'Registrazione';line.append(label);
 const player=document.createElement('audio');player.controls=true;player.preload='none';player.src=a.data;player.setAttribute('aria-label','Ascolta '+(a.name||'registrazione'));line.append(player);
 if(editable){const del=document.createElement('button');del.textContent='Elimina audio';del.className='danger';del.onclick=()=>{if(confirm('Eliminare questa registrazione dalla nota?')){audioClips=audioClips.filter(x=>x.id!==a.id);renderAudioGallery();markDirty();}};line.append(del);}
 return line;
}
function onfimUpdateMediaTab(){const count=images.length+audioClips.length;$('photoCount').textContent=count?String(count):'';$('tabPhotos').setAttribute('aria-label',count?'Media, '+images.length+' foto e '+audioClips.length+' audio':'Media');}
function renderAudioGallery(){const list=$('audioGallery');list.replaceChildren();for(const clip of audioClips)list.append(buildAudioItem(clip));onfimUpdateMediaTab();}
async function startAudioRecording(){
 if(isRecording())return;
 if(!navigator.mediaDevices?.getUserMedia||!window.MediaRecorder){$('audioStatus').textContent='Registrazione non supportata in questo contesto: prova nella PWA HTTPS.';return;}
 audioStarting=true;recordingUI();
 try{
  micStream=await navigator.mediaDevices.getUserMedia({audio:true});
  const choices=['audio/webm;codecs=opus','audio/mp4','audio/webm'];
  const mime=choices.find(t=>MediaRecorder.isTypeSupported?.(t))||'';
  recorder=new MediaRecorder(micStream,mime?{mimeType:mime}:undefined);
  audioPieces=[];audioStarted=performance.now();audioPauseTotal=0;audioPausedAt=0;
  const ownRecorder=recorder;
  recorder.ondataavailable=e=>{const total=audioPieces.reduce((s,b)=>s+b.size,0);if(e.data?.size&&total+e.data.size<=MAX_AUDIO_BYTES-350000)audioPieces.push(e.data);if((e.data?.size&&total+e.data.size>MAX_AUDIO_BYTES-350000)||audioPieces.reduce((sum,b)=>sum+b.size,0)>MAX_AUDIO_BYTES-900000){if(ownRecorder.state!=='inactive'){$('audioStatus').textContent='Limite audio raggiunto: registrazione interrotta. La parte acquisita sarà conservata.';ownRecorder.stop();}}};
  recorder.onerror=e=>{$('audioStatus').textContent='Errore nella registrazione: '+(e.error?.message||'sconosciuto');stopMic();};
  recorder.onstop=async()=>{
    audioFinalizing=true;clearInterval(audioTick);audioTick=null;stopMic();
    const blob=new Blob(audioPieces,{type:ownRecorder.mimeType||audioPieces[0]?.type||'audio/webm'});
    recorder=null;recordingUI();
    try{
      if(!blob.size){$('audioStatus').textContent='Nessun audio acquisito.';return;}
      if(blob.size>MAX_AUDIO_BYTES){$('audioStatus').textContent='Registrazione non salvata: supera 10 MB.';return;}
      const data=await fileAsDataURL(blob),name='Registrazione '+new Date().toLocaleString('it-IT');
      audioClips.push({id:uid(),name,data,created:Date.now()});renderAudioGallery();markDirty();
      $('audioStatus').textContent='Registrazione aggiunta. Premi Salva per conservarla.';
    }catch(e){$('audioStatus').textContent='Impossibile salvare audio: '+e.message;}
    finally{audioFinalizing=false;recordingUI();}
  };
  recorder.start(850);audioStarting=false;$('audioStatus').textContent='Registrazione in corso…';$('audioClock').textContent='00:00';audioTick=setInterval(tickAudio,500);recordingUI();
 }catch(e){audioStarting=false;stopMic();recorder=null;recordingUI();const locallyOpened=/^(file:|content:)$/i.test(location.protocol);$('audioStatus').textContent=e.name==='NotAllowedError'?'Microfono: permesso negato.':e.name==='NotReadableError'&&locallyOpened?'Il microfono non si avvia da questa apertura locale. Prova onfim Lite dalla pagina HTTPS; se l’errore continua, controlla se un’altra app sta usando il microfono.':'Microfono non disponibile: '+(e.message||e.name||'errore sconosciuto');}
}
async function importAudioFiles(files){for(const f of files){if(!f.type.startsWith('audio/'))continue;if(f.size>MAX_AUDIO_BYTES){toast('Audio troppo grande (limite 10 MB): '+f.name);continue;}try{const data=await fileAsDataURL(f);audioClips.push({id:uid(),name:f.name||'Audio allegato',data,created:Date.now()});markDirty();}catch(e){toast('Errore audio: '+e.message);}}renderAudioGallery();}

function photoList(){const host=$('photoGallery');host.replaceChildren();onfimUpdateMediaTab();images.forEach((src,i)=>{const card=document.createElement('div');card.className='photo';const img=document.createElement('img');img.src=src;img.alt='Foto allegata';const del=document.createElement('button');del.type='button';del.className='remove-photo';del.textContent='×';del.title='Rimuovi foto';del.onclick=()=>{images.splice(i,1);photoMarks.splice(i,1);photoList();markDirty();};const edit=document.createElement('button');edit.type='button';edit.className='edit-photo';edit.innerHTML='<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><path d="M12 20h9"/><path d="M16.5 3.5a2.12 2.12 0 0 1 3 3L7 19l-4 1 1-4Z"/></svg>';edit.setAttribute('aria-label','Modifica segni sulla fotografia');edit.title='Modifica segni';edit.onclick=()=>openPhotoMarkup(i);if(/^data:image\/gif;/i.test(src)){edit.classList.add('hidden');edit.disabled=true;edit.title='Le GIF animate non si possono annotare';}card.append(img);if(photoMarks[i]){const mark=document.createElement('img');mark.src=photoMarks[i];mark.className='photo-mark-preview';mark.alt='';card.append(mark);}card.append(del,edit);host.append(card);});}
function editNote(n,allowPart=true){editorHasStoredCopy=!!allowPart;$('recoverNote').disabled=!allowPart;$('addPartEditor').classList.toggle('hidden',!allowPart);$('noteTitle').placeholder='Titolo (facoltativo)';clearTimeout(saveTimer);dirty=false;note={...n};images=[...(n.photos||[])];photoMarks=Array.isArray(n.photoMarks)?images.map((_,i)=>typeof n.photoMarks[i]==='string'?n.photoMarks[i]:''):images.map(()=>'');$('noteTitle').value=n.title||'';$('editorDates').textContent=noteDates(n);$('noteBody').innerHTML=sanitizeHTML(migratedText(n));selectionRange=null;lastHighlightAction=null;resetTextHistory();const colorSelect=$('noteColor');colorSelect.querySelector('[data-legacy-color]')?.remove();if(n.color&&![...colorSelect.options].some(o=>o.value===n.color)){const o=new Option('Colore precedente',n.color);o.dataset.legacyColor='1';colorSelect.add(o);}colorSelect.value=n.color||'#ffffff';updateNoteColorButton();$('reminder').value=n.reminder||'';$('reserved').checked=!!n.reserved;audioClips=Array.isArray(n.audios)?n.audios.filter(a=>a&&typeof a.data==='string'&&a.data.startsWith('data:audio/')):[];$('audioRecorderControls').classList.add('hidden');$('audioStatus').classList.add('hidden');$('audioClock').textContent='00:00';recordingUI();onfimEditorLinks=Array.isArray(n.linkedFiles)?n.linkedFiles.map(f=>({...f})):[];onfimRenderEditorLinks();renderAudioGallery();$('saveState').textContent='';$('deleteNote').classList.toggle('hidden',!n.title&&!n.text&&!(n.photos||[]).length&&!n.drawing&&!(n.audios||[]).length&&!n.persisted);photoList();showDrawing(n.drawing||'');updateTextMark();chooseTab('text');updateFormat();view('editView');}
function newNote(){editorFrom='list';const n=emptyNote();n.reserved=$('filter').value==='reserved'&&unlocked;n.favorite=$('filter').value==='favorites';editNote(n,false);$('deleteNote').classList.add('hidden');$('noteTitle').focus();}
// Un carosello per ciascuna sezione fotografica della nota aperta (anche composta).
// Non tocca la galleria dell'editor, le miniature Home o l'HTML condiviso.
function onfimReadCarousel(part,track){
  track.replaceChildren();track.scrollLeft=0;track.classList.add('onfim-photo-carousel');
  track.parentElement.querySelector('.onfim-photo-controls')?.remove();
  const photos=part.photos||[];
  for(let i=0;i<photos.length;i++){
    const src=photos[i];if(typeof src!=='string'||!src.startsWith('data:image/'))continue;
    const slide=document.createElement('div');slide.className='onfim-photo-slide';
    const frame=document.createElement('div');frame.className='annotated-photo';
    const img=document.createElement('img');img.src=src;img.alt='Fotografia '+(i+1);frame.append(img);
    const overlay=part.photoMarks?.[i];
    if(typeof overlay==='string'&&overlay.startsWith('data:image/')){
      const mark=document.createElement('img');mark.src=overlay;mark.alt='';mark.className='annotation-overlay';frame.append(mark);
    }
    if(typeof onfimPhotoTextButton==='function'){
      const ocr=onfimPhotoTextButton(src,part.id,'read');
      if(ocr){const bar=document.createElement('div');bar.className='onfim-photo-actions';bar.append(ocr);frame.append(bar);}
    }
    slide.append(frame);track.append(slide);
  }
  const total=track.children.length;if(total<2)return;
  const controls=document.createElement('div');controls.className='onfim-photo-controls';
  const prev=document.createElement('button'),next=document.createElement('button'),counter=document.createElement('span');
  prev.type=next.type='button';prev.textContent='‹';next.textContent='›';
  prev.setAttribute('aria-label','Foto precedente');next.setAttribute('aria-label','Foto successiva');
  counter.className='onfim-photo-count';counter.setAttribute('role','status');
  controls.append(prev,counter,next);track.after(controls);
  const current=()=>Math.max(0,Math.min(total-1,Math.round(track.scrollLeft/(track.clientWidth||1))));
  const update=()=>{const idx=current();counter.textContent=(idx+1)+'/'+total;prev.disabled=idx===0;next.disabled=idx===total-1;};
  prev.onclick=()=>track.scrollTo({left:(current()-1)*track.clientWidth,behavior:'smooth'});
  next.onclick=()=>track.scrollTo({left:(current()+1)*track.clientWidth,behavior:'smooth'});
  track.addEventListener('scroll',update,{passive:true});
  update();
}

async function openRead(n){
  const all=await allNotes(),root=groupRootFor(n,all),parts=chainMembers(root,all);
  n=root;
  if(!n)return;
  readId=n.id;
  $('chainParts').replaceChildren();
  $('chainParts').classList.toggle('hidden',parts.length===1);
  for(const id of ['readBody','readDrawWrap','readPhotoWrap','readAudioWrap'])$(id).classList.toggle('hidden',parts.length>1);
  $('readNote').style.setProperty('--note-color',n.color||'#ffffff');
  $('readTitle').textContent=n.title||'Senza titolo';$('readDates').textContent=noteDates(n,parts);
  const content=sanitizeHTML(migratedText(n));
  $('readBody').innerHTML=onfimLinkifyHTML(content);
  $('readBody').classList.toggle('read-empty',!txt(content).trim());
  if(!txt(content).trim())$('readBody').textContent=(n.drawing||(n.photos||[]).length||(n.audios||[]).length)?'':'Appunto vuoto';
  const goodData=s=>typeof s==='string'&&s.startsWith('data:image/');
  $('readDrawWrap').classList.toggle('hidden',!goodData(n.drawing));
  if(goodData(n.drawing))$('readDrawing').src=n.drawing;else $('readDrawing').removeAttribute('src');
  const gallery=$('readPhotos');onfimReadCarousel(n,gallery);
  $('readPhotoWrap').classList.toggle('hidden',!gallery.children.length);
  const audios=$('readAudios');audios.replaceChildren();
  for(const a of n.audios||[]){if(a&&typeof a.data==='string'&&a.data.startsWith('data:audio/'))audios.append(buildAudioItem(a,false));}
  $('readAudioWrap').classList.toggle('hidden',!audios.children.length);
  $('readNote').querySelectorAll('.root-linked-files').forEach(x=>x.remove());
  if(parts.length===1&&(n.linkedFiles||[]).length){const wrap=document.createElement('div');wrap.className='root-linked-files';onfimRenderFileRefs(n,wrap);$('readMeta').before(wrap);}
  const meta=$('readMeta');meta.replaceChildren();
  const addChip=s=>{const span=document.createElement('span');span.className='chip';span.textContent=s;meta.append(span);};
  if(n.reserved)addChip('🔒 Archivio');
  for(const tag of [...new Set(parts.flatMap(noteTags))]){
    const c=document.createElement('button');c.type='button';c.className='chip tag-filter-link';c.textContent=onfimTagLabel(tag);
    c.onclick=()=>{onfimToggleTagFilter(tag);view('listView');};
    meta.append(c);
  }
  if(n.reminder||n.geofence?.enabled){
    const button=document.createElement('button');button.type='button';button.className='read-reminder-link';
    button.innerHTML=ONFIM_ICONS.bell;
    const label=document.createElement('span');const when=new Date(n.reminder);
    label.textContent=n.reminder&&!Number.isNaN(when.getTime())?'Promemoria: '+when.toLocaleString('it-IT')+' · Modifica':'Promemoria geografico · Modifica';
    button.append(label);button.title='Modifica o rimuovi il promemoria';
    if(!onfimReminderActive(n))button.classList.add('onfim-reminder-expired');button.onclick=()=>void openReminderFor(n,false);meta.append(button);
  }
  if(parts.length>1){for(const [i,part] of parts.entries()){
    const block=makeChainPart(part,i+1,parts.length);
    $('chainParts').append(block);
  }}
  $('addSequel').classList.remove('hidden');
  $('joinExisting').classList.remove('hidden');
  $('starFromRead').classList.toggle('hidden',!!n.reserved);
  $('starFromRead').textContent='Preferito';
  $('starFromRead').setAttribute('aria-pressed',String(!!n.favorite));
  $('detachParts').classList.toggle('hidden',parts.length===1);
  $('editFromRead').textContent='Modifica';
  $('readFavOption').classList.toggle('hidden',!!n.reserved);
  $('readFavOption').querySelector('span').textContent=n.favorite?'Rimuovi dai Preferiti':'Aggiungi ai Preferiti';
  $('readPinOption').querySelector('span').textContent=n.pinned?'Rimuovi da Fissati':'Fissa in alto';
  $('readArchiveOption').querySelector('svg').outerHTML=n.reserved?ONFIM_ICONS.restore:ONFIM_ICONS.archive;$('readArchiveOption').querySelector('span').textContent=n.reserved?'Rimuovi dall’Archivio':'Sposta in Archivio';$('readReminderOption').querySelector('span').textContent=n.reminder||n.geofence?.enabled?'Modifica promemoria':'Promemoria';
  $('readDetachOption').classList.toggle('hidden',parts.length<=1);
  $('readDeleteOption').querySelector('span').textContent=parts.length>1?'Sposta appunto nel Cestino':'Sposta nel Cestino';
  for(const [key,isOn] of [['Pin',!!n.pinned],['Star',!!n.favorite],['Bell',!!(parts.some(onfimReminderActive))]]){
    const btn=$('readQuick'+key);btn.setAttribute('aria-pressed',String(isOn));
    const unavailable=key==='Star'&&!!n.reserved;btn.disabled=unavailable;
    const act=key==='Pin'?(isOn?'Rimuovi da Fissati':'Fissa in alto'):key==='Star'?(isOn?'Rimuovi dai Preferiti':'Aggiungi ai Preferiti'):(isOn?'Modifica promemoria':'Imposta promemoria');
    btn.title=unavailable?'Non disponibile nell’Archivio':act;btn.setAttribute('aria-label',btn.title);
  }
  $('readEditTop').title=parts.length>1?'Modifica prima parte':'Modifica';
  $('readEditTop').setAttribute('aria-label',parts.length>1?'Modifica prima parte':'Modifica');
  closeReadMenu();
  $('backRead').textContent=$('readBackBottom').textContent=n.reserved?'← Archivio':'← Appunti';
  view('readView');
}
// La lettura concatenata usa gli stessi contenuti salvati delle note semplici.
// Ogni parte e' ancora modificabile indipendentemente nell'editor normale.
const ONFIM_ICONS={pin:'<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><path d="m16 3 5 5-4 1-3 4-1 4-4-4-4-1 5-5 1-4zM9 15l-5 6"/></svg>',pencil:'<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><path d="M12 20h9"/><path d="M16.5 3.5a2.12 2.12 0 0 1 3 3L7 19l-4 1 1-4Z"/></svg>',more:'<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="5" r="1"/><circle cx="12" cy="12" r="1"/><circle cx="12" cy="19" r="1"/></svg>',star:'<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><path d="m12 2 3.1 6.3 6.9 1-5 4.9 1.2 6.8-6.2-3.3-6.2 3.3 1.2-6.8-5-4.9 6.9-1Z"/></svg>',archive:"<svg class=\"oi\" aria-hidden=\"true\" viewBox=\"0 0 24 24\" width=\"20\" height=\"20\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.85\" stroke-linecap=\"round\" stroke-linejoin=\"round\"><rect x=\"5\" y=\"10\" width=\"14\" height=\"11\" rx=\"2\"/><path d=\"M8 10V7a4 4 0 0 1 8 0v3\"/></svg>",restore:"<svg class=\"oi\" aria-hidden=\"true\" viewBox=\"0 0 24 24\" width=\"20\" height=\"20\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.85\" stroke-linecap=\"round\" stroke-linejoin=\"round\"><rect x=\"5\" y=\"10\" width=\"14\" height=\"11\" rx=\"2\"/><path d=\"M8 10V7a4 4 0 0 1 7-2.65\"/></svg>",bell:"<svg class=\"oi\" aria-hidden=\"true\" viewBox=\"0 0 24 24\" width=\"20\" height=\"20\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.85\" stroke-linecap=\"round\" stroke-linejoin=\"round\"><path d=\"M18 8a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9\"/><path d=\"M10 21h4\"/></svg>",plus:"<svg class=\"oi\" aria-hidden=\"true\" viewBox=\"0 0 24 24\" width=\"20\" height=\"20\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.85\" stroke-linecap=\"round\" stroke-linejoin=\"round\"><path d=\"M12 5v14M5 12h14\"/></svg>",trash:"<svg class=\"oi\" aria-hidden=\"true\" viewBox=\"0 0 24 24\" width=\"20\" height=\"20\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.85\" stroke-linecap=\"round\" stroke-linejoin=\"round\"><path d=\"M3 6h18M8 6V4h8v2M6 6l1 15h10l1-15M10 10v7M14 10v7\"/></svg>",up:"<svg class=\"oi\" aria-hidden=\"true\" viewBox=\"0 0 24 24\" width=\"20\" height=\"20\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.85\" stroke-linecap=\"round\" stroke-linejoin=\"round\"><path d=\"M12 19V5m-6 6 6-6 6 6\"/></svg>",down:"<svg class=\"oi\" aria-hidden=\"true\" viewBox=\"0 0 24 24\" width=\"20\" height=\"20\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.85\" stroke-linecap=\"round\" stroke-linejoin=\"round\"><path d=\"M12 5v14m-6-6 6 6 6-6\"/></svg>"};
function makeChainPart(n,number,total){
  const block=document.createElement('section');block.className='chain-part';
  const head=document.createElement('div');head.className='chain-part-head';
  const label=document.createElement('span');label.className='chain-part-label';
  const kind=txt(n.text||'').trim()?'Testo':(n.photos||[]).length?'Foto':n.drawing?'Disegno':(n.audios||[]).length?'Audio':'Appunto';
  label.textContent=number+' · '+kind;
  const actions=document.createElement('div');actions.className='chain-part-actions';
  const edit=document.createElement('button');edit.type='button';edit.innerHTML=ONFIM_ICONS.pencil;edit.title='Modifica parte '+number;edit.classList.add('icon-button','part-edit');edit.setAttribute('aria-label','Modifica parte '+number);
  edit.onclick=async()=>{const fresh=(await allNotes()).find(x=>x.id===n.id);if(!fresh){toast('Parte non trovata');return;}if(fresh.reserved&&!unlocked&&!await checkPin())return;editorFrom='read';editNote(fresh);};
  actions.append(edit);
  // Direct controls: no hidden popup for reordering.
  // The first part remains the stable root of the concatenation.
  function arrow(direction,label,svg){
    const btn=document.createElement('button');btn.type='button';
    btn.className='icon-button chain-move';btn.innerHTML=svg;
    btn.title=label+' parte '+number;
    btn.setAttribute('aria-label',label+' parte '+number);
    btn.onclick=e=>{e.stopPropagation();btn.disabled=true;void onfimMovePart(n.id,direction).finally(()=>{if(btn.isConnected)btn.disabled=false;});};
    return btn;
  }
  if(number>2)actions.prepend(arrow(-1,'Sposta su',ONFIM_ICONS.up));
  if(number>1&&number<total)actions.insertBefore(arrow(+1,'Sposta giù',ONFIM_ICONS.down),edit);
  head.append(label,actions);block.append(head);
  head.title='Tocca l’intestazione per modificare questa parte';
  head.addEventListener('click',e=>{if(e.target.closest('button,a,input,select'))return;edit.click();});
  if(number>1&&n.title){const title=document.createElement('h2');title.className='chain-part-title';title.textContent=n.title;block.append(title);}
  const markup=sanitizeHTML(migratedText(n));
  if(txt(markup).trim()){const body=document.createElement('div');body.className='read-body';body.innerHTML=onfimLinkifyHTML(markup);block.append(body);}
  if(typeof n.drawing==='string'&&n.drawing.startsWith('data:image/')){const wrap=document.createElement('div');wrap.className='read-media';const h=document.createElement('h2');h.textContent='Disegno';const img=document.createElement('img');img.className='read-drawing';img.src=n.drawing;img.alt='Disegno della parte '+number;wrap.append(h,img);block.append(wrap);}
  const photos=(n.photos||[]).filter(src=>typeof src==='string'&&src.startsWith('data:image/'));
  if(photos.length){const wrap=document.createElement('div');wrap.className='read-media';const h=document.createElement('h2');h.textContent='Foto';const gallery=document.createElement('div');gallery.className='read-photos';
    wrap.append(h,gallery);block.append(wrap);
    onfimReadCarousel(n,gallery);
  }
  if((n.audios||[]).length){const wrap=document.createElement('div');wrap.className='read-media';const h=document.createElement('h2');h.textContent='Registrazioni vocali';wrap.append(h);for(const a of n.audios){if(a&&typeof a.data==='string'&&a.data.startsWith('data:audio/'))wrap.append(buildAudioItem(a,false));}block.append(wrap);}
  onfimRenderFileRefs(n,block);
  if((n.reminder||noteTags(n).length)){const footer=document.createElement('div');footer.className='read-footer';for(const t of noteTags(n)){const c=document.createElement('span');c.className='chip';c.textContent=onfimTagLabel(t);footer.append(c);}if(n.reminder){const c=document.createElement('span');c.className='chip';c.textContent='◷ '+new Date(n.reminder).toLocaleString('it-IT');footer.append(c);}block.append(footer);}
  return block;
}

async function showSavedRead(){
  // Invocata soltanto dopo un salvataggio confermato, non da Chiudi.
  if(!(await ensureEditorSaved()))return;
  if(!note||!hasContent(note)){if(editorFrom==='read'&&readId){const root=(await allNotes()).find(n=>n.id===readId);if(root){await openRead(root);return;}}await reload();view('listView');return;}
  const current=(await allNotes()).find(n=>n.id===note.id);
  if(current)await openRead(current);else{await reload();view('listView');}
}

function chooseTab(name){
  if(name!=='draw'&&$('drawTab').classList.contains('expanded'))$('closeExpanded').click();
  for(const t of ['text','draw','photos']){
    $(t+'Tab').classList.toggle('shown',t===name);
    const tabButton=$('tab'+t[0].toUpperCase()+t.slice(1));tabButton.classList.toggle('selected',t===name);tabButton.setAttribute('aria-selected',String(t===name));
  }
  document.body.classList.toggle('onfim-drawing',name==='draw'&&$('editView').classList.contains('show'));
  if(name==='draw')requestAnimationFrame(fitDrawingCanvas);
}

// Keep an editor selection when the formatting toolbar receives a tap.
function rememberRange(){const s=window.getSelection();if(s&&s.rangeCount&&$('noteBody').contains(s.anchorNode))selectionRange=s.getRangeAt(0).cloneRange();}
function restoreRange(){const e=$('noteBody');e.focus();if(selectionRange){try{const s=window.getSelection();s.removeAllRanges();s.addRange(selectionRange);}catch{}}}
function updateFormat(){for(const b of document.querySelectorAll('[data-command]')){let active=false;try{active=document.queryCommandState(b.dataset.command);}catch{}b.classList.toggle('active',active);b.setAttribute('aria-pressed',String(active));}}
function dateTimeLabel(value){const d=new Date(Number(value));return Number.isFinite(d.getTime())?d.toLocaleString('it-IT',{day:'2-digit',month:'2-digit',year:'numeric',hour:'2-digit',minute:'2-digit'}):'—';}
function noteDates(n,parts=[n]){return 'Creato: '+dateTimeLabel(n.created)+' · Modificato: '+dateTimeLabel(Math.max(...parts.map(p=>Number(p.updated)||Number(p.created)||0)));}
function onfimTextAtEditor(value,where=null){
 const body=$('noteBody');body.focus();const selection=window.getSelection();
 let range=where?.cloneRange?.()||selectionRange?.cloneRange?.();
 if(!range||!body.contains(range.commonAncestorContainer)){range=document.createRange();range.selectNodeContents(body);range.collapse(false);}
 range.deleteContents();const text=document.createTextNode(value);range.insertNode(text);
 range.setStartAfter(text);range.collapse(true);selection.removeAllRanges();selection.addRange(range);
 rememberRange();markDirty();recordTextHistory(true);updateTextMark();onfimUpdatePointEdit();
}
function onfimEditorInsertionPrefix(){
 const range=selectionRange;if(!range||!$('noteBody').contains(range.startContainer))return '';
 const before=range.cloneRange();before.selectNodeContents($('noteBody'));before.setEnd(range.startContainer,range.startOffset);
 const value=before.toString();return value&&!value.endsWith('\n')?'\n':'';
}
function onfimStampDate(d){const z=v=>String(v).padStart(2,'0');return '@'+z(d.getDate())+'/'+z(d.getMonth()+1)+'/'+d.getFullYear()+'-'+z(d.getHours())+':'+z(d.getMinutes());}
function insertJournalTimestamp(){onfimTextAtEditor(onfimEditorInsertionPrefix()+onfimStampDate(new Date())+' ');}
function onfimCoordText(lat,lon,latDecimals=4,lonDecimals=latDecimals){
 const axis=(v,p,n,digits)=>Math.abs(v).toFixed(Math.max(4,Math.min(6,digits)))+(v<0?n:p);
 return '@'+axis(lat,'N','S',latDecimals)+','+axis(lon,'E','W',lonDecimals);
}
function onfimEditorGeoAtCaret(){
 const body=$('noteBody');const sel=window.getSelection();
 let range=sel&&sel.rangeCount?sel.getRangeAt(0):null;
 if(!range||!body.contains(range.commonAncestorContainer))range=selectionRange;
 if(!range||!body.contains(range.startContainer)||range.startContainer.nodeType!==Node.TEXT_NODE)return null;
 if(range.startContainer!==range.endContainer)return null;
 const node=range.startContainer,refs=onfimFindRefs(node.nodeValue,'point');
 const ref=refs.find(r=>range.startOffset>=r.start&&range.startOffset<=r.end&&range.endOffset<=r.end);
 return ref?{node,...ref}:null;
}
const onfimGpsIcon=$('insertGpsPoint').innerHTML;
const onfimMapEditIcon='<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><path d="m3 6 6-3 6 3 6-3v15l-6 3-6-3-6 3Z"/><path d="M9 3v15M15 6v15"/></svg>';
function onfimUpdatePointEdit(){
 const b=$('insertGpsPoint'),editing=!!onfimEditorGeoAtCaret();
 b.innerHTML=editing?onfimMapEditIcon:onfimGpsIcon;
 b.title=editing?'Modifica questa posizione sulla mappa':'Inserisci posizione GPS nel testo';
 b.setAttribute('aria-label',b.title);
}
function onfimPositionGPS(){
 if(onfimEditorGeoAtCaret()){onfimOpenPointMap();return;}
 const selected=selectionRange?.cloneRange?.()||null;
 if(!navigator.geolocation){toast('GPS non disponibile in questo browser');return;}
 $('insertGpsPoint').disabled=true;
 navigator.geolocation.getCurrentPosition(p=>{
  $('insertGpsPoint').disabled=false;
  const value=onfimCoordText(p.coords.latitude,p.coords.longitude);
  onfimTextAtEditor(value+' ',selected);
  toast('Posizione inserita; puoi correggerla nel testo o sulla mappa.');
 },e=>{$('insertGpsPoint').disabled=false;toast('Posizione non disponibile: '+e.message);},
 {enableHighAccuracy:true,timeout:14000,maximumAge:30000});
}
// Il selettore cartografico è quello dei geofence, ma in questa modalità
// modifica solo il testo, mai i promemoria né le relative impostazioni.
let onfimGeoInsertMode=false,onfimGeoEditTarget=null;
function onfimOpenPointMap(){
 const ref=onfimEditorGeoAtCaret();if(!ref)return;
 onfimGeoEditTarget={node:ref.node,start:ref.start,end:ref.end,original:ref.value};
 onfimGeoInsertMode=true;
 $('onfimPointMapDock').append($('geoMapFrame'));
 $('onfimPointLat').value=String(ref.lat);$('onfimPointLon').value=String(ref.lon);
 $('onfimPointStatus').textContent='Sposta il punto o modifica i numeri. La mappa richiede Internet.';
 $('onfimPointDialog').showModal();onfimGeoCenter(ref.lat,ref.lon,16,false);
 requestAnimationFrame(geoMapRender);
}
function onfimClosePointMap(){
 if($('geoExpandedDialog').open)onfimCloseExpandedMap();
 if($('onfimPointDialog').open)$('onfimPointDialog').close();
 if($('geoMapFrame').parentElement!==$('geoMapHome'))$('geoMapHome').append($('geoMapFrame'));
 onfimGeoInsertMode=false;onfimGeoEditTarget=null;
}
$('insertJournalStamp').addEventListener('pointerdown',e=>e.preventDefault());
$('insertJournalStamp').onclick=insertJournalTimestamp;
$('insertGpsPoint').addEventListener('pointerdown',e=>e.preventDefault());
$('insertGpsPoint').onclick=onfimPositionGPS;
$('onfimPointCancel').onclick=onfimClosePointMap;
$('onfimPointDialog').addEventListener('close',()=>{
 if($('geoExpandedDialog').open)onfimCloseExpandedMap();
 if($('geoMapFrame').parentElement!==$('geoMapHome'))$('geoMapHome').append($('geoMapFrame'));
 onfimGeoInsertMode=false;onfimGeoEditTarget=null;
});
$('onfimPointConfirm').onclick=()=>{
 const lat=Number($('onfimPointLat').value),lon=Number($('onfimPointLon').value),target=onfimGeoEditTarget;
 if(!$('onfimPointLat').value.trim()||!$('onfimPointLon').value.trim()||!Number.isFinite(lat)||!Number.isFinite(lon)||Math.abs(lat)>90||Math.abs(lon)>180){$('onfimPointStatus').textContent='Coordinate non valide (latitudine ±90°, longitudine ±180°).';return;}
 const node=target?.node;
 if(!node||!$('noteBody').contains(node)||node.nodeValue.slice(target.start,target.end)!==target.original){$('onfimPointStatus').textContent='Il testo è cambiato: chiudi e seleziona nuovamente le coordinate.';return;}
 const range=document.createRange();range.setStart(node,target.start);range.setEnd(node,target.end);
 const decimals=[...(target.original.matchAll(/\.(\d{1,6})[NSEW]/g))].map(m=>m[1].length);
 onfimClosePointMap();onfimTextAtEditor(onfimCoordText(lat,lon,decimals[0]||4,decimals[1]||4),range);toast('Posizione aggiornata nella nota.');
};
$('onfimPointCurrent').onclick=()=>{
 if(!navigator.geolocation){$('onfimPointStatus').textContent='GPS non disponibile';return;}
 $('onfimPointStatus').textContent='Rilevamento posizione…';
 navigator.geolocation.getCurrentPosition(p=>{
  if(!$('onfimPointDialog').open)return;
  onfimGeoCenter(p.coords.latitude,p.coords.longitude,16,true);
  $('onfimPointStatus').textContent='Posizione attuale rilevata.';
 },e=>{$('onfimPointStatus').textContent='GPS non disponibile: '+e.message;},
 {enableHighAccuracy:true,timeout:14000,maximumAge:30000});
};
for(const id of ['onfimPointLat','onfimPointLon'])$(id).addEventListener('change',()=>{
 const la=$('onfimPointLat').value,lo=$('onfimPointLon').value;
 if(la&&lo){const lat=Number(la),lon=Number(lo);
  if(Number.isFinite(lat)&&Number.isFinite(lon)&&Math.abs(lat)<=90&&Math.abs(lon)<=180)onfimGeoCenter(lat,lon,onfimGeo.z,false);
 }
});

// Onfim 0.8.14: elenchi automatici all'inizio di un paragrafo.
// Eseguito DOPO l'inserimento dello spazio per supportare anche la tastiera Android.
// Non interpreta gli incollaggi, la composizione IME o segni nel mezzo del testo.
function onfimAutoListFromTyping(e){
  if(e.isComposing || e.inputType!=='insertText' || (e.data!==null && e.data!==undefined && e.data!==' '))return false;
  const host=$('noteBody'),sel=window.getSelection();
  if(document.activeElement!==host || !sel || !sel.rangeCount || !sel.isCollapsed)return false;
  const caret=sel.getRangeAt(0),node=caret.startContainer;
  if(node.nodeType!==Node.TEXT_NODE)return false;
  const text=node.textContent||'',offset=caret.startOffset;
  if(offset!==text.length)return false;
  const prefix=text.slice(0,offset);
  // Chrome e Android possono normalizzare lo spazio finale in NBSP.
  const typed=prefix.replace(/ /g,' ');
  if(typed!=='- ' && typed!=='1. ')return false;
  let block=node.parentElement;
  while(block&&block!==host&&!['P','DIV'].includes(block.tagName))block=block.parentElement;
  if(!block || (block!==host && (block.textContent!==prefix||block.closest('li'))))return false;
  if(block===host && (node.parentNode!==host||host.textContent!==prefix))return false;
  const ordered=typed==='1. ';
  // Sostituiamo SOLO il paragrafo corrente. execCommand sui paragrafi vuoti
  // può formattare la riga precedente e trasformare contenuti non richiesti.
  recordTextHistory(true);
  const list=document.createElement(ordered?'ol':'ul');
  const li=document.createElement('li');li.append(document.createElement('br'));list.append(li);
  if(block===host)node.replaceWith(list);else block.replaceWith(list);
  const atStart=document.createRange();atStart.setStart(li,0);atStart.collapse(true);
  sel.removeAllRanges();sel.addRange(atStart);
  rememberRange();markDirty();recordTextHistory(true);updateFormat();updateTextMark();
  return true;
}
function applyCommand(command,value=null){restoreRange();document.execCommand(command,false,value);rememberRange();updateFormat();markDirty();recordTextHistory(true);updateTextMark();}
function updateTextUndoUI(){$('textUndo').disabled=textHistoryAt<=0;$('textRedo').disabled=textHistoryAt>=textHistory.length-1;}
function resetTextHistory(){clearTimeout(textHistoryTimer);textHistory=[$('noteBody').innerHTML];textHistoryAt=0;updateTextUndoUI();}
function recordTextHistory(immediate=false){clearTimeout(textHistoryTimer);if(!immediate){textHistoryTimer=setTimeout(()=>recordTextHistory(true),420);return;}const html=$('noteBody').innerHTML;if(textHistory[textHistoryAt]===html)return;textHistory=textHistory.slice(0,textHistoryAt+1);textHistory.push(html);if(textHistory.length>60)textHistory.shift();textHistoryAt=textHistory.length-1;updateTextUndoUI();}
// Recupero di emergenza: solo contenuti della nota, non permessi, raccolte o promemoria.
const ONFIM_RECOVERY_FIELDS=['title','text','checklist','photos','photoMarks','drawing','audios','linkedFiles','color','tags'];
function onfimRecoveryKey(n){
  function canonical(value){
    if(Array.isArray(value))return value.map(canonical);
    if(value&&typeof value==='object')return Object.fromEntries(Object.keys(value).sort().map(k=>[k,canonical(value[k])]));
    return value===undefined?null:value;
  }
  return JSON.stringify(ONFIM_RECOVERY_FIELDS.map(key=>canonical(n?.[key]??null)));
}
let onfimRecoveryWorking=false;
async function onfimFindPreviousVersion(current){
  if(typeof window.OnfimAndroid!=='undefined'){
    if(typeof OnfimAndroid.findPreviousNote!=='function')throw new Error('Aggiorna il contenitore Android per usare il recupero.');
    const response=JSON.parse(OnfimAndroid.findPreviousNote(current.id,JSON.stringify(current)));
    if(response.error)throw new Error(response.error);
    return response.found?response:null;
  }
  if(!snapshotDb)throw new Error('Copie interne non disponibili nel browser.');
  const copies=(await snapshotStoreAll()).sort((a,b)=>b.id-a.id),fingerprint=onfimRecoveryKey(current);
  for(const copy of copies){
    const old=(copy.notes||[]).find(x=>x?.id===current.id);
    if(old&&!old.deletedAt&&onfimRecoveryKey(old)!==fingerprint)return {found:true,note:old,createdAt:copy.createdAt||new Date(copy.id).toISOString()};
  }
  return null;
}
async function onfimRecoverNote(){
  if(onfimRecoveryWorking||!note)return;
  onfimRecoveryWorking=true;
  const button=$('recoverNote');button.disabled=true;
  try{
    if(isRecording()){toast('Ferma la registrazione prima del recupero.');return;}
    if(!(await ensureEditorSaved()))return;
    const current=note,old=await onfimFindPreviousVersion(current);
    if(!old?.note){toast(old?.reason||'Nessuna versione differente nei backup disponibili.');return;}
    const candidate=old.note;
    const stamp=new Date(old.createdAt||old.date||0);
    const date=Number.isFinite(stamp.getTime())?stamp.toLocaleString('it-IT'):'data non disponibile';
    const preview=txt(candidate.text||'').trim();
    const details=[candidate.title?'Titolo: '+candidate.title:'Senza titolo',
      preview?'Testo: '+preview.slice(0,650)+(preview.length>650?'…':''):'Testo vuoto',
      (candidate.photos||[]).length+' foto · '+(candidate.audios||[]).length+' audio'+(candidate.drawing?' · disegno':'')];
    if(!confirm('Versione del '+date+'\n\n'+details.join('\n')+'\n\nRecuperare questo contenuto? Le altre note e i promemoria non verranno modificati.'))return;
    if(note?.id!==current.id)throw new Error('La nota aperta è cambiata.');
    const recovered={...current};
    for(const field of ONFIM_RECOVERY_FIELDS){if(Object.hasOwn(candidate,field))recovered[field]=candidate[field];else delete recovered[field];}
    recovered.updated=Date.now();
    await putNote(recovered);
    editorFrom=editorFrom||'list';
    editNote(recovered);
    toast('Versione precedente recuperata.');
  }catch(e){toast('Recupero non riuscito: '+(e.message||e));}
  finally{onfimRecoveryWorking=false;button.disabled=false;}
}
$('recoverNote').onclick=onfimRecoverNote;

function textUndoOrRedo(direction){clearTimeout(textHistoryTimer);recordTextHistory(true);const next=textHistoryAt+direction;if(next<0||next>=textHistory.length)return;textHistoryAt=next;const el=$('noteBody');el.innerHTML=textHistory[textHistoryAt];el.focus();const sel=window.getSelection(),range=document.createRange();range.selectNodeContents(el);range.collapse(false);sel.removeAllRanges();sel.addRange(range);rememberRange();updateTextUndoUI();updateFormat();markDirty();updateTextMark();}

// Text stamps are part of the same raster layer as pen marks; undo restores the previous raster.
function onfimStampText(c,ctx,text,p,size,col){
 const box=c.getBoundingClientRect();if(!box.width||!box.height)return;
 const font=Math.max(9,Math.round((21+size*1.1)*c.width/box.width));
 ctx.save();ctx.globalCompositeOperation='source-over';ctx.fillStyle=col;ctx.font='600 '+font+'px system-ui, sans-serif';ctx.textBaseline='top';
 const maxW=Math.max(12,c.width-p.x-3);ctx.fillText(text,p.x,p.y,maxW);ctx.restore();
}
function onfimMoveTextPreview(preview,c,txt,p,col,size){
 const box=c.getBoundingClientRect(),parent=preview.parentElement.getBoundingClientRect();
 preview.textContent=txt;preview.style.color=col;preview.style.fontSize=(21+size*1.1)+'px';
 preview.style.left=(box.left-parent.left+p.x/c.width*box.width)+'px';
 preview.style.top=(box.top-parent.top+p.y/c.height*box.height)+'px';
 preview.classList.remove('hidden');
}

const canvas=$('drawCanvas'),ctx=canvas.getContext('2d');ctx.lineJoin='round';ctx.lineCap='round';
// Dimensioni CSS del foglio: l'immagine intera resta visibile, senza zoom o tagli.
// Non modifica né i pixel né i dati del disegno.
function fitDrawingCanvas(){
  if(!$('drawTab').classList.contains('shown'))return;
  const frame=$('drawTab').querySelector('.drawframe');
  const box=frame.getBoundingClientRect();
  const w=Math.max(1,box.width-2),h=Math.max(1,box.height-2);
  const ratio=canvas.width/canvas.height;
  const actualW=Math.min(w,h*ratio),actualH=actualW/ratio;
  canvas.style.width=actualW+'px';canvas.style.height=actualH+'px';
}
const fitObserver=new ResizeObserver(()=>{if(document.body.classList.contains('onfim-drawing'))requestAnimationFrame(fitDrawingCanvas);});
fitObserver.observe($('drawTab').querySelector('.drawframe'));
window.addEventListener('resize',()=>requestAnimationFrame(fitDrawingCanvas));
window.visualViewport?.addEventListener('resize',()=>requestAnimationFrame(fitDrawingCanvas));
function point(e){const r=canvas.getBoundingClientRect();return{x:(e.clientX-r.left)/r.width*canvas.width,y:(e.clientY-r.top)/r.height*canvas.height};}
canvas.addEventListener('pointerdown',e=>{e.preventDefault();if(drawTextMode){const text=$('drawTextInput').value.trim();if(!text){$('drawTextInput').focus();return;}drawTextActive=true;drawTextPoint=point(e);canvas.setPointerCapture(e.pointerId);onfimMoveTextPreview($('drawTextPreview'),canvas,text,drawTextPoint,pen,Number($('penSize').value));return;}saveDrawUndo();painting=true;last=point(e);canvas.setPointerCapture(e.pointerId);ctx.strokeStyle=erasing?'#ffffff':pen;ctx.lineWidth=Number($('penSize').value)*(erasing?4:1);ctx.beginPath();ctx.arc(last.x,last.y,ctx.lineWidth/2,0,Math.PI*2);ctx.fillStyle=ctx.strokeStyle;ctx.fill();});
canvas.addEventListener('pointermove',e=>{if(drawTextActive){e.preventDefault();drawTextPoint=point(e);onfimMoveTextPreview($('drawTextPreview'),canvas,$('drawTextInput').value.trim(),drawTextPoint,pen,Number($('penSize').value));return;}if(!painting)return;e.preventDefault();const p=point(e);ctx.strokeStyle=erasing?'#ffffff':pen;ctx.lineWidth=Number($('penSize').value)*(erasing?4:1);ctx.beginPath();ctx.moveTo(last.x,last.y);ctx.lineTo(p.x,p.y);ctx.stroke();last=p;});
function finishStroke(){if(drawTextActive){drawTextActive=false;return;}if(!painting)return;painting=false;last=null;drawn=true;updateDrawingMark();markDirty();}canvas.addEventListener('pointerup',finishStroke);canvas.addEventListener('pointercancel',finishStroke);
let drawTextMode=false,drawTextActive=false,drawTextPoint=null;function drawTextSet(enabled){if(!enabled&&drawTextMode&&drawTextPoint&&$('drawTextInput').value.trim())$('drawTextApply').click();if(!enabled){drawTextPoint=null;$('drawTextPreview').classList.add('hidden');}drawTextMode=enabled;$('penSizeLabel').textContent=enabled?'Dimensione':'Spessore';$('drawTextTool').classList.toggle('active',enabled);$('drawTextTool').setAttribute('aria-pressed',String(enabled));$('drawTextEntry').classList.toggle('hidden',!enabled);if(enabled){$('penButton').classList.remove('active');$('eraserButton').classList.remove('active');$('drawTextInput').focus();}else $('drawTextPreview').classList.add('hidden');}
$('drawTextTool').onclick=()=>drawTextSet(!drawTextMode);
$('drawTextApply').onclick=()=>{const text=$('drawTextInput').value.trim();if(!drawTextPoint||!text){toast('Scrivi e posiziona il testo sul foglio');return;}
  saveDrawUndo();onfimStampText(canvas,ctx,text,drawTextPoint,Number($('penSize').value),pen);
  drawn=true;updateDrawingMark();markDirty();drawTextPoint=null;$('drawTextPreview').classList.add('hidden');};
$('drawTextCancel').onclick=()=>{drawTextPoint=null;$('drawTextPreview').classList.add('hidden');};
$('drawTextInput').addEventListener('input',()=>{if(drawTextMode&&drawTextPoint)onfimMoveTextPreview($('drawTextPreview'),canvas,$('drawTextInput').value.trim(),drawTextPoint,pen,Number($('penSize').value));});

function penMode(eraser){drawTextSet(false);erasing=eraser;$('penButton').classList.toggle('active',!eraser);$('eraserButton').classList.toggle('active',eraser);$('penButton').setAttribute('aria-pressed',String(!eraser));$('eraserButton').setAttribute('aria-pressed',String(eraser));}

// Annotazioni foto: un PNG trasparente separato conserva sempre l'immagine originale.
let photoTextMode=false,photoTextActive=false,photoTextPoint=null;
let activePhotoMark=-1,markPainting=false,markLast=null,markErase=false,markColor='#202a34',markUndo=[],markRedo=[],markGeneration=0;
const markCanvas=$('photoMarkCanvas'),markCtx=markCanvas.getContext('2d');
function photoMarkButtons(){$('photoMarkUndo').disabled=!markUndo.length;$('photoMarkRedo').disabled=!markRedo.length;}
function markSnapshot(){return markCanvas.toDataURL('image/png');}
function pushPhotoMark(){markUndo.push(markSnapshot());if(markUndo.length>15)markUndo.shift();markRedo=[];photoMarkButtons();}
function loadMarkSnapshot(src){const token=++markGeneration,img=new Image();img.onload=()=>{if(token!==markGeneration)return;markCtx.clearRect(0,0,markCanvas.width,markCanvas.height);markCtx.drawImage(img,0,0,markCanvas.width,markCanvas.height);};img.src=src;}
function historyPhotoMark(direction){const src=direction===-1?markUndo:markRedo,dst=direction===-1?markRedo:markUndo;if(!src.length)return;dst.push(markSnapshot());loadMarkSnapshot(src.pop());photoMarkButtons();}
function photoTextSet(enabled){if(!enabled&&photoTextMode&&photoTextPoint&&$('photoTextInput').value.trim())$('photoTextApply').click();if(!enabled){photoTextPoint=null;$('photoTextPreview').classList.add('hidden');}photoTextMode=enabled;$('photoMarkSizeLabel').textContent=enabled?'Dimensione':'Spessore';$('photoMarkTextTool').classList.toggle('active',enabled);$('photoMarkTextTool').setAttribute('aria-pressed',String(enabled));$('photoTextEntry').classList.toggle('hidden',!enabled);if(enabled){$('photoMarkPen').classList.remove('active');$('photoMarkEraser').classList.remove('active');$('photoTextInput').focus();}else $('photoTextPreview').classList.add('hidden');}
$('photoMarkTextTool').onclick=()=>photoTextSet(!photoTextMode);
$('photoTextApply').onclick=()=>{const text=$('photoTextInput').value.trim();if(!photoTextPoint||!text){toast('Scrivi e posiziona il testo sulla foto');return;}
  pushPhotoMark();onfimStampText(markCanvas,markCtx,text,photoTextPoint,Number($('photoMarkSize').value),markColor);
  photoTextPoint=null;$('photoTextPreview').classList.add('hidden');};
$('photoTextCancel').onclick=()=>{photoTextPoint=null;$('photoTextPreview').classList.add('hidden');};
$('photoTextInput').addEventListener('input',()=>{if(photoTextMode&&photoTextPoint)onfimMoveTextPreview($('photoTextPreview'),markCanvas,$('photoTextInput').value.trim(),photoTextPoint,markColor,Number($('photoMarkSize').value));});
// 0.8.12 — dimensione testo, conferma da tastiera, anteprima aggiornabile
for(const cfg of [
 {input:'drawTextInput',size:'penSize',preview:'drawTextPreview',canvas:canvas, point:()=>drawTextPoint, active:()=>drawTextMode, color:()=>pen,confirm:'drawTextApply',cancel:'drawTextCancel'},
 {input:'photoTextInput',size:'photoMarkSize',preview:'photoTextPreview',canvas:markCanvas, point:()=>photoTextPoint, active:()=>photoTextMode, color:()=>markColor,confirm:'photoTextApply',cancel:'photoTextCancel'}
]){
 const inp=$(cfg.input),size=$(cfg.size);
 const refresh=()=>{if(cfg.active()&&cfg.point())onfimMoveTextPreview($(cfg.preview),cfg.canvas,inp.value.trim(),cfg.point(),cfg.color(),Number(size.value));};
 size.addEventListener('input',refresh);
 inp.addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();$(cfg.confirm).click();}else if(e.key==='Escape'){e.preventDefault();$(cfg.cancel).click();}});
}


function markMode(erase){photoTextSet(false);markErase=erase;$('photoMarkPen').classList.toggle('active',!erase);$('photoMarkEraser').classList.toggle('active',erase);}

// The right-hand rail scrolls independently from the annotation canvas.
let photoMarkScrollUpdating=false;
function onfimSyncPhotoRail(){const view=$('photoMarkViewport'),rail=$('photoMarkScrollbar');const amount=Math.max(0,view.scrollHeight-view.clientHeight);rail.disabled=amount<2;rail.value=amount?String(Math.round(view.scrollTop/amount*1000)):'0';$('photoMarkScrollWrap').classList.toggle('inactive',amount<2);}
$('photoMarkScrollbar').addEventListener('input',()=>{const view=$('photoMarkViewport'),rail=$('photoMarkScrollbar');view.scrollTop=(view.scrollHeight-view.clientHeight)*(Number(rail.value)/1000);});
$('photoMarkViewport').addEventListener('scroll',onfimSyncPhotoRail,{passive:true});
new ResizeObserver(onfimSyncPhotoRail).observe($('photoMarkViewport'));
new ResizeObserver(onfimSyncPhotoRail).observe($('photoMarkSurface'));

function closePhotoMarkup(){photoTextSet(false);$('photoMarkDialog').close();document.body.classList.remove('annotating');activePhotoMark=-1;}
function openPhotoMarkup(i){if(!images[i])return;activePhotoMark=i;const img=new Image();const src=images[i],old=photoMarks[i]||'';img.onload=()=>{if(activePhotoMark!==i)return;const w=img.naturalWidth,h=img.naturalHeight;markCanvas.width=w;markCanvas.height=h;$('photoMarkBase').src=src;$('photoMarkSurface').style.aspectRatio=w+' / '+h;markCtx.clearRect(0,0,w,h);markUndo=[];markRedo=[];photoMarkButtons();markMode(false);markColor='#202a34';document.querySelectorAll('[data-mark]').forEach(b=>b.classList.toggle('selected',b.dataset.mark===markColor));if(old)loadMarkSnapshot(old);$('photoMarkDialog').showModal();$('photoMarkViewport').scrollTop=0;requestAnimationFrame(onfimSyncPhotoRail);document.body.classList.add('annotating');};img.src=src;}
function markPoint(e){const box=markCanvas.getBoundingClientRect();return{x:(e.clientX-box.left)/box.width*markCanvas.width,y:(e.clientY-box.top)/box.height*markCanvas.height};}
markCanvas.addEventListener('pointerdown',e=>{if(activePhotoMark<0)return;e.preventDefault();if(photoTextMode){const text=$('photoTextInput').value.trim();if(!text){$('photoTextInput').focus();return;}photoTextActive=true;photoTextPoint=markPoint(e);markCanvas.setPointerCapture(e.pointerId);onfimMoveTextPreview($('photoTextPreview'),markCanvas,text,photoTextPoint,markColor,Number($('photoMarkSize').value));return;}pushPhotoMark();markPainting=true;markLast=markPoint(e);markCanvas.setPointerCapture(e.pointerId);const ctx=markCtx;ctx.save();ctx.globalCompositeOperation=markErase?'destination-out':'source-over';ctx.fillStyle=markErase?'rgba(0,0,0,1)':markColor;const radius=Number($('photoMarkSize').value)*(markErase?4:1)/2;ctx.beginPath();ctx.arc(markLast.x,markLast.y,radius,0,Math.PI*2);ctx.fill();ctx.restore();});
markCanvas.addEventListener('pointermove',e=>{if(photoTextActive){e.preventDefault();photoTextPoint=markPoint(e);onfimMoveTextPreview($('photoTextPreview'),markCanvas,$('photoTextInput').value.trim(),photoTextPoint,markColor,Number($('photoMarkSize').value));return;}if(!markPainting)return;e.preventDefault();const p=markPoint(e);markCtx.save();markCtx.globalCompositeOperation=markErase?'destination-out':'source-over';markCtx.strokeStyle=markErase?'rgba(0,0,0,1)':markColor;markCtx.lineWidth=Number($('photoMarkSize').value)*(markErase?4:1);markCtx.lineCap='round';markCtx.lineJoin='round';markCtx.beginPath();markCtx.moveTo(markLast.x,markLast.y);markCtx.lineTo(p.x,p.y);markCtx.stroke();markCtx.restore();markLast=p;});
function finishPhotoMark(){if(photoTextActive){photoTextActive=false;return;}markPainting=false;markLast=null;}
markCanvas.addEventListener('pointerup',finishPhotoMark);markCanvas.addEventListener('pointercancel',finishPhotoMark);
$('photoMarkClear').onclick=()=>{if(!confirm('Cancellare tutti i segni su questa foto?'))return;pushPhotoMark();markCtx.clearRect(0,0,markCanvas.width,markCanvas.height);photoMarkButtons();};
$('photoMarkPen').onclick=()=>markMode(false);$('photoMarkEraser').onclick=()=>markMode(true);$('photoMarkUndo').onclick=()=>historyPhotoMark(-1);$('photoMarkRedo').onclick=()=>historyPhotoMark(1);
for(const b of document.querySelectorAll('[data-mark]'))b.onclick=()=>{markColor=b.dataset.mark;if(!photoTextMode)markMode(false);document.querySelectorAll('[data-mark]').forEach(x=>x.classList.toggle('selected',x===b));};
$('photoMarkCustom').onclick=()=>openOnfimColorPicker('photo');
$('photoMarkClose').onclick=$('photoMarkCancel').onclick=closePhotoMarkup;
$('photoMarkDialog').addEventListener('cancel',e=>{e.preventDefault();closePhotoMarkup();});
$('photoMarkSave').onclick=()=>{if(activePhotoMark<0)return;if(photoTextPoint)$('photoTextApply').click();photoMarks[activePhotoMark]=markSnapshot();closePhotoMarkup();photoList();markDirty();};
function resizePhoto(f){return new Promise((res,rej)=>{const url=URL.createObjectURL(f),im=new Image();im.onload=()=>{URL.revokeObjectURL(url);const scale=Math.min(1,1600/Math.max(im.width,im.height));const c=document.createElement('canvas');c.width=Math.max(1,Math.round(im.width*scale));c.height=Math.max(1,Math.round(im.height*scale));const x=c.getContext('2d');x.fillStyle='white';x.fillRect(0,0,c.width,c.height);x.drawImage(im,0,0,c.width,c.height);res(c.toDataURL('image/jpeg',.8));};im.onerror=()=>{URL.revokeObjectURL(url);rej(new Error('Formato immagine non supportato.'));};im.src=url;});}
const ONFIM_MAX_GIF_BYTES=5*1024*1024;
function onfimReadGif(file){return new Promise((resolve,reject)=>{
  if(file.size>ONFIM_MAX_GIF_BYTES){reject(new Error('GIF superiore a 5 MB: scegli una GIF più piccola.'));return;}
  const reader=new FileReader();
  reader.onload=()=>{
    const data=String(reader.result||'');
    if(!/^data:image\/gif;base64,/i.test(data))reject(new Error('GIF non valida.'));
    else resolve(data);
  };
  reader.onerror=()=>reject(new Error('Lettura GIF non riuscita.'));
  reader.readAsDataURL(file);
});}
async function readPhotos(list){
  let added=0;
  for(const file of [...list]){
    if(!file.type.startsWith('image/')&&!/\.gif$/i.test(file.name))continue;
    try{
      const gif=file.type.toLowerCase()==='image/gif'||/\.gif$/i.test(file.name);
      images.push(gif?await onfimReadGif(file):await resizePhoto(file));
      photoMarks.push('');added++;
    }catch(e){toast('Immagine non importata: '+e.message);}
  }
  photoList();if(added)markDirty();
}
function recordDataChange(){try{localStorage.setItem(LAST_CHANGE_KEY,String(Date.now()));}catch(e){console.warn('Onfim: impossibile registrare data modifica',e);}void refreshBackupStatus();scheduleLocalSnapshot();}
function backupState(notes){
  const lastExport=Number(localStorage.getItem(LAST_EXPORT_KEY))||0;
  const marker=Number(localStorage.getItem(LAST_CHANGE_KEY))||0;
  const latestChange=Math.max(marker,...notes.map(n=>Number(n.updated)||Number(n.created)||0),0);
  const format=t=>new Date(t).toLocaleString(onfimCurrentLocale(),{day:'2-digit',month:'2-digit',year:'numeric',hour:'2-digit',minute:'2-digit'});
  if(!lastExport)return {needs:notes.length>0,text:notes.length?'Nessun backup JSON registrato. Esporta una copia prima di cancellare i dati dell’app.':'Nessun backup registrato. Non ci sono ancora appunti.'};
  const ageDays=(Date.now()-lastExport)/86400000;
  if(latestChange>lastExport)return {needs:true,text:'Ultima esportazione avviata: '+format(lastExport)+'. Alcuni appunti sono stati modificati dopo: crea un nuovo backup.'};
  if(ageDays>=BACKUP_MAX_AGE_DAYS)return {needs:true,text:'Ultima esportazione avviata: '+format(lastExport)+' (oltre 7 giorni fa). È consigliato un nuovo backup.'};
  return {needs:false,text:'Ultima esportazione avviata: '+format(lastExport)+'. Non risultano modifiche successive.'};
}
async function refreshBackupStatus(){if(!db)return;try{const notes=await allNotes(),state=backupState(notes);$('backupStatus').textContent=state.text+' La data registra la richiesta di esportazione, non la verifica che il file sia stato effettivamente salvato.';$('backupReminderText').textContent=state.text;$('backupReminder').classList.toggle('hidden',!state.needs);}catch(e){console.warn('Onfim: stato backup',e);}}
async function checkPersistentStorage(){const el=$('storageStatus'),b=$('persistButton');if(!navigator.storage?.persisted){el.textContent='Non supportato dal browser in uso.';b.disabled=true;return;}try{const active=await navigator.storage.persisted();el.textContent=active?'Archiviazione persistente attiva.':'Dati non ancora protetti dalla cancellazione automatica per spazio insufficiente.';b.disabled=active;b.textContent=active?'Attiva':'Proteggi dati';}catch(e){el.textContent='Stato non disponibile: '+e.message;}}
async function requestPersistentStorage(){const el=$('storageStatus');if(!navigator.storage?.persist){el.textContent='Richiesta non supportata dal browser.';return;}try{const granted=await navigator.storage.persist();el.textContent=granted?'Archiviazione persistente concessa.':'Il browser non ha concesso l’archiviazione persistente; gli appunti continuano a essere salvati normalmente.';await checkPersistentStorage();}catch(e){el.textContent='Impossibile richiedere archiviazione persistente: '+e.message;}}
async function reload(){await showTags();await renderNotes();await refreshBackupStatus();await refreshTrashCount();}
// PIN is deliberately only an everyday visual barrier, not cryptographic protection.
function pinStored(){return localStorage.getItem('onfim-pin');}
// Il PIN e' un filtro di lettura, non una cifratura. I PIN preesistenti si convertono senza perdere l'accesso.
function pinDialog(mode){return new Promise(resolve=>{
  const d=$('pinDialog'),form=$('pinForm'),input=$('pinEntry'),label=$('pinEntryLabel'),error=$('pinError');
  const previous=pinStored()||'';
  let phase=mode==='new'?'choose':(/^\d{4}$/.test(previous)?'unlock':'old');
  let first='';
  const prompt=()=>{
    error.textContent='';input.value='';input.inputMode=phase==='old'?'text':'numeric';
    if(phase==='old')input.removeAttribute('maxlength');else input.maxLength=4;
    if(phase==='old'){
      $('pinHeading').textContent='Aggiorna il PIN';
      $('pinMessage').textContent='Inserisci il PIN attuale per passare a 4 cifre.';
      label.textContent='PIN attuale';
    }else if(phase==='unlock'){
      $('pinHeading').textContent='Sblocca Archivio';
      $('pinMessage').textContent='Inserisci le 4 cifre. Lo sblocco è automatico.';
      label.textContent='PIN di 4 cifre';
    }else if(phase==='choose'){
      $('pinHeading').textContent='Imposta PIN';
      $('pinMessage').textContent='Scegli un PIN numerico di 4 cifre.';
      label.textContent='Nuovo PIN';
    }else{
      $('pinHeading').textContent='Ripeti PIN';
      $('pinMessage').textContent='Inserisci di nuovo le 4 cifre.';
      label.textContent='Conferma nuovo PIN';
    }
    input.focus();
  };
  const finish=ok=>{
    input.removeEventListener('input',onInput);
    form.onsubmit=null;$('pinCancel').onclick=null;d.oncancel=null;
    input.value='';d.close();resolve(ok);
  };
  const onInput=()=>{
    if(phase==='old'){
      if(input.value===previous){phase='choose';prompt();}
      else error.textContent=input.value.length>=previous.length?'PIN attuale non corretto.':'';
      return;
    }
    const value=input.value.replace(/\D/g,'').slice(0,4);
    if(input.value!==value)input.value=value;
    if(value.length!==4)return;
    if(phase==='unlock'){
      if(value===pinStored()){unlocked=true;finish(true);}
      else{input.value='';error.textContent='PIN errato.';}
    }else if(phase==='choose'){
      first=value;phase='repeat';prompt();
    }else{
      if(value!==first){first='';phase='choose';prompt();error.textContent='I PIN non coincidono. Riprova.';return;}
      try{localStorage.setItem('onfim-pin',value);}
      catch(e){first='';phase='choose';prompt();error.textContent='Impossibile memorizzare il PIN.';return;}
      unlocked=true;finish(true);
    }
  };
  input.addEventListener('input',onInput);
  form.onsubmit=e=>e.preventDefault();
  $('pinCancel').onclick=()=>finish(false);
  d.oncancel=e=>{e.preventDefault();finish(false);};
  d.showModal();prompt();
});}
async function checkPin(){if(unlocked)return true;return pinDialog(pinStored()?'unlock':'new');}
function download(content,filename,type){const blob=content instanceof Blob?content:new Blob([content],{type});const url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download=filename;document.body.append(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),4000);}
// Nome breve in ora locale; la data completa resta nel contenuto JSON.
function manualBackupFilename(now){
  const p=n=>String(n).padStart(2,'0');
  return 'onfim_'+now.getFullYear()+p(now.getMonth()+1)+p(now.getDate())+'_'+p(now.getHours())+p(now.getMinutes())+'.json';
}
async function exportJSON(){try{
  if(dirty&&!await ensureEditorSaved())throw new Error('Salvataggio della nota non riuscito.');
  const notes=await allNotes(),now=new Date();
  const payload={format:'appunti-backup',version:2,app:'Onfim',exportedAt:now.toISOString(),notes,smartCollections,reminderDayparts:onfimQuickTimes,customReminderPreset:onfimExtra};
  download(JSON.stringify(payload,null,2),manualBackupFilename(now),'application/json');
  try{localStorage.setItem(LAST_EXPORT_KEY,String(now.getTime()));}catch(e){console.warn('Onfim: data esportazione non registrata',e);}
  await refreshBackupStatus();
  $('settingsStatus').textContent='Download avviato. Verifica che il file JSON sia stato effettivamente salvato sul dispositivo o su Drive.';
}catch(e){$('settingsStatus').textContent='Errore nell’esportazione: '+e.message;}}
async function importJSON(file){try{const data=JSON.parse(await file.text());if(!Array.isArray(data.notes)|| !['appunti-backup','onfim-backup'].includes(data.format))throw new Error('Formato JSON non riconosciuto.');if(!confirm('Importare '+data.notes.length+' appunti? Gli ID già presenti saranno aggiornati; gli altri verranno aggiunti.'))return;if(dirty)throw new Error('Prima salva o chiudi l’appunto in modifica.');const existing=await allNotes();if(existing.length&&!await makeLocalSnapshot('prima-importazione',true))throw new Error('Non è stato possibile creare una copia preventiva: esporta un JSON e riprova.');let count=0;const imported=[];for(const n of data.notes){if(!n?.id||typeof n!=='object')continue;const cleaned={id:String(n.id),title:String(n.title||''),text:sanitizeHTML(n.text),checklist:onfimNormalizeChecklist(n.checklist),color:String(n.color||'#ffffff'),tags:Array.isArray(n.tags)?n.tags.map(String):[],photos:Array.isArray(n.photos)?n.photos.filter(s=>typeof s==='string'&&s.startsWith('data:image/')):[],photoMarks:Array.isArray(n.photoMarks)?n.photoMarks.map(s=>typeof s==='string'&&(s===''||s.startsWith('data:image/'))?s:''):[],drawing:typeof n.drawing==='string'&&n.drawing.startsWith('data:image/')?n.drawing:'',reminder:String(n.reminder||''),reminderRepeat:['none','daily','weekly','monthly','weekday','monday','tuesday','wednesday','thursday','friday','saturday','sunday'].includes(n.reminderRepeat)?n.reminderRepeat:'none',reminderBase:typeof n.reminderBase==='string'?n.reminderBase:String(n.reminder||''),geofence:cleanGeofence(n.geofence),reserved:!!n.reserved,favorite:!!n.favorite,pinned:!!n.pinned,created:Number(n.created)||Date.now(),updated:Number(n.updated)||Date.now(),audios:Array.isArray(n.audios)?n.audios.filter(a=>a&&typeof a.data==='string'&&a.data.startsWith('data:audio/')&&a.data.length<=Math.ceil(MAX_AUDIO_BYTES*1.4)).map(a=>({id:String(a.id||uid()),name:String(a.name||'Registrazione'),data:a.data,created:Number(a.created)||Date.now()})):[],chainRoot:typeof n.chainRoot==='string'?n.chainRoot:'',chainOrder:Number.isFinite(Number(n.chainOrder))?Number(n.chainOrder):0,manualOrder:Number.isSafeInteger(Number(n.manualOrder))&&Number(n.manualOrder)>0?Number(n.manualOrder):0,linkedFiles:Array.isArray(n.linkedFiles)?n.linkedFiles.filter(f=>f&&typeof f.uri==='string'&&/^content:\/\//.test(f.uri)&&f.uri.length<4096).slice(0,15).map(f=>({uri:f.uri,name:String(f.name||'Documento').slice(0,180),type:String(f.type||'').slice(0,120),size:Number(f.size)||0})):[]};if(Number(n.deletedAt)>0){cleaned.deletedAt=Number(n.deletedAt);cleaned.trashBatchId=typeof n.trashBatchId==='string'&&n.trashBatchId?n.trashBatchId:cleaned.id;}imported.push(cleaned);count++;}await putNotesBatch(imported);
 if(data.reminderDayparts&&typeof data.reminderDayparts==='object'){
  for(const key of ['morning','afternoon'])if(onfimValidQuickTime(data.reminderDayparts[key]))onfimQuickTimes[key]=data.reminderDayparts[key];
  localStorage.setItem(ONFIM_QUICK_TIMES_KEY,JSON.stringify(onfimQuickTimes));
  $('onfimTimeMorning').value=onfimQuickTimes.morning;$('onfimTimeAfternoon').value=onfimQuickTimes.afternoon;
 }
 if(data.customReminderPreset&&typeof data.customReminderPreset==='object'){
  const c=data.customReminderPreset;
  if(['off','daypart','days','weekday'].includes(c.mode)&&Number.isInteger(Number(c.days))&&Number(c.days)>=1&&Number(c.days)<=365&&Number(c.weekday)>=0&&Number(c.weekday)<=6&&onfimValidQuickTime(c.time)){
   onfimExtra={mode:c.mode,days:Number(c.days),weekday:Number(c.weekday),time:c.time};
   localStorage.setItem(ONFIM_EXTRA_PRESET_KEY,JSON.stringify(onfimExtra));onfimExtraRefreshUI();
  }
 }
 if(Array.isArray(data.smartCollections)){
  const safe=data.smartCollections.filter(c=>c&&typeof c.id==='string'&&typeof c.name==='string'&&Array.isArray(c.tags)).slice(0,40)
   .map(c=>({id:c.id.slice(0,70),name:c.name.slice(0,48),tags:[...new Set(c.tags.map(legacyTagSlug).filter(Boolean))].slice(0,30),hideHome:!!c.hideHome})).filter(c=>c.tags.length);
  // Preserve existing local collections, resolving same-id entries from the imported backup.
  const existingIds=new Set(safe.map(c=>c.id));smartCollections=[...smartCollections.filter(c=>!existingIds.has(c.id)),...safe].slice(0,40);
  localStorage.setItem(ONFIM_COLLECTIONS_KEY,JSON.stringify(smartCollections));
 }
 await reload();void onfimRenderCollections();scheduleReminders();$('settingsStatus').textContent='Importati '+count+' appunti.';}catch(e){$('settingsStatus').textContent='Importazione non riuscita: '+e.message;}finally{$('jsonInput').value='';}}
function icsEscape(s){return String(s||'').replace(/\\/g,'\\\\').replace(/\r?\n/g,'\\n').replace(/[;,]/g,m=>'\\'+m);}
async function exportICS(){const notes=(await allNotes()).filter(n=>!n.deletedAt&&n.reminder&&!Number.isNaN(new Date(n.reminder).getTime()));if(!notes.length){$('settingsStatus').textContent='Nessun promemoria da esportare.';return;}const stamp=new Date().toISOString().replace(/[-:]/g,'').replace(/\.\d{3}/,'');const out=['BEGIN:VCALENDAR','VERSION:2.0','PRODID:-//Onfim//Promemoria//IT','CALSCALE:GREGORIAN','METHOD:PUBLISH'];for(const n of notes){const t=n.reminder.replace(/[-:]/g,'').replace('T','T');const local=t.length===13?t+'00':t;out.push('BEGIN:VEVENT','UID:'+n.id.replace(/[^a-zA-Z0-9-]/g,'-')+'@onfim.local','DTSTAMP:'+stamp,'DTSTART:'+local,'DTEND:'+local,'SUMMARY:'+icsEscape('Onfim: '+(n.reserved?'Appunto riservato':(n.title||'Promemoria'))),...onfimIcsRepeat(n),'DESCRIPTION:'+icsEscape(n.reserved?'Apri gli appunti riservati in Onfim.':txt(n.text).slice(0,300)),'BEGIN:VALARM','TRIGGER:PT0M','ACTION:DISPLAY','DESCRIPTION:Promemoria Onfim','END:VALARM','END:VEVENT');}out.push('END:VCALENDAR');download(out.join('\r\n')+'\r\n','onfim-promemoria.ics','text/calendar;charset=utf-8');$('settingsStatus').textContent='Esportati '+notes.length+' promemoria. Importa il file nel calendario Android; l’importazione non si aggiorna automaticamente.';}
async function tryNotify(title){const msg='Promemoria onfim: '+title;try{if('Notification'in window&&Notification.permission==='granted'){if('serviceWorker'in navigator&&location.protocol.startsWith('http')){const reg=await navigator.serviceWorker.ready;await reg.showNotification(msg,{body:'Apri onfim per leggere la nota.'});return;}new Notification(msg);return;}}catch{}alert(msg+'\n\nPer notifiche a pagina chiusa, esporta il promemoria nel calendario Android.');}
async function scheduleReminders(){for(const t of reminderTimers.values())clearTimeout(t);reminderTimers.clear();const notes=await allNotes();for(const n of notes){if(n.deletedAt)continue;const wait=new Date(n.reminder).getTime()-Date.now();if(!n.reminder||!Number.isFinite(wait)||wait<=0||wait>2147480000)continue;const t=setTimeout(async()=>{tryNotify(n.reserved?'Appunto riservato':(n.title||'Appunto'));reminderTimers.delete(n.id);const repeat=n.reminderRepeat||'none';if(repeat!=='none'){const next=onfimNextRepeat(n.reminder,repeat,Date.now(),n.reminderBase||n.reminder);if(next){await putNote({...n,reminder:next,updated:Date.now()});await scheduleReminders();}}},wait);reminderTimers.set(n.id,t);}}
$('backRead').onclick=async()=>{await reload();view('listView');};
$('readBackBottom').onclick=async()=>{await reload();view('listView');};
$('addSequel').onclick=async()=>{
  const all=await allNotes(),root=all.find(n=>n.id===readId);
  if(!root){toast('Appunto non trovato');return;}
  if(root.reserved&&!unlocked&&!await checkPin())return;
  const members=chainMembers(root,all);
  const nextOrder=Math.max(0,...members.slice(1).map(n=>Number(n.chainOrder)||0))+1;
  const next=emptyNote();next.chainRoot=root.id;next.chainOrder=nextOrder;next.reserved=root.reserved;next.color=root.color||'#ffffff';
  editorFrom='read';editNote(next,false);$('deleteNote').classList.add('hidden');$('noteTitle').placeholder='Titolo della parte (facoltativo)';$('noteBody').focus();
};

// Copy the contents of an explicit source note into a chosen destination.
// The source is moved into the recoverable Cestino in the same batch.
let onfimJoinSourceId=null;
const closeJoinDialog=()=>{if($('joinDialog').open)$('joinDialog').close();};
function onfimChooseDestinationFrom(id){onfimJoinSourceId=id;return $('joinExisting').onclick();}
$('joinCancel').onclick=closeJoinDialog;
$('joinCancelTop').onclick=closeJoinDialog;
function candidatesToJoin(all,root){
  return all.filter(n=>!n.deletedAt&&n.id!==root.id && !n.chainRoot && n.reserved===root.reserved && !all.some(p=>!p.deletedAt&&p.chainRoot===n.id))
    .sort((a,b)=>(b.updated||0)-(a.updated||0));
}
$('joinExisting').onclick=async()=>{
  const all=await allNotes(),root=all.find(n=>n.id===onfimJoinSourceId);
  if(!root||root.deletedAt){toast('Appunto non trovato');return;}
  if(root.reserved&&!unlocked&&!await checkPin())return;
  if(chainMembers(root,all).length>1){toast('Prima separa le parti concatenate di questa nota');return;}
  const choices=candidatesToJoin(all,root);
  if(!choices.length){toast('Nessun appunto autonomo disponibile');return;}
  $('joinSearch').value='';$('joinSourceName').textContent='Da: '+(root.title||'Senza titolo');
  function drawOptions(){
    const q=$('joinSearch').value.toLocaleLowerCase().trim(),host=$('joinOptions');host.replaceChildren();
    const matches=choices.filter(n=>!q||[n.title,txt(n.text),...noteTags(n),...(n.checklist||[]).map(x=>x?.text||'')].join(' ').toLocaleLowerCase().includes(q));
    if(!matches.length){const msg=document.createElement('p');msg.className='small';msg.textContent='Nessun risultato';host.append(msg);return;}
    for(const candidate of matches){
      const btn=document.createElement('button');btn.type='button';btn.className='join-option';btn.setAttribute('role','listitem');
      const title=document.createElement('span');title.className='join-title';title.textContent=candidate.title||'Senza titolo';
      const preview=document.createElement('span');preview.className='join-preview';preview.textContent=txt(candidate.text).trim().slice(0,130)||((candidate.photos||[]).length?'📷 Foto':candidate.drawing?'✎ Disegno':(candidate.audios||[]).length?'🎙 Audio':'');
      btn.append(title,preview);
      btn.onclick=async()=>{
        btn.disabled=true;
        try{
          const current=await allNotes(),source=current.find(n=>n.id===onfimJoinSourceId),target=current.find(n=>n.id===candidate.id);
          if(!target||!source||!candidatesToJoin(current,source).some(n=>n.id===target.id))throw new Error('Le note sono cambiate: riapri la scelta');
          if(chainMembers(target,current).length!==1||chainMembers(source,current).length!==1)throw new Error('Prima separa le eventuali parti concatenate');
          if(target.reserved&&!unlocked&&!await checkPin()){btn.disabled=false;return;}
          if(target.id===source.id||target.reserved!==source.reserved)throw new Error('Note non compatibili');
          const destFiles=Array.isArray(target.linkedFiles)?target.linkedFiles:[],srcFiles=Array.isArray(source.linkedFiles)?source.linkedFiles:[];
          const mergedFiles=[...destFiles];for(const f of srcFiles)if(!mergedFiles.some(v=>v.uri===f.uri))mergedFiles.push(f);
          if(mergedFiles.length>15)throw new Error('Troppi file collegati: limite di 15 per nota');
          const left=sanitizeHTML(migratedText(target)).trim(),body=sanitizeHTML(migratedText(source)).trim();
          const sourceHeading=source.title.trim()?'<p><strong>'+htmlEscape(source.title.trim())+'</strong></p>':'';
          const right=sourceHeading+body;
          const mergedText=left&&right?left+'<div>---</div>'+right:left||right;
          const pictures=[...(target.photos||[]),...(source.photos||[])],masks=[...(target.photos||[]).map((_,i)=>target.photoMarks?.[i]||''),...(source.photos||[]).map((_,i)=>source.photoMarks?.[i]||'')];
          let drawing=target.drawing||'';
          if(source.drawing){if(drawing){pictures.push(source.drawing);masks.push('');}else drawing=source.drawing;}
          const name1=target.title||'Senza titolo',name2=source.title||'Senza titolo';
          const reminderWarning=source.reminder||source.geofence?.enabled?' Il promemoria della nota di partenza non sarà trasferito.':'';
          if(!confirm('Aggiungere «'+name2+'» a «'+name1+'»? La nota «'+name2+'» passerà nel Cestino e potrà essere recuperata.'+reminderWarning)){btn.disabled=false;return;}
          const now=Date.now(),batchId=uid();
          const merged={...target,checklist:[...onfimNormalizeChecklist(target.checklist),...onfimNormalizeChecklist(source.checklist).map(x=>({...x,id:uid()}))],text:sanitizeHTML(mergedText),tags:[...new Set([...noteTags(target),...noteTags(source)])],photos:pictures,photoMarks:masks,drawing,audios:[...(target.audios||[]),...(source.audios||[])],linkedFiles:mergedFiles,updated:now};
          const trashed={...source,deletedAt:now,trashBatchId:batchId,updated:now};
          // One IndexedDB transaction: either both changes persist or neither does.
          await putNotesBatch([merged,trashed]);
          closeJoinDialog();await reload();await openRead(merged);
          toast('Contenuti uniti; originale recuperabile dal Cestino');
        }catch(err){toast('Unione non riuscita: '+(err?.message||'errore'));btn.disabled=false;}
      };
      host.append(btn);
    }
  }
  $('joinSearch').oninput=drawOptions;
  drawOptions();$('joinDialog').showModal();$('joinSearch').focus();
};
$('starFromRead').onclick=async()=>{
  const current=(await allNotes()).find(n=>n.id===readId);
  if(!current||current.reserved)return;
  try{await putNote({...current,favorite:!current.favorite,updated:Date.now()});const updated=(await allNotes()).find(n=>n.id===readId);await openRead(updated);toast(updated.favorite?'Aggiunto ai Preferiti':'Rimosso dai Preferiti');}
  catch(err){toast('Non è stato possibile aggiornare il preferito');}
};
$('detachParts').onclick=async()=>{
  const all=await allNotes(),root=all.find(n=>n.id===readId);
  if(!root)return;
  const parts=chainMembers(root,all);
  if(parts.length<=1)return;
  if(root.reserved&&!unlocked&&!await checkPin())return;
  if(!confirm('Separare le '+parts.length+' parti? Rimarranno tutte salvate come appunti autonomi.'))return;
  await unlinkChildrenOf(root.id);
  await reload();await openRead(root);
  toast('Parti separate, nessun contenuto eliminato');
};


// Esportazione di una nota come HTML autonomo, offline e di sola lettura.
function onfimShareSafeImage(value){
  return typeof value==='string' && /^data:image\/(?:png|jpeg|webp|gif|avif);base64,[a-z0-9+/=]+$/i.test(value) ? value : '';
}
function onfimShareSafeAudio(value){
  return typeof value==='string' && /^data:audio\/[\w.+-]+(?:;[\w.+-]+)*;base64,[a-z0-9+/=]+$/i.test(value) ? value : '';
}
function onfimShareSafeColor(value){
  return typeof value==='string' && /^#[0-9a-f]{3}(?:[0-9a-f]{3})?$/i.test(value) ? value : '#ffffff';
}
function onfimShareFilename(title){
  const raw=String(title||'appunto').normalize('NFC').replace(/[\\/:*?"<>|\x00-\x1f]+/g,' ').replace(/\s+/g,' ').trim().replace(/[. ]+$/g,'');
  return (raw||'appunto').slice(0,72)+'.html';
}
function onfimSharePartHTML(n,partNumber,total){
  const fragments=[];
  // Testo formattato, filtrato attraverso lo stesso sanitizzatore usato in lettura.
  const body=onfimLinkifyHTML(sanitizeHTML(migratedText(n)));
  const heading=total>1?`<div class="part-label">Parte ${partNumber}${n.title&&partNumber>1?` · ${htmlEscape(n.title)}`:''}</div>`:'';
  if(body&&txt(body).trim())fragments.push(`<div class="note-text">${body}</div>`);
  const checkItems=onfimNormalizeChecklist(n.checklist).filter(x=>x.text.trim());
  if(checkItems.length)fragments.push(`<section class="media"><h3>Checklist</h3><ul>${checkItems.map(x=>`<li>${x.done?"☑":"☐"} ${htmlEscape(x.text)}</li>`).join("")}</ul></section>`);
  const image=onfimShareSafeImage(n.drawing);
  if(image)fragments.push(`<section class="media"><h3>Disegno</h3><img class="drawing" src="${image}" alt="Disegno della parte ${partNumber}" loading="lazy"></section>`);
  const photos=[];
  for(const [index,item] of (Array.isArray(n.photos)?n.photos:[]).entries()){
    const src=onfimShareSafeImage(item);if(!src)continue;
    const overlay=onfimShareSafeImage(n.photoMarks?.[index]);
    photos.push(`<figure class="photo"><div class="photo-visual"><img src="${src}" alt="Fotografia ${index+1}" loading="lazy">${overlay?`<img class="photo-annotation" src="${overlay}" alt="" loading="lazy">`:''}</div></figure>`);
  }
  if(photos.length)fragments.push(`<section class="media"><h3>Foto</h3><div class="photo-grid">${photos.join('')}</div></section>`);
  const clips=[];
  for(const clip of Array.isArray(n.audios)?n.audios:[]){
    const src=onfimShareSafeAudio(clip?.data);if(!src)continue;
    clips.push(`<div class="audio-entry"><div class="audio-label">${htmlEscape(clip.name||'Registrazione vocale')}</div><audio controls preload="none" src="${src}">Registrazione audio non supportata dal browser.</audio></div>`);
  }
  if(clips.length)fragments.push(`<section class="media"><h3>Audio</h3>${clips.join('')}</section>`);
  const files=Array.isArray(n.linkedFiles)?n.linkedFiles.filter(f=>f&&f.name):[];
  if(files.length)fragments.push(`<section class="media linked"><h3>Documenti collegati (non incorporati)</h3><ul>${files.map(f=>`<li>${htmlEscape(f.name)}</li>`).join('')}</ul></section>`);
  const tags=noteTags(n);
  if(tags.length)fragments.push(`<div class="tags">${tags.map(t=>`<span class="tag">${htmlEscape(onfimTagLabel(t))}</span>`).join('')}</div>`);
  return `<section class="part">${heading}${fragments.length?fragments.join('\n'):'<p class="empty-part">Parte senza contenuto esportabile</p>'}</section>`;
}
function onfimBuildStandaloneNoteHTML(root,parts){
  const title=String(root.title||'Senza titolo');
  const when=dateTimeLabel(root.created);
  const latest=dateTimeLabel(Math.max(...parts.map(p=>Number(p.updated)||Number(p.created)||0)));
  const background=onfimShareSafeColor(root.color);
  const exportedOn=new Intl.DateTimeFormat('it-IT',{day:'2-digit',month:'long',year:'numeric'}).format(new Date());
  const content=parts.map((p,i)=>onfimSharePartHTML(p,i+1,parts.length)).join('\n');
  return `<!doctype html>
<html lang="it"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; img-src data:; media-src data:; style-src 'unsafe-inline'; connect-src 'none'; base-uri 'none'; form-action 'none'">
<meta name="color-scheme" content="light">
<title>${htmlEscape(title)} · onfim</title>
<style>
:root{color-scheme:light;font-family:system-ui,-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;color:#222e38;background:#f3f5f7}
*{box-sizing:border-box}body{margin:0;line-height:1.55;padding:30px 16px 60px}main{max-width:760px;margin:0 auto}
.sheet{background:${background};border-radius:18px;padding:clamp(18px,5vw,42px);box-shadow:0 4px 20px #17233212;overflow-wrap:anywhere}
.header{margin-bottom:26px;padding-bottom:17px;border-bottom:1px solid #222e3820}
h1{font-size:clamp(1.5rem,5vw,2.2rem);line-height:1.25;letter-spacing:-.025em;margin:0 0 10px}
.meta{font-size:.75rem;color:#52646d;line-height:1.6}
.part+.part{border-top:1px solid #222e3823;margin-top:30px;padding-top:24px}
.part-label{font-size:.84rem;letter-spacing:.03em;font-weight:700;color:#315b69;margin-bottom:12px}
.note-text{font:15px/1.72 ui-monospace,SFMono-Regular,Consolas,'Liberation Mono',monospace;white-space:pre-wrap;overflow-wrap:anywhere}
.note-text p{margin:0 0 .65em}.note-text ul,.note-text ol{margin:5px 0 11px;padding-left:25px;white-space:normal}
.note-text li{white-space:pre-wrap}.note-text blockquote{border-left:3px solid #8099a7;padding-left:13px;margin:8px 0}
 .note-text a{color:#24638b;text-decoration:underline;text-underline-offset:2px;overflow-wrap:anywhere}
.media{margin-top:25px}.media h3{font:700 .84rem/1.4 system-ui,sans-serif;letter-spacing:.01em;color:#52646d;margin:0 0 10px}
.drawing{display:block;width:100%;max-width:700px;height:auto;background:#fff;border-radius:11px;border:1px solid #222e381a}
.photo-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,250px),1fr));gap:14px}
.photo{margin:0}.photo-visual{position:relative;overflow:hidden;border-radius:11px;line-height:0;background:#fff;border:1px solid #222e381a}
.photo-visual img{display:block;width:100%;height:auto;object-fit:contain}
.photo-visual .photo-annotation{position:absolute;inset:0;width:100%;height:100%;object-fit:fill;pointer-events:none}
.audio-entry{margin:13px 0 18px;max-width:100%}.audio-label{font:.82rem/1.4 system-ui,sans-serif;margin-bottom:6px;color:#52646d}
audio{display:block;width:100%;max-width:500px}.linked ul{font-size:.87rem;padding-left:22px}
.tags{display:flex;flex-wrap:wrap;gap:6px;margin-top:21px}.tag{font-size:.72rem;color:#3b5360;padding:4px 8px;border-radius:9px;background:#ffffff8c;border:1px solid #222e3814}
footer{font-size:.72rem;color:#71808a;text-align:center;padding:16px}
footer button{font:600 .83rem system-ui,sans-serif;border:1px solid #c7d2d8;color:#315b69;background:#fff;border-radius:10px;padding:9px 14px;cursor:pointer;margin-bottom:8px}
footer button:focus-visible{outline:2px solid #315b69;outline-offset:2px}.exported-meta{margin-top:5px}.empty-part{font-size:.88rem;color:#75828a;font-style:italic}
@media(max-width:500px){body{padding:12px 9px 35px}.sheet{border-radius:13px;padding:19px 16px}.note-text{font-size:13.5px}}
@media print{body{background:#fff;padding:0}.sheet{box-shadow:none;border-radius:0;padding:0;background:#fff}.part{break-inside:auto}.photo,.audio-entry{break-inside:avoid}footer{padding-top:25px}}
</style></head><body><main><article class="sheet"><header class="header"><h1>${htmlEscape(title)}</h1>
<div class="meta">Creato: ${htmlEscape(when)} · Modificato: ${htmlEscape(latest)}</div></header>
${content}</article><footer>
<div class="exported-meta">Condivisa da onfim · ${htmlEscape(exportedOn)}</div>
</footer></main>
 

</body></html>`;
}
async function onfimExportNote(noteId){
  closeReadMenu();
  try{
    const all=await allNotes();
    const found=all.find(n=>n.id===noteId&&!n.deletedAt);
    if(!found){toast('Appunto non trovato');return;}
    const root=groupRootFor(found,all),parts=chainMembers(root,all);
    if(root.reserved){
      if(!unlocked&&!await checkPin())return;
      if(!confirm('L’appunto riservato sarà esportato in chiaro. Chiunque riceva il file potrà leggerlo, senza PIN. Continuare?'))return;
    }
    const html=onfimBuildStandaloneNoteHTML(root,parts);
    const mb=new Blob([html]).size/(1024*1024);
    if(mb>18&&!confirm('Questo HTML contiene allegati incorporati e occupa circa '+mb.toFixed(1)+' MB. Vuoi esportarlo comunque?'))return;
    const name=onfimShareFilename(root.title);
    const file=new File([html],name,{type:'text/html'});
    if(typeof navigator.share==='function'&&(!navigator.canShare||navigator.canShare({files:[file]}))){
      try{await navigator.share({files:[file],title:root.title||'Appunto'});return;}
      catch(err){if(err?.name==='AbortError')return;console.warn('Condivisione file non disponibile',err);}
    }
    download(file,name,'text/html;charset=utf-8');
    toast('Condivisione file non disponibile: HTML salvato per l’invio');
  }catch(e){console.error('Esportazione HTML fallita',e);toast('Errore durante la creazione della pagina HTML');}
}
$('onfimShareHtml').onclick=()=>void onfimExportNote(readId);

// Menu lettura: azioni di organizzazione, separate dalla modifica dei contenuti.
function closeReadMenu(){
  $('readPopup').classList.add('hidden');
  $('readMoreTop').setAttribute('aria-expanded','false');
}
$('readMoreTop').onclick=e=>{
  e.stopPropagation();
  const next=$('readPopup').classList.contains('hidden');
  $('readPopup').classList.toggle('hidden',!next);
  $('readMoreTop').setAttribute('aria-expanded',String(next));
};
// Controlli contestuali: il selettore esistente resta la fonte del colore salvato.
$('noteColorButton').onclick=()=>{updateNoteColorButton();$('noteColorDialog').showModal();};
$('noteColorClose').onclick=()=>$('noteColorDialog').close();
for(const b of document.querySelectorAll('[data-note-color]'))b.onclick=()=>{
  $('noteColor').value=b.dataset.noteColor;
  updateNoteColorButton();markDirty();$('noteColorDialog').close();
};
let reminderOpenedFromList=false,reminderOriginalValue='',reminderOriginalRule='none',reminderOriginalBase='',reminderOriginalHadGeo=false;
async function openReminderFor(source,fromList=false){
  const all=await allNotes();const fresh=all.find(n=>n.id===source.id);if(!fresh)return;const root=groupRootFor(fresh,all);
  if(!root||root.deletedAt)return;
  if(root.reserved&&!unlocked&&!await checkPin())return;
  reminderOpenedFromList=fromList;reminderOriginalHadGeo=!!root.geofence?.enabled;
  readId=root.id;
  $('readReminderValue').value=root.reminder||'';reminderOriginalValue=root.reminder||'';reminderOriginalRule=root.reminderRepeat||'none';reminderOriginalBase=root.reminderBase||root.reminder||'';
  $('reminderRepeat').value=root.reminderRepeat||'none';
  $('repeatFold').open=!!(root.reminderRepeat&&root.reminderRepeat!=='none');$('dateFold').open=!!root.reminder;$('moreQuickReminders').open=false;onfimChosenDay='today';onfimChosenPeriod='';$('reminderOtherDate').value='';onfimSmartApplied=false;
  onfimUpdateRepeatInfo();
  fillGeo(root.geofence);onfimRefreshPresets();onfimUpdateReminderSelected();
  $('reminderRemove').disabled=!root.reminder&&!root.geofence?.enabled;
  $('reminderDialog').showModal();
  $('liteGeoNotice').hidden=!root.geofence?.enabled;
}
$('readReminderOption').onclick=async()=>{
  closeReadMenu();
  const all=await allNotes(),root=all.find(n=>n.id===readId);
  if(root)await openReminderFor(root,false);
};
$('reminderClose').onclick=()=>$('reminderDialog').close();
async function saveReadReminder(value,geofence=null,repeat='none',base=''){
  const all=await allNotes(),root=all.find(n=>n.id===readId);
  if(!root)return;
  if(root.reserved&&!unlocked&&!await checkPin())return;
  try{
    await putNote({...root,reminder:value,geofence:value&&!geofence?(root.geofence||null):geofence,reminderRepeat:value?repeat:'none',reminderBase:value?(base||value):'',updated:Date.now()});
    $('reminderDialog').close();await reload();await scheduleReminders();
    const latest=(await allNotes()).find(n=>n.id===readId);
    if(latest&&!reminderOpenedFromList)await openRead(latest);
    reminderOpenedFromList=false;
    toast(value||geofence?'Promemoria salvato':'Promemoria rimosso');
  }catch(e){toast('Errore: promemoria non salvato');}
}
$('reminderSave').onclick=()=>{
 let value=$('readReminderValue').value;const repeat=$('reminderRepeat').value,base=value===reminderOriginalValue&&repeat===reminderOriginalRule?reminderOriginalBase:value;if(value&&repeat!=='none')value=onfimNextRepeat(value,repeat,Date.now(),base);
 if(value&&(!Number.isFinite(new Date(value).getTime())||new Date(value).getTime()<=Date.now())){toast('Scegli data e ora future');return;}
 let geo=null;
 if($('geoEnabled').checked){
  if(!$('geoLat').value.trim()||!$('geoLon').value.trim()){toast('Inserisci le coordinate del luogo');return;}
  geo=cleanGeofence({enabled:true,name:'',lat:Number($('geoLat').value),lon:Number($('geoLon').value),radius:Number($('geoRadius').value),transition:$('geoTransition').value,token:String(Date.now())});
  if(!geo){toast('Coordinate non valide o raggio fuori da 100–10000 m');return;}
 }
 if(!value&&!geo&&!reminderOriginalValue&&!reminderOriginalHadGeo){toast('Scegli data e ora oppure un luogo');return;}
 void saveReadReminder(value,geo,repeat,base);
};
$('reminderRemove').onclick=()=>void saveReadReminder('',null,'none');
$('readEditTop').onclick=()=>{closeReadMenu();$('editFromRead').click();};
$('readFavOption').onclick=()=>{closeReadMenu();$('starFromRead').click();};
$('readQuickPin').onclick=()=>{$('readPinOption').click();};
$('readQuickStar').onclick=()=>{$('readFavOption').click();};
$('readQuickBell').onclick=()=>{$('readReminderOption').click();};

$('readPinOption').onclick=async()=>{
  closeReadMenu();const all=await allNotes(),n=all.find(x=>x.id===readId&&!x.deletedAt);if(!n)return;
  if(n.reserved&&!unlocked&&!await checkPin())return;
  await putNote({...n,pinned:!n.pinned});const latest=(await allNotes()).find(x=>x.id===readId);
  if(latest)await openRead(latest);toast(n.pinned?'Non più fissato':'Fissato in alto');
};
$('readMergeOption').onclick=()=>{closeReadMenu();void onfimChooseDestinationFrom(readId);};
$('readDetachOption').onclick=()=>{closeReadMenu();$('detachParts').click();};
$('readArchiveOption').onclick=async()=>{
  closeReadMenu();const all=await allNotes(),root=all.find(n=>n.id===readId);
  if(!root)return;
  if(!root.reserved&&!await checkPin())return;
  if(root.reserved&&!unlocked&&!await checkPin())return;
  const stamp=Date.now(),members=chainMembers(root,all);
  try{
    await putNotesBatch(members.map(n=>({...n,reserved:!root.reserved,updated:stamp})));
    if(root.reserved&&$('filter').value==='reserved'){lockArchive();$('filter').value='ordinary';syncFilterPills();}
    await reload();
    const latest=(await allNotes()).find(n=>n.id===readId);
    if(latest)await openRead(latest);else view('listView');
    toast(root.reserved?'Rimosso dall’Archivio':'Spostato nell’Archivio');
  }catch(err){toast('Non è stato possibile spostare la nota');}
};
$('readDeleteOption').onclick=async()=>{
  closeReadMenu();const all=await allNotes(),root=all.find(n=>n.id===readId);
  if(!root)return;if(root.reserved&&!unlocked&&!await checkPin())return;
  if(!confirmMoveToTrash(chainMembers(root,all).length))return;
   await safeDeleteNote(root);await reload();await scheduleReminders();view('listView');toast('Spostato nel Cestino');
};
// Aggiunta delle parti solo in modifica, senza aggiungere comandi alla lettura.
function closeAddPart(){if($('addPartDialog').open)$('addPartDialog').close();}
$('addPartEditor').onclick=async()=>{if(isRecording()){toast('Ferma la registrazione prima di spostare i contenuti');return;}if(!(await ensureEditorSaved()))return;if(!note){toast('Appunto non disponibile');return;}void onfimChooseDestinationFrom(note.id);};
$('partCancel').onclick=closeAddPart;
async function performAddPart(kind){
  closeAddPart();
  if(isRecording()){toast('Ferma prima la registrazione');return;}
  if(!(await ensureEditorSaved()))return;
  if(!note||!hasContent(note))return;
  const all=await allNotes(),saved=all.find(n=>n.id===note.id);
  if(!saved){toast('Appunto non ancora salvato');return;}
  const root=groupRootFor(saved,all);
  if(root.reserved&&!unlocked&&!await checkPin())return;
  readId=root.id;
  if(kind==='new')await $('addSequel').onclick();
  else await onfimChooseDestinationFrom(root.id);
}
$('partNew').onclick=()=>performAddPart('new');
$('partExisting').onclick=()=>performAddPart('existing');
document.addEventListener('pointerdown',e=>{if(!e.target.closest('.chain-options-host'))onfimClosePartMenus();
  if(!$('readPopup').classList.contains('hidden')&&!e.target.closest('.read-menu-host'))closeReadMenu();
});
document.addEventListener('keydown',e=>{if(e.key==='Escape')closeReadMenu();});
$('editFromRead').onclick=async()=>{const target=(await allNotes()).find(n=>n.id===readId);if(!target){toast('Appunto non trovato');await reload();view('listView');return;}if(target.reserved&&!unlocked&&!await checkPin())return;editorFrom='read';editNote(target);};
// Onfim 0.7.7: app-style navigation and compact home controls.
$('topBack').onclick=async()=>{
  if($('editView').classList.contains('show')){await leaveEditor();return;}
  if($('trashView').classList.contains('show')){unlocked=false;await refreshTrashCount();view('settingsView');return;}
  await reload();view('listView');
};
$('searchClose').onclick=()=>{
  $('search').value='';$('searchClose').classList.add('hidden');
  $('search').focus();renderNotes();
};
$('addButton').onclick=async()=>{if($('editView').classList.contains('show')){await leaveEditor();if($('editView').classList.contains('show'))return;}newNote();};$('settingsButton').onclick=async()=>{if($('editView').classList.contains('show')){await leaveEditor();if($('editView').classList.contains('show'))return;}if($('filter').value==='reserved')lockArchive();view('settingsView');void refreshBackupStatus();void checkPersistentStorage();void renderLocalSnapshots();};$('backEditor').onclick=leaveEditor;$('backSettings').onclick=async()=>{await reload();view('listView')};$('deleteNote').onclick=async()=>{if(isRecording()){toast('Ferma prima la registrazione.');return;}if(!note)return;if(note.reserved&&!await checkPin())return;if(!confirmMoveToTrash(note.chainRoot?1:chainMembers(note,await allNotes()).length))return;await safeDeleteNote(note);note=null;dirty=false;clearTimeout(saveTimer);await reload();await scheduleReminders();view('listView');toast('Spostato nel Cestino');};
function closeCardMenus(){document.querySelectorAll('.card.menu-open').forEach(c=>c.classList.remove('menu-open'));document.querySelectorAll('.card-popup').forEach(p=>p.classList.add('hidden'));document.querySelectorAll('.card-more[aria-expanded="true"]').forEach(b=>b.setAttribute('aria-expanded','false'));}
document.addEventListener('click',e=>{if(!e.target.closest('.card-menu'))closeCardMenus();});
document.addEventListener('keydown',e=>{if(e.key==='Escape')closeCardMenus();});
function lockArchive(){unlocked=false;if($('filter').value==='reserved')$('filter').value='ordinary';$('readBody').replaceChildren();$('readPhotos').replaceChildren();$('readAudios').replaceChildren();$('chainParts').replaceChildren();syncFilterPills();}
function syncFilterPills(){for(const b of document.querySelectorAll('[data-filter-choice]')){const on=b.dataset.filterChoice===$('filter').value;b.classList.toggle('selected',on);b.setAttribute('aria-pressed',String(on));}}
for(const b of document.querySelectorAll('[data-filter-choice]'))b.onclick=async()=>{if(b.dataset.filterChoice==='reserved'&&!await checkPin())return;if(b.dataset.filterChoice==='ordinary'&&$('filter').value==='reserved')unlocked=false;onfimActiveTags.clear();onfimTagReturnView=null;$('filter').value=b.dataset.filterChoice;syncFilterPills();await showTags();renderNotes();};
$('search').oninput=()=>{$('searchClose').classList.toggle('hidden',!$('search').value);renderNotes();};
for(const [id,mode] of [['notesGridView','grid'],['notesListView','list']])$(id).onclick=()=>{
  if(onfimNotesView===mode)return;
  onfimNotesView=mode;localStorage.setItem('onfim-notes-view',mode);renderNotes();
};
const oldSortPref=localStorage.getItem('onfim-sort-order');
if(oldSortPref&&[...$('sortOrder').options].some(o=>o.value===oldSortPref))$('sortOrder').value=oldSortPref;else if(oldSortPref==='manual')localStorage.removeItem('onfim-sort-order');
$('sortOrder').onchange=()=>{localStorage.setItem('onfim-sort-order',$('sortOrder').value);renderNotes();};$('filter').onchange=async()=>{if($('filter').value==='reserved'&&!await checkPin())$('filter').value='ordinary';onfimActiveTags.clear();onfimTagReturnView=null;syncFilterPills();await showTags();renderNotes();};
for(const b of document.querySelectorAll('[data-tab]'))b.onclick=()=>chooseTab(b.dataset.tab);
document.addEventListener('visibilitychange',()=>{if(document.hidden&&dirty&&note)void flushSave();});
$('noteTitle').oninput=markDirty;for(const id of ['noteColor','reminder'])$(id).onchange=markDirty;

 function onfimTagAutofill(){
  const host=$('onfimTagSuggestions');host.replaceChildren();host.classList.add('hidden');
  if(document.activeElement!==$('noteBody'))return;
  const sel=getSelection();if(!sel||!sel.rangeCount||!sel.isCollapsed)return;
  const range=sel.getRangeAt(0),node=range.startContainer;
  if(node.nodeType!==Node.TEXT_NODE)return;
  const before=node.textContent.slice(0,range.startOffset);
  const m=before.match(/(?:^|[\s\u00a0])#([\p{L}\p{N}_\p{Extended_Pictographic}\p{Regional_Indicator}\p{Emoji_Modifier}\uFE0E\uFE0F\u200D-]*)$/u);
  if(!m)return;
  const query=normalizedTag(m[1]);
  const matched=knownTags.filter(t=>t!=='📆'&&t!=='📍'&&t.startsWith(query)&&t!==query);
  for(const t of matched){const b=document.createElement('button');b.type='button';b.textContent='#'+t;b.setAttribute('role','option');
   b.onmousedown=e=>e.preventDefault();b.onpointerdown=e=>e.preventDefault();
   b.onclick=()=>{const current=sel.rangeCount?sel.getRangeAt(0):range;
    if(current.startContainer!==node)return;
    const start=current.startOffset-m[1].length;
    const r=document.createRange();r.setStart(node,start);r.setEnd(node,current.startOffset);
    r.deleteContents();const span=document.createTextNode(t+' ');r.insertNode(span);r.setStartAfter(span);r.collapse(true);sel.removeAllRanges();sel.addRange(r);
    markDirty();recordTextHistory(true);host.classList.add('hidden');$('noteBody').focus();};host.append(b);
  }
  if(matched.length){
   host.classList.remove('hidden');
   const rect=range.getBoundingClientRect(),viewport=window.visualViewport;
   const bottom=(viewport?.offsetTop||0)+(viewport?.height||innerHeight);
   const left=Math.max(10,Math.min(rect.left,innerWidth-240));
   host.style.left=left+'px';host.style.right='auto';
   const desired=Math.min(184,matched.length*35+12);
   const below=rect.bottom+6;
   host.style.top=(below+desired>bottom?Math.max(8,rect.top-desired-6):below)+'px';
  }
 }
$('reserved').onchange=async()=>{if($('reserved').checked){$('reserved').checked=false;const ok=await checkPin();if(ok)$('reserved').checked=true;}markDirty();};$('noteBody').oninput=e=>{lastHighlightAction=null;if(onfimAutoListFromTyping(e))return;markDirty();recordTextHistory();updateTextMark();onfimTagAutofill();onfimUpdatePointEdit();};$('textUndo').onclick=()=>textUndoOrRedo(-1);$('textRedo').onclick=()=>textUndoOrRedo(1);document.addEventListener('selectionchange',()=>{rememberRange();if(document.activeElement===$('noteBody')){updateFormat();onfimUpdatePointEdit();}});
for(const b of document.querySelectorAll('[data-command]')){b.addEventListener('pointerdown',e=>e.preventDefault());b.onclick=()=>applyCommand(b.dataset.command);}
for(const b of document.querySelectorAll('[data-ink]')){b.addEventListener('pointerdown',e=>e.preventDefault());b.onclick=()=>{applyCommand('foreColor',b.dataset.ink);document.querySelectorAll('[data-ink]').forEach(x=>x.classList.toggle('selected',x===b));};}
// Three highlighting swatches are always visible. With the same selected
// text, tapping the same colour twice removes highlighting (no hidden picker).
let lastHighlightAction=null;
function highlightSelectionKey(range){
  const before=document.createRange();before.selectNodeContents($('noteBody'));
  before.setEnd(range.startContainer,range.startOffset);
  return before.toString().length+':'+range.toString().length+':'+range.toString();
}
function sameHighlightSelection(a,range,color){return !!(a&&a.color===color&&a.key===highlightSelectionKey(range));}
for(const b of document.querySelectorAll('[data-highlight]')){
  b.addEventListener('pointerdown',e=>e.preventDefault());
  b.onclick=()=>{
    if(!selectionRange||selectionRange.collapsed){toast('Seleziona prima il testo da evidenziare.');return;}
    const r=selectionRange.cloneRange(),color=b.dataset.highlight;
    const clearing=sameHighlightSelection(lastHighlightAction,r,color);
    // Reuse the existing WebView/Chrome editable formatting implementation.
    restoreRange();
    document.execCommand('styleWithCSS',false,true);
    const chosen=clearing?'transparent':color;
    const ok=document.execCommand('hiliteColor',false,chosen);
    if(!ok)document.execCommand('backColor',false,chosen);
    rememberRange();markDirty();recordTextHistory(true);updateTextMark();
    lastHighlightAction=clearing?null:{color,key:highlightSelectionKey(r)};
    document.querySelectorAll('[data-highlight]').forEach(x=>x.classList.toggle('selected',!clearing&&x===b));
  };
}
$('penButton').onclick=()=>penMode(false);$('eraserButton').onclick=()=>penMode(true);$('drawUndo').onclick=()=>stepDrawHistory(-1);$('drawRedo').onclick=()=>stepDrawHistory(1);$('clearDrawing').onclick=()=>{if(confirm('Cancellare il disegno?')){saveDrawUndo();clearCanvas();markDirty();}};
for(const b of document.querySelectorAll('[data-draw]'))b.onclick=()=>{pen=b.dataset.draw;if(!drawTextMode)penMode(false);document.querySelectorAll('[data-draw]').forEach(x=>x.classList.toggle('selected',x===b));};

// Custom Onfim palette: the first choices are OUR seven pen colors, not the browser's presets.
let pickerTarget='',pickerColor='#202a34';
function clampByte(x){return Math.max(0,Math.min(255,Math.round(x)));}
function rgbHex(r,g,b){return '#'+[r,g,b].map(x=>clampByte(x).toString(16).padStart(2,'0')).join('');}
function hslToHex(h,s,l){h=Number(h)%360;s=Number(s)/100;l=Number(l)/100;const a=s*Math.min(l,1-l);const f=n=>{const k=(n+h/30)%12;return l-a*Math.max(-1,Math.min(k-3,9-k,1));};return rgbHex(f(0)*255,f(8)*255,f(4)*255);}
function hexToHsl(hex){const r=parseInt(hex.slice(1,3),16)/255,g=parseInt(hex.slice(3,5),16)/255,b=parseInt(hex.slice(5,7),16)/255;const hi=Math.max(r,g,b),lo=Math.min(r,g,b),d=hi-lo;let h=0,s=0,l=(hi+lo)/2;if(d){s=d/(1-Math.abs(2*l-1));switch(hi){case r:h=((g-b)/d)%6;break;case g:h=(b-r)/d+2;break;default:h=(r-g)/d+4;}h=(h*60+360)%360;}return [Math.round(h),Math.round(s*100),Math.round(l*100)];}
function normalizeHex(input){const s=String(input||'').trim().toLowerCase();if(/^#[a-f0-9]{6}$/.test(s))return s;if(/^#[a-f0-9]{3}$/.test(s))return '#'+[...s.slice(1)].map(c=>c+c).join('');return null;}
function syncPicker(hex){const normalized=normalizeHex(hex);if(!normalized)return false;pickerColor=normalized;const [h,sa,l]=hexToHsl(pickerColor);$('pickerHue').value=h;$('pickerSat').value=sa;$('pickerLight').value=l;$('pickerHex').value=pickerColor.toUpperCase();$('pickerHex').setCustomValidity('');refreshPickerPreview();return true;}
function refreshPickerPreview(){$('pickerPreview').style.background=pickerColor;$('pickerHueValue').textContent=$('pickerHue').value+'°';$('pickerSatValue').textContent=$('pickerSat').value+'%';$('pickerLightValue').textContent=$('pickerLight').value+'%';document.querySelectorAll('[data-picker]').forEach(b=>b.classList.toggle('selected',b.dataset.picker.toLowerCase()===pickerColor));}
function openOnfimColorPicker(target){pickerTarget=target;syncPicker(target==='photo'?markColor:pen);$('onfimColorDialog').showModal();}
function closeOnfimColorPicker(){$('onfimColorDialog').close();pickerTarget='';}
for(const b of document.querySelectorAll('[data-picker]'))b.onclick=()=>syncPicker(b.dataset.picker);
for(const id of ['pickerHue','pickerSat','pickerLight'])$(id).oninput=()=>{pickerColor=hslToHex($('pickerHue').value,$('pickerSat').value,$('pickerLight').value);$('pickerHex').value=pickerColor.toUpperCase();refreshPickerPreview();};
$('pickerHex').oninput=e=>{const result=normalizeHex(e.target.value);if(result)syncPicker(result);};
$('pickerClose').onclick=$('pickerCancel').onclick=closeOnfimColorPicker;
$('onfimColorDialog').addEventListener('cancel',()=>{pickerTarget='';});
$('pickerApply').onclick=()=>{
 const hex=normalizeHex($('pickerHex').value);if(!hex){$('pickerHex').setCustomValidity('Inserisci un colore esadecimale valido (es. #315B69)');$('pickerHex').reportValidity();return;}
 pickerColor=hex;
 if(pickerTarget==='photo'){markColor=hex;if(!photoTextMode)markMode(false);document.querySelectorAll('[data-mark]').forEach(x=>x.classList.toggle('selected',x.dataset.mark.toLowerCase()===markColor));}
 else if(pickerTarget==='draw'){pen=hex;if(!drawTextMode)penMode(false);document.querySelectorAll('[data-draw]').forEach(x=>x.classList.toggle('selected',x.dataset.draw.toLowerCase()===pen));}
 closeOnfimColorPicker();
};

$('customDrawColor').onclick=()=>openOnfimColorPicker('draw');
$('expandDrawing').onclick=()=>{
 $('drawTab').classList.add('expanded');
 $('expandDrawing').classList.add('hidden');
 $('closeExpanded').classList.remove('hidden');
 document.body.classList.add('onfim-drawing-full');
 requestAnimationFrame(fitDrawingCanvas);
};
$('closeExpanded').onclick=()=>{
 $('drawTab').classList.remove('expanded');
 $('expandDrawing').classList.remove('hidden');
 $('closeExpanded').classList.add('hidden');
 document.body.classList.remove('onfim-drawing-full');
 requestAnimationFrame(fitDrawingCanvas);
};
$('galleryButton').onclick=()=>$('galleryInput').click();
$('cameraButton').onclick=()=>$('cameraInput').click();
for(const id of ['galleryInput','cameraInput'])$(id).onchange=async e=>{await readPhotos(e.target.files);e.target.value='';};

// Cestino nella schermata Impostazioni: nessuna scheda aggiuntiva nella home.
async function refreshTrashCount(){
  const deleted=(await allNotes()).filter(n=>n.deletedAt);
  const groups=new Set(deleted.map(n=>n.trashBatchId||n.id));
  $('trashSettingsCount').textContent=groups.size===1?'1 appunto eliminato. Puoi ripristinarlo o eliminarlo definitivamente.':groups.size+' appunti eliminati. Puoi ripristinarli o eliminarli definitivamente.';
}
async function renderTrash(){
  const deleted=(await allNotes()).filter(n=>n.deletedAt);
  const batches=new Map();
  for(const n of deleted){const id=n.trashBatchId||n.id;if(!batches.has(id))batches.set(id,[]);batches.get(id).push(n);}
  const groups=[...batches.values()].sort((a,b)=>(Number(b[0].deletedAt)||0)-(Number(a[0].deletedAt)||0));
  const list=$('trashList');list.replaceChildren();
  $('trashCount').textContent=groups.length+' '+(groups.length===1?'appunto':'appunti')+' nel Cestino';
  $('emptyTrash').disabled=!groups.length;
  if(!groups.length){const e=document.createElement('p');e.className='hint';e.textContent='Il Cestino è vuoto.';list.append(e);return;}
  for(const group of groups){
    const root=group.find(n=>!n.chainRoot)||group[0],sensitive=group.some(n=>n.reserved),visible=!sensitive||unlocked;
    const item=document.createElement('article');item.className='trash-item';
    const title=document.createElement('div');title.className='trash-item-title';title.textContent=visible?(root.title||'Senza titolo'):'🔒 Appunto riservato';item.append(title);
    const meta=document.createElement('div');meta.className='trash-item-details';
    const date=new Date(root.deletedAt).toLocaleString('it-IT',{day:'2-digit',month:'2-digit',year:'numeric',hour:'2-digit',minute:'2-digit'});
    meta.textContent='Eliminato il '+date+(group.length>1?' · '+group.length+' parti collegate':'');item.append(meta);
    const actions=document.createElement('div');actions.className='trash-item-actions';
    if(!visible){const unlock=document.createElement('button');unlock.type='button';unlock.textContent='Sblocca';unlock.onclick=async()=>{if(await checkPin())await renderTrash();};actions.append(unlock);}
    const restore=document.createElement('button');restore.type='button';restore.textContent='Ripristina';restore.disabled=!visible;
    restore.onclick=async()=>{if(sensitive&&!unlocked&&!await checkPin())return;try{await restoreTrashBatch(group);await reload();await renderTrash();await scheduleReminders();toast(group.length>1?'Parti ripristinate insieme':'Appunto ripristinato');}catch(e){toast('Ripristino non riuscito: '+(e.message||e));}};
    const remove=document.createElement('button');remove.type='button';remove.className='danger';remove.textContent='Elimina definitivamente';remove.disabled=!visible;
    remove.onclick=async()=>{if(sensitive&&!unlocked&&!await checkPin())return;if(!confirm('Eliminare definitivamente '+(group.length>1?'queste '+group.length+' parti':'questo appunto')+'? Non sarà più possibile ripristinare i dati.'))return;try{await removeNotesBatch(group.map(n=>n.id));await reload();await renderTrash();toast('Eliminato definitivamente');}catch(e){toast('Eliminazione non riuscita: '+(e.message||e));}};
    actions.append(restore,remove);item.append(actions);list.append(item);
  }
}
$('openTrash').onclick=async()=>{unlocked=false;await renderTrash();view('trashView');};
$('backTrash').onclick=async()=>{unlocked=false;await refreshTrashCount();view('settingsView');};
$('emptyTrash').onclick=async()=>{
  const all=await allNotes(),deleted=all.filter(n=>n.deletedAt),sensitive=deleted.some(n=>n.reserved);
  if(!deleted.length)return;
  if(sensitive&&!unlocked&&!await checkPin())return;
  if(!confirm('Svuotare tutto il Cestino? Verranno eliminati definitivamente '+deleted.length+' elementi, compresi eventuali allegati.'))return;
  if(!confirm('Seconda conferma: questa operazione NON si può annullare. Svuotare davvero il Cestino?'))return;
  try{await emptyTrashNow();await reload();await renderTrash();toast('Cestino svuotato');}catch(e){toast('Impossibile svuotare il Cestino: '+(e.message||e));}
};
$('exportJson').onclick=exportJSON;
$('shareBackup').onclick=shareBackupViaAndroid;
$('makeSnapshot').onclick=async()=>{if(dirty){snapshotUpdateStatus('Salva o chiudi la nota prima della copia.');return;}const ok=await makeLocalSnapshot('manuale',true);snapshotUpdateStatus(ok?'Copia creata: esportala anche fuori dal browser.':'Copia non riuscita: verifica spazio e presenza di appunti.');};$('backupReminderAction').onclick=()=>{view('settingsView');void refreshBackupStatus();void renderLocalSnapshots();};$('persistButton').onclick=requestPersistentStorage;$('importJson').onclick=()=>$('jsonInput').click();$('jsonInput').onchange=e=>{if(e.target.files[0])importJSON(e.target.files[0]);};$('exportIcs').onclick=exportICS;
$('notifyButton').onclick=async()=>{if(!('Notification'in window)){$('settingsStatus').textContent='Notifiche web non supportate da questo browser.';return;}try{const p=await Notification.requestPermission();$('settingsStatus').textContent=p==='granted'?'Permesso concesso. L’avviso resta comunque non garantito a pagina chiusa.':'Permesso non concesso.';}catch(e){$('settingsStatus').textContent='Impossibile chiedere il permesso: '+e.message;}};
$('audioRecord').onclick=()=>{$('audioRecorderControls').classList.remove('hidden');$('audioStatus').classList.remove('hidden');$('audioStatus').textContent='Premi Registra per iniziare.';recordingUI();};
$('audioStart').onclick=()=>void startAudioRecording();
$('audioExistingButton').onclick=()=>$('audioInput').click();
$('audioStop').onclick=()=>{if(isRecording())recorder.stop();};
$('audioPause').onclick=()=>{if(!isRecording())return;if(recorder.state==='recording'){recorder.pause();audioPausedAt=performance.now();$('audioStatus').textContent='Registrazione in pausa.';}else if(recorder.state==='paused'){audioPauseTotal+=performance.now()-audioPausedAt;recorder.resume();$('audioStatus').textContent='Registrazione in corso…';}recordingUI();};
$('audioInput').onchange=async e=>{await importAudioFiles(e.target.files);e.target.value='';};
$('managePin').onclick=async()=>{
  const old=pinStored();
  if(old){
    unlocked=false;
    if(!await checkPin())return;
    // Un vecchio PIN non numerico o non di 4 cifre e' stato gia' sostituito nell'accesso.
    if(!/^\d{4}$/.test(old)&&/^\d{4}$/.test(pinStored()||'')){
      $('settingsStatus').textContent='PIN aggiornato a 4 cifre.';return;
    }
  }
  const done=await pinDialog('new');
  $('settingsStatus').textContent=done?'PIN di 4 cifre impostato.':'PIN non modificato.';
};$('lockPin').onclick=async()=>{unlocked=false;if($('filter').value==='reserved')$('filter').value='ordinary';await showTags();syncFilterPills();await renderNotes();$('settingsStatus').textContent='Archivio bloccato.';};
window.addEventListener('beforeunload',e=>{if(dirty){e.preventDefault();e.returnValue='';}});
// Browser adapter: original IndexedDB functions above remain authoritative.
// Geofences imported from APK remain in JSON but are not monitored here.
function cleanGeofence(g){if(!g||!g.enabled)return null;const lat=Number(g.lat),lon=Number(g.lon),radius=Number(g.radius);if(!Number.isFinite(lat)||lat< -90||lat>90||!Number.isFinite(lon)||lon< -180||lon>180||!Number.isFinite(radius)||radius<100||radius>10000)return null;return{enabled:true,name:String(g.name||''),lat,lon,radius,transition:g.transition==='exit'?'exit':'enter',token:String(g.token||'imported')};}
function fillGeo(g){
 const v=cleanGeofence(g);$('geoEnabled').checked=!!v;$('geoFields').hidden=false;
 $('geoLat').value=v?.lat??'';$('geoLon').value=v?.lon??'';
 $('geoRadius').value=v?.radius||200;$('geoTransition').value=v?.transition||'enter';
 $('geoFold').open=!!v;if(v){onfimGeoCenter(v.lat,v.lon,15,false);}else{onfimGeoCenter(42.5,12.5,6,false);}
 requestAnimationFrame(geoMapRender);
}
// Standalone map: selection + storage only, never a background geofence monitor.
const ONFIM_TILE_SIZE=256;let onfimGeo={lat:42.5,lon:12.5,z:6};
function onfimGeoClampLat(lat){return Math.max(-85.051128,Math.min(85.051128,lat));}
function onfimGeoWorld(lat,lon,z){const scale=ONFIM_TILE_SIZE*(2**z);const rad=onfimGeoClampLat(lat)*Math.PI/180;return{x:(lon+180)/360*scale,y:(1-Math.log(Math.tan(rad)+1/Math.cos(rad))/Math.PI)/2*scale};}
function onfimGeoInverse(x,y,z){const s=ONFIM_TILE_SIZE*(2**z);const lat=Math.atan(Math.sinh(Math.PI*(1-2*y/s)))*180/Math.PI;return{lat:onfimGeoClampLat(lat),lon:((x/s*360)%360+360)%360-180};}
function onfimGeoCenter(lat,lon,z=onfimGeo.z,commit=true){
 if(!Number.isFinite(Number(lat))||!Number.isFinite(Number(lon)))return;
 onfimGeo={lat:onfimGeoClampLat(Number(lat)),lon:((Number(lon)+180)%360+360)%360-180,z:Math.max(3,Math.min(18,z))};
 if(commit){if(onfimGeoInsertMode){$('onfimPointLat').value=onfimGeo.lat.toFixed(6);$('onfimPointLon').value=onfimGeo.lon.toFixed(6);}else{$('geoLat').value=onfimGeo.lat.toFixed(6);$('geoLon').value=onfimGeo.lon.toFixed(6);$('geoEnabled').checked=true;onfimUpdateRepeatInfo();}}
 geoMapRender();
}
function geoMapRender(){
 const map=$('geoMap'),host=$('geoMapTiles');if(!map||!host||!map.clientWidth||!map.clientHeight)return;
 const width=map.clientWidth,height=map.clientHeight,c=onfimGeoWorld(onfimGeo.lat,onfimGeo.lon,onfimGeo.z),z=onfimGeo.z;
 const xMin=Math.floor((c.x-width/2)/256),xMax=Math.floor((c.x+width/2)/256),yMin=Math.floor((c.y-height/2)/256),yMax=Math.floor((c.y+height/2)/256),n=2**z;
 // Non eliminare e ricreare ogni tessera a ogni tocco: quelle già caricate
 // rimangono visibili, mentre cambiano soltanto posizione e nuovi bordi.
 const present=new Map([...host.children].filter(t=>t.tagName==='IMG').map(t=>[t.dataset.tileKey,t]));
 const visible=new Set();
 for(let x=xMin;x<=xMax;x++)for(let y=yMin;y<=yMax;y++){
  if(y<0||y>=n)continue;
  const wrappedX=((x%n)+n)%n,key=z+'/'+wrappedX+'/'+y;
  let tile=present.get(key);
  if(!tile){
   tile=document.createElement('img');tile.alt='';tile.loading='eager';tile.decoding='async';tile.draggable=false;
   tile.dataset.tileKey=key;tile.src='https://tile.openstreetmap.org/'+key+'.png';host.append(tile);
  }
  tile.style.left=Math.round(x*256-c.x+width/2)+'px';tile.style.top=Math.round(y*256-c.y+height/2)+'px';
  visible.add(key);
 }
 for(const [key,tile] of present){if(!visible.has(key))tile.remove();}
 $('geoMapHint').textContent='Punto: '+onfimGeo.lat.toFixed(5)+', '+onfimGeo.lon.toFixed(5)+' · zoom '+z;
}
function onfimMapOffset(dx,dy){const c=onfimGeoWorld(onfimGeo.lat,onfimGeo.lon,onfimGeo.z),p=onfimGeoInverse(c.x+dx,c.y+dy,onfimGeo.z);onfimGeoCenter(p.lat,p.lon,onfimGeo.z,true);}
let onfimGeoDown=null;
$('geoMap').addEventListener('pointerdown',e=>{if(e.target.closest('button'))return;onfimGeoDown={x:e.clientX,y:e.clientY,id:e.pointerId};$('geoMap').setPointerCapture?.(e.pointerId);});
$('geoMap').addEventListener('pointerup',e=>{if(!onfimGeoDown||e.pointerId!==onfimGeoDown.id)return;const rect=$('geoMap').getBoundingClientRect(),dx=e.clientX-onfimGeoDown.x,dy=e.clientY-onfimGeoDown.y;
 if(Math.hypot(dx,dy)>7)onfimMapOffset(-dx,-dy);else onfimMapOffset(e.clientX-(rect.left+rect.width/2),e.clientY-(rect.top+rect.height/2));onfimGeoDown=null;});
$('geoMap').addEventListener('pointercancel',()=>{onfimGeoDown=null;});
$('geoMapZoomIn').onclick=()=>onfimGeoCenter(onfimGeo.lat,onfimGeo.lon,onfimGeo.z+1,false);
$('geoMapZoomOut').onclick=()=>onfimGeoCenter(onfimGeo.lat,onfimGeo.lon,onfimGeo.z-1,false);
$('geoFold').ontoggle=()=>{if($('geoFold').open){$('geoFields').hidden=false;requestAnimationFrame(geoMapRender);}};
$('geoRemove').onclick=()=>{$('geoEnabled').checked=false;$('geoLat').value='';$('geoLon').value='';$('geoFold').open=false;onfimUpdateRepeatInfo();toast('Luogo rimosso');};
for(const id of ['geoLat','geoLon'])$(id).addEventListener('change',()=>{const lat=Number($('geoLat').value),lon=Number($('geoLon').value);if($('geoLat').value&&$('geoLon').value&&Math.abs(lat)<=90&&Math.abs(lon)<=180)onfimGeoCenter(lat,lon,onfimGeo.z,false);});
$('geoCurrent').onclick=()=>{if(!navigator.geolocation){$('geoSearchStatus').textContent='Localizzazione non disponibile';return;}navigator.geolocation.getCurrentPosition(p=>{onfimGeoCenter(p.coords.latitude,p.coords.longitude,16);$('geoSearchStatus').textContent='Posizione rilevata';},e=>{$('geoSearchStatus').textContent='Posizione non disponibile: '+e.message;},{enableHighAccuracy:false,timeout:10000,maximumAge:120000});};
let onfimLastGeoSearch=0;
$('geoSearchGo').onclick=async()=>{
 const q=$('geoSearch').value.trim();if(q.length<3){$('geoSearchStatus').textContent='Scrivi almeno 3 caratteri';return;}
 const host=$('geoSearchResults');host.replaceChildren();$('geoSearchStatus').textContent='Ricerca in corso…';
 const wait=Math.max(0,1100-(Date.now()-onfimLastGeoSearch));$('geoSearchGo').disabled=true;
 try{
  if(wait)await new Promise(r=>setTimeout(r,wait));onfimLastGeoSearch=Date.now();
  const ctrl=new AbortController(),timeout=setTimeout(()=>ctrl.abort(),9500);
  let response;try{response=await fetch('https://nominatim.openstreetmap.org/search?format=json&limit=5&addressdetails=1&q='+encodeURIComponent(q),{signal:ctrl.signal,headers:{'Accept':'application/json'}});}finally{clearTimeout(timeout);}
  if(!response.ok)throw new Error('Servizio non disponibile ('+response.status+')');const list=await response.json();
  $('geoSearchStatus').textContent=list.length?list.length+' risultati · scegli un luogo':'Nessun risultato; prova un nome più preciso';
  for(const place of list){const button=document.createElement('button');button.type='button';button.className='geo-search-result';button.textContent=place.display_name||'Località';button.onclick=()=>{onfimGeoCenter(Number(place.lat),Number(place.lon),16,true);host.replaceChildren();$('geoSearchStatus').textContent='Punto impostato sulla mappa';};host.append(button);}
 }catch(e){$('geoSearchStatus').textContent='Ricerca non riuscita (richiede Internet). Usa la mappa o inserisci le coordinate.';}
 finally{$('geoSearchGo').disabled=false;}
};
$('geoSearch').addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();$('geoSearchGo').click();}});
let onfimExpandedMapParent=null;
$('geoMapExpand').onclick=()=>{onfimExpandedMapParent=$('geoMapFrame').parentElement;$('geoExpandedDock').append($('geoMapFrame'));$('geoExpandedDialog').showModal();requestAnimationFrame(geoMapRender);};
function onfimCloseExpandedMap(){if($('geoExpandedDialog').open)$('geoExpandedDialog').close();(onfimExpandedMapParent||$('geoMapHome')).append($('geoMapFrame'));onfimExpandedMapParent=null;requestAnimationFrame(geoMapRender);}
$('geoMapClose').onclick=onfimCloseExpandedMap;
$('geoExpandedDialog').addEventListener('close',()=>{if($('geoMapFrame').parentElement===$('geoExpandedDock')){(onfimExpandedMapParent||$('geoMapHome')).append($('geoMapFrame'));onfimExpandedMapParent=null;requestAnimationFrame(geoMapRender);}});

// User-initiated web share of a JSON backup; the destination must confirm storage.
function makeBackupFile(notes){const now=new Date(),payload={format:'appunti-backup',version:2,app:'Onfim',exportedAt:now.toISOString(),notes,smartCollections,reminderDayparts:onfimQuickTimes,customReminderPreset:onfimExtra};return new File([JSON.stringify(payload,null,2)],manualBackupFilename(now),{type:'application/json'});}
async function shareBackupViaAndroid(){const out=$('settingsStatus');try{
  if(dirty)throw new Error('Salva o chiudi la nota prima di condividere il backup.');
  if(typeof navigator.share!=='function')throw new Error('La condivisione di file non è disponibile: usa Esporta JSON.');
  const file=makeBackupFile(await allNotes());
  if(navigator.canShare&&!navigator.canShare({files:[file]}))throw new Error('Il browser non supporta la condivisione di questo file. Usa Esporta JSON.');
  await navigator.share({files:[file],title:'backup onfim'});
  out.textContent='Backup consegnato al menu Condividi. Verifica sulla destinazione (per esempio Drive) che il file sia stato salvato.';
}catch(e){out.textContent=e.name==='AbortError'?'Condivisione annullata.':'Condivisione non riuscita: '+e.message;}}
const SNAPSHOT_INTERVAL=3*60*60*1000, MAX_SNAPSHOTS=5;
let internalSnapshotTimer=0, internalSnapshotBusy=false, snapshotDb=null;
function openSnapshotDB(){return new Promise((res,rej)=>{const r=indexedDB.open('onfim-internal-snapshots-v1',1);r.onupgradeneeded=()=>{if(!r.result.objectStoreNames.contains(SNAPSTORE))r.result.createObjectStore(SNAPSTORE,{keyPath:'id'});};r.onsuccess=()=>{snapshotDb=r.result;res();};r.onerror=()=>rej(r.error);});}
function snapshotDate(ms){return new Date(ms).toLocaleString('it-IT',{day:'2-digit',month:'2-digit',year:'numeric',hour:'2-digit',minute:'2-digit'});}
function snapshotStoreAll(){return new Promise((res,rej)=>{const tx=snapshotDb.transaction(SNAPSTORE,'readonly');const q=tx.objectStore(SNAPSTORE).getAll();q.onsuccess=()=>res(q.result||[]);q.onerror=()=>rej(q.error);});}
function snapshotSave(copy){return new Promise((res,rej)=>{const tx=snapshotDb.transaction(SNAPSTORE,'readwrite');tx.objectStore(SNAPSTORE).put(copy);tx.oncomplete=()=>res();tx.onabort=()=>rej(tx.error||new Error('Salvataggio copia annullato'));tx.onerror=()=>rej(tx.error||new Error('Impossibile salvare la copia'));});}
function snapshotPrune(ids){if(!ids.length)return Promise.resolve();return new Promise((res,rej)=>{const tx=snapshotDb.transaction(SNAPSTORE,'readwrite');const store=tx.objectStore(SNAPSTORE);for(const id of ids)store.delete(id);tx.oncomplete=()=>res();tx.onerror=()=>rej(tx.error||new Error('Errore pulizia copie'));});}
function snapshotUpdateStatus(message){const el=$('snapshotStatus');if(el)el.textContent=message;}
function latestNoteUpdate(notes){let ts=Number(localStorage.getItem(LAST_CHANGE_KEY))||0;for(const n of notes)ts=Math.max(ts,Number(n.updated)||0,Number(n.created)||0);return ts;}
async function makeLocalSnapshot(reason='automatica', force=false){
  if(!db||!snapshotDb||internalSnapshotBusy)return false;
  internalSnapshotBusy=true;
  try{
    const notes=await allNotes();if(!notes.length)return false;
    const prior=(await snapshotStoreAll()).sort((a,b)=>b.id-a.id);
    const changed=latestNoteUpdate(notes),latest=prior[0];
    const current={notes,smartCollections,onfimQuickTimes,onfimExtra};
    const same=latest&&JSON.stringify({notes:latest.notes,smartCollections:latest.smartCollections||[],onfimQuickTimes:latest.reminderDayparts||{},onfimExtra:latest.customReminderPreset||{}})===JSON.stringify(current);
    if(!force&&latest&&(Date.now()-latest.id<SNAPSHOT_INTERVAL||same))return false;
    const stamp=Date.now(),copy={id:stamp,createdAt:new Date(stamp).toISOString(),changedAt:changed,reason,notes,smartCollections:JSON.parse(JSON.stringify(smartCollections)),reminderDayparts:{...onfimQuickTimes},customReminderPreset:{...onfimExtra}};
    await snapshotSave(copy);
    const all=(await snapshotStoreAll()).sort((a,b)=>b.id-a.id);
    if(all.length>MAX_SNAPSHOTS)await snapshotPrune(all.slice(MAX_SNAPSHOTS).map(x=>x.id));
    await renderLocalSnapshots();
    return true;
  }catch(e){console.warn('Onfim: copia locale non riuscita',e);snapshotUpdateStatus('Copia locale non riuscita: '+e.message);return false;}
  finally{internalSnapshotBusy=false;}
}
async function scheduleLocalSnapshot(){
  if(!db||!snapshotDb)return;clearTimeout(internalSnapshotTimer);
  try{const notes=await allNotes();if(!notes.length)return;const copies=await snapshotStoreAll();const latest=copies.reduce((a,b)=>!a||b.id>a.id?b:a,null);
    if(latest&&Date.now()-latest.id>=SNAPSHOT_INTERVAL&&latestNoteUpdate(notes)<=Number(latest.changedAt))return;
    const delay=latest?Math.max(12000,SNAPSHOT_INTERVAL-(Date.now()-latest.id)):12000;
    internalSnapshotTimer=setTimeout(()=>{void makeLocalSnapshot('automatica').finally(()=>{void scheduleLocalSnapshot();});},delay);
  }catch(e){console.warn('Onfim: controllo copie interne non disponibile',e);}
}
window.addEventListener('visibilitychange',()=>{if(!document.hidden&&snapshotDb){void makeLocalSnapshot('automatica').finally(()=>{void scheduleLocalSnapshot();});}});
window.addEventListener('pageshow',()=>{if(snapshotDb)void scheduleLocalSnapshot();});
async function renderLocalSnapshots(){
  if(!db||!snapshotDb)return;const host=$('localBackupList');if(!host)return;
  try{
    const list=(await snapshotStoreAll()).sort((a,b)=>b.id-a.id);host.replaceChildren();
    if(!list.length){host.textContent='Nessuna copia interna: verrà creata durante l’uso, se ci sono appunti.';return;}
    for(const snap of list){const row=document.createElement('div');row.className='backup-local-item';
      const info=document.createElement('div');const date=document.createElement('strong');date.textContent=snapshotDate(snap.id);const desc=document.createElement('small');desc.textContent=(snap.notes||[]).length+' elementi · '+(snap.reason==='automatica'?'Automatica':snap.reason==='prima-importazione'?'Prima dell’importazione':snap.reason==='prima-ripristino'?'Prima del ripristino':'Manuale');info.append(date,desc);
      const actions=document.createElement('div');actions.className='backup-local-actions';const save=document.createElement('button');save.type='button';save.textContent='Esporta';save.onclick=()=>{const pack={format:'appunti-backup',version:2,app:'Onfim',exportedAt:snap.createdAt,notes:snap.notes};for(const field of ['smartCollections','reminderDayparts','customReminderPreset'])if(Object.hasOwn(snap,field))pack[field]=snap[field];download(JSON.stringify(pack,null,2),manualBackupFilename(new Date(snap.id)),'application/json');snapshotUpdateStatus('Download della copia avviato: verifica il file fuori da Onfim.');};
      const restore=document.createElement('button');restore.type='button';restore.textContent='Ripristina';restore.onclick=async()=>{
        if(!confirm('Ripristinare questa copia del '+snapshotDate(snap.id)+'? Gli appunti attuali saranno sostituiti, compresi quelli nel Cestino. Una copia preventiva verrà salvata internamente.'))return;
        try{
          if(dirty)throw new Error('Chiudi o salva l’appunto prima di ripristinare.');
          const existing=await allNotes();if(existing.length){const ok=await makeLocalSnapshot('prima-ripristino',true);if(!ok)throw new Error('Impossibile creare la copia preventiva: ripristino interrotto.');}
          await replaceAllNotes(snap.notes);
           // Le vecchie copie possono avere soltanto le note: in quel caso non tocchiamo le raccolte.
           if(Array.isArray(snap.smartCollections)){smartCollections=onfimCleanCollections(snap.smartCollections);localStorage.setItem(ONFIM_COLLECTIONS_KEY,JSON.stringify(smartCollections));smartActive='home';}
           if(snap.reminderDayparts&&typeof snap.reminderDayparts==='object'){
             for(const key of ['morning','afternoon'])if(onfimValidQuickTime(snap.reminderDayparts[key]))onfimQuickTimes[key]=snap.reminderDayparts[key];
             localStorage.setItem(ONFIM_QUICK_TIMES_KEY,JSON.stringify(onfimQuickTimes));
             $('onfimTimeMorning').value=onfimQuickTimes.morning;$('onfimTimeAfternoon').value=onfimQuickTimes.afternoon;
           }
           if(snap.customReminderPreset&&typeof snap.customReminderPreset==='object'){
             const c=snap.customReminderPreset;
             if(['off','daypart','days','weekday'].includes(c.mode)&&Number.isInteger(Number(c.days))&&Number(c.days)>=1&&Number(c.days)<=365&&Number(c.weekday)>=0&&Number(c.weekday)<=6&&onfimValidQuickTime(c.time)){
               onfimExtra={mode:c.mode,days:Number(c.days),weekday:Number(c.weekday),time:c.time};localStorage.setItem(ONFIM_EXTRA_PRESET_KEY,JSON.stringify(onfimExtra));onfimExtraRefreshUI();
             }
           }
           unlocked=false;readId=null;note=null;
          if($('filter').value==='reserved')$('filter').value='ordinary';syncFilterPills();
          await reload();await scheduleReminders();view('listView');
          snapshotUpdateStatus('Copia ripristinata. Gli appunti sono stati sostituiti.');
        }catch(e){snapshotUpdateStatus('Ripristino non riuscito: '+e.message);}
      };actions.append(save,restore);row.append(info,actions);host.append(row);
    }
  }catch(e){host.textContent='Impossibile leggere le copie: '+e.message;}
}
function replaceAllNotes(notes){return new Promise((res,rej)=>{const tx=db.transaction(STORE,'readwrite'),store=tx.objectStore(STORE);store.clear();for(const n of notes)if(n&&typeof n.id==='string')store.put(n);tx.oncomplete=()=>{recordDataChange();res();};tx.onerror=()=>rej(tx.error||new Error('Ripristino non riuscito'));tx.onabort=()=>rej(tx.error||new Error('Ripristino annullato'));});}


/* onfim 0.8: UX condivisa, promemoria rapidi, collegamenti e riordino. */
const ONFIM_REPEAT_DAYS={sunday:0,monday:1,tuesday:2,wednesday:3,thursday:4,friday:5,saturday:6};
function onfimLocalDateTime(d){const p=v=>String(v).padStart(2,'0');return `${d.getFullYear()}-${p(d.getMonth()+1)}-${p(d.getDate())}T${p(d.getHours())}:${p(d.getMinutes())}`;}
 const ONFIM_QUICK_TIMES_KEY='onfim-reminder-daypart-times-v1';
 const ONFIM_DEFAULT_QUICK_TIMES={morning:'09:00',afternoon:'15:00'};
 function onfimValidQuickTime(v){return typeof v==='string'&&/^([01]\d|2[0-3]):[0-5]\d$/.test(v);}
 function onfimLoadQuickTimes(){
  try{const o=JSON.parse(localStorage.getItem(ONFIM_QUICK_TIMES_KEY)||'{}');
   return Object.fromEntries(Object.entries(ONFIM_DEFAULT_QUICK_TIMES).map(([k,v])=>[k,onfimValidQuickTime(o?.[k])?o[k]:v]));
  }catch{return {...ONFIM_DEFAULT_QUICK_TIMES};}
 }
 let onfimQuickTimes=onfimLoadQuickTimes();
 let onfimChosenDay='today',onfimChosenPeriod='',onfimSmartApplied=false;
 function onfimSelectedDayDate(now=new Date()){
  const d=new Date(now);
  if(onfimChosenDay==='tomorrow')d.setDate(d.getDate()+1);
  if(onfimChosenDay==='other'){
   const raw=$('reminderOtherDate').value;if(!raw)return null;
   const [y,m,dd]=raw.split('-').map(Number);if(!y||!m||!dd)return null;
   const proposed=new Date(y,m-1,dd);if(proposed.getFullYear()!==y||proposed.getMonth()!==m-1||proposed.getDate()!==dd)return null;
   return proposed;
  }
  return d;
 }
 function onfimPresetDate(period,now=new Date()){
  const d=onfimSelectedDayDate(now);if(!d)return null;
  const [h,m]=onfimQuickTimes[period].split(':').map(Number);
  d.setHours(h,m,0,0);return d;
 }
 function onfimRefreshPresets(){
  const now=new Date();
  for(const b of document.querySelectorAll('[data-reminder-day]'))b.setAttribute('aria-pressed',String(b.dataset.reminderDay===onfimChosenDay));
  $('reminderOtherDate').classList.toggle('hidden',onfimChosenDay!=='other');
  for(const b of document.querySelectorAll('[data-reminder-period]')){
   const period=b.dataset.reminderPeriod,d=onfimPresetDate(period,now);
   b.disabled=!d||d<=now;
   b.setAttribute('aria-pressed',String(period===onfimChosenPeriod));
   const display=document.querySelector('[data-period-time="'+period+'"]');if(display)display.textContent=onfimQuickTimes[period];
  }
  if(onfimChosenPeriod&&document.querySelector('[data-reminder-period="'+onfimChosenPeriod+'"]')?.disabled){onfimChosenPeriod='';for(const b of document.querySelectorAll('[data-reminder-period]'))b.setAttribute('aria-pressed','false');}
  $('reminderSmartHint').textContent=onfimChosenDay==='today'?'Le fasce orarie già trascorse non sono disponibili.':onfimChosenDay==='other'&&!$('reminderOtherDate').value?'Scegli una data.':'Scegli Mattina o Pomeriggio.';
 }
 function onfimApplySmartChoice(){
  if(!onfimChosenPeriod)return;
  const date=onfimPresetDate(onfimChosenPeriod);if(!date||date<=new Date()){toast('Scegli una data e un orario futuri');onfimRefreshPresets();return;}
  $('readReminderValue').value=onfimLocalDateTime(date);onfimSmartApplied=true;
  $('dateFold').open=false;onfimUpdateRepeatInfo();onfimUpdateReminderSelected();
 }
 for(const b of document.querySelectorAll('[data-reminder-day]'))b.addEventListener('click',()=>{
  onfimChosenDay=b.dataset.reminderDay;onfimRefreshPresets();if(!onfimChosenPeriod&&onfimSmartApplied){$('readReminderValue').value='';onfimSmartApplied=false;onfimUpdateReminderSelected();onfimUpdateRepeatInfo();}onfimApplySmartChoice();
 });
 $('reminderOtherDate').addEventListener('change',()=>{onfimRefreshPresets();onfimApplySmartChoice();});
 for(const b of document.querySelectorAll('[data-reminder-period]'))b.addEventListener('click',()=>{
  if(b.disabled)return;onfimChosenPeriod=b.dataset.reminderPeriod;onfimRefreshPresets();onfimApplySmartChoice();
 });
 for(const [id,key] of [['onfimTimeMorning','morning'],['onfimTimeAfternoon','afternoon']]){
  const input=$(id);input.value=onfimQuickTimes[key];
  input.addEventListener('change',()=>{
   if(!onfimValidQuickTime(input.value)){input.value=onfimQuickTimes[key];toast('Orario non valido');return;}
   onfimQuickTimes[key]=input.value;
   try{localStorage.setItem(ONFIM_QUICK_TIMES_KEY,JSON.stringify(onfimQuickTimes));}catch(e){console.warn('Impossibile salvare gli orari',e);}
   onfimRefreshPresets();
  });
 }
function onfimUpdateReminderSelected(){const v=$('readReminderValue').value,d=v?new Date(v):null;
 $('chosenReminderDate').textContent=d&&Number.isFinite(+d)?d.toLocaleDateString(onfimCurrentLocale(),{day:'numeric',month:'short'})+' · '+d.toLocaleTimeString(onfimCurrentLocale(),{hour:'2-digit',minute:'2-digit'}):'Nessuna data';
}
function onfimNextRepeat(value,rule,after=Date.now(),anchor=value){
 if(!value||!rule||rule==='none')return '';
 const first=new Date(value),base=new Date(anchor),now=new Date(after);if(!Number.isFinite(+first))return '';
 const day0=new Date(first.getFullYear(),first.getMonth(),first.getDate()),day1=new Date(now.getFullYear(),now.getMonth(),now.getDate());
 let steps=rule==='monthly'?Math.max(0,(now.getFullYear()-first.getFullYear())*12+now.getMonth()-first.getMonth()):Math.max(0,Math.round((day1-day0)/86400000));if(rule==='weekly')steps=Math.floor(steps/7);
 for(let i=0;i<10;i++,steps++){
  const candidate=new Date(first);if(rule==='monthly'){candidate.setDate(1);candidate.setMonth(first.getMonth()+steps);candidate.setDate(Math.min(Number.isFinite(+base)?base.getDate():first.getDate(),new Date(candidate.getFullYear(),candidate.getMonth()+1,0).getDate()));}else candidate.setDate(first.getDate()+steps*(rule==='weekly'?7:1));
  if(candidate<first)continue;const day=candidate.getDay(),allowed=rule==='weekday'?day>=1&&day<=5:rule in ONFIM_REPEAT_DAYS?day===ONFIM_REPEAT_DAYS[rule]:true;
  if(+candidate>after&&allowed)return onfimLocalDateTime(candidate);
 }return '';
}
function onfimIcsRepeat(n){const days={monday:'MO',tuesday:'TU',wednesday:'WE',thursday:'TH',friday:'FR',saturday:'SA',sunday:'SU'};let rule={daily:'DAILY',weekly:'WEEKLY',weekday:'WEEKLY;BYDAY=MO,TU,WE,TH,FR',monthly:'MONTHLY;BYMONTHDAY='+new Date(n.reminderBase||n.reminder).getDate()+',-1;BYSETPOS=1'}[n.reminderRepeat];if(days[n.reminderRepeat])rule='WEEKLY;BYDAY='+days[n.reminderRepeat];return rule?['RRULE:FREQ='+rule]:[];}
function onfimFormatRepeat(rule){const names={daily:'ogni giorno',weekly:'ogni settimana',monthly:'ogni mese',weekday:'lun–ven',monday:'ogni lunedì',tuesday:'ogni martedì',wednesday:'ogni mercoledì',thursday:'ogni giovedì',friday:'ogni venerdì',saturday:'ogni sabato',sunday:'ogni domenica'};return names[rule]||'';}
function onfimUpdateRepeatInfo(){const rule=$('reminderRepeat').value;
  const d=$('readReminderValue').value,day=d?new Date(d).getDay():new Date().getDay();
  const keys=['sunday','monday','tuesday','wednesday','thursday','friday','saturday'];
  const names=['domenica','lunedì','martedì','mercoledì','giovedì','venerdì','sabato'];
  $('reminderMatchingWeekday').textContent='Ogni '+names[day]+' (giorno scelto)';
  $('reminderMatchingWeekday').dataset.rule=keys[day];
  $('repeatFoldLabel').textContent=rule==='none'?'Mai':onfimFormatRepeat(rule);
  const hasGeo=$('geoEnabled').checked;$('recurrenceSection').classList.toggle('hidden',hasGeo&&!$('readReminderValue').value);$('repeatInfo').textContent=rule==='none'?'Una sola volta.':`Ripetizione ${onfimFormatRepeat(rule)}. ${typeof window.OnfimAndroid==='undefined'?'In Lite funziona soltanto con la PWA aperta.':'Gli avvisi ripetuti con app chiusa richiedono l’aggiornamento del servizio Android.'}`;}
$('reminderMatchingWeekday').onclick=()=>{$('reminderRepeat').value=$('reminderMatchingWeekday').dataset.rule;onfimUpdateRepeatInfo();};
$('readReminderValue').addEventListener('input',()=>{onfimChosenPeriod='';onfimSmartApplied=false;onfimRefreshPresets();onfimUpdateRepeatInfo();onfimUpdateReminderSelected();});$('reminderRepeat').addEventListener('change',onfimUpdateRepeatInfo);
function onfimReminderActive(n){return !!(n.geofence?.enabled||(n.reminder&&(new Date(n.reminder).getTime()>Date.now()||(n.reminderRepeat&&n.reminderRepeat!=='none'))));}
function onfimRenderFileRefs(n,container){
 const items=Array.isArray(n.linkedFiles)?n.linkedFiles:[];if(!items.length)return;
 const list=document.createElement('div');list.className='linked-file-list';
 for(const f of items){const row=document.createElement('div');row.className='linked-file';const icon=document.createElement('span');icon.textContent='↗';icon.setAttribute('aria-hidden','true');const name=document.createElement('span');name.className='linked-file-name';name.textContent=String(f.name||'Documento collegato');const btn=document.createElement('button');btn.type='button';btn.textContent='Apri';btn.title='Apri file collegato';if(!onfimLinkedFileBridge()){btn.disabled=true;btn.title='Disponibile soltanto nell’APK con supporto ai file del telefono';}
 btn.onclick=()=>onfimOpenLinkedFile(f);row.append(icon,name,btn);list.append(row);}
 container.append(list);
}
const onfimLinkedFileBridge=()=>typeof window.OnfimAndroid!=='undefined'&&typeof OnfimAndroid.pickLinkedFile==='function'&&typeof OnfimAndroid.openLinkedFile==='function';
let onfimEditorLinks=[];
function onfimRenderEditorLinks(){const list=$('linkedFileEditorList');list.replaceChildren();for(const [index,f] of onfimEditorLinks.entries()){
 const row=document.createElement('div');row.className='linked-file';const name=document.createElement('span');name.className='linked-file-name';name.textContent=String(f.name||'Documento collegato');const remove=document.createElement('button');remove.type='button';remove.textContent='Scollega';remove.onclick=()=>{onfimEditorLinks.splice(index,1);onfimRenderEditorLinks();markDirty();};row.append(name,remove);list.append(row);
 }}
function onfimOpenLinkedFile(f){if(!onfimLinkedFileBridge()){toast('Il collegamento si apre soltanto nell’APK con supporto Android');return;}try{OnfimAndroid.openLinkedFile(f.uri);}catch(e){toast('File non disponibile: '+e.message);}}
if(!onfimLinkedFileBridge()){$('pickLinkedFile').disabled=true;$('pickLinkedFile').title='Disponibile nell’APK Android';$('linkFileExplanation').textContent='Collegamento disponibile nell’APK Android.';}
$('pickLinkedFile').onclick=()=>{if(!onfimLinkedFileBridge()){toast('Collegamento ai file disponibile nell’APK Android');return;}try{OnfimAndroid.pickLinkedFile();}catch(e){toast('Selezione non disponibile');}};
window.onfimFilePicked=(raw)=>{try{if(!$('editView').classList.contains('show'))throw new Error('L’editor non è aperto');const o=typeof raw==='string'?JSON.parse(raw):raw;if(!o||typeof o.uri!=='string'||!/^content:\/\//.test(o.uri)||o.uri.length>4096)throw new Error('Riferimento non valido');if(onfimEditorLinks.length>=15)throw new Error('Massimo 15 file per parte');if(!onfimEditorLinks.some(f=>f.uri===o.uri))onfimEditorLinks.push({uri:o.uri,name:String(o.name||'Documento').slice(0,180),type:String(o.type||'').slice(0,120),size:Number(o.size)||0});onfimRenderEditorLinks();markDirty();toast('File collegato: ricorda di premere Salva');}catch(e){toast('Impossibile collegare il file: '+e.message);}};
function onfimClosePartMenus(){} // Compatibilità con la gestione del tocco globale.
async function onfimMovePart(partId,direction){const all=await allNotes();const part=all.find(n=>n.id===partId&&!n.deletedAt);if(!part)return;const root=groupRootFor(part,all),parts=chainMembers(root,all);const index=parts.findIndex(x=>x.id===partId),other=parts[index+direction];
 // La radice resta prima: cambiare il primo elemento muterebbe l'identità dell'appunto.
 if(index<=0||index+direction<=0||!other)return;
 if(root.reserved&&!unlocked&&!await checkPin())return;
 const order1=Number(part.chainOrder)||index,order2=Number(other.chainOrder)||index+direction;
 await putNotesBatch([{...part,chainOrder:order2,updated:Date.now()},{...other,chainOrder:order1,updated:Date.now()}]);
 const refreshed=(await allNotes()).find(n=>n.id===root.id);if(refreshed)await openRead(refreshed);await reload();toast('Ordine delle parti aggiornato');
}
// Add-part menu reachable directly from home-card ⋮. Reading stays uncluttered.
let onfimPartFromCard=false;
function onfimAskPartFromCard(id){onfimPartFromCard=false;void onfimChooseDestinationFrom(id);}
$('partCancel').addEventListener('click',()=>{onfimPartFromCard=false;});$('addPartDialog').addEventListener('close',()=>{onfimPartFromCard=false;});
// Note: partNew/partExisting handlers are wrapped after their existing assignments.
for(const kind of ['New','Existing']){
 const b=$('part'+kind),original=b.onclick;
 b.onclick=async e=>{if(!onfimPartFromCard)return original.call(b,e);
   onfimPartFromCard=false;closeAddPart();if(kind==='New')return $('addSequel').onclick();return onfimChooseDestinationFrom(readId);};
}

// PWA installed share target receiver (text/link only).
// Android ACTION_SEND/ACTION_SEND_MULTIPLE receiver. The native Activity delivers a JSON string
// via evaluateJavascript('window.onfimReceiveShare(' + JSONObject.quote(json) + ')').
// Never create or overwrite an existing note without the user's confirmation.
const shareInboxQueue=[];
let shareInboxActive=null, shareInboxReady=false;
const shareInboxDialog=$('shareInboxDialog');
function onfimNormalizeShare(raw){
  const o=typeof raw==='string'?JSON.parse(raw):raw;
  if(!o||typeof o!=='object'||Array.isArray(o))throw new Error('Condivisione non valida');
  const text=typeof o.text==='string'?o.text.slice(0,100000):'';
  const title=typeof o.title==='string'?o.title.slice(0,200):'';
  const images=(Array.isArray(o.images)?o.images:[]).filter(s=>typeof s==='string'&&/^data:image\/(?:jpeg|png|webp);base64,/i.test(s)&&s.length<9*1024*1024).slice(0,10);
  const audios=(Array.isArray(o.audios)?o.audios:[]).filter(a=>a&&typeof a.name==='string'&&typeof a.data==='string'&&/^data:audio\/[\w.+-]+;base64,/i.test(a.data)&&a.data.length<14*1024*1024).slice(0,3);
  if(!text.trim()&&!title.trim()&&!images.length&&!audios.length)throw new Error('Nessun contenuto supportato');
  return {text,title,images,audios};
}
function onfimOpenNextShare(){
  if(!shareInboxReady||shareInboxActive||!shareInboxQueue.length)return;
  if(document.querySelector('dialog[open]')){setTimeout(onfimOpenNextShare,500);return;}
  shareInboxActive=shareInboxQueue.shift();
  const items=[];
  if(shareInboxActive.text.trim()||shareInboxActive.title.trim())items.push('testo o collegamento');
  if(shareInboxActive.images.length)items.push(shareInboxActive.images.length+' foto');
  if(shareInboxActive.audios.length)items.push(shareInboxActive.audios.length+' audio');
  $('shareInboxSummary').textContent='Contenuto ricevuto: '+items.join(', ')+'.';
  shareInboxDialog.showModal();
}
window.onfimReceiveShare=function(raw){
  try{if(shareInboxQueue.length>=5)throw new Error('Completa prima le condivisioni in attesa');shareInboxQueue.push(onfimNormalizeShare(raw));onfimOpenNextShare();return 'queued';}
  catch(e){console.warn('onfim: condivisione non utilizzabile',e);toast('Condivisione non supportata: '+e.message);return 'invalid';}
};
function closeOnfimShareInbox(){if(shareInboxDialog.open)shareInboxDialog.close();shareInboxActive=null;onfimOpenNextShare();}
$('shareInboxClose').onclick=$('shareInboxCancel').onclick=closeOnfimShareInbox;
shareInboxDialog.addEventListener('cancel',e=>{e.preventDefault();closeOnfimShareInbox();});
$('shareInboxAccept').onclick=async()=>{
 const incoming=shareInboxActive;if(!incoming)return;
 const accept=$('shareInboxAccept');accept.disabled=true;
 try{
   if(isRecording()){toast('Termina la registrazione in corso');return;}
   if(dirty){toast('Salva o chiudi l’appunto corrente prima di ricevere la condivisione');return;}
   // Open a fresh ordinary note: never inherit the currently active Archivio filter/PIN.
   $('filter').value='ordinary';syncFilterPills();newNote();
   $('noteTitle').value=incoming.title;
   $('noteBody').textContent=incoming.text;
   images.push(...incoming.images);photoMarks.push(...incoming.images.map(() => ''));
   for(const a of incoming.audios){audioClips.push({id:uid(),name:a.name.slice(0,150)||'Audio condiviso',data:a.data,created:Date.now()});}
   photoList();renderAudioGallery();updateTextMark();resetTextHistory();
   chooseTab(incoming.text.trim()||incoming.title.trim()?'text':'photos');
   markDirty();
   closeOnfimShareInbox();
   toast('Appunto ricevuto da un’altra app');
 }catch(e){toast('Importazione non riuscita: '+(e.message||e));}
 finally{accept.disabled=false;}
};
window.addEventListener('resize',()=>{if($('reminderDialog').open&&$('geoEnabled').checked)requestAnimationFrame(geoMapRender);});
(async()=>{try{await database();clearCanvas();await reload();await checkPersistentStorage();await scheduleReminders();
  try{await openSnapshotDB();await renderLocalSnapshots();scheduleLocalSnapshot();}
  catch(e){console.warn('onfim Lite: copie interne non disponibili',e);$('localBackupList').textContent='Copie interne non disponibili: '+e.message;}
  shareInboxReady=true;onfimOpenNextShare();
  const query=new URL(location.href),params=query.searchParams;
  const incoming={title:params.get('title')||'',text:[params.get('text')||'',params.get('url')||''].filter(Boolean).join('\n')};
  if(incoming.title||incoming.text){window.onfimReceiveShare(incoming);query.search='';history.replaceState(null,'',query.pathname+query.hash);}}catch(e){alert('Impossibile aprire il database locale: '+(e.message||e));}})();

// ONFIM 0.8.7 single-file preview. The original IndexedDB name and note IDs are unchanged.
const ONFIM_PREVIEW_VERSION='0.8.18.1';

// CHECKLISTS: stored as an optional property on the note, carried by JSON backups.
function onfimNormalizeChecklist(value){
 if(!Array.isArray(value))return [];
 return value.filter(x=>x&&typeof x.text==='string').slice(0,300).map(x=>({id:typeof x.id==='string'&&x.id.length<100?x.id:uid(),text:x.text.slice(0,500),done:!!x.done}));
}
let onfimChecklistDraft=[];
const onfimPreviousEmptyNote=emptyNote;
emptyNote=()=>({...onfimPreviousEmptyNote(),checklist:[]});
const onfimPreviousHasContent=hasContent;
hasContent=n=>onfimPreviousHasContent(n)||onfimNormalizeChecklist(n.checklist).some(x=>x.text.trim());
const onfimPreviousSnapshot=snapshot;
snapshot=()=>({...onfimPreviousSnapshot(),checklist:onfimNormalizeChecklist(onfimChecklistDraft).filter(x=>x.text.trim())});
function onfimChecklistEditorRender(){
 const host=$('checklistEditorItems');host.replaceChildren();
 for(const item of onfimChecklistDraft){
  const row=document.createElement('div');row.className='onfim-checklist-line';
  const checked=document.createElement('input');checked.type='checkbox';checked.checked=item.done;checked.setAttribute('aria-label','Voce completata');
  checked.onchange=()=>{item.done=checked.checked;markDirty();};
  const field=document.createElement('input');field.type='text';field.maxLength=500;field.placeholder='Voce della lista';field.value=item.text;
  field.oninput=()=>{item.text=field.value;markDirty();};
  const del=document.createElement('button');del.type='button';del.textContent='×';del.title='Rimuovi voce';del.setAttribute('aria-label','Rimuovi voce');
  del.onclick=()=>{onfimChecklistDraft=onfimChecklistDraft.filter(x=>x.id!==item.id);onfimChecklistEditorRender();markDirty();};
  row.append(checked,field,del);host.append(row);
 }
}
$('addChecklistItem').onclick=()=>{
 if(onfimChecklistDraft.length>=300){toast('Limite di 300 voci raggiunto');return;}
 onfimChecklistDraft.push({id:uid(),text:'',done:false});onfimChecklistEditorRender();markDirty();
 const inputs=$('checklistEditorItems').querySelectorAll('input[type="text"]');inputs[inputs.length-1]?.focus();
};
const onfimPreviousEditNote=editNote;
editNote=function(n,...args){onfimChecklistDraft=onfimNormalizeChecklist(n.checklist);onfimPreviousEditNote(n,...args);onfimChecklistEditorRender();};

function onfimReadChecklistHost(n){
 const list=onfimNormalizeChecklist(n.checklist).filter(x=>x.text.trim());
 if(!list.length)return null;
 const host=document.createElement('div');host.className='onfim-checklist-read';
 const heading=document.createElement('h2');heading.textContent='Checklist';host.append(heading);
 for(const it of list){
  const label=document.createElement('label');
  const check=document.createElement('input');check.type='checkbox';check.checked=it.done;
  check.setAttribute('aria-label','Completa '+it.text);
  const span=document.createElement('span');span.textContent=it.text;if(it.done)span.className='completed';
  check.onchange=async()=>{
   const original=check.checked;check.disabled=true;
   try{
    const fresh=(await allNotes()).find(x=>x.id===n.id&&!x.deletedAt);
    if(!fresh){toast('Appunto non trovato');check.checked=!original;return;}
    if(fresh.reserved&&!unlocked&&!await checkPin()){check.checked=!original;return;}
    const updated=onfimNormalizeChecklist(fresh.checklist);
    const target=updated.find(x=>x.id===it.id);
    if(!target){toast('Voce non trovata');check.checked=!original;return;}
    target.done=original;
    await putNote({...fresh,checklist:updated,updated:Date.now()});
    span.classList.toggle('completed',original);
   }catch(e){console.error(e);toast('Non è stato possibile aggiornare la lista');check.checked=!original;}
   finally{check.disabled=false;}
  };
  label.append(check,span);host.append(label);
 }
 return host;
}
const onfimPreviousOpenRead=openRead;
openRead=async function(n){
 await onfimPreviousOpenRead(n);
 const all=await allNotes(),root=all.find(x=>x.id===readId&&!x.deletedAt);if(!root)return;
 const checkHost=$('readChecklist');checkHost.replaceChildren();
 const parts=chainMembers(root,all);
 if(parts.length===1){const block=onfimReadChecklistHost(root);if(block)checkHost.append(...block.childNodes);}
 checkHost.classList.toggle('hidden',parts.length>1);
};
const onfimPreviousMakeChainPart=makeChainPart;
makeChainPart=function(n,...args){const part=onfimPreviousMakeChainPart(n,...args);const block=onfimReadChecklistHost(n);if(block)part.append(block);return part;};

// OPTIONAL SMART PRESET: computes a normal datetime-local, never a new recurrence rule.
const ONFIM_EXTRA_PRESET_KEY='onfim-custom-preset-v1';
function onfimExtraRead(){
 try{const v=JSON.parse(localStorage.getItem(ONFIM_EXTRA_PRESET_KEY)||'{}');
  return {mode:['off','daypart','days','weekday'].includes(v.mode)?v.mode:'off',days:Math.max(1,Math.min(365,Number(v.days)||3)),weekday:Number.isInteger(+v.weekday)&&+v.weekday>=0&&+v.weekday<=6?+v.weekday:4,time:onfimValidQuickTime(v.time)?v.time:'20:00'};
 }catch{return {mode:'off',days:3,weekday:4,time:'20:00'};}
}
let onfimExtra=onfimExtraRead();
const onfimWeekdayIt=['Domenica','Lunedì','Martedì','Mercoledì','Giovedì','Venerdì','Sabato'];
function onfimExtraTitle(){return onfimExtra.mode==='daypart'?'Altro orario · '+onfimExtra.time:onfimExtra.mode==='days'?'Fra '+onfimExtra.days+' '+(onfimExtra.days===1?'giorno':'giorni')+' · '+onfimExtra.time:onfimExtra.mode==='weekday'?'Prossimo '+onfimWeekdayIt[onfimExtra.weekday].toLowerCase()+' · '+onfimExtra.time:'';}
function onfimExtraDate(now=new Date()){
 if(onfimExtra.mode==='off')return null;
 const d=onfimExtra.mode==='daypart'?onfimSelectedDayDate(now):new Date(now);
 if(!d)return null;
 if(onfimExtra.mode==='days')d.setDate(d.getDate()+onfimExtra.days);
 if(onfimExtra.mode==='weekday'){
  // "Prossimo giovedì" is strictly the next occurrence (not today).
  const delta=(onfimExtra.weekday-d.getDay()+7)%7||7;d.setDate(d.getDate()+delta);
 }
 const [h,m]=onfimExtra.time.split(':').map(Number);d.setHours(h,m,0,0);
 return d;
}
function onfimExtraRefreshUI(){
 const cfg=onfimExtra;
 $('extraPresetMode').value=cfg.mode;
 $('extraPresetDays').value=cfg.days;
 $('extraPresetWeekday').value=String(cfg.weekday);
 $('extraPresetTime').value=cfg.time;
 $('extraPresetOptions').classList.toggle('hidden',cfg.mode==='off');
 $('extraPresetDaysLabel').classList.toggle('hidden',cfg.mode!=='days');
 $('extraPresetWeekdayLabel').classList.toggle('hidden',cfg.mode!=='weekday');
 $('extraPresetPreview').textContent=onfimExtraTitle();
 const b=$('extraReminderButton');b.classList.toggle('hidden',cfg.mode==='off');
 b.textContent=onfimExtraTitle();const d=onfimExtraDate();b.disabled=!d||d<=new Date();
}
for(const id of ['extraPresetMode','extraPresetDays','extraPresetWeekday','extraPresetTime']){
 $(id).addEventListener('change',()=>{
  const mode=$('extraPresetMode').value,days=Number($('extraPresetDays').value),weekday=Number($('extraPresetWeekday').value),time=$('extraPresetTime').value;
  if(!Number.isInteger(days)||days<1||days>365||!onfimValidQuickTime(time)){toast('Controlla giorni e orario');onfimExtraRefreshUI();return;}
  onfimExtra={mode,days,weekday,time};localStorage.setItem(ONFIM_EXTRA_PRESET_KEY,JSON.stringify(onfimExtra));onfimExtraRefreshUI();
 });
}
$('extraReminderButton').onclick=()=>{
 const date=onfimExtraDate();if(!date||date<=new Date()){toast('La scadenza deve essere futura');return;}
 onfimChosenPeriod='';onfimSmartApplied=false;onfimRefreshPresets();
 $('readReminderValue').value=onfimLocalDateTime(date);
 onfimUpdateRepeatInfo();onfimUpdateReminderSelected();$('dateFold').open=false;
};
const onfimPreviousRefreshPresets=onfimRefreshPresets;
onfimRefreshPresets=()=>{onfimPreviousRefreshPresets();onfimExtraRefreshUI();};
onfimExtraRefreshUI();

// Include the new third preset in the same *manual* backup schema; old JSON files remain accepted.
const onfimPrevExportJSON=exportJSON;
// Source exportJSON and shareBackupFile payloads are modified in the generated source to carry customReminderPreset.

// LOCALE: one UI, two string dictionaries; system-language default plus explicit override.
const ONFIM_LANG_KEY='onfim-ui-language-v1';
const ONFIM_UI_EN={"Dati nel browser":"Data in this browser","Le note sono salvate automaticamente su questo dispositivo.":"Notes are saved automatically on this device.","Protezione dei dati locali":"Local data protection","Copie locali":"Local copies","Fino a cinque copie nel browser. Si perdono se ne cancelli i dati.":"Up to five copies in this browser. Clearing browser data deletes them.","Backup esterno":"External backup","Salva una copia JSON fuori dal browser, sul telefono o su Drive.":"Save a JSON copy outside the browser, on your device or Drive.","Esporta backup":"Export backup","Esporta JSON":"Export JSON","Condividi backup":"Share backup","Ripristina da file":"Restore from file","Importa JSON":"Import JSON","Link a file esterni":"Links to external files","Informazioni sui file esterni":"About external files","Proteggi dati":"Protect data","Crea copia ora":"Create a copy now","Archivio interno":"Internal storage","Backup sul telefono":"Backups on device","Backup cloud":"Cloud backup","Esporta e importa":"Export and import","Le note correnti sono salvate nell’app.":"Current notes are stored in the app.","Fino a 10 copie nella cartella scelta.":"Up to 10 copies in the selected folder.","Backup automatico sul file cloud collegato.":"Automatic backup to the linked cloud file.","Trasferisci o recupera note tramite JSON.":"Transfer or restore notes using JSON.","Archivio salvato sul telefono":"Archive saved on device","Copia ora":"Back up now","Le copie automatiche non includono ancora le definizioni delle raccolte.":"Automatic copies do not yet include collection definitions.","Tutti":"All","Tutte":"All","Tutti gli appunti":"All notes","Testo":"Text","Inserisci testo nel disegno":"Insert text on drawing","Inserisci testo sulla fotografia":"Insert text on photo","Scrivi, poi tocca o trascina sul foglio":"Type, then tap or drag on the canvas","Scrivi, poi tocca o trascina sulla foto":"Type, then tap or drag on the photo","Scorrimento verticale fotografia":"Photo vertical scroll","Scorri fotografia":"Scroll photo","Nessun backup JSON registrato. Esporta una copia prima di cancellare i dati dell’app.":"No JSON backup recorded. Export a copy before clearing app data.","La data registra la richiesta di esportazione, non la verifica che il file sia stato effettivamente salvato.":"The date records when export was requested, not confirmation that the file was saved.","Cancella tutti i segni su questa foto?":"Clear all annotations on this photo?","Cancellare il disegno?":"Clear drawing?","Nessun backup registrato. Non ci sono ancora appunti.":"No backups yet; there are no notes.","Nessuna copia interna: verrà creata durante l’uso, se ci sono appunti.":"No local snapshots yet. A snapshot will be created when notes are available.","Non supportato dal browser in uso.":"Not supported by this browser.","La data registrata è richiesta di esportazione, non la verifica che il file sia stato effettivamente salvato.":"The recorded date means an export was requested, not that the file was saved.","Archivio vuoto":"Archive empty","Nessun preferito":"No favorites","Nessun appunto":"No notes","Premi ＋ per crearne uno.":"Press + to create one.","Aggiungi una stella a un appunto dal menu ⋮.":"Star a note using the ⋮ menu.","Puoi spostare qui gli appunti dal menu ⋮.":"Move notes here using the ⋮ menu.","Modifica nota":"Edit note","Appunti":"Notes","Preferiti":"Favorites","Archivio":"Archive","Filtri":"Filters","Etichette":"Tags","Azzera":"Clear","Ordina per":"Sort by","Modificati di recente":"Recently edited","Creati di recente":"Recently created","Modificati meno di recente":"Least recently edited","Creati meno di recente":"Oldest first","Titolo A–Z":"Title A–Z","Titolo Z–A":"Title Z–A","Backup":"Backup","I tuoi appunti":"Your notes","Indietro":"Back","Lettura":"Reading","Fissa in alto":"Pin to top","Promemoria":"Reminders","Condividi nota":"Share note","Aggiungi a un’altra nota":"Add to another note","Separa parti":"Separate parts","Sposta in Archivio":"Move to archive","Elimina appunto":"Delete note","Disegno":"Drawing","Foto":"Photos","Registrazioni vocali":"Voice recordings","Aggiungi seguito":"Append a part","Preferito":"Favorite","Modifica":"Edit","← Appunti":"← Notes","Testo":"Text","Audio":"Audio","Foglio da disegno":"Drawing canvas","Ingrandisci":"Expand","Riduci":"Reduce","Penna":"Pen","Gomma":"Eraser","Spessore":"Thickness","Cancella":"Clear","Aggiungi una foto dalla galleria o scattane una. Le GIF animate (max 5 MB) mantengono il movimento.":"Choose a photo or take one. Animated GIFs (up to 5 MB) remain animated.","Le fotografie vengono ridimensionate. Le GIF non si possono annotare.":"Photos may be resized. Animated GIFs cannot be annotated.","Registra un messaggio vocale o allega un file audio. Le registrazioni rimangono in onfim e vengono incluse nel backup JSON.":"Record a voice note or attach audio. Recordings are kept locally and included in JSON backups.","● Registra":"● Record","Pausa":"Pause","■ Stop":"■ Stop","Per registrare, autorizza il microfono quando richiesto.":"Allow microphone access to make a recording.","＋ Aggiungi file audio":"＋ Add audio file","Limite consigliato: clip fino a 10 MB. Audio e foto aumentano la dimensione del backup.":"Suggested limit: 10 MB per recording. Audio and photos increase backup size.","Dettagli":"Details","Colore della nota":"Note color","Bianco":"White","Rosso":"Red","Azzurro":"Light blue","Giallo":"Yellow","Verde":"Green","Grigio":"Gray","Blu":"Blue","Nero":"Black","Scrivi #etichetta nel testo per organizzare la nota.":"Use #tags in the text to organize notes.","Nell’Archivio 🔒 (accesso con PIN)":"In the archive 🔒 (PIN protected)","Link a file esterni":"Links to external files","↗ Collega file":"↗ Link file","Il backup non include i file esterni.":"External files are not included in backups.","Elimina":"Delete","Chiudi":"Close","Salva":"Save","Lingua / Language":"Language / Lingua","Lingua dell’interfaccia":"Interface language","Scegli una lingua oppure segui quella del dispositivo.":"Choose a language or use the device language.","Automatica":"Automatic","Italiano":"Italian","Orari utilizzati per Mattina e Pomeriggio.":"Times used for Morning and Afternoon.","Mattina":"Morning","Pomeriggio":"Afternoon","Le modifiche valgono per i nuovi promemoria.":"Changes affect new reminders.","Terza scorciatoia (facoltativa)":"Third shortcut (optional)","Tipo":"Type","Disattivata":"Disabled","Altro momento della giornata":"Another time of day","Fra un numero di giorni":"After a number of days","Prossimo giorno della settimana":"Next weekday","Fra quanti giorni":"After how many days","Giorno":"Day","Ora":"Time","Lunedì":"Monday","Martedì":"Tuesday","Mercoledì":"Wednesday","Giovedì":"Thursday","Venerdì":"Friday","Sabato":"Saturday","Domenica":"Sunday","Promemoria nel calendario":"Calendar reminders","Esporta eventi .ics per importarli nel calendario Android, che potrà notificarti anche con Onfim chiusa.":"Export .ics events to your calendar so you can be notified even when Onfim is closed.","Esporta .ics":"Export .ics","Avvisi web":"Web notifications","Avvisa mentre onfim Lite è aperta. Con la PWA chiusa non sono garantiti.":"Notifications while Onfim is open. Background alerts are not guaranteed.","Abilita":"Enable","Dati e backup":"Data & backups","Backup JSON":"JSON backup","Esporta tutti gli appunti, compresi Cestino, Archivio, disegni, foto e audio.":"Exports notes including Trash, Archive, drawings, photos and audio.","Esporta":"Export","Stato backup: controllo…":"Backup status: checking…","Importa JSON":"Import JSON","Legge anche i backup del prototipo precedente. Le note con lo stesso ID vengono aggiornate. Prima dell’importazione è creata una copia interna preventiva.":"Also reads older backups. Matching note IDs will be updated. A local snapshot is created before import.","Importa":"Import","Copie e archiviazione · browser":"Backups & storage · browser","Gli appunti sono archiviati sul dispositivo, non su un server.":"Notes are stored on your device, not on a server.","Condividi backup":"Share backup","Consegna il JSON al menu Condividi di Android: puoi scegliere Drive, se disponibile, e verificare lì che il file sia stato salvato.":"Shares the JSON using your device; you can save it to Drive or another destination.","Condividi":"Share","Copie interne":"Local snapshots","Fino a cinque copie recuperabili nel browser, create durante l'uso (non più di una ogni 3 ore se sono cambiate note).":"Up to five recoverable browser snapshots (at most one every 3 hours if notes changed).","Non sono copie su Drive":"These are not Drive backups","e si perdono cancellando i dati della PWA.":"and are lost if browser storage is cleared.","Controllo copie interne…":"Checking local snapshots…","Crea copia ora":"Create snapshot now","Archiviazione persistente":"Persistent storage","Controllo permesso…":"Checking permission…","Proteggi dati":"Protect data","Per un backup realmente separato, esporta il JSON o condividilo con Drive. I backup non sono cifrati: possono contenere anche note dell'Archivio.":"For an independent backup, export JSON or save it to Drive. Backups are unencrypted and may contain private notes.","Privacy e sicurezza":"Privacy & security","Il PIN non cifra gli appunti. I backup JSON includono anche quelli riservati in chiaro. Conservali con attenzione.":"The PIN does not encrypt notes. JSON backups contain private notes as readable text.","PIN dell’Archivio":"Archive PIN","Serve per aprire e visualizzare l’Archivio.":"Required to open the private archive.","Gestisci":"Manage","Blocca Archivio":"Lock archive","Chiude la sessione dell’Archivio e richiede nuovamente il PIN.":"Locks the archive until the PIN is entered again.","Blocca":"Lock","Cestino":"Trash","Appunti eliminati":"Deleted notes","Il Cestino conserva gli appunti finché non decidi di eliminarli definitivamente.":"Deleted notes remain in Trash until permanently removed.","Apri":"Open","Informazioni · browser":"About · browser","Questa versione funziona offline e condivide gli appunti tramite file JSON con onfim Android, ma alcune funzioni richiedono l'APK:":"This browser version works offline and exchanges notes with the Android app through JSON, but some features require the APK:","Promemoria:":"Reminders:","nessuna sveglia affidabile con la PWA chiusa; puoi esportarli nel Calendario.":"background alerts are not guaranteed; you can export events to your calendar.","Geofence:":"Location alerts:","non disponibili in background; quelli importati restano nel backup senza attivarsi.":"not active in the background; imported location settings remain in backups.","Backup su Drive:":"Drive backup:","manuale tramite Condividi; non automatico in background.":"manual through Share, not automatic in the background.","Widget e notifiche native Android:":"Widget and native Android notifications:","non disponibili.":"unavailable.","Estrazione testo dalle fotografie (OCR):":"Extract text from photos (OCR):","disponibile nell’APK completa. La Lite non incorpora un motore OCR.":"Available in the full Android app. Lite does not include an OCR engine.","← Impostazioni":"← Settings","Gli appunti rimangono qui fino allo svuotamento. I promemoria nel Cestino non vengono notificati.":"Deleted notes remain here until emptied. Reminders in Trash do not trigger alerts.","Svuota":"Empty","Colore della scheda":"Card color","Il colore si applica alla scheda.":"The color applies to the card.","Quando":"When","Oggi":"Today","Domani":"Tomorrow","Altra data":"Another date","Scegli giorno e fascia oraria.":"Choose a day and time of day.","Data e ora libera":"Custom date & time","Nessuna data":"No date","Data e ora":"Date & time","Scelte aggiuntive":"Additional choices","Ripeti":"Repeat","Mai":"Never","Ogni giorno della data scelta":"Repeat on the selected weekday","Frequenza":"Frequency","Mai (una volta)":"Never (once)","Ogni giorno":"Every day","Ogni settimana":"Every week","Ogni mese":"Every month","Ogni lunedì–venerdì":"Every weekday","Ogni lunedì":"Every Monday","Ogni martedì":"Every Tuesday","Ogni mercoledì":"Every Wednesday","Ogni giovedì":"Every Thursday","Ogni venerdì":"Every Friday","Ogni sabato":"Every Saturday","Ogni domenica":"Every Sunday","I promemoria a orario della PWA non sono affidabili quando è chiusa.":"Time reminders may not work when the browser app is closed.","Questa nota contiene un geofence importato dall’APK. Rimane nel backup, ma non è attivo nella PWA.":"This note has an imported location alert. It stays in backups but is inactive in the browser.","Luogo":"Location","Ricerca o mappa":"Search or map","Seleziona un punto sulla mappa oppure cercalo per indirizzo.":"Select a map point or search for an address.","Gli avvisi geografici non sono attivi nella PWA.":"Location alerts are not active in the browser.","Cerca indirizzo o località":"Search for address or place","Ricerca online, solo quando premi Cerca.":"Online search starts only when you press Search.","Scegli sulla mappa":"Choose on map","⛶ Ingrandisci":"⛶ Expand","Il mirino al centro indica il punto scelto. Tocca o trascina la mappa.":"The crosshair marks the selected point. Tap or drag the map.","· La mappa necessita di Internet":"· Maps require internet","Usa posizione attuale":"Use current location","Latitudine":"Latitude","Longitudine":"Longitude","Raggio (metri)":"Radius (meters)","Avvisami":"Notify me","Quando arrivo":"When arriving","Quando esco":"When leaving","Rimuovi luogo":"Remove location","Rimuovi":"Remove","Scegli il luogo":"Choose location","✓ Fine":"✓ Done","Trascina per spostare il mirino oppure tocca un punto. Il luogo scelto apparirà nel promemoria.":"Drag to move the crosshair or tap a point. The selected place appears in the reminder.","Condividi con onfim":"Share with Onfim","Il contenuto verrà aperto in un nuovo appunto: potrai completarlo e salvarlo normalmente.":"The shared content will open as a new note.","Annulla":"Cancel","Crea appunto":"Create note","Crea una nuova parte":"Create a new part","Scegli la nota di destinazione":"Choose destination note","Scegli dove aggiungere il contenuto. L’originale sarà spostato nel Cestino, senza trasferire promemoria o impostazioni.":"Choose where to add the content. The original is moved to Trash; reminders and settings are not transferred.","Raccolte dinamiche":"Smart collections","Le note restano nell’archivio. La raccolta mostra automaticamente gli appunti che contengono almeno uno degli hashtag scelti.":"Notes stay in the archive. Collections show notes matching any selected tag.","Nuova raccolta":"New collection","Hashtag (separati da spazio o virgola)":"Hashtags (space or comma separated)","Nascondi queste note dalla Home":"Hide these notes from Home","Crea raccolta":"Create collection","Le raccolte sono viste, non copie delle note. Sono incluse nei backup JSON manuali; il backup nativo Android va verificato separatamente.":"Collections are views, not duplicate notes. They are included in manual JSON backups.","PIN Archivio":"Archive PIN","PIN di 4 cifre":"4-digit PIN","Annota fotografia":"Annotate photo","Salva segni":"Save annotations","I segni vengono conservati separatamente dalla foto originale.":"Annotations are saved separately from the original photo.","Colore della penna":"Pen color","I sette colori di onfim":"Seven Onfim colors","Oppure regola un colore personalizzato":"Or choose a custom color","Tonalità":"Hue","Saturazione":"Saturation","Luminosità":"Lightness","Codice colore":"Color code","Usa colore":"Use color","Checklist":"Checklist","＋ Aggiungi voce":"＋ Add item","Voce della lista":"List item","Voce completata":"Item completed","Rimuovi voce":"Remove item","Cerca negli appunti":"Search notes","Cerca tra le etichette…":"Search tags…","Titolo (facoltativo)":"Title (optional)","Scrivi qui…":"Write here…","Nuovo appunto":"New note","Grassetto":"Bold","Corsivo":"Italic","Sottolineato":"Underline","Barrato":"Strikethrough","Elenco puntato":"Bulleted list","Evidenziatore viola":"Purple highlighter","Annulla modifica testo":"Undo text","Ripristina modifica testo":"Redo text","Testo nero":"Black text","Testo rosso":"Red text","Testo blu":"Blue text","Testo verde":"Green text","Inserisci data e ora nel testo":"Insert date and time","Data/ora":"Date/time","Personalizza colore":"Custom color","Galleria":"Gallery","Fotocamera":"Camera","Ingrandisci foglio":"Expand canvas","Senza titolo":"Untitled","Modifiche non salvate":"Unsaved changes","Scegli una data.":"Choose a date.","Scegli Mattina o Pomeriggio.":"Choose Morning or Afternoon.","Le fasce orarie già trascorse non sono disponibili.":"Past times today are unavailable.","Scegli data e ora future":"Choose a future date and time","Promemoria salvato":"Reminder saved","Promemoria rimosso":"Reminder removed","Appunto vuoto":"Empty note","Rimuovi dai Preferiti":"Remove from Favorites","Aggiungi ai Preferiti":"Add to Favorites","Rimuovi da Fissati":"Unpin","Fissato in alto":"Pinned","Sposta nel Cestino":"Move to Trash","Rimosso dai Preferiti":"Removed from Favorites","Aggiunto ai Preferiti":"Added to Favorites","Prima separa le parti concatenate di questa nota":"First separate this note’s linked parts","Appunto non trovato":"Note not found","Voce non trovata":"Item not found","Limite di 300 voci raggiunto":"300-item limit reached","Non è stato possibile aggiornare la lista":"Could not update checklist","Altro orario":"Other time","Terza scelta":"Third choice","Fra":"In","giorni":"days","giorno":"day","Prossimo":"Next"};
function onfimCurrentLocale(){return onfimLang==='en'?'en-GB':'it-IT';}
function onfimLanguageCode(){
 const configured=localStorage.getItem(ONFIM_LANG_KEY)||'auto';
 return configured==='en'?'en':configured==='it'?'it':/^en\b/i.test(navigator.language||'')?'en':'it';
}
let onfimLang=onfimLanguageCode();
Object.assign(ONFIM_UI_EN, {'✓ Applica':'✓ Apply','Dimensione':'Size','Spessore':'Thickness','Conferma testo':'Confirm text','Annulla testo':'Cancel text','Scrivi e posiziona il testo sul foglio':'Type and position text on the canvas','Scrivi e posiziona il testo sulla foto':'Type and position text on the photo','Imposta promemoria':'Set reminder','Non disponibile nell’Archivio':'Not available in Archive'});
Object.assign(ONFIM_UI_EN,{'Filtri:':'Filters:','＋ Nuova raccolta':'+ New collection','Nessuna raccolta':'No collections','Sposta su':'Move up','Sposta giù':'Move down','Rimuovi filtro':'Remove filter','Etichette selezionate':'Selected tags'});
const onfimOriginalText=new WeakMap(),onfimOriginalAttrs=new WeakMap();
const onfimSkippedUserText='#noteBody,#noteTitle,#readBody,#readTitle,#readPhotos,#readAudios,#readChecklist,#checklistEditorItems,#noteList .title,#noteList .preview,#noteList .chip,#joinOptions .join-title,#joinOptions .join-preview,.chain-part-title,.read-body,.read-footer,.chip,.audio-label,#linkedFileEditorList,#onfimTagSuggestions';
function onfimSkipLocaleNode(el){return !el||!!el.closest('script,style,'+onfimSkippedUserText);}
function onfimEnglishText(v){
 const match=(pattern,text)=>{const m=v.match(pattern);return m?text(...m.slice(1)):null;};
 return ONFIM_UI_EN[v]||
  match(/^Ultima esportazione avviata: (.+)\. Alcuni appunti sono stati modificati dopo: crea un nuovo backup\.$/,d=>'Last export started: '+d+'. Some notes have changed since then; make a new backup.')||
  match(/^Ultima esportazione avviata: (.+) \(oltre 7 giorni fa\)\. È consigliato un nuovo backup\.$/,d=>'Last export started: '+d+' (more than 7 days ago). A new backup is recommended.')||
  match(/^Ultima esportazione avviata: (.+)\. Non risultano modifiche successive\.$/,d=>'Last export started: '+d+'. No subsequent changes found.')||
  match(/^(\d+) appunti eliminati\. Puoi ripristinarli o eliminarli definitivamente\.$/,n=>n+' deleted notes. Restore or permanently delete them.')||
  match(/^(\d+) appunto eliminato\. Puoi ripristinarlo o eliminarlo definitivamente\.$/,n=>n+' deleted note. Restore or permanently delete it.')||
  match(/^(\d+) appunti nel Cestino$/,n=>n+' notes in Trash')||
  match(/^(\d+) appunto nel Cestino$/,n=>n+' note in Trash')||
  match(/^(\d+) appunti$/,n=>n+' notes')||
  match(/^(\d+) appunto$/,n=>n+' note')||
  v;
}
function onfimTranslateTextNode(node){
 if(node.nodeType!==Node.TEXT_NODE||!node.parentElement||onfimSkipLocaleNode(node.parentElement))return;
 const raw=node.nodeValue;if(!raw.trim())return;
 let prev=onfimOriginalText.get(node);
 if(prev===undefined||(raw!==prev&&raw!==prev.replace(prev.trim(),onfimEnglishText(prev.trim())))){prev=raw;onfimOriginalText.set(node,raw);}
 const trimmed=prev.trim(),target=onfimLang==='en'?onfimEnglishText(trimmed):trimmed;
 const next=prev.replace(trimmed,target);
 if(next!==raw)node.nodeValue=next;
}
function onfimTranslateAttributes(el){
 if(el.nodeType!==1||onfimSkipLocaleNode(el))return;
 const attrs=['placeholder','title','aria-label'];let saved=onfimOriginalAttrs.get(el);
 if(!saved){saved={};onfimOriginalAttrs.set(el,saved);}
 for(const name of attrs){const raw=el.getAttribute(name);if(!raw)continue;
  if(!saved[name]||raw!==saved[name]&&raw!==ONFIM_UI_EN[saved[name]])saved[name]=raw;
  const next=onfimLang==='en'?(ONFIM_UI_EN[saved[name]]||saved[name]):saved[name];
  if(raw!==next)el.setAttribute(name,next);
 }
}
function onfimTranslateTree(root){
 if(root.nodeType===Node.TEXT_NODE){onfimTranslateTextNode(root);return;}
 if(root.nodeType!==Node.ELEMENT_NODE)return;
 if(root.matches('script,style'))return;
 onfimTranslateAttributes(root);
 const walker=document.createTreeWalker(root,NodeFilter.SHOW_ELEMENT|NodeFilter.SHOW_TEXT);
 while(walker.nextNode()){
  const node=walker.currentNode;if(node.nodeType===Node.TEXT_NODE)onfimTranslateTextNode(node);
  else if(!node.matches('script,style'))onfimTranslateAttributes(node);
 }
}
const onfimOriginalExtraTitle=onfimExtraTitle;
onfimExtraTitle=function(){
 if(onfimLang!=='en')return onfimOriginalExtraTitle();
 const t=onfimExtra.time,days=onfimExtra.days;
 return onfimExtra.mode==='daypart'?'Other time · '+t:onfimExtra.mode==='days'?'In '+days+' '+(days===1?'day':'days')+' · '+t:onfimExtra.mode==='weekday'?'Next '+['Sunday','Monday','Tuesday','Wednesday','Thursday','Friday','Saturday'][onfimExtra.weekday]+' · '+t:'';
};
function onfimApplyLanguage(){onfimLang=onfimLanguageCode();document.documentElement.lang=onfimLang;onfimExtraRefreshUI();onfimTranslateTree(document.body);}
$('onfimLanguage').value=localStorage.getItem(ONFIM_LANG_KEY)||'auto';
$('onfimLanguage').onchange=()=>{localStorage.setItem(ONFIM_LANG_KEY,$('onfimLanguage').value);onfimApplyLanguage();};
let onfimLocalizePending=false;
const onfimLocaleObserver=new MutationObserver(muts=>{
 if(onfimLocalizePending)return;
 if(!muts.some(m=>m.type==='childList'||m.type==='characterData'||m.type==='attributes'))return;
 onfimLocalizePending=true;
 queueMicrotask(()=>{onfimLocalizePending=false;if(onfimLang==='en')onfimTranslateTree(document.body);});
});
onfimLocaleObserver.observe(document.body,{childList:true,subtree:true,characterData:true});
onfimApplyLanguage();

})();
