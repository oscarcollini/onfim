
(()=>{'use strict';
const $=id=>document.getElementById(id);const DB='appunti-prototipo-v1',STORE='notes',SNAPSTORE='localSnapshots',VERSION='0.7.78.5 Lite';
const LAST_EXPORT_KEY='onfim-last-json-export-v06',LAST_CHANGE_KEY='onfim-last-data-change-v06',BACKUP_MAX_AGE_DAYS=7;let db=null,note=null,images=[],photoMarks=[],drawData='',drawn=false,pen='#202a34',erasing=false,painting=false,last=null,saveTimer=0,dirty=false,saving=Promise.resolve(),knownTags=[],unlocked=false,audioClips=[],recorder=null,audioFinalizing=false,micStream=null,audioPieces=[],audioTick=null,audioStarted=0,audioPausedAt=0,audioPauseTotal=0,readId=null,editorFrom='list',reminderTimers=new Map(),selectionRange=null,toastTimer=0;
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
function sanitizeHTML(markup){const tpl=document.createElement('template');tpl.innerHTML=String(markup||'');const allowed=new Set(['B','STRONG','I','EM','U','S','STRIKE','DEL','CODE','SPAN','FONT','P','DIV','BR','UL','OL','LI','BLOCKQUOTE']);function walk(parent){for(const el of [...parent.children]){if(['SCRIPT','STYLE','IFRAME','OBJECT','SVG','MATH','IMG','VIDEO','AUDIO','INPUT','FORM'].includes(el.tagName)){el.remove();continue;}walk(el);if(!allowed.has(el.tagName)){el.replaceWith(...el.childNodes);continue;}const oldColor=el.getAttribute('color')||el.style.color,oldBackground=el.style.backgroundColor;for(const attr of [...el.attributes])el.removeAttribute(attr.name);const safe=/^(#[0-9a-f]{3,8}|rgba?\([\d\s,.%]+\)|[a-z]{3,20})$/i;if(oldColor&&safe.test(oldColor))el.style.color=oldColor;if(oldBackground&&safe.test(oldBackground))el.style.backgroundColor=oldBackground;}}walk(tpl.content);return tpl.innerHTML;}
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
  $('searchToggle').classList.toggle('hidden',!home);
  $('settingsButton').classList.toggle('hidden',!home);
  window.scrollTo(0,0);
  if(id==='editView'&&$('drawTab').classList.contains('shown'))requestAnimationFrame(fitDrawingCanvas);
}
// Gli hashtag sono parte del testo: Unicode, senza distinzione fra maiuscole/minuscole.
// Le vecchie etichette restano leggibili e vengono trascritte nel testo quando la nota viene modificata.
function normalizedTag(v){return String(v||'').normalize('NFC').toLocaleLowerCase('it-IT');}
function extractHashtags(content){
  const text=String(content||'');
  const pattern=/(^|[^\p{L}\p{N}_])#([\p{L}\p{N}_]+(?:-[\p{L}\p{N}_]+)*)/gu;
  return [...new Set([...text.matchAll(pattern)].map(m=>normalizedTag(m[2])))];
}
function legacyTagSlug(t){return String(t||'').trim().normalize('NFC').replace(/^#+/,'').replace(/\s+/g,'_').replace(/[^\p{L}\p{N}_-]/gu,'').replace(/^-+|-+$/g,'').toLocaleLowerCase('it-IT');}
function noteTags(n){const raw=extractHashtags(txt(n.text||''));const old=(n.tags||[]).map(legacyTagSlug).filter(Boolean);return [...new Set([...raw,...old])];}
function htmlEscape(text){return String(text).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));}
function migratedText(n){
  const old=(n.tags||[]).map(legacyTagSlug).filter(Boolean);
  const have=new Set(extractHashtags(txt(n.text||'')));
  const missing=[...new Set(old)].filter(t=>!have.has(t));
  if(!missing.length)return n.text||'';
  const line=missing.map(t=>'#'+t).join(' ');
  return String(n.text||'')+'<p>'+htmlEscape(line)+'</p>';
}
async function showTags(){
  const notes=await allNotes();
  knownTags=[...new Set(notes.filter(n=>!n.deletedAt&&($('filter').value==='reserved'?n.reserved:!n.reserved)&&($('filter').value!=='favorites'||(groupRootFor(n,notes).favorite===true))&&(!n.reserved||unlocked)).flatMap(noteTags))].sort((a,b)=>a.localeCompare(b,'it'));
  const sel=$('tagFilter'),before=sel.value;sel.replaceChildren();sel.add(new Option('Tutti gli hashtag',''));
  for(const t of knownTags)sel.add(new Option('#'+t,t));
  sel.value=knownTags.includes(before)?before:'';
}
function previewAllowed(n){return !n.reserved||unlocked;}
async function renderNotes(){
  const all=await allNotes(),q=$('search').value.toLocaleLowerCase().trim(),tag=$('tagFilter').value,fil=$('filter').value,order=$('sortOrder').value;
  $('filterActiveDot').classList.toggle('hidden',!tag&&order==='updated-desc');
  $('homeHeading').textContent=fil==='reserved'?'Archivio 🔒':fil==='favorites'?'Preferiti ⭐':'I tuoi appunti';
  // Raggruppiamo PRIMA di filtrare: la ricerca in una parte deve trovare l'appunto composto.
  const groups=new Map();
  for(const n of all.filter(x=>!x.deletedAt&&(fil==='reserved'?!!x.reserved:!x.reserved))){
    const root=groupRootFor(n,all),key=root.id;
    if(!groups.has(key))groups.set(key,{root,parts:chainMembers(root,all)});
  }
  let a=[...groups.values()];
  if(fil==='favorites')a=a.filter(g=>g.root.favorite===true);
  a=a.filter(g=>!tag||g.parts.some(n=>noteTags(n).includes(tag)));
  a=a.filter(g=>!q||g.parts.some(n=>[n.title,txt(n.text),...noteTags(n)].join(' ').toLocaleLowerCase().includes(q)));
  function moment(g,which){return Math.max(...g.parts.map(n=>Number(n[which])||0));}
  a.sort((x,y)=>order==='created-desc'?moment(y,'created')-moment(x,'created'):order==='created-asc'?moment(x,'created')-moment(y,'created'):order==='updated-asc'?moment(x,'updated')-moment(y,'updated'):order==='title-asc'?(x.root.title||'').localeCompare(y.root.title||''):order==='title-desc'?(y.root.title||'').localeCompare(x.root.title||''):moment(y,'updated')-moment(x,'updated'));
  $('noteCount').textContent=a.length+' '+(a.length===1?'appunto':'appunti');
  const host=$('noteList');host.replaceChildren();
  if(!a.length){const empty=document.createElement('div');empty.className='empty';empty.innerHTML=fil==='reserved'?'<div class="empty-symbol">🔒</div><strong>Archivio vuoto</strong><span>Puoi spostare qui gli appunti dal menu ⋮.</span>':fil==='favorites'?'<div class="empty-symbol">⭐</div><strong>Nessun preferito</strong><span>Aggiungi una stella a un appunto dal menu ⋮.</span>':'<div class="empty-symbol">✎</div><strong>Nessun appunto</strong><span>Premi ＋ per crearne uno.</span>';host.append(empty);return;}
  const columns=[document.createElement('div'),document.createElement('div')];
  for(const col of columns){col.className='note-column';host.append(col);}
  for(let i=0;i<a.length;i++){
    const {root:n,parts}=a[i],allowed=previewAllowed(n),el=document.createElement('article'),count=parts.length;
    el.className='card';el.tabIndex=0;el.setAttribute('role','button');
    el.setAttribute('aria-label',allowed?'Leggi '+(n.title||'appunto senza titolo'):'Sblocca archivio');
    el.style.setProperty('--note-color',allowed?(n.color||'#fff'):'#e8ecef');
    const title=document.createElement('div');title.className='title';title.textContent=allowed?(n.title||'Senza titolo'):'🔒 Riservato';if(allowed&&n.favorite&&!n.reserved){const mark=document.createElement('span');mark.className='favorite-mark';mark.innerHTML=ONFIM_ICONS.star;mark.setAttribute('aria-label','Preferito');title.append(mark);}el.append(title);
    if(allowed&&count>1){const chain=document.createElement('div');chain.className='chain-summary';chain.textContent='▤ '+count+' parti collegate';el.append(chain);}
    const excerpt=document.createElement('div');excerpt.className='preview';
    const content=txt(n.text||'').trim();excerpt.textContent=allowed?(content||''):'Inserisci il PIN per leggere';
    if(excerpt.textContent)el.append(excerpt);
    if(allowed){
      const picSource=parts.find(p=>(p.photos||[]).some(s=>typeof s==='string'&&s.startsWith('data:image/'))||(typeof p.drawing==='string'&&p.drawing.startsWith('data:image/')))||n;
      const picture=(picSource.photos||[]).find(s=>typeof s==='string'&&s.startsWith('data:image/'))||(typeof picSource.drawing==='string'&&picSource.drawing.startsWith('data:image/')?picSource.drawing:'');
      if(picture){const thumb=document.createElement('img');thumb.className='cardthumb'+(picture===picSource.drawing?' drawing':'');thumb.src=picture;thumb.alt=picture===picSource.drawing?'Disegno':'Fotografia';thumb.loading='lazy';el.append(thumb);
        if(picture!==picSource.drawing&&picSource.photoMarks?.length){const index=(picSource.photos||[]).indexOf(picture),overlay=picSource.photoMarks[index];if(typeof overlay==='string'&&overlay.startsWith('data:image/')){const composite=document.createElement('canvas'),context=composite.getContext('2d');const source=new Image(),paint=new Image();source.onload=()=>{composite.width=source.naturalWidth;composite.height=source.naturalHeight;context.drawImage(source,0,0);paint.onload=()=>{context.drawImage(paint,0,0,composite.width,composite.height);thumb.src=composite.toDataURL('image/jpeg',0.83);};paint.src=overlay;};source.src=picture;}}}
    }
    const meta=document.createElement('div');meta.className='meta';
    if(n.reserved){const b=document.createElement('span');b.className='chip';b.textContent='🔒';b.title='Archivio';meta.append(b);}
    if(allowed){const uniqueTags=[...new Set(parts.flatMap(noteTags))];for(const t of uniqueTags.slice(0,3)){const c=document.createElement('span');c.className='chip';c.textContent='#'+t;meta.append(c);}if(parts.some(x=>x.reminder)){const r=document.createElement('span');r.className='chip';r.textContent='◷ Promemoria';meta.append(r);}const voiceCount=parts.reduce((sum,p)=>sum+(p.audios||[]).length,0);if(voiceCount){const voice=document.createElement('span');voice.className='chip';voice.textContent='🎙 '+voiceCount;meta.append(voice);}}
    if(meta.childNodes.length)el.append(meta);
    const menu=document.createElement('div');menu.className='card-menu';
    const quickReminder=document.createElement('button');
    quickReminder.type='button';quickReminder.className='card-quick-reminder';
    quickReminder.innerHTML='<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M18 8a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9"/><path d="M10 21h4"/></svg>';
    quickReminder.setAttribute('aria-label','Promemoria per '+(n.title||'appunto'));
    quickReminder.title='Promemoria';
    if(parts.some(x=>x.reminder||x.geofence?.enabled))quickReminder.classList.add('has-reminder');else quickReminder.classList.add('hidden');
    quickReminder.onclick=async e=>{e.stopPropagation();closeCardMenus();await openReminderFor(n,true);};
    const more=document.createElement('button');more.type='button';more.className='card-more';more.setAttribute('aria-label','Opzioni per '+(n.title||'appunto'));more.setAttribute('aria-expanded','false');more.innerHTML=ONFIM_ICONS.more;
    const popup=document.createElement('div');popup.className='card-popup hidden';
    const del=document.createElement('button');del.type='button';del.textContent=count>1?'Sposta appunto nel Cestino':'Sposta nel Cestino';del.className='danger';
    del.onclick=async(e)=>{e.stopPropagation();popup.classList.add('hidden');if(n.reserved&&!await checkPin())return;if(!confirmMoveToTrash(count))return;await safeDeleteNote(n);await reload();await scheduleReminders();toast('Spostato nel Cestino');};
    const move=document.createElement('button');move.type='button';move.textContent=n.reserved?'↩ Riporta negli appunti':'🔒 Sposta in Archivio';move.className='archive-option';
    move.onclick=async e=>{e.stopPropagation();popup.classList.add('hidden');if(!n.reserved&&!await checkPin())return;const now=Date.now(),updated=parts.map(p=>({...p,reserved:!n.reserved,updated:now}));await putNotesBatch(updated);await reload();toast(n.reserved?'Riportato negli appunti':'Spostato nell’Archivio');};
    if(!n.reserved){
      const star=document.createElement('button');star.type='button';star.innerHTML=ONFIM_ICONS.star+' '+(n.favorite?'Rimuovi dai Preferiti':'Aggiungi ai Preferiti');
      star.onclick=async e=>{e.stopPropagation();popup.classList.add('hidden');const fresh=(await allNotes()).find(x=>x.id===n.id);if(!fresh)return;await putNote({...fresh,favorite:!fresh.favorite,updated:Date.now()});await reload();toast(fresh.favorite?'Rimosso dai Preferiti':'Aggiunto ai Preferiti');};
      popup.append(star);
    }
    const remindAction=document.createElement('button');remindAction.type='button';remindAction.textContent='Promemoria';remindAction.onclick=async e=>{e.stopPropagation();closeCardMenus();if(n.reserved&&!unlocked&&!await checkPin())return;await openReminderFor(n,true);};
    const partAction=document.createElement('button');partAction.type='button';partAction.textContent='＋ Aggiungi parte';partAction.onclick=async e=>{e.stopPropagation();closeCardMenus();if(n.reserved&&!unlocked&&!await checkPin())return;onfimAskPartFromCard(n.id);};
    popup.append(remindAction,partAction,move,del);menu.append(quickReminder,more,popup);el.append(menu);
    more.onclick=e=>{e.stopPropagation();const wasOpen=!popup.classList.contains('hidden');closeCardMenus();if(!wasOpen){popup.classList.remove('hidden');el.classList.add('menu-open');more.setAttribute('aria-expanded','true');}};
    const open=async()=>{if(n.reserved&&!await checkPin())return;await openRead(n);};
    el.addEventListener('click',e=>{if(e.target.closest('button'))return;void open();});
    el.addEventListener('keydown',e=>{if(e.target===el&&(e.key==='Enter'||e.key===' ')){e.preventDefault();void open();}});
    columns[i%2].append(el);
  }
}

function emptyNote(){return{id:uid(),title:'',text:'',color:'#ffffff',tags:[],reminder:'',reminderRepeat:'none',reserved:false,favorite:false,photos:[],photoMarks:[],drawing:'',audios:[],linkedFiles:[],created:Date.now(),updated:Date.now()};}
function hasContent(n){return !!(n.title.trim()||txt(n.text).trim()||(n.photos||[]).length||n.drawing||(n.audios||[]).length||(n.linkedFiles||[]).length);}
function markDirty(){dirty=true;$('saveState').textContent='Modifiche non salvate';clearTimeout(saveTimer);}
function snapshot(){return{...note,title:$('noteTitle').value.trim(),text:sanitizeHTML($('noteBody').innerHTML),color:$('noteColor').value,tags:extractHashtags(txt($('noteBody').innerHTML)),reminder:$('reminder').value,reserved:$('reserved').checked,photos:[...images],photoMarks:[...photoMarks],drawing:drawn?$('drawCanvas').toDataURL('image/png'):drawData,audios:[...audioClips],linkedFiles:[...onfimEditorLinks],updated:Date.now()};}
function flushSave(){clearTimeout(saveTimer);if(!dirty||!note)return saving;const snap=snapshot();if(!hasContent(snap)){dirty=false;$('saveState').textContent='';return saving;}dirty=false;$('saveState').textContent='Salvataggio…';saving=saving.catch(()=>{}).then(async()=>{try{await putNote(snap);{const allSaved=await allNotes(),rootId=chainRootOf(snap);const related=allSaved.filter(x=>!x.deletedAt&&(x.id===rootId||x.chainRoot===rootId)&&x.id!==snap.id&&x.reserved!==snap.reserved);if(related.length)await putNotesBatch(related.map(x=>({...x,reserved:snap.reserved,updated:Date.now()})));}note=snap;$('editorDates').textContent=noteDates(snap);if(snap.reserved&&unlocked&&$('filter').value!=='reserved'){$('filter').value='reserved';syncFilterPills();}else if(!snap.reserved&&$('filter').value==='reserved'){$('filter').value='ordinary';unlocked=false;syncFilterPills();}$('saveState').textContent='Salvato';$('deleteNote').classList.remove('hidden');await showTags();scheduleReminders();}catch(e){dirty=true;$('saveState').textContent='Errore: '+(e.name||'salvataggio')+' — '+(e.message||'');}});return saving;}
async function leaveEditor(){
  if(isRecording()){toast('Ferma la registrazione prima di uscire.');chooseTab('audio');return;}
  // Chiudi = annulla, anche per foto, disegni, allegati audio e nuove note.
  // Attende un eventuale Salva già in corso, senza avviare altre scritture.
  await saving.catch(()=>{});
  if(dirty&&!confirm('Scartare le modifiche non salvate e chiudere l’appunto?'))return;
  clearTimeout(saveTimer);
  dirty=false;
  $('saveState').textContent='';
  note=null;
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
function isRecording(){return audioFinalizing||(!!recorder&&recorder.state!=='inactive');}
function clockString(ms){const sec=Math.floor(Math.max(0,ms)/1000);return String(Math.floor(sec/60)).padStart(2,'0')+':'+String(sec%60).padStart(2,'0');}
function recordingUI(){const live=!!recorder&&recorder.state!=='inactive';$('audioRecord').disabled=isRecording();$('audioPause').disabled=!live;$('audioStop').disabled=!live;$('audioPause').textContent=live&&recorder.state==='paused'?'Riprendi':'Pausa';$('audioRecord').textContent=audioFinalizing?'Elaborazione…':(live?'● In registrazione':'● Registra');}
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
function renderAudioGallery(){const list=$('audioGallery');list.replaceChildren();for(const clip of audioClips)list.append(buildAudioItem(clip));$('audioCount').textContent=audioClips.length?String(audioClips.length):'';$('tabAudio').setAttribute('aria-label',audioClips.length?'Audio, '+audioClips.length+' allegati':'Audio');}
async function startAudioRecording(){
 if(isRecording())return;
 if(!navigator.mediaDevices?.getUserMedia||!window.MediaRecorder){$('audioStatus').textContent='Registrazione non supportata in questo contesto: prova nella PWA HTTPS.';return;}
 try{
  micStream=await navigator.mediaDevices.getUserMedia({audio:true});
  const choices=['audio/webm;codecs=opus','audio/mp4','audio/webm'];
  const mime=choices.find(t=>MediaRecorder.isTypeSupported?.(t))||'';
  recorder=new MediaRecorder(micStream,mime?{mimeType:mime}:undefined);
  audioPieces=[];audioStarted=performance.now();audioPauseTotal=0;audioPausedAt=0;
  const ownRecorder=recorder;
  recorder.ondataavailable=e=>{if(e.data?.size)audioPieces.push(e.data);const total=audioPieces.reduce((s,b)=>s+b.size,0);if(total>MAX_AUDIO_BYTES&&ownRecorder.state!=='inactive'){$('audioStatus').textContent='Limite 10 MB raggiunto: registrazione interrotta.';ownRecorder.stop();}};
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
  recorder.start(850);$('audioStatus').textContent='Registrazione in corso…';$('audioClock').textContent='00:00';audioTick=setInterval(tickAudio,500);recordingUI();
 }catch(e){stopMic();recorder=null;recordingUI();$('audioStatus').textContent='Microfono non disponibile: '+(e.name==='NotAllowedError'?'permesso negato':e.message);}
}
async function importAudioFiles(files){for(const f of files){if(!f.type.startsWith('audio/'))continue;if(f.size>MAX_AUDIO_BYTES){toast('Audio troppo grande (limite 10 MB): '+f.name);continue;}try{const data=await fileAsDataURL(f);audioClips.push({id:uid(),name:f.name||'Audio allegato',data,created:Date.now()});markDirty();}catch(e){toast('Errore audio: '+e.message);}}renderAudioGallery();}
function photoList(){const host=$('photoGallery');host.replaceChildren();$('photoCount').textContent=images.length?String(images.length):'';$('tabPhotos').setAttribute('aria-label',images.length?'Foto, '+images.length+' allegate':'Foto');images.forEach((src,i)=>{const card=document.createElement('div');card.className='photo';const img=document.createElement('img');img.src=src;img.alt='Foto allegata';const del=document.createElement('button');del.type='button';del.className='remove-photo';del.textContent='×';del.title='Rimuovi foto';del.onclick=()=>{images.splice(i,1);photoMarks.splice(i,1);photoList();markDirty();};const edit=document.createElement('button');edit.type='button';edit.className='edit-photo';edit.innerHTML='<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><path d="M12 20h9"/><path d="M16.5 3.5a2.12 2.12 0 0 1 3 3L7 19l-4 1 1-4Z"/></svg>';edit.setAttribute('aria-label','Modifica segni sulla fotografia');edit.title='Modifica segni';edit.onclick=()=>openPhotoMarkup(i);card.append(img);if(photoMarks[i]){const mark=document.createElement('img');mark.src=photoMarks[i];mark.className='photo-mark-preview';mark.alt='';card.append(mark);}card.append(del,edit);host.append(card);});}
function editNote(n,allowPart=true){$('addPartEditor').classList.toggle('hidden',!allowPart);$('noteTitle').placeholder='Titolo (facoltativo)';clearTimeout(saveTimer);dirty=false;note={...n};images=[...(n.photos||[])];photoMarks=Array.isArray(n.photoMarks)?images.map((_,i)=>typeof n.photoMarks[i]==='string'?n.photoMarks[i]:''):images.map(()=>'');$('noteTitle').value=n.title||'';$('editorDates').textContent=noteDates(n);$('noteBody').innerHTML=sanitizeHTML(migratedText(n));selectionRange=null;lastHighlightAction=null;resetTextHistory();const colorSelect=$('noteColor');colorSelect.querySelector('[data-legacy-color]')?.remove();if(n.color&&![...colorSelect.options].some(o=>o.value===n.color)){const o=new Option('Colore precedente',n.color);o.dataset.legacyColor='1';colorSelect.add(o);}colorSelect.value=n.color||'#ffffff';updateNoteColorButton();$('reminder').value=n.reminder||'';$('reserved').checked=!!n.reserved;audioClips=Array.isArray(n.audios)?n.audios.filter(a=>a&&typeof a.data==='string'&&a.data.startsWith('data:audio/')):[];onfimEditorLinks=Array.isArray(n.linkedFiles)?n.linkedFiles.map(f=>({...f})):[];onfimRenderEditorLinks();renderAudioGallery();$('saveState').textContent='';$('deleteNote').classList.toggle('hidden',!n.title&&!n.text&&!(n.photos||[]).length&&!n.drawing&&!(n.audios||[]).length&&!n.persisted);photoList();showDrawing(n.drawing||'');updateTextMark();chooseTab('text');updateFormat();view('editView');}
function newNote(){editorFrom='list';const n=emptyNote();n.reserved=$('filter').value==='reserved'&&unlocked;n.favorite=$('filter').value==='favorites';editNote(n,false);$('deleteNote').classList.add('hidden');$('noteTitle').focus();}
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
  $('readBody').innerHTML=content;
  $('readBody').classList.toggle('read-empty',!txt(content).trim());
  if(!txt(content).trim())$('readBody').textContent=(n.drawing||(n.photos||[]).length||(n.audios||[]).length)?'':'Appunto vuoto';
  const goodData=s=>typeof s==='string'&&s.startsWith('data:image/');
  $('readDrawWrap').classList.toggle('hidden',!goodData(n.drawing));
  if(goodData(n.drawing))$('readDrawing').src=n.drawing;else $('readDrawing').removeAttribute('src');
  const gallery=$('readPhotos');gallery.replaceChildren();
  for(const [idx,src] of (n.photos||[]).entries()){if(!goodData(src))continue;const wrapper=document.createElement('div');wrapper.className='annotated-photo';const img=document.createElement('img');img.src=src;img.alt='Foto allegata';wrapper.append(img);const overlay=n.photoMarks?.[idx];if(goodData(overlay)){const mark=document.createElement('img');mark.src=overlay;mark.className='annotation-overlay';mark.alt='';wrapper.append(mark);}gallery.append(wrapper);}
  $('readPhotoWrap').classList.toggle('hidden',!gallery.children.length);
  const audios=$('readAudios');audios.replaceChildren();
  for(const a of n.audios||[]){if(a&&typeof a.data==='string'&&a.data.startsWith('data:audio/'))audios.append(buildAudioItem(a,false));}
  $('readAudioWrap').classList.toggle('hidden',!audios.children.length);
  $('readNote').querySelectorAll('.root-linked-files').forEach(x=>x.remove());
  if(parts.length===1&&(n.linkedFiles||[]).length){const wrap=document.createElement('div');wrap.className='root-linked-files';onfimRenderFileRefs(n,wrap);$('readMeta').before(wrap);}
  const meta=$('readMeta');meta.replaceChildren();
  const addChip=s=>{const span=document.createElement('span');span.className='chip';span.textContent=s;meta.append(span);};
  if(n.reserved)addChip('🔒 Archivio');
  for(const tag of noteTags(n))addChip('#'+tag);
  if(n.reminder){const when=new Date(n.reminder);if(!Number.isNaN(when.getTime()))addChip('⏰ '+when.toLocaleString('it-IT'));}
  if(parts.length>1){for(const [i,part] of parts.entries()){
    const block=makeChainPart(part,i+1);if(i===parts.length-1)block.querySelector('.chain-options button:last-child')?.remove();
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
  $('readArchiveOption').querySelector('span').textContent=n.reserved?'Rimuovi dall’Archivio':'Sposta in Archivio';$('readReminderOption').querySelector('span').textContent=n.reminder||n.geofence?.enabled?'Modifica promemoria':'Promemoria';
  $('readDetachOption').classList.toggle('hidden',parts.length<=1);
  $('readDeleteOption').querySelector('span').textContent=parts.length>1?'Sposta appunto nel Cestino':'Sposta nel Cestino';
  $('readEditTop').title=parts.length>1?'Modifica prima parte':'Modifica';
  $('readEditTop').setAttribute('aria-label',parts.length>1?'Modifica prima parte':'Modifica');
  closeReadMenu();
  $('backRead').textContent=$('readBackBottom').textContent=n.reserved?'← Archivio':'← Appunti';
  view('readView');
}
// La lettura concatenata usa gli stessi contenuti salvati delle note semplici.
// Ogni parte e' ancora modificabile indipendentemente nell'editor normale.
const ONFIM_ICONS={pencil:'<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><path d="M12 20h9"/><path d="M16.5 3.5a2.12 2.12 0 0 1 3 3L7 19l-4 1 1-4Z"/></svg>',more:'<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="5" r="1"/><circle cx="12" cy="12" r="1"/><circle cx="12" cy="19" r="1"/></svg>',star:'<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.85" stroke-linecap="round" stroke-linejoin="round"><path d="m12 2 3.1 6.3 6.9 1-5 4.9 1.2 6.8-6.2-3.3-6.2 3.3 1.2-6.8-5-4.9 6.9-1Z"/></svg>'};
function makeChainPart(n,number){
  const block=document.createElement('section');block.className='chain-part';
  const head=document.createElement('div');head.className='chain-part-head';
  const label=document.createElement('span');label.className='chain-part-label';
  const kind=txt(n.text||'').trim()?'Testo':(n.photos||[]).length?'Foto':n.drawing?'Disegno':(n.audios||[]).length?'Audio':'Appunto';
  label.textContent=number+' · '+kind;
  const actions=document.createElement('div');actions.className='chain-part-actions';
  const edit=document.createElement('button');edit.type='button';edit.innerHTML=ONFIM_ICONS.pencil;edit.title='Modifica parte '+number;edit.classList.add('icon-button','part-edit');edit.setAttribute('aria-label','Modifica parte '+number);
  edit.onclick=async()=>{const fresh=(await allNotes()).find(x=>x.id===n.id);if(!fresh){toast('Parte non trovata');return;}if(fresh.reserved&&!unlocked&&!await checkPin())return;editorFrom='read';editNote(fresh);};
  actions.append(edit);
  const optionsHost=document.createElement('div');optionsHost.className='chain-options-host';
  const more=document.createElement('button');more.className='icon-button';more.type='button';more.innerHTML='<svg class="oi" aria-hidden="true" viewBox="0 0 24 24" width="19" height="19" fill="currentColor"><circle cx="12" cy="5" r="1.6"/><circle cx="12" cy="12" r="1.6"/><circle cx="12" cy="19" r="1.6"/></svg>';more.title='Opzioni parte';more.setAttribute('aria-label','Opzioni parte '+number);
  const popup=document.createElement('div');popup.className='chain-options hidden';
  const moveUp=document.createElement('button');moveUp.type='button';moveUp.textContent='↑ Sposta su';
  const moveDown=document.createElement('button');moveDown.type='button';moveDown.textContent='↓ Sposta giù';
  if(number>2)popup.append(moveUp); // Parte 1 resta la radice stabile
  // Inserita da openRead dopo aver conosciuto la lunghezza della sequenza.
  popup.append(moveDown);
  moveUp.onclick=e=>{e.stopPropagation();onfimClosePartMenus();void onfimMovePart(n.id,-1);};
  moveDown.onclick=e=>{e.stopPropagation();onfimClosePartMenus();void onfimMovePart(n.id,+1);};
  more.onclick=e=>{e.stopPropagation();const hidden=popup.classList.contains('hidden');onfimClosePartMenus();popup.classList.toggle('hidden',!hidden);};
  optionsHost.append(more,popup);actions.append(optionsHost);
  if(number===1)optionsHost.classList.add('hidden');
  head.append(label,actions);block.append(head);
  if(number>1&&n.title){const title=document.createElement('h2');title.className='chain-part-title';title.textContent=n.title;block.append(title);}
  const markup=sanitizeHTML(migratedText(n));
  if(txt(markup).trim()){const body=document.createElement('div');body.className='read-body';body.innerHTML=markup;block.append(body);}
  if(typeof n.drawing==='string'&&n.drawing.startsWith('data:image/')){const wrap=document.createElement('div');wrap.className='read-media';const h=document.createElement('h2');h.textContent='Disegno';const img=document.createElement('img');img.className='read-drawing';img.src=n.drawing;img.alt='Disegno della parte '+number;wrap.append(h,img);block.append(wrap);}
  const photos=(n.photos||[]).filter(src=>typeof src==='string'&&src.startsWith('data:image/'));
  if(photos.length){const wrap=document.createElement('div');wrap.className='read-media';const h=document.createElement('h2');h.textContent='Foto';const gallery=document.createElement('div');gallery.className='read-photos';
    for(const [idx,src] of (n.photos||[]).entries()){if(typeof src!=='string'||!src.startsWith('data:image/'))continue;const container=document.createElement('div');container.className='annotated-photo';const img=document.createElement('img');img.src=src;img.alt='Fotografia allegata';container.append(img);const mask=n.photoMarks?.[idx];if(typeof mask==='string'&&mask.startsWith('data:image/')){const layer=document.createElement('img');layer.src=mask;layer.className='annotation-overlay';layer.alt='';container.append(layer);}gallery.append(container);}
    wrap.append(h,gallery);block.append(wrap);
  }
  if((n.audios||[]).length){const wrap=document.createElement('div');wrap.className='read-media';const h=document.createElement('h2');h.textContent='Registrazioni vocali';wrap.append(h);for(const a of n.audios){if(a&&typeof a.data==='string'&&a.data.startsWith('data:audio/'))wrap.append(buildAudioItem(a,false));}block.append(wrap);}
  onfimRenderFileRefs(n,block);
  if((n.reminder||noteTags(n).length)){const footer=document.createElement('div');footer.className='read-footer';for(const t of noteTags(n)){const c=document.createElement('span');c.className='chip';c.textContent='#'+t;footer.append(c);}if(n.reminder){const c=document.createElement('span');c.className='chip';c.textContent='◷ '+new Date(n.reminder).toLocaleString('it-IT');footer.append(c);}block.append(footer);}
  return block;
}

async function showSavedRead(){
  // Invocata soltanto dopo un salvataggio confermato, non da Chiudi.
  if(dirty){alert('Ci sono modifiche non salvate. Premi Salva.');return;}
  if(!note||!hasContent(note)){if(editorFrom==='read'&&readId){const root=(await allNotes()).find(n=>n.id===readId);if(root){await openRead(root);return;}}await reload();view('listView');return;}
  const current=(await allNotes()).find(n=>n.id===note.id);
  if(current)await openRead(current);else{await reload();view('listView');}
}

function chooseTab(name){
  if(name!=='draw'&&$('drawTab').classList.contains('expanded'))$('closeExpanded').click();
  for(const t of ['text','draw','photos','audio']){
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
function insertJournalTimestamp(){
  const now=new Date();
  const stamp=new Intl.DateTimeFormat('it-IT',{day:'2-digit',month:'2-digit',year:'numeric',hour:'2-digit',minute:'2-digit',hour12:false}).format(now).replace(',', ' ·');
  restoreRange();
  const sel=window.getSelection(),range=sel&&sel.rangeCount?sel.getRangeAt(0):null;
  const before=range&&$('noteBody').contains(range.startContainer)?range.cloneRange():null;
  if(before){before.selectNodeContents($('noteBody'));before.setEnd(range.startContainer,range.startOffset);}
  const prefix=before&&before.toString()&&!before.toString().endsWith(String.fromCharCode(10))?String.fromCharCode(10):'';
  const value=prefix+stamp+' — ';if(!document.execCommand('insertText',false,value)){const r=range&&$('noteBody').contains(range.commonAncestorContainer)?range:document.createRange();if(r!==range){r.selectNodeContents($('noteBody'));r.collapse(false);}r.deleteContents();const node=document.createTextNode(value);r.insertNode(node);r.setStartAfter(node);r.collapse(true);sel.removeAllRanges();sel.addRange(r);}
  rememberRange();markDirty();recordTextHistory(true);updateTextMark();
}
$('insertJournalStamp').addEventListener('pointerdown',e=>e.preventDefault());
$('insertJournalStamp').onclick=insertJournalTimestamp;
function applyCommand(command,value=null){restoreRange();document.execCommand(command,false,value);rememberRange();updateFormat();markDirty();recordTextHistory(true);updateTextMark();}
function updateTextUndoUI(){$('textUndo').disabled=textHistoryAt<=0;$('textRedo').disabled=textHistoryAt>=textHistory.length-1;}
function resetTextHistory(){clearTimeout(textHistoryTimer);textHistory=[$('noteBody').innerHTML];textHistoryAt=0;updateTextUndoUI();}
function recordTextHistory(immediate=false){clearTimeout(textHistoryTimer);if(!immediate){textHistoryTimer=setTimeout(()=>recordTextHistory(true),420);return;}const html=$('noteBody').innerHTML;if(textHistory[textHistoryAt]===html)return;textHistory=textHistory.slice(0,textHistoryAt+1);textHistory.push(html);if(textHistory.length>60)textHistory.shift();textHistoryAt=textHistory.length-1;updateTextUndoUI();}
function textUndoOrRedo(direction){clearTimeout(textHistoryTimer);recordTextHistory(true);const next=textHistoryAt+direction;if(next<0||next>=textHistory.length)return;textHistoryAt=next;const el=$('noteBody');el.innerHTML=textHistory[textHistoryAt];el.focus();const sel=window.getSelection(),range=document.createRange();range.selectNodeContents(el);range.collapse(false);sel.removeAllRanges();sel.addRange(range);rememberRange();updateTextUndoUI();updateFormat();markDirty();updateTextMark();}
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
canvas.addEventListener('pointerdown',e=>{e.preventDefault();saveDrawUndo();painting=true;last=point(e);canvas.setPointerCapture(e.pointerId);ctx.strokeStyle=erasing?'#ffffff':pen;ctx.lineWidth=Number($('penSize').value)*(erasing?4:1);ctx.beginPath();ctx.arc(last.x,last.y,ctx.lineWidth/2,0,Math.PI*2);ctx.fillStyle=ctx.strokeStyle;ctx.fill();});
canvas.addEventListener('pointermove',e=>{if(!painting)return;e.preventDefault();const p=point(e);ctx.strokeStyle=erasing?'#ffffff':pen;ctx.lineWidth=Number($('penSize').value)*(erasing?4:1);ctx.beginPath();ctx.moveTo(last.x,last.y);ctx.lineTo(p.x,p.y);ctx.stroke();last=p;});
function finishStroke(){if(!painting)return;painting=false;last=null;drawn=true;updateDrawingMark();markDirty();}canvas.addEventListener('pointerup',finishStroke);canvas.addEventListener('pointercancel',finishStroke);
function penMode(eraser){erasing=eraser;$('penButton').classList.toggle('active',!eraser);$('eraserButton').classList.toggle('active',eraser);$('penButton').setAttribute('aria-pressed',String(!eraser));$('eraserButton').setAttribute('aria-pressed',String(eraser));}

// Annotazioni foto: un PNG trasparente separato conserva sempre l'immagine originale.
let activePhotoMark=-1,markPainting=false,markLast=null,markErase=false,markColor='#ce292f',markUndo=[],markRedo=[],markGeneration=0;
const markCanvas=$('photoMarkCanvas'),markCtx=markCanvas.getContext('2d');
function photoMarkButtons(){$('photoMarkUndo').disabled=!markUndo.length;$('photoMarkRedo').disabled=!markRedo.length;}
function markSnapshot(){return markCanvas.toDataURL('image/png');}
function pushPhotoMark(){markUndo.push(markSnapshot());if(markUndo.length>15)markUndo.shift();markRedo=[];photoMarkButtons();}
function loadMarkSnapshot(src){const token=++markGeneration,img=new Image();img.onload=()=>{if(token!==markGeneration)return;markCtx.clearRect(0,0,markCanvas.width,markCanvas.height);markCtx.drawImage(img,0,0,markCanvas.width,markCanvas.height);};img.src=src;}
function historyPhotoMark(direction){const src=direction===-1?markUndo:markRedo,dst=direction===-1?markRedo:markUndo;if(!src.length)return;dst.push(markSnapshot());loadMarkSnapshot(src.pop());photoMarkButtons();}
function markMode(erase){markErase=erase;$('photoMarkPen').classList.toggle('active',!erase);$('photoMarkEraser').classList.toggle('active',erase);}
function closePhotoMarkup(){$('photoMarkDialog').close();document.body.classList.remove('annotating');activePhotoMark=-1;}
function openPhotoMarkup(i){if(!images[i])return;activePhotoMark=i;const img=new Image();const src=images[i],old=photoMarks[i]||'';img.onload=()=>{if(activePhotoMark!==i)return;const w=img.naturalWidth,h=img.naturalHeight;markCanvas.width=w;markCanvas.height=h;$('photoMarkBase').src=src;$('photoMarkSurface').style.aspectRatio=w+' / '+h;markCtx.clearRect(0,0,w,h);markUndo=[];markRedo=[];photoMarkButtons();markMode(false);markColor='#ce292f';document.querySelectorAll('[data-mark]').forEach(b=>b.classList.toggle('selected',b.dataset.mark===markColor));if(old)loadMarkSnapshot(old);$('photoMarkDialog').showModal();document.body.classList.add('annotating');};img.src=src;}
function markPoint(e){const box=markCanvas.getBoundingClientRect();return{x:(e.clientX-box.left)/box.width*markCanvas.width,y:(e.clientY-box.top)/box.height*markCanvas.height};}
markCanvas.addEventListener('pointerdown',e=>{if(activePhotoMark<0)return;e.preventDefault();pushPhotoMark();markPainting=true;markLast=markPoint(e);markCanvas.setPointerCapture(e.pointerId);const ctx=markCtx;ctx.save();ctx.globalCompositeOperation=markErase?'destination-out':'source-over';ctx.fillStyle=markErase?'rgba(0,0,0,1)':markColor;const radius=Number($('photoMarkSize').value)*(markErase?4:1)/2;ctx.beginPath();ctx.arc(markLast.x,markLast.y,radius,0,Math.PI*2);ctx.fill();ctx.restore();});
markCanvas.addEventListener('pointermove',e=>{if(!markPainting)return;e.preventDefault();const p=markPoint(e);markCtx.save();markCtx.globalCompositeOperation=markErase?'destination-out':'source-over';markCtx.strokeStyle=markErase?'rgba(0,0,0,1)':markColor;markCtx.lineWidth=Number($('photoMarkSize').value)*(markErase?4:1);markCtx.lineCap='round';markCtx.lineJoin='round';markCtx.beginPath();markCtx.moveTo(markLast.x,markLast.y);markCtx.lineTo(p.x,p.y);markCtx.stroke();markCtx.restore();markLast=p;});
function finishPhotoMark(){markPainting=false;markLast=null;}
markCanvas.addEventListener('pointerup',finishPhotoMark);markCanvas.addEventListener('pointercancel',finishPhotoMark);
$('photoMarkPen').onclick=()=>markMode(false);$('photoMarkEraser').onclick=()=>markMode(true);$('photoMarkUndo').onclick=()=>historyPhotoMark(-1);$('photoMarkRedo').onclick=()=>historyPhotoMark(1);
for(const b of document.querySelectorAll('[data-mark]'))b.onclick=()=>{markColor=b.dataset.mark;markMode(false);document.querySelectorAll('[data-mark]').forEach(x=>x.classList.toggle('selected',x===b));};
$('photoMarkCustom').onclick=()=>openOnfimColorPicker('photo');
$('photoMarkClose').onclick=$('photoMarkCancel').onclick=closePhotoMarkup;
$('photoMarkDialog').addEventListener('cancel',e=>{e.preventDefault();closePhotoMarkup();});
$('photoMarkSave').onclick=()=>{if(activePhotoMark<0)return;photoMarks[activePhotoMark]=markSnapshot();closePhotoMarkup();photoList();markDirty();};
function resizePhoto(f){return new Promise((res,rej)=>{const url=URL.createObjectURL(f),im=new Image();im.onload=()=>{URL.revokeObjectURL(url);const scale=Math.min(1,1600/Math.max(im.width,im.height));const c=document.createElement('canvas');c.width=Math.max(1,Math.round(im.width*scale));c.height=Math.max(1,Math.round(im.height*scale));const x=c.getContext('2d');x.fillStyle='white';x.fillRect(0,0,c.width,c.height);x.drawImage(im,0,0,c.width,c.height);res(c.toDataURL('image/jpeg',.8));};im.onerror=()=>{URL.revokeObjectURL(url);rej(new Error('Formato immagine non supportato.'));};im.src=url;});}
async function readPhotos(list){for(const file of [...list]){if(!file.type.startsWith('image/'))continue;try{images.push(await resizePhoto(file));photoMarks.push('');}catch(e){toast('Foto non importata: '+e.message);}}photoList();markDirty();}
function recordDataChange(){try{localStorage.setItem(LAST_CHANGE_KEY,String(Date.now()));}catch(e){console.warn('Onfim: impossibile registrare data modifica',e);}void refreshBackupStatus();scheduleLocalSnapshot();}
function backupState(notes){
  const lastExport=Number(localStorage.getItem(LAST_EXPORT_KEY))||0;
  const marker=Number(localStorage.getItem(LAST_CHANGE_KEY))||0;
  const latestChange=Math.max(marker,...notes.map(n=>Number(n.updated)||Number(n.created)||0),0);
  const format=t=>new Date(t).toLocaleString('it-IT',{day:'2-digit',month:'2-digit',year:'numeric',hour:'2-digit',minute:'2-digit'});
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
function pinDialog(mode){return new Promise(resolve=>{const d=$('pinDialog'),form=$('pinForm');$('pinHeading').textContent=mode==='new'?'Imposta un PIN':'Inserisci il PIN';$('pinMessage').textContent=mode==='new'?'Protezione leggera contro gli sguardi indiscreti.':'Sblocca gli appunti riservati.';$('confirmPinWrap').classList.toggle('hidden',mode!=='new');$('pinEntry').value='';$('pinConfirm').value='';$('pinError').textContent='';$('pinConfirm').required=mode==='new';const done=v=>{form.onsubmit=null;$('pinCancel').onclick=null;d.oncancel=null;d.close();resolve(v);};form.onsubmit=e=>{e.preventDefault();const a=$('pinEntry').value;if(!a){$('pinError').textContent='Inserisci un PIN.';return;}if(mode==='new'){if(a!==$('pinConfirm').value){$('pinError').textContent='I due PIN non coincidono.';return;}localStorage.setItem('onfim-pin',a);unlocked=true;done(true);}else if(a===pinStored()){unlocked=true;done(true);}else{$('pinError').textContent='PIN errato.';}};$('pinCancel').onclick=()=>done(false);d.oncancel=e=>{e.preventDefault();done(false);};d.showModal();$('pinEntry').focus();});}
async function checkPin(){if(unlocked)return true;return pinDialog(pinStored()?'unlock':'new');}
function download(content,filename,type){const blob=content instanceof Blob?content:new Blob([content],{type});const url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download=filename;document.body.append(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),4000);}
// Nome breve in ora locale; la data completa resta nel contenuto JSON.
function manualBackupFilename(now){
  const p=n=>String(n).padStart(2,'0');
  return 'onfim_'+now.getFullYear()+p(now.getMonth()+1)+p(now.getDate())+'_'+p(now.getHours())+p(now.getMinutes())+'.json';
}
async function exportJSON(){try{
  if(dirty)throw new Error('Ci sono modifiche non salvate: salva l’appunto prima di esportare.');
  const notes=await allNotes(),now=new Date();
  const payload={format:'appunti-backup',version:2,app:'Onfim',exportedAt:now.toISOString(),notes};
  download(JSON.stringify(payload,null,2),manualBackupFilename(now),'application/json');
  try{localStorage.setItem(LAST_EXPORT_KEY,String(now.getTime()));}catch(e){console.warn('Onfim: data esportazione non registrata',e);}
  await refreshBackupStatus();
  $('settingsStatus').textContent='Download avviato. Verifica che il file JSON sia stato effettivamente salvato sul dispositivo o su Drive.';
}catch(e){$('settingsStatus').textContent='Errore nell’esportazione: '+e.message;}}
async function importJSON(file){try{const data=JSON.parse(await file.text());if(!Array.isArray(data.notes)|| !['appunti-backup','onfim-backup'].includes(data.format))throw new Error('Formato JSON non riconosciuto.');if(!confirm('Importare '+data.notes.length+' appunti? Gli ID già presenti saranno aggiornati; gli altri verranno aggiunti.'))return;if(dirty)throw new Error('Prima salva o chiudi l’appunto in modifica.');const existing=await allNotes();if(existing.length&&!await makeLocalSnapshot('prima-importazione',true))throw new Error('Non è stato possibile creare una copia preventiva: esporta un JSON e riprova.');let count=0;const imported=[];for(const n of data.notes){if(!n?.id||typeof n!=='object')continue;const cleaned={id:String(n.id),title:String(n.title||''),text:sanitizeHTML(n.text),color:String(n.color||'#ffffff'),tags:Array.isArray(n.tags)?n.tags.map(String):[],photos:Array.isArray(n.photos)?n.photos.filter(s=>typeof s==='string'&&s.startsWith('data:image/')):[],photoMarks:Array.isArray(n.photoMarks)?n.photoMarks.map(s=>typeof s==='string'&&(s===''||s.startsWith('data:image/'))?s:''):[],drawing:typeof n.drawing==='string'&&n.drawing.startsWith('data:image/')?n.drawing:'',reminder:String(n.reminder||''),reminderRepeat:['none','daily','weekly','monthly','weekday','monday','tuesday','wednesday','thursday','friday','saturday','sunday'].includes(n.reminderRepeat)?n.reminderRepeat:'none',reminderBase:typeof n.reminderBase==='string'?n.reminderBase:String(n.reminder||''),geofence:cleanGeofence(n.geofence),reserved:!!n.reserved,favorite:!!n.favorite,created:Number(n.created)||Date.now(),updated:Number(n.updated)||Date.now(),audios:Array.isArray(n.audios)?n.audios.filter(a=>a&&typeof a.data==='string'&&a.data.startsWith('data:audio/')&&a.data.length<=Math.ceil(MAX_AUDIO_BYTES*1.4)).map(a=>({id:String(a.id||uid()),name:String(a.name||'Registrazione'),data:a.data,created:Number(a.created)||Date.now()})):[],chainRoot:typeof n.chainRoot==='string'?n.chainRoot:'',chainOrder:Number.isFinite(Number(n.chainOrder))?Number(n.chainOrder):0,linkedFiles:Array.isArray(n.linkedFiles)?n.linkedFiles.filter(f=>f&&typeof f.uri==='string'&&/^content:\/\//.test(f.uri)&&f.uri.length<4096).slice(0,15).map(f=>({uri:f.uri,name:String(f.name||'Documento').slice(0,180),type:String(f.type||'').slice(0,120),size:Number(f.size)||0})):[]};if(Number(n.deletedAt)>0){cleaned.deletedAt=Number(n.deletedAt);cleaned.trashBatchId=typeof n.trashBatchId==='string'&&n.trashBatchId?n.trashBatchId:cleaned.id;}imported.push(cleaned);count++;}await putNotesBatch(imported);await reload();scheduleReminders();$('settingsStatus').textContent='Importati '+count+' appunti.';}catch(e){$('settingsStatus').textContent='Importazione non riuscita: '+e.message;}finally{$('jsonInput').value='';}}
function icsEscape(s){return String(s||'').replace(/\\/g,'\\\\').replace(/\r?\n/g,'\\n').replace(/[;,]/g,m=>'\\'+m);}
async function exportICS(){const notes=(await allNotes()).filter(n=>!n.deletedAt&&n.reminder&&!Number.isNaN(new Date(n.reminder).getTime()));if(!notes.length){$('settingsStatus').textContent='Nessun promemoria da esportare.';return;}const stamp=new Date().toISOString().replace(/[-:]/g,'').replace(/\.\d{3}/,'');const out=['BEGIN:VCALENDAR','VERSION:2.0','PRODID:-//Onfim//Promemoria//IT','CALSCALE:GREGORIAN','METHOD:PUBLISH'];for(const n of notes){const t=n.reminder.replace(/[-:]/g,'').replace('T','T');const local=t.length===13?t+'00':t;out.push('BEGIN:VEVENT','UID:'+n.id.replace(/[^a-zA-Z0-9-]/g,'-')+'@onfim.local','DTSTAMP:'+stamp,'DTSTART:'+local,'DTEND:'+local,'SUMMARY:'+icsEscape('Onfim: '+(n.reserved?'Appunto riservato':(n.title||'Promemoria'))),'DESCRIPTION:'+icsEscape(n.reserved?'Apri gli appunti riservati in Onfim.':txt(n.text).slice(0,300)),'BEGIN:VALARM','TRIGGER:PT0M','ACTION:DISPLAY','DESCRIPTION:Promemoria Onfim','END:VALARM','END:VEVENT');}out.push('END:VCALENDAR');download(out.join('\r\n')+'\r\n','onfim-promemoria.ics','text/calendar;charset=utf-8');$('settingsStatus').textContent='Esportati '+notes.length+' promemoria. Importa il file nel calendario Android; l’importazione non si aggiorna automaticamente.';}
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

// Attach an EXISTING standalone note to the currently open group.
// Both notes survive as independent records with only chainRoot/order metadata added.
const closeJoinDialog=()=>{if($('joinDialog').open)$('joinDialog').close();};
$('joinCancel').onclick=closeJoinDialog;
$('joinCancelTop').onclick=closeJoinDialog;
function candidatesToJoin(all,root){
  return all.filter(n=>!n.deletedAt&&n.id!==root.id && !n.chainRoot && n.reserved===root.reserved && !all.some(p=>!p.deletedAt&&p.chainRoot===n.id))
    .sort((a,b)=>(b.updated||0)-(a.updated||0));
}
$('joinExisting').onclick=async()=>{
  const all=await allNotes(),root=all.find(n=>n.id===readId);
  if(!root){toast('Appunto non trovato');return;}
  if(root.reserved&&!unlocked&&!await checkPin())return;
  const choices=candidatesToJoin(all,root);
  if(!choices.length){toast('Nessun appunto autonomo disponibile');return;}
  $('joinSearch').value='';
  function drawOptions(){
    const q=$('joinSearch').value.toLocaleLowerCase().trim(),host=$('joinOptions');host.replaceChildren();
    const matches=choices.filter(n=>!q||[n.title,txt(n.text),...noteTags(n)].join(' ').toLocaleLowerCase().includes(q));
    if(!matches.length){const msg=document.createElement('p');msg.className='small';msg.textContent='Nessun risultato';host.append(msg);return;}
    for(const candidate of matches){
      const btn=document.createElement('button');btn.type='button';btn.className='join-option';btn.setAttribute('role','listitem');
      const title=document.createElement('span');title.className='join-title';title.textContent=candidate.title||'Senza titolo';
      const preview=document.createElement('span');preview.className='join-preview';preview.textContent=txt(candidate.text).trim().slice(0,130)||((candidate.photos||[]).length?'📷 Foto':candidate.drawing?'✎ Disegno':(candidate.audios||[]).length?'🎙 Audio':'');
      btn.append(title,preview);
      btn.onclick=async()=>{
        btn.disabled=true;
        try{
          const current=await allNotes(),freshRoot=current.find(n=>n.id===readId),freshCandidate=current.find(n=>n.id===candidate.id);
          if(!freshRoot||!freshCandidate||!candidatesToJoin(current,freshRoot).some(n=>n.id===freshCandidate.id)){
            toast('La nota è cambiata: riapri la selezione');closeJoinDialog();return;
          }
          if(freshRoot.reserved&&!unlocked&&!await checkPin()){btn.disabled=false;return;}
          const parts=chainMembers(freshRoot,current);
          const nextOrder=Math.max(0,...parts.slice(1).map(n=>Number(n.chainOrder)||0))+1;
          await putNotesBatch([{...freshCandidate,chainRoot:freshRoot.id,chainOrder:nextOrder,updated:Date.now()}]);
          closeJoinDialog();await reload();await openRead(freshRoot);
          toast('Nota aggiunta alla sequenza');
        }catch(err){toast('Non è stato possibile unire: '+(err?.message||'errore'));btn.disabled=false;}
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
let reminderOpenedFromList=false;
async function openReminderFor(source,fromList=false){
  const all=await allNotes();const fresh=all.find(n=>n.id===source.id);if(!fresh)return;const root=groupRootFor(fresh,all);
  if(!root||root.deletedAt)return;
  if(root.reserved&&!unlocked&&!await checkPin())return;
  reminderOpenedFromList=fromList;
  readId=root.id;
  $('readReminderValue').value=root.reminder||'';
  $('reminderRepeat').value=root.reminderRepeat||'none';
  onfimUpdateRepeatInfo();
  fillGeo(root.geofence);
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
 let value=$('readReminderValue').value;const repeat=$('reminderRepeat').value,base=value;if(value&&repeat!=='none')value=onfimNextRepeat(value,repeat,Date.now());
 if(value&&(!Number.isFinite(new Date(value).getTime())||new Date(value).getTime()<=Date.now())){toast('Scegli data e ora future');return;}
 let geo=null;
 if($('geoEnabled').checked){
  if(!$('geoLat').value.trim()||!$('geoLon').value.trim()){toast('Inserisci le coordinate del luogo');return;}
  geo=cleanGeofence({enabled:true,name:$('geoName').value.trim(),lat:Number($('geoLat').value),lon:Number($('geoLon').value),radius:Number($('geoRadius').value),transition:$('geoTransition').value,token:String(Date.now())});
  if(!geo){toast('Coordinate non valide o raggio fuori da 100–10000 m');return;}
 }
 if(!value&&!geo){toast('Scegli data e ora oppure un luogo');return;}
 void saveReadReminder(value,geo,repeat,base);
};
$('reminderRemove').onclick=()=>void saveReadReminder('',null,'none');
$('readEditTop').onclick=()=>{closeReadMenu();$('editFromRead').click();};
$('readFavOption').onclick=()=>{closeReadMenu();$('starFromRead').click();};
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
$('addPartEditor').onclick=()=>{if(isRecording()){toast('Ferma la registrazione prima di aggiungere una parte');return;}$('addPartDialog').showModal();};
$('partCancel').onclick=closeAddPart;
async function performAddPart(kind){
  closeAddPart();
  if(isRecording()){toast('Ferma prima la registrazione');return;}
  if(dirty){toast('Salva prima le modifiche per aggiungere una parte');return;}
  if(!note||!hasContent(note))return;
  const all=await allNotes(),saved=all.find(n=>n.id===note.id);
  if(!saved){toast('Salva prima questo appunto');return;}
  const root=groupRootFor(saved,all);
  if(root.reserved&&!unlocked&&!await checkPin())return;
  readId=root.id;
  if(kind==='new')await $('addSequel').onclick();
  else await $('joinExisting').onclick();
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
$('searchToggle').onclick=()=>{
  const opening=$('searchPanel').classList.contains('hidden');
  $('searchPanel').classList.toggle('hidden',!opening);
  $('searchToggle').classList.toggle('selected',opening);
  $('searchToggle').setAttribute('aria-expanded',String(opening));
  if(opening)$('search').focus();
};
$('searchClose').onclick=()=>{
  $('search').value='';$('searchPanel').classList.add('hidden');
  $('searchToggle').classList.remove('selected');
  $('searchToggle').setAttribute('aria-expanded','false');
  renderNotes();
};
$('filtersToggle').onclick=()=>{
  const opening=$('filterControls').classList.contains('hidden');
  $('filterControls').classList.toggle('hidden',!opening);
  $('filtersToggle').classList.toggle('selected',opening);
  $('filtersToggle').setAttribute('aria-expanded',String(opening));
};
$('addButton').onclick=async()=>{if($('editView').classList.contains('show')){await leaveEditor();if($('editView').classList.contains('show'))return;}newNote();};$('settingsButton').onclick=async()=>{if($('editView').classList.contains('show')){await leaveEditor();if($('editView').classList.contains('show'))return;}if($('filter').value==='reserved')lockArchive();view('settingsView');void refreshBackupStatus();void checkPersistentStorage();void renderLocalSnapshots();};$('backEditor').onclick=leaveEditor;$('closeEditor').onclick=leaveEditor;$('backSettings').onclick=async()=>{await reload();view('listView')};$('saveNote').onclick=async()=>{if(isRecording()){toast('Ferma la registrazione prima di salvare.');chooseTab('audio');return;}if(!hasContent(snapshot())){toast('Scrivi qualcosa o aggiungi un allegato.');return;}await flushSave();if(!dirty){toast('Appunto salvato');await showSavedRead();}};$('deleteNote').onclick=async()=>{if(isRecording()){toast('Ferma prima la registrazione.');return;}if(!note)return;if(note.reserved&&!await checkPin())return;if(!confirmMoveToTrash(note.chainRoot?1:chainMembers(note,await allNotes()).length))return;await safeDeleteNote(note);note=null;dirty=false;clearTimeout(saveTimer);await reload();await scheduleReminders();view('listView');toast('Spostato nel Cestino');};
function closeCardMenus(){document.querySelectorAll('.card.menu-open').forEach(c=>c.classList.remove('menu-open'));document.querySelectorAll('.card-popup').forEach(p=>p.classList.add('hidden'));document.querySelectorAll('.card-more[aria-expanded="true"]').forEach(b=>b.setAttribute('aria-expanded','false'));}
document.addEventListener('click',e=>{if(!e.target.closest('.card-menu'))closeCardMenus();});
document.addEventListener('keydown',e=>{if(e.key==='Escape')closeCardMenus();});
function lockArchive(){unlocked=false;if($('filter').value==='reserved')$('filter').value='ordinary';$('readBody').replaceChildren();$('readPhotos').replaceChildren();$('readAudios').replaceChildren();$('chainParts').replaceChildren();syncFilterPills();}
function syncFilterPills(){for(const b of document.querySelectorAll('[data-filter-choice]')){const on=b.dataset.filterChoice===$('filter').value;b.classList.toggle('selected',on);b.setAttribute('aria-pressed',String(on));}}
for(const b of document.querySelectorAll('[data-filter-choice]'))b.onclick=async()=>{if(b.dataset.filterChoice==='reserved'&&!await checkPin())return;if(b.dataset.filterChoice==='ordinary'&&$('filter').value==='reserved')unlocked=false;$('filter').value=b.dataset.filterChoice;syncFilterPills();await showTags();renderNotes();};
$('search').oninput=renderNotes;$('sortOrder').onchange=renderNotes;$('tagFilter').onchange=renderNotes;$('filter').onchange=async()=>{if($('filter').value==='reserved'&&!await checkPin())$('filter').value='ordinary';syncFilterPills();await showTags();renderNotes();};
for(const b of document.querySelectorAll('[data-tab]'))b.onclick=()=>chooseTab(b.dataset.tab);
$('noteTitle').oninput=markDirty;for(const id of ['noteColor','reminder'])$(id).onchange=markDirty;
$('reserved').onchange=async()=>{if($('reserved').checked){$('reserved').checked=false;const ok=await checkPin();if(ok)$('reserved').checked=true;}markDirty();};$('noteBody').oninput=()=>{lastHighlightAction=null;markDirty();recordTextHistory();updateTextMark();};$('textUndo').onclick=()=>textUndoOrRedo(-1);$('textRedo').onclick=()=>textUndoOrRedo(1);document.addEventListener('selectionchange',()=>{rememberRange();if(document.activeElement===$('noteBody'))updateFormat();});
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
for(const b of document.querySelectorAll('[data-draw]'))b.onclick=()=>{pen=b.dataset.draw;penMode(false);document.querySelectorAll('[data-draw]').forEach(x=>x.classList.toggle('selected',x===b));};

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
 if(pickerTarget==='photo'){markColor=hex;markMode(false);document.querySelectorAll('[data-mark]').forEach(x=>x.classList.toggle('selected',x.dataset.mark.toLowerCase()===markColor));}
 else if(pickerTarget==='draw'){pen=hex;penMode(false);document.querySelectorAll('[data-draw]').forEach(x=>x.classList.toggle('selected',x.dataset.draw.toLowerCase()===pen));}
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
$('galleryButton').onclick=()=>$('galleryInput').click();$('cameraButton').onclick=()=>$('cameraInput').click();for(const id of ['galleryInput','cameraInput'])$(id).onchange=async e=>{await readPhotos(e.target.files);e.target.value='';};

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
$('audioRecord').onclick=startAudioRecording;
$('audioStop').onclick=()=>{if(isRecording())recorder.stop();};
$('audioPause').onclick=()=>{if(!isRecording())return;if(recorder.state==='recording'){recorder.pause();audioPausedAt=performance.now();$('audioStatus').textContent='Registrazione in pausa.';}else if(recorder.state==='paused'){audioPauseTotal+=performance.now()-audioPausedAt;recorder.resume();$('audioStatus').textContent='Registrazione in corso…';}recordingUI();};
$('audioInput').onchange=async e=>{await importAudioFiles(e.target.files);e.target.value='';};
$('managePin').onclick=async()=>{if(pinStored()){unlocked=false;if(!await checkPin())return;}const done=await pinDialog('new');$('settingsStatus').textContent=done?'PIN impostato.':'PIN non modificato.';};$('lockPin').onclick=async()=>{unlocked=false;if($('filter').value==='reserved')$('filter').value='ordinary';await showTags();syncFilterPills();await renderNotes();$('settingsStatus').textContent='Archivio bloccato.';};
window.addEventListener('beforeunload',e=>{if(dirty){e.preventDefault();e.returnValue='';}});
// Browser adapter: original IndexedDB functions above remain authoritative.
// Geofences imported from APK remain in JSON but are not monitored here.
function cleanGeofence(g){if(!g||!g.enabled)return null;const lat=Number(g.lat),lon=Number(g.lon),radius=Number(g.radius);if(!Number.isFinite(lat)||lat< -90||lat>90||!Number.isFinite(lon)||lon< -180||lon>180||!Number.isFinite(radius)||radius<100||radius>10000)return null;return{enabled:true,name:String(g.name||''),lat,lon,radius,transition:g.transition==='exit'?'exit':'enter',token:String(g.token||'imported')};}
function fillGeo(g){$('geoEnabled').checked=false;$('geoFields').hidden=true;}
// User-initiated web share of a JSON backup; the destination must confirm storage.
function makeBackupFile(notes){const now=new Date(),payload={format:'appunti-backup',version:2,app:'Onfim',exportedAt:now.toISOString(),notes};return new File([JSON.stringify(payload,null,2)],manualBackupFilename(now),{type:'application/json'});}
async function shareBackupViaAndroid(){const out=$('settingsStatus');try{
  if(dirty)throw new Error('Salva o chiudi la nota prima di condividere il backup.');
  if(typeof navigator.share!=='function')throw new Error('La condivisione di file non è disponibile: usa Esporta JSON.');
  const file=makeBackupFile(await allNotes());
  if(navigator.canShare&&!navigator.canShare({files:[file]}))throw new Error('Il browser non supporta la condivisione di questo file. Usa Esporta JSON.');
  await navigator.share({files:[file],title:'backup onfim'});
  out.textContent='Backup consegnato al menu Condividi. Verifica sulla destinazione (per esempio Drive) che il file sia stato salvato.';
}catch(e){out.textContent=e.name==='AbortError'?'Condivisione annullata.':'Condivisione non riuscita: '+e.message;}}
const SNAPSHOT_INTERVAL=24*60*60*1000, MAX_SNAPSHOTS=3;
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
    if(!force&&latest&&(Date.now()-latest.id<SNAPSHOT_INTERVAL||changed<=Number(latest.changedAt)))return false;
    const stamp=Date.now(),copy={id:stamp,createdAt:new Date(stamp).toISOString(),changedAt:changed,reason,notes};
    await snapshotSave(copy);
    const all=(await snapshotStoreAll()).sort((a,b)=>b.id-a.id);
    if(all.length>MAX_SNAPSHOTS)await snapshotPrune(all.slice(MAX_SNAPSHOTS).map(x=>x.id));
    await renderLocalSnapshots();
    return true;
  }catch(e){console.warn('Onfim: copia locale non riuscita',e);snapshotUpdateStatus('Copia locale non riuscita: '+e.message);return false;}
  finally{internalSnapshotBusy=false;}
}
function scheduleLocalSnapshot(){if(!db||!snapshotDb)return;clearTimeout(internalSnapshotTimer);internalSnapshotTimer=setTimeout(()=>{void makeLocalSnapshot('automatica');},12000);}
async function renderLocalSnapshots(){
  if(!db||!snapshotDb)return;const host=$('localBackupList');if(!host)return;
  try{
    const list=(await snapshotStoreAll()).sort((a,b)=>b.id-a.id);host.replaceChildren();
    if(!list.length){host.textContent='Nessuna copia interna: verrà creata durante l’uso, se ci sono appunti.';return;}
    for(const snap of list){const row=document.createElement('div');row.className='backup-local-item';
      const info=document.createElement('div');const date=document.createElement('strong');date.textContent=snapshotDate(snap.id);const desc=document.createElement('small');desc.textContent=(snap.notes||[]).length+' elementi · '+(snap.reason==='automatica'?'Automatica':snap.reason==='prima-importazione'?'Prima dell’importazione':snap.reason==='prima-ripristino'?'Prima del ripristino':'Manuale');info.append(date,desc);
      const actions=document.createElement('div');actions.className='backup-local-actions';const save=document.createElement('button');save.type='button';save.textContent='Esporta';save.onclick=()=>{const pack={format:'appunti-backup',version:2,app:'Onfim',exportedAt:snap.createdAt,notes:snap.notes};download(JSON.stringify(pack,null,2),manualBackupFilename(new Date(snap.id)),'application/json');snapshotUpdateStatus('Download della copia avviato: verifica il file fuori da Onfim.');};
      const restore=document.createElement('button');restore.type='button';restore.textContent='Ripristina';restore.onclick=async()=>{
        if(!confirm('Ripristinare questa copia del '+snapshotDate(snap.id)+'? Gli appunti attuali saranno sostituiti, compresi quelli nel Cestino. Una copia preventiva verrà salvata internamente.'))return;
        try{
          if(dirty)throw new Error('Chiudi o salva l’appunto prima di ripristinare.');
          const existing=await allNotes();if(existing.length){const ok=await makeLocalSnapshot('prima-ripristino',true);if(!ok)throw new Error('Impossibile creare la copia preventiva: ripristino interrotto.');}
          await replaceAllNotes(snap.notes);unlocked=false;readId=null;note=null;
          if($('filter').value==='reserved')$('filter').value='ordinary';syncFilterPills();
          await reload();await scheduleReminders();view('listView');
          snapshotUpdateStatus('Copia ripristinata. Gli appunti sono stati sostituiti.');
        }catch(e){snapshotUpdateStatus('Ripristino non riuscito: '+e.message);}
      };actions.append(save,restore);row.append(info,actions);host.append(row);
    }
  }catch(e){host.textContent='Impossibile leggere le copie: '+e.message;}
}
function replaceAllNotes(notes){return new Promise((res,rej)=>{const tx=db.transaction(STORE,'readwrite'),store=tx.objectStore(STORE);store.clear();for(const n of notes)if(n&&typeof n.id==='string')store.put(n);tx.oncomplete=()=>{recordDataChange();res();};tx.onerror=()=>rej(tx.error||new Error('Ripristino non riuscito'));tx.onabort=()=>rej(tx.error||new Error('Ripristino annullato'));});}


/* onfim 0.7.78.5: UX condivisa, promemoria rapidi, collegamenti e riordino. */
const ONFIM_REPEAT_DAYS={sunday:0,monday:1,tuesday:2,wednesday:3,thursday:4,friday:5,saturday:6};
function onfimLocalDateTime(d){const p=v=>String(v).padStart(2,'0');return `${d.getFullYear()}-${p(d.getMonth()+1)}-${p(d.getDate())}T${p(d.getHours())}:${p(d.getMinutes())}`;}
function onfimPresetDate(kind,now=new Date()){
 const d=new Date(now);
 if(kind==='hour')d.setHours(d.getHours()+1);
 if(kind==='week')d.setDate(d.getDate()+7);
 if(kind==='tomorrow'){d.setDate(d.getDate()+1);d.setHours(9,0,0,0);}
 if(kind==='evening'){d.setHours(19,0,0,0);if(d.getTime()<=now.getTime())d.setDate(d.getDate()+1);}
 d.setSeconds(0,0);return d;
}
function onfimNextRepeat(value,rule,after=Date.now(),anchor=value){
 if(!value||rule==='none'||!rule)return '';
 const first=new Date(value),anchorDay=new Date(anchor),hour=first.getHours(),minute=first.getMinutes();
 if(!Number.isFinite(first.getTime()))return '';
 const candidate=new Date(first);
 const advance=()=>{if(rule==='daily'){candidate.setDate(candidate.getDate()+1);return;}
 if(rule==='weekly'){candidate.setDate(candidate.getDate()+7);return;}
 if(rule==='monthly'){const want=Number.isFinite(anchorDay.getTime())?anchorDay.getDate():first.getDate();candidate.setDate(1);candidate.setMonth(candidate.getMonth()+1);candidate.setDate(Math.min(want,new Date(candidate.getFullYear(),candidate.getMonth()+1,0).getDate()));return;}
 candidate.setDate(candidate.getDate()+1);
 };
 for(let i=0;i<2000;i++){
   if(candidate.getTime()>after){
    const day=candidate.getDay();
    const allowed=(rule==='weekday'?day>=1&&day<=5:rule in ONFIM_REPEAT_DAYS?day===ONFIM_REPEAT_DAYS[rule]:true);
    if(allowed)return onfimLocalDateTime(candidate);
   }
   advance();candidate.setHours(hour,minute,0,0);
 }
 return '';
}
function onfimFormatRepeat(rule){const names={daily:'ogni giorno',weekly:'ogni settimana',monthly:'ogni mese',weekday:'lun–ven',monday:'ogni lunedì',tuesday:'ogni martedì',wednesday:'ogni mercoledì',thursday:'ogni giovedì',friday:'ogni venerdì',saturday:'ogni sabato',sunday:'ogni domenica'};return names[rule]||'';}
function onfimUpdateRepeatInfo(){const rule=$('reminderRepeat').value;const hasGeo=$('geoEnabled').checked;$('recurrenceSection').classList.toggle('hidden',hasGeo&&!$('readReminderValue').value);$('repeatInfo').textContent=rule==='none'?'Una sola volta.':`Ripetizione ${onfimFormatRepeat(rule)}. ${typeof window.OnfimAndroid==='undefined'?'In Lite funziona soltanto con la PWA aperta.':'Gli avvisi ripetuti con app chiusa richiedono l’aggiornamento del servizio Android.'}`;}
for(const b of document.querySelectorAll('[data-reminder-preset]'))b.addEventListener('click',()=>{$('readReminderValue').value=onfimLocalDateTime(onfimPresetDate(b.dataset.reminderPreset));onfimUpdateRepeatInfo();});
$('readReminderValue').addEventListener('input',onfimUpdateRepeatInfo);$('reminderRepeat').addEventListener('change',onfimUpdateRepeatInfo);
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
if(!onfimLinkedFileBridge()){$('pickLinkedFile').disabled=true;$('linkFileExplanation').textContent='Il collegamento ai documenti sarà disponibile dopo l’aggiornamento del servizio Android.';}
$('pickLinkedFile').onclick=()=>{if(!onfimLinkedFileBridge()){toast('Collegamento ai file: richiede aggiornamento della parte Android');return;}try{OnfimAndroid.pickLinkedFile();}catch(e){toast('Selezione non disponibile');}};
window.onfimFilePicked=(raw)=>{try{if(!$('editView').classList.contains('show'))throw new Error('L’editor non è aperto');const o=typeof raw==='string'?JSON.parse(raw):raw;if(!o||typeof o.uri!=='string'||!/^content:\/\//.test(o.uri)||o.uri.length>4096)throw new Error('Riferimento non valido');if(onfimEditorLinks.length>=15)throw new Error('Massimo 15 file per parte');if(!onfimEditorLinks.some(f=>f.uri===o.uri))onfimEditorLinks.push({uri:o.uri,name:String(o.name||'Documento').slice(0,180),type:String(o.type||'').slice(0,120),size:Number(o.size)||0});onfimRenderEditorLinks();markDirty();toast('File collegato: ricorda di premere Salva');}catch(e){toast('Impossibile collegare il file: '+e.message);}};
function onfimClosePartMenus(){document.querySelectorAll('.chain-options').forEach(x=>x.classList.add('hidden'));}
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
function onfimAskPartFromCard(id){readId=id;onfimPartFromCard=true;$('addPartDialog').showModal();}
$('partCancel').addEventListener('click',()=>{onfimPartFromCard=false;});$('addPartDialog').addEventListener('close',()=>{onfimPartFromCard=false;});
// Note: partNew/partExisting handlers are wrapped after their existing assignments.
for(const kind of ['New','Existing']){
 const b=$('part'+kind),original=b.onclick;
 b.onclick=async e=>{if(!onfimPartFromCard)return original.call(b,e);
   onfimPartFromCard=false;closeAddPart();if(kind==='New')return $('addSequel').onclick();return $('joinExisting').onclick();};
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
   chooseTab(incoming.text.trim()||incoming.title.trim()?'text':incoming.images.length?'photos':'audio');
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
})();
