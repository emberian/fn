#!/usr/bin/env python3
"""Tracked canonical book navigator. Generate/check docs/books, or query one book.

Reuses ledger's non-evaluating reader/book analysis, callgraph's conservative
mention graph, interface_emit declarations and shape_books reverse fan-in.
No source loading, certification, deletion or runtime reachability claim.
"""
from __future__ import annotations
import argparse
import collections
from contextlib import contextmanager
import fnmatch
import hashlib
import html
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import callgraph
import certify_books
import interface_emit
import ledger
import shape_books

ROOT = Path(__file__).resolve().parents[1]
CATEGORIES = ('served-load', 'host-reference', 'interface', 'proof', 'test', 'generation')


def tracked(root):
    return set(subprocess.check_output(['git','ls-files','-z'],cwd=root).decode().split('\0'))-{''}


@contextmanager
def in_tree(root):
    modules=(ledger,callgraph,certify_books)
    saved=[m.ROOT for m in modules]
    try:
        for m in modules: m.ROOT=root
        yield
    finally:
        for m,v in zip(modules,saved): m.ROOT=v


def resolve_reference(source, reference, known, cwd_fallback=False):
    suffix=reference if reference.endswith('.lisp') else reference+'.lisp'
    candidates=[ledger.resolve((Path(source).parent/suffix).as_posix())]
    if cwd_fallback: candidates.append(ledger.resolve(suffix))
    return sorted(set(p for p in candidates if p in known)), sorted(set(candidates))


def namespace_rows(root):
    rows=[]
    path=root/'docs/prefixes.md'
    if not path.is_file(): return rows
    for line in path.read_text().splitlines():
        cells=line.split('|')
        if len(cells)>=5:
            prefixes=re.findall(r'`([^`]+)`',cells[1])
            modules=re.findall(r'`([^`]+)`',cells[2])
            if prefixes and modules: rows.append((prefixes,modules,cells[3].strip()))
    return rows


def subsystem(path,catalog):
    stem=Path(path).stem
    for s in catalog.get('subsystems',[]):
        if any(fnmatch.fnmatchcase(stem,p) for p in s['patterns']):
            return s['name'],s['responsibility']
    return 'Unassigned', 'No maintained subsystem pattern; add a precise catalog note.'


def load_json(root,path,default):
    return json.loads((root/path).read_text()) if (root/path).is_file() else default


def graph_closure(edges,roots):
    graph=callgraph.Graph(edges={k:set(v) for k,v in edges.items()})
    graph.edges['@roots']=set(roots)
    return set(graph.reach('@roots'))


def build(root=ROOT):
    root=root.resolve()
    files=tracked(root)
    canonical=sorted(p for p in files if p.startswith('books/') and p.endswith('.lisp'))
    lisp=sorted(p for p in files if p.endswith('.lisp') and p.startswith(('books/','host/','tests/','tools/')))
    known=set(lisp)
    catalog=load_json(root,'docs/books/catalog.json',{})
    warnings=[]; root_records=[]; edges={}; nonlocal_edges={}; analyses={}
    inputs=set(lisp)|{'Makefile','docs/prefixes.md','docs/books/catalog.json','planning/proofs.json','planning/proof-events.json'}
    def add_root(book,category,source,line=0,reason=''):
        if book in known:
            root_records.append(dict(book=book,category=category,source=source,line=line,reason=reason))
        else: warnings.append(dict(source=source,kind='unresolved-root',target=book,reason=reason))
    with in_tree(root):
        for p in lisp:
            try: analysis=ledger.analyze_book(root/p,p)
            except (OSError,ValueError) as exc:
                warnings.append(dict(source=p,kind='unreadable',reason=str(exc)));continue
            analyses[p]=analysis
            if analysis.read_error:
                warnings.append(dict(source=p,kind='unreadable',reason=analysis.read_error))
            deps=[]; nonlocal_deps=[]
            for ref in analysis.includes:
                target=ledger.included_path(analysis,ref)
                if target in known: deps.append(target)
                elif p.startswith('books/'): warnings.append(dict(source=p,kind='missing-or-untracked-include',target=target))
            for line,ref in analysis.nonlocal_includes:
                target=ledger.included_path(analysis,ref)
                if target in known: nonlocal_deps.append(target)
            # Host/build scripts are run both file-relative and at repository
            # cwd. Ledger host_visible has the same two-candidate policy.
            if not p.startswith('books/'):
                host=ledger.analyze_host(root/p,p)
                refs=[(ref,'include-book') for ref in host.includes]+[(ref,'load') for ref in host.lds]
                for ref,kind in refs:
                    targets,candidates=resolve_reference(p,ref,known,True)
                    if not targets: warnings.append(dict(source=p,kind='unresolved-load',target=ref,candidates=candidates))
                    if len(targets)>1: warnings.append(dict(source=p,kind='ambiguous-load',target=ref,candidates=targets))
                    deps+=targets;nonlocal_deps+=targets
                    for target in targets:
                        category='served-load' if p.startswith('host/') else 'test' if p.startswith('tests/') else 'generation'
                        add_root(target,category,p,reason=kind+' literal')
            edges[p]=sorted(set(deps)); nonlocal_edges[p]=sorted(set(nonlocal_deps))
            if p.startswith('tests/'):
                for dep in deps: add_root(dep,'test',p,reason='scenario/proof-test include')
            if p.startswith('tools/'):
                for dep in deps: add_root(dep,'generation',p,reason='generation/tool include')
            # Computed forms are inventory gaps, never evidence of disuse.
            text=(root/p).read_text(errors='replace')
            if re.search(r'\((?:make-event|include-raw|apply\$|intern)\b',text,re.I):
                warnings.append(dict(source=p,kind='dynamic-or-generated-source',reason='Static includes/mention graph cannot establish complete computed uses.'))
        graph=callgraph.build([(root/p,p) for p in lisp if not p.startswith('tests/')])
        # Native wrappers often spell core names ACL2::FN-... explicitly.
        # Preserve callgraph's conservative mentions, adding the same symbol's
        # unqualified core identity only when that definition actually exists.
        for name,definitions in graph.definitions.items():
            for d in definitions:
                for symbol in callgraph.symbols(d.form[2:]):
                    if symbol.startswith(('acl2::','acl2:')):
                        core=symbol.split(':')[-1]
                        if core in graph.definitions and core!=name: graph.edges[name].add(core)
        for p,error in graph.unreadable.items(): warnings.append(dict(source=p,kind='function-graph-unreadable',reason=error))
        # All tracked host function bodies are positive references, including
        # PROGRAM/raw wrappers. A reference is not evidence of activation.
        host_names={name for name,defs in graph.definitions.items() if any(d.path.startswith('host/') for d in defs)}
        reached=set(host_names)
        graph.edges['@hosts']=host_names
        reached.update(graph.reach('@hosts'))
        host_reached_books=collections.defaultdict(list)
        for name in sorted(reached):
            for d in graph.definitions.get(name,[]):
                if d.path in canonical: host_reached_books[d.path].append((name,d.line))
        for p,matches in host_reached_books.items():
            add_root(p,'host-reference',p,matches[0][1],
                     'Conservative union of tracked host function mention closures: '+
                     str(len(matches))+' symbols; example '+matches[0][0]+' (not a host caller coordinate)')
        try: declarations=interface_emit.declarations(root)
        except (ValueError,ledger.ReadError) as exc:
            declarations=[];warnings.append(dict(source='host/interfaces*.lisp',kind='interface-unreadable',reason=str(exc)))
        declared_sources={d['source'] for d in declarations}
        for source in lisp:
            if source.startswith('host/') and source not in declared_sources and re.search(r'\(definterface\s', (root/source).read_text(errors='replace'), re.I):
                warnings.append(dict(source=source,kind='additional-interface-source',reason='Outside standard interface_emit declaration files; host mention edges retained, declaration root census incomplete.'))
        interface_names={d['name'] for d in declarations}
        graph.edges['@interfaces']=interface_names
        interface_reached=interface_names|set(graph.reach('@interfaces'))
        interface_books=collections.defaultdict(list)
        for name in sorted(interface_reached):
            for definition in graph.definitions.get(name,[]):
                if definition.path in canonical: interface_books[definition.path].append(name)
        for p,names in interface_books.items():
            add_root(p,'interface','host/interfaces.lisp',reason=
                     'Conservative declared-entry mention closure: '+str(len(names))+' symbols; example '+names[0])
        for d in declarations:
            for definition in graph.definitions.get(d['name'],[]):
                if definition.path in canonical:
                    add_root(definition.path,'interface',d['source'],d['line'],'direct declaration '+d['name'])
            if d['name'] not in graph.definitions:
                warnings.append(dict(source=d['source'],kind='unresolved-interface',target=d['name']))
        # Proof references retain non-executable/local support. Make roots are
        # separately shown; listing a book for certification is not usage.
        proof_ids=collections.defaultdict(set)
        event_map=collections.defaultdict(set)
        for p,a in analyses.items():
            for theorem in a.theorems: event_map[theorem.name].add(p)
        curated=load_json(root,'planning/proof-events.json',{'targets':[]})
        for target in curated.get('targets',[]):
            for event in target.get('events',[]):
                if not isinstance(event,dict): continue
                name=event.get('name','')
                for p in event_map.get(name,()):
                    if p in canonical:
                        proof_ids[p].add(target['id']);add_root(p,'proof','planning/proof-events.json',reason=target['id']+': '+name)
                if name and name not in event_map: warnings.append(dict(source='planning/proof-events.json',kind='unresolved-proof-event',target=name,proof=target['id']))
        for target in load_json(root,'planning/proofs.json',{'proofs':[]}).get('proofs',[]):
            for p in target.get('evidence',[]):
                if p in canonical:
                    proof_ids[p].add(target['id']);add_root(p,'proof','planning/proofs.json',reason=target['id']+' evidence')
        # Literal book paths in tracked scripts, scenarios and generated root
        # lists. Lexical references are wider than execution and are labeled.
        path_pattern=re.compile(r'(?<![\w/-])(books/[A-Za-z0-9_./-]+?)(?:\.lisp|\.cert|(?=[\s\x27"\\)]))')
        for p in sorted(files):
            if not p.startswith(('tools/','tests/','host/')) or not p.endswith(('.py','.sh','.json','.lisp','.txt')): continue
            inputs.add(p)
            text=(root/p).read_text(errors='replace')
            category='test' if p.startswith('tests/') else 'served-load' if p.startswith('host/') else 'generation'
            for line_no,line in enumerate(text.splitlines(),1):
                # Comments/documentation are not loader roots; lisp roots are
                # already parsed above, except tracked generated roots lists.
                if p.endswith('.lisp') or line.lstrip().startswith(('#',';')): continue
                for match in path_pattern.finditer(line):
                    target=ledger.resolve(match.group(1)+'.lisp')
                    if target in canonical: add_root(target,category,p,line_no,'literal script/path reference (not execution proof)')
        try: make_roots={p+'.lisp' if not p.endswith('.lisp') else p for p in certify_books.default_books()}
        except ValueError as exc:
            make_roots=set();warnings.append(dict(source='Makefile',kind='missing-certification-roots',reason=str(exc)))
    for extra in catalog.get('extra_roots',[]):
        if not all(extra.get(k) for k in ('path','category','source','reason')) or extra['category'] not in CATEGORIES:
            raise ValueError('catalog extra_roots needs path/category/source/reason and known category')
        add_root(extra['path'],extra['category'],extra['source'],reason=extra['reason'])
    root_records=sorted({json.dumps(r,sort_keys=True):r for r in root_records}.values(),key=lambda r:(r['category'],r['book'],r['source'],r['line'],r['reason']))
    reached_by={}
    for category in CATEGORIES:
        roots={r['book'] for r in root_records if r['category']==category}
        reached_by[category]=graph_closure(nonlocal_edges if category in ('served-load','host-reference','interface') else edges,roots)
    # Local proof ancestors of served roots are separately visible.
    served_roots={r['book'] for r in root_records if r['category'] in ('served-load','host-reference','interface')}
    local_support=graph_closure(edges,served_roots)-graph_closure(nonlocal_edges,served_roots)
    reached_by['proof'].update(local_support)
    backwards=collections.defaultdict(set)
    for p,deps in edges.items():
        for dep in deps: backwards[dep].add(p)
    counts=shape_books.fan_in(edges,sorted(make_roots))
    namespaces=namespace_rows(root)
    direct=collections.defaultdict(list)
    for r in root_records: direct[r['book']].append(r)
    books=[]
    for p in canonical:
        a=analyses.get(p); roles=[]
        uses=[c for c in CATEGORIES if p in reached_by[c]]
        if any(c in uses for c in ('served-load','host-reference','interface')): roles.append('served/reference')
        if 'proof' in uses: roles.append('proof-support')
        if 'generation' in uses: roles.append('generation-support')
        if 'test' in uses: roles.append('test-support' if roles else 'test-only')
        if not roles: roles=['unknown']
        note=catalog.get('book_notes',{}).get(p,{})
        if note.get('role')=='superseded':
            if not note.get('replacement') or not note.get('evidence'): raise ValueError('superseded note requires replacement and evidence: '+p)
            roles.append('superseded')
        group,owner=subsystem(p,catalog)
        if note.get('subsystem'): group=note['subsystem']
        public_prefixes=[]
        for prefixes,modules,purpose in namespaces:
            if any(fnmatch.fnmatchcase(Path(p).stem,m) or p.removesuffix('.lisp')==m for m in modules):
                public_prefixes.append(dict(prefixes=prefixes,purpose=purpose,source='docs/prefixes.md'))
        text=(root/p).read_text(errors='replace')
        defs=sorted({name for name,ds in graph.definitions.items() if any(d.path==p for d in ds)})
        books.append(dict(path=p,lines=len(text.splitlines()),sha256=hashlib.sha256(text.encode()).hexdigest(),roles=roles,uses=uses,
            subsystem=group,responsibility=owner,namespaces=public_prefixes,definitions=defs,
            proof_ids=sorted(proof_ids[p]),dependencies=[dict(path=d,kind='nonlocal' if d in nonlocal_edges.get(p,[]) else 'local/proof') for d in edges.get(p,[])],
            included_by=sorted(backwards[p]),reverse_dependents=counts.get(p,(1,0))[0]-1,certification_roots_affected=counts.get(p,(1,0))[1],
            certification_root=p in make_roots,system_dependencies=sorted(set(a.system_includes)) if a else [],
            direct_uses=direct[p][:16],direct_use_count=len(direct[p]),note=note))
    # Exact syntax-body matches are candidates only, retaining guards/formals.
    duplicates=collections.defaultdict(list)
    for name,defs in graph.definitions.items():
        for d in defs:
            if d.path not in canonical or d.kind!='function': continue
            body=repr(d.form[2:])
            if len(repr(d.form[-1]))<180: continue
            duplicates[hashlib.sha256(body.encode()).hexdigest()].append(dict(path=d.path,name=name,line=d.line))
    candidates=[]
    for digest,entries in duplicates.items():
        if len({e['path'] for e in entries})>1:
            candidates.append(dict(kind='identical-definition-body',digest=digest,definitions=entries,
                uncertainty='Exact syntax incl. formals/guards, not a semantic/refinement or deletion proof; local/generation/custody roles must be checked.',proposal='Review one reusable leaf or document intentional alternatives in a later coordinated batch.'))
    candidates.sort(key=lambda c:(-len(c['definitions']),c['definitions'][0]['path']))
    input_hashes={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sorted(inputs) if p in files or p=='docs/books/catalog.json' and (root/p).is_file()}
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
    return dict(schema_version=1,source_revision=revision,canonical_count=len(books),canonical_lines=sum(b['lines'] for b in books),
        source_input_digest=hashlib.sha256(json.dumps(input_hashes,sort_keys=True).encode()).hexdigest(),
        scope='Tracked canonical books only; conservative source references/include graphs, not runtime activation, obsolescence or deletion authority.',
        inventory_complete=False,limitations=['Computed loaders/calls and macro-generated names can evade static reading.','Mention edges include quoted function symbols; positive roles are conservative references, not execution proofs.','Certification listing is shown separately and is not functional usage.','Untracked lane WIP and other worktrees are excluded.','Missing/unreadable/dynamic uses remain explicit; no discovered path means unknown.'],
        books=books,roots=root_records,warnings=sorted(warnings,key=lambda w:(w['source'],w['kind'],w.get('target',''))),
        candidates=candidates,interfaces=declarations,conventions=catalog.get('conventions',{}))

HTML = r'''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>fn book navigator</title>
<style>
:root{font:15px/1.45 system-ui,sans-serif;color:#18242d;background:#f5f7f8}body{max-width:1440px;margin:28px auto;padding:0 24px}h1{font-size:28px;margin:0}p{max-width:1050px;color:#4b5b66}a{color:#175f87}header{margin-bottom:20px}.controls{display:flex;gap:12px;flex-wrap:wrap}input,select,button{font:inherit;border:1px solid #b9c7cf;border-radius:5px;padding:9px;background:white}input{flex:1;min-width:270px}button{cursor:pointer}table{border-collapse:collapse;width:100%;background:white}th,td{text-align:left;vertical-align:top;padding:9px 12px;border-bottom:1px solid #e0e6ea}th{background:#eaf0f3;position:sticky;top:0;font-weight:600}tr[data-i]{cursor:pointer}tr[data-i]:hover{background:#edf6fa}.small{font-size:12px;color:#586975}.badge{display:inline-block;border:1px solid #c5d4dc;border-radius:4px;padding:1px 5px;margin:1px;font-size:12px}.layout{display:grid;grid-template-columns:minmax(500px,1fr) 420px;gap:20px}aside{background:white;border:1px solid #d6e0e6;padding:18px;position:sticky;top:16px;align-self:start;max-height:85vh;overflow:auto}aside h2{font-size:18px;margin-top:0;overflow-wrap:anywhere}ul{padding-left:20px}code{font-size:12px;overflow-wrap:anywhere}summary{cursor:pointer}#details:empty:before{content:"Select a book to see its dependencies, reverse uses, namespace and evidence.";color:#586975}.paging{display:flex;gap:12px;align-items:center;margin:12px 0}.warning{border-left:4px solid #bb8628;padding-left:12px}@media(max-width:1000px){.layout{display:block}aside{position:static;margin-top:20px;max-height:none}}
</style>
<header><h1>fn book navigator</h1><p>Tracked canonical ACL2 books, their source references and responsibilities. Loaded/referenced means positive source evidence; it does not mean activated, proved, qualified or obsolete. Missing and computed uses stay explicit.</p>
<div id="counts" class="small"></div></header>
<div class="controls"><input id="search" aria-label="Search books, functions, prefixes or proof IDs" placeholder="Book, function, prefix, proof ID…"><select id="role" aria-label="Role"><option value="">Every role</option></select><select id="group" aria-label="Subsystem"><option value="">Every subsystem</option></select><select id="order" aria-label="Sort"><option value="name">Name</option><option value="reverse">Most reverse dependents</option><option value="lines">Most lines</option></select></div>
<div class="paging"><button id="prev">Previous</button><span id="page"></span><button id="next">Next</button></div>
<div class="layout"><main><table><thead><tr><th>Book</th><th>Role / responsibility</th><th>Reverse uses</th><th>Lines</th></tr></thead><tbody id="rows"></tbody></table></main><aside id="details"></aside></div>
<details><summary>Root inventory, gaps and later review candidates</summary><p id="scope" class="warning"></p><div id="review"></div></details>
<script id="data" type="application/json">__DATA__</script>
<script>
const DATA=JSON.parse(document.getElementById('data').textContent), BOOKS=DATA.books, BYPATH=new Map(BOOKS.map((b,i)=>[b.path,{b,i}]));
const $=id=>document.getElementById(id), esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const sourceLink=(path,label=path)=>`<a href="../../${path.split('/').map(encodeURIComponent).join('/')}" target="_blank">${esc(label)}</a>`;
let page=0, filtered=[], size=100;
for(const r of [...new Set(BOOKS.flatMap(b=>b.roles))].sort())$('role').add(new Option(r,r));
for(const r of [...new Set(BOOKS.map(b=>b.subsystem))].sort())$('group').add(new Option(r,r));
$('counts').textContent=`${DATA.canonical_count} tracked books · ${DATA.canonical_lines.toLocaleString()} lines · ${DATA.root_count} explicit source root records · ${DATA.warning_count} inventory warnings · input ${DATA.source_input_digest.slice(0,12)}`;
function render(){
 const term=$('search').value.trim().toLowerCase(),role=$('role').value,group=$('group').value;
 filtered=BOOKS.map((b,i)=>({b,i})).filter(({b})=>(!role||b.roles.includes(role))&&(!group||b.subsystem===group)&&(!term||[b.path,b.subsystem,b.responsibility,...b.definitions,...b.proof_ids,...b.namespaces.flatMap(n=>n.prefixes)].join(' ').toLowerCase().includes(term)));
 filtered.sort((a,b)=>$('order').value==='reverse'?b.b.reverse_dependents-a.b.reverse_dependents||a.b.path.localeCompare(b.b.path):$('order').value==='lines'?b.b.lines-a.b.lines||a.b.path.localeCompare(b.b.path):a.b.path.localeCompare(b.b.path));
 page=Math.min(page,Math.max(0,Math.ceil(filtered.length/size)-1));
 $('rows').innerHTML=filtered.slice(page*size,(page+1)*size).map(({b,i})=>`<tr data-i="${i}"><td>${esc(b.path.replace('books/',''))}<div class="small">${b.namespaces.map(n=>n.prefixes.map(esc).join(' ')).join(' · ')}</div></td><td>${b.roles.map(r=>`<span class="badge">${esc(r)}</span>`).join('')}<div class="small">${esc(b.subsystem)}</div></td><td>${b.reverse_dependents}<div class="small">${b.included_by.length} direct</div></td><td>${b.lines}</td></tr>`).join('');
 $('page').textContent=`${filtered.length} matches · page ${page+1} / ${Math.max(1,Math.ceil(filtered.length/size))}`;
 $('prev').disabled=page===0;$('next').disabled=(page+1)*size>=filtered.length;
}
function bookLink(path){return BYPATH.has(path)?`<a href="#${encodeURIComponent(path)}">${esc(path)}</a>`:sourceLink(path)}
function select(i){
 const b=BOOKS[i];
 $('details').innerHTML=`<h2>${sourceLink(b.path)}</h2><p>${esc(b.responsibility)}</p><div>${b.roles.map(r=>`<span class="badge">${esc(r)}</span>`).join('')}</div><p class="small">Uses: ${b.uses.map(esc).join(', ')||'No discovered source path; unknown'}<br>Certification root: ${b.certification_root?'yes (listing alone is not usage)':'no'}<br>Current content: <code>${b.sha256.slice(0,16)}</code></p>
 <h3>Namespace / purpose</h3>${b.namespaces.length?b.namespaces.map(n=>`<p><code>${n.prefixes.map(esc).join(', ')}</code><br>${esc(n.purpose)}</p>`).join(''):'<p>No explicit namespace row found.</p>'}
 <h3>Direct dependencies</h3><ul>${b.dependencies.map(d=>`<li>${bookLink(d.path)} <span class="small">${esc(d.kind)}</span></li>`).join('')||'<li>None discovered</li>'}</ul>
 <h3>Included by</h3><ul>${b.included_by.map(p=>`<li>${bookLink(p)}</li>`).join('')||'<li>None discovered; this is not deletion evidence</li>'}</ul>
 <details><summary>Direct root evidence (${b.direct_use_count})</summary><ul>${b.direct_uses.map(r=>`<li>${esc(r.category)} · ${sourceLink(r.source)}${r.line?':'+r.line:''}<br><span class="small">${esc(r.reason)}</span></li>`).join('')}</ul>${b.direct_use_count>b.direct_uses.length?'<p class="small">More records are in map.json.</p>':''}</details>
 <details><summary>Definitions (${b.definitions.length}) / proof targets</summary><p>${b.proof_ids.map(esc).join(', ')||'No direct registry target found'}</p><ul>${b.definitions.map(n=>`<li><code>${esc(n)}</code></li>`).join('')}</ul></details>
 ${Object.keys(b.note).length?`<h3>Maintained note</h3><pre>${esc(JSON.stringify(b.note,null,2))}</pre>`:''}`;
}
$('rows').addEventListener('click',e=>{let tr=e.target.closest('tr[data-i]');if(tr){let i=Number(tr.dataset.i);location.hash=encodeURIComponent(BOOKS[i].path);select(i)}});
function hashSelect(){let p=decodeURIComponent(location.hash.slice(1));if(BYPATH.has(p))select(BYPATH.get(p).i)}
window.addEventListener('hashchange',hashSelect);
for(let id of ['search','role','group','order'])$(id).addEventListener('input',()=>{page=0;render()});
$('prev').onclick=()=>{page--;render()};$('next').onclick=()=>{page++;render()};
$('scope').textContent=DATA.limitations.join(' ');
$('review').innerHTML=`<p>${DATA.candidates.length} identical syntax-body groups are review candidates, not obsolete books. Inspect local/proof/generation and custody roles before any later consolidation. Full candidates and unresolved roots are in ${sourceLink('docs/books/map.json','map.json')}.</p>`+DATA.candidates.slice(0,12).map(c=>`<details><summary>${esc(c.kind)} · ${c.definitions.length} definitions · ${c.digest.slice(0,10)}</summary><ul>${c.definitions.map(d=>`<li>${bookLink(d.path)}:${d.line} · <code>${esc(d.name)}</code></li>`).join('')}</ul><p>${esc(c.uncertainty)}</p></details>`).join('');
render();hashSelect();
</script></html>'''


def render_html(data):
    # The generation Git coordinate is informational. Content digest is the
    # stable freshness coordinate; an unrelated commit must not stale a map.
    payload={k:v for k,v in data.items() if k not in ('source_revision','roots','warnings','interfaces')}
    payload.update(root_count=len(data['roots']),warning_count=len(data['warnings']))
    embedded=json.dumps(payload,separators=(',',':')).replace('<',r'\u003c')
    return HTML.replace('__DATA__',embedded)+'\n'


def comparable(data):
    return {k:v for k,v in data.items() if k!='source_revision'}


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--root',type=Path,default=ROOT)
    p.add_argument('--write',action='store_true')
    p.add_argument('--check',action='store_true')
    p.add_argument('--book',help='Book path or basename; prints dependency/ownership record')
    p.add_argument('--search',help='Search the generated map by book/function/prefix/proof ID')
    args=p.parse_args(argv);root=args.root.resolve()
    if args.book or args.search:
        path=root/'docs/books/map.json'
        if not path.is_file(): p.error('generate map first with --write')
        data=json.loads(path.read_text())
        term=(args.book or args.search).lower()
        matches=[b for b in data['books'] if (b['path']==term or Path(b['path']).stem==term)] if args.book else [b for b in data['books'] if term in json.dumps([b['path'],b['definitions'],b['namespaces'],b['proof_ids'],b['subsystem']]).lower()]
        print(json.dumps(matches,indent=2));return 0 if matches else 1
    data=build(root)
    folder=root/'docs/books';map_path=folder/'map.json';html_path=folder/'index.html'
    if args.write:
        folder.mkdir(parents=True,exist_ok=True)
        map_path.write_text(json.dumps(data,separators=(',',':'))+'\n');html_path.write_text(render_html(data))
    if args.check:
        if not map_path.is_file() or comparable(json.loads(map_path.read_text()))!=comparable(data) or not html_path.is_file() or html_path.read_text()!=render_html(data):
            print('Book navigator stale: python3 tools/book_navigator.py --write',file=sys.stderr);return 1
    print(f"Book navigator: {data['canonical_count']} tracked books, {data['canonical_lines']} lines; {len(data['roots'])} root records, {len(data['warnings'])} explicit gaps, {len(data['candidates'])} review candidates.")
    return 0


if __name__=='__main__':
    raise SystemExit(main())
