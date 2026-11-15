#!/usr/bin/env python3
"""Parameterize canonical sufficient-summary storage, preserving active row zero.
Uses the shared Lisp reader; refuses unknown targeted definition/call shapes.
"""
from pathlib import Path
import lisp_rewrite as lr
PREFIX='fn2-checkpoint-summary-authority'
NAMES={'descriptor-p':'descriptor-p','current-p':'row-current-p','complete-p':'row-complete-p',
       'frontier-word':'row-frontier-word','cut-seal-word':'row-cut-seal-word'}
ARRAYS={'descriptori':32,'frontieri':480,'cut-seali':8}
def text_of(source,node): return source[node.start:node.end]
def parameterize_reader(source, suffix):
    parsed=lr.parse(source)
    found=lr.match(f'(defun {PREFIX}-{suffix} ?args ?*body)',parsed.forms,deep=False)
    if len(found)!=1: raise ValueError('expected one reader '+suffix)
    fn=found[0].node
    edits=[(fn.items[1].start,fn.items[1].end,PREFIX+'-'+NAMES[suffix])]
    args=fn.items[2];edits.append((args.start,args.start+1,'(r '))
    # Body/declare recursive calls all receive the same record index.
    for call in lr.match('(?head ?*args)',[fn]):
        node=call.node
        if not node.items or not hasattr(node.items[0],'low'): continue
        head=node.items[0].low
        if head in {PREFIX+'-'+x for x in NAMES}:
            name=head[len(PREFIX)+1:]
            edits.append((node.items[0].start,node.items[0].end,PREFIX+'-'+NAMES[name]))
            edits.append((node.items[0].end,node.items[0].end,' r'))
        elif head in {PREFIX+'-'+x for x in ARRAYS}:
            name=head[len(PREFIX)+1:];index=node.items[1]
            edits.append((index.start,index.end,f'(+ (* {ARRAYS[name]} r) {text_of(source,index)})'))
        elif head.startswith(PREFIX+'-') and len(node.items)==3 and getattr(node.items[1],'low',None)=='0' and getattr(node.items[2],'low',None)==PREFIX:
            edits.append((node.items[1].start,node.items[1].end,'r'))
    # Guard record indexing in descriptor recursion; current-p checks before use.
    if suffix=='descriptor-p':
        wfp=lr.match(f'({PREFIX}-wfp {PREFIX})',[fn])[0].node
        edits.append((wfp.end,wfp.end,' (natp r) (< r 2) (< r ('+PREFIX+'-rows '+PREFIX+'))'))
    if suffix=='current-p':
        body=fn.items[-1]
        if getattr(body.items[0],'low',None)!='and': raise ValueError('current reader body is not AND')
        edits.append((body.items[0].end,body.items[0].end,' (natp r) (< r 2) (< r ('+PREFIX+'-rows '+PREFIX+'))'))
    return lr.write(source,edits)
def rewrite_state(source):
    for suffix in NAMES: source=parameterize_reader(source,suffix)
    source=source.replace('(array (unsigned-byte 8) (32))','(array (unsigned-byte 8) (64))')
    source=source.replace('(array (unsigned-byte 32) (480))','(array (unsigned-byte 32) (960))')
    source=source.replace('(array (unsigned-byte 32) (8))','(array (unsigned-byte 32) (16))')
    source=source.replace('Exact descriptor identity of the sufficient summary, not a slot number.','Two disjoint exact descriptors: active base and sole inflight live summary.')
    source=source.replace('Sixty authenticated semantic-member peaks, eight little-endian words per peak.','Per active/pending record: sixty authenticated peaks of eight words.')
    source=source.replace('Physical predecessor at cut C, distinct from descriptor and later installation J.','Per active/pending record: physical cut-C predecessor, distinct from descriptor or installation J.')
    wrappers=[]
    signatures={'current-p':'','complete-p':'','frontier-word':'level i ','cut-seal-word':'i '}
    for suffix, scalar in signatures.items():
        args=scalar+PREFIX+' fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes'
        wrappers.append(f'''(defun {PREFIX}-{suffix} ({args})
 (declare (xargs :stobjs ({PREFIX} fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
 :guard (and ({PREFIX}-wfp {PREFIX}) (fn2-checkpoints-wfp fn2-checkpoints)
             (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 ({PREFIX}-{NAMES[suffix]} 0 {args}))
''')
    return source+'\n; Active record0 readers retain the prior API. Pending record1 is independent.\n'+''.join(wrappers)
def pending_live(source):
    edits=[]
    for match in lr.match('(?head ?*args)',lr.parse(source).forms):
        node=match.node
        if not node.items or not hasattr(node.items[0],'low'):continue
        head=node.items[0].low
        if head==PREFIX+'-current-p':
            edits.append((node.items[0].start,node.items[0].end,PREFIX+'-row-current-p'))
            edits.append((node.items[0].end,node.items[0].end,' 1'))
        elif (head==PREFIX+'-put' or (head.startswith(PREFIX+'-') and len(node.items)==3 and getattr(node.items[-1],'low',None)==PREFIX)) and getattr(node.items[1],'low',None)=='0':
            if head.endswith('-rows'):continue
            edits.append((node.items[1].start,node.items[1].end,'1'))
        elif head.startswith('update-'+PREFIX+'-'):
            name=head[len('update-'+PREFIX+'-'):]
            if name in ARRAYS:
                index=node.items[1]
                edits.append((index.start,index.end,f'(+ {ARRAYS[name]} {text_of(source,index)})'))
    source=lr.write(source,edits)
    source=source.replace('(< 0 ('+PREFIX+'-rows '+PREFIX+'))','(< 1 ('+PREFIX+'-rows '+PREFIX+'))')
    return source
if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]
    state=root/'books/checkpoint-summary-authority-state.lisp';live=root/'books/checkpoint-summary-authority-live.lisp'
    state.write_text(rewrite_state(state.read_text()))
    live.write_text(pending_live(live.read_text()))

def bind_live_publication_lifecycle(source):
    """Bind the actual producer publication phase; never require nonexistent PROMOTED."""
    edits=[]
    for m in lr.match('(?head ?*args)',lr.parse(source).forms):
        n=m.node
        if not n.items or not hasattr(n.items[0],'low'):continue
        h=n.items[0].low
        if h==PREFIX or h==PREFIX+'-live-source-p':
            if any(getattr(x,'low',None)=='fn2-checkpoint-lifecycle' for x in n.items):raise ValueError('already lifecycle-bound')
            if any(getattr(x,'low',None)=='fn2-checkpoint-source' for x in n.items):
                edits.append((n.items[-1].end,n.items[-1].end,' fn2-checkpoint-lifecycle'))
        elif h=='fn2-checkpoint-publication-wfp':
            edits.append((n.end,n.end,' (fn2-checkpoint-lifecycle-wfp fn2-checkpoint-lifecycle)'))
        elif h=='fn2-core-checkpoint-summary-authority':
            edits.append((n.items[-1].end,n.items[-1].end,' fn2-core-checkpoint-lifecycle'))
    source=lr.write(source,edits)
    source=source.replace('(= (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-promoted*)',
      '''(= (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-installed*)
        (fn2-checkpoint-lifecycle-ownerp c (fn2-checkpoint-source-token 0 fn2-checkpoint-source)
         (fn2-checkpoint-source-owner-kind 0 fn2-checkpoint-source) (fn2-checkpoint-source-owner-slot 0 fn2-checkpoint-source)
         (fn2-checkpoint-source-owner-gen 0 fn2-checkpoint-source) fn2-checkpoint-lifecycle)
        (= (fn2-checkpoint-lifecycle-phase 0 fn2-checkpoint-lifecycle) *fn2-checkpoint-lifecycle-phase-publication*)''')
    return source
