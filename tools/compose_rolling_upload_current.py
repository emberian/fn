#!/usr/bin/env python3
"""Compose owned rolling source onto the current ROOT extraction.

Critical shared compiler/access files are separate named-hunk donors. This
script never writes them or checkpoint/pool/service/transport source.
"""
from pathlib import Path
import subprocess
import lisp_rewrite as lr
AUTHOR='af3ab4c00'
GEOMETRY='d51a39aba'
def read(rev,path):return subprocess.check_output(['git','show',rev+':'+path],text=True)
def named(text,tag,name):
 matches=lr.match('('+tag+' '+name+' ?*body)',lr.parse(text).forms)
 assert len(matches)==1,(tag,name,len(matches))
 return matches[0]
def fragment(text,tag,name):
 m=named(text,tag,name);return text[m.start:m.end]
def replace(text,tag,name,value):
 m=named(text,tag,name);return lr.write(text,[(m.start,m.end,value)])
def consts(text):
 p=lr.parse(text);out={}
 for tag in ['defconst','defun']:
  for m in lr.match('('+tag+' ?name ?*body)',p.forms):
   if isinstance(m.captures['name'],lr.Atom):out[(tag,m.captures['name'].text.lower())]=text[m.start:m.end]
 return out
def canon(s):return lr.emit(lr.parse(s).forms[0],drop_comments=True)
def upper_cut(text,lower):
 edits=[]
 for (tag,name),body in lower.items():
  matches=lr.match('('+tag+' '+name+' ?*body)',lr.parse(text).forms)
  if not matches:continue
  assert len(matches)==1,(tag,name)
  m=matches[0]
  assert canon(text[m.start:m.end])==canon(body),('moved form changed',tag,name)
  edits.append((m.start,m.end,''))
 text=lr.write(text,edits)
 # Duplicate unchanged assertions move with their authoritative constants.
 # Keep unrelated new budget/geometry assertions in the producer.
 assertions=set()
 for path in ['books/source-manifest-codec.lisp','books/upload-page-geometry.lisp','books/upload-window-geometry.lisp']:
  t=Path(path).read_text()
  for m in lr.match('(assert-event ?*body)',lr.parse(t).forms):assertions.add(canon(t[m.start:m.end]))
 edits=[]
 for m in lr.match('(assert-event ?*body)',lr.parse(text).forms):
  if canon(text[m.start:m.end]) in assertions:edits.append((m.start,m.end,''))
 return lr.write(text,edits)
def main():
 # The original ROOT codec/page extraction is already applied. These exact
 # author-owned leaves add only the explicit d51 followup policy/geometry.
 for path in ['books/source-manifest-codec.lisp','books/upload-page-geometry.lisp','books/upload-window-geometry.lisp']:
  Path(path).write_text(read(GEOMETRY,path))
 lower={}
 for path in ['books/source-manifest-codec.lisp','books/upload-page-geometry.lisp','books/upload-window-geometry.lisp']:
  lower.update(consts(Path(path).read_text()))
 old_kind=Path('books/upload-kind.lisp').read_text()
 old_upload=Path('books/upload.lisp').read_text()
 # Preserve ROOT's actual shared profile/bound consumers rather than
 # restoring parallel upper formulas from the pre-extraction author lane.
 keep_kind={n:fragment(old_kind,'defun',n) for n in ['fn2-input-config-profilep','fn2-input-config-from']}
 keep_bound=fragment(old_upload,'defun','fn2-upload-bound')
 for path in ['books/upload-kind.lisp','books/upload.lisp','books/upload-stream.lisp']:
  text=upper_cut(read(AUTHOR,path),lower)
  if path.endswith('upload-kind.lisp'):
   for name,body in keep_kind.items():text=replace(text,'defun',name,body)
   text=text.replace('(include-book "upload-window-geometry")','(include-book "upload-window-geometry")\n(include-book "upload-page-geometry")')
  elif path.endswith('upload.lisp'):
   text=replace(text,'defun','fn2-upload-bound',keep_bound)
   text=text.replace('(include-book "upload-kind")','(include-book "upload-kind")\n(include-book "upload-page-geometry")')
  else:
   text=text.replace('(include-book "upload-stream-stage")','(include-book "upload-stream-stage")\n(include-book "upload-page-geometry")')
  if path.endswith('upload-stream.lisp'):
   text=text.replace('(in-package "ACL2")','(in-package "ACL2")\n(include-book "std/util/bstar" :dir :system)')
  Path(path).write_text(text)
 # These files are solely the owned upload producer/continuations; the
 # unrelated ROOT machine/protocol/compiler books are not replaced.
 for path in ['books/upload-feed.lisp','books/upload-scan.lisp','books/assembly-callbacks-d-upload.lisp',
              'books/txn-kind.lisp','books/txn.lisp','books/upload-stream-stage.lisp',
              'books/upload-stream-manifest.lisp','books/upload-stream-reset.lisp','books/upload-stream-settle.lisp']:
  text=read(AUTHOR,path)
  if path.endswith('upload-stream-stage.lisp'):
   text=text.replace('(in-package "ACL2")','(in-package "ACL2")\n(include-book "std/util/bstar" :dir :system)')
  Path(path).write_text(text)
 # Shared D protocol book: exactly the two owned feed wrappers.
 path='books/assembly-callbacks-d.lisp';text=Path(path).read_text();source=read(AUTHOR,path)
 for name in ['fn2-upload-feed-pool','fn2-upload-feed-run']:
  text=replace(text,'defun',name,fragment(source,'defun',name))
 Path(path).write_text(text)
 # Shared ordered C code: one unchanged constant move, all other bytes kept.
 path='books/ordered.lisp';text=Path(path).read_text()
 m=named(text,'defconst','*fn2-overview-octets-max*')
 assert canon(text[m.start:m.end])==canon(lower[('defconst','*fn2-overview-octets-max*')])
 text=lr.write(text,[(m.start,m.end,'')])
 anchor='(in-package "ACL2")';assert text.count(anchor)==1
 text=text.replace(anchor,anchor+'\n(include-book "upload-window-geometry")')
 Path(path).write_text(text)
 # Paired physical decoder fixes: named bodies only, no recovery-machine or
 # boot selector/release changes.
 path='books/recovery-payload.lisp';text=Path(path).read_text();source=read(AUTHOR,path)
 for name in ['fn2-recovery-claim-article','fn2-rp-entries']:
  text=replace(text,'defun',name,fragment(source,'defun',name))
 Path(path).write_text(text)
 # Authoritative paired2W+CNS geometry, scoped to the original format
 # section. No commit directory, allocator pin or checkpoint child change.
 path='books/machines-b.lisp';text=Path(path).read_text();source=read(AUTHOR,path)
 a='(defun fn2-b-upload-windows (profile)';b='(defcorechild fn2-core-fc fn2-fc'
 assert text.count(a)==source.count(a)==text.count(b)==source.count(b)==1
 ta,tb=text.index(a),text.index(b);sa,sb=source.index(a),source.index(b)
 allowed={'fn2-b-ctl-slot','fn2-b-format-floor','fn2-b-ctl-runtime-row'}
 for m in lr.match('(defun ?name ?*body)',lr.parse(text[ta:tb]).forms):
  name=m.captures['name'].text
  if name not in allowed:
   assert canon(text[ta:tb][m.start:m.end])==canon(fragment(source[sa:sb],'defun',name)),name
 text=text[:ta]+source[sa:sb]+text[tb:]
 text=replace(text,'defun','fn2-b-alloc-edge-floor',fragment(source,'defun','fn2-b-alloc-edge-floor'))
 Path(path).write_text(text)
 # Exactly the stable paired sealer hunk; keep all other C sealer changes.
 patch=subprocess.check_output(['git','diff','0506c97c9^','0506c97c9','--','books/machines-c-sealer.lisp'])
 subprocess.run(['git','apply','--check'],input=patch,check=True)
 subprocess.run(['git','apply'],input=patch,check=True)
 # Direct constructor control in the historical helper book: one call only.
 path='books/owed-cursor.lisp';text=Path(path).read_text();source=read(AUTHOR,path)
 old=lr.match('(fn2-txn-put-post-for ?*args)',lr.parse(text).forms)
 new=lr.match('(fn2-txn-put-post-for ?*args)',lr.parse(source).forms)
 assert len(old)==len(new)==1
 text=lr.write(text,[(old[0].start,old[0].end,source[new[0].start:new[0].end])])
 Path(path).write_text(text)
if __name__=='__main__':main()
