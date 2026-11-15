"""Named configured resident/physical-bank C geometry projection."""
from pathlib import Path
import json
import lisp_rewrite as lr
DATA=json.loads((Path(__file__).parent/'fixtures/replacement-bank-c-source.json').read_text())
def once(text,old,new):
 if new in text:return text
 if text.count(old)!=1:raise ValueError('exact named boundary '+old[:80])
 return text.replace(old,new,1)
def event(text,head,name):
 ms=lr.match('('+head+' '+name+' ?*body)',lr.parse(text).forms,deep=False)
 if len(ms)!=1:raise ValueError('one event '+name)
 return ms[0].node

def _project_banks(book,text):
 if book=='runs':
  extras='''
 (fn2-run-installed-resident-limit :type (unsigned-byte 32) :initially 0 :why "Configured resident-only prefix R; never derived from physical bank occupancy.")
 (fn2-run-installed-bank-capacity :type (unsigned-byte 32) :initially 0 :why "Each of the two physical-only replacement banks has the configured E rows.")
 (fn2-run-installed-bank-configured :type (unsigned-byte 1) :initially 0 :why "Bare generated init cannot authorize physical-bank installation.")'''
  marker=' :extra-fields ((fn2-run-installed-physical-count'
  text=once(text,marker,' :extra-fields ('+extras+'\n (fn2-run-installed-physical-count')
  if '(defun fn2-run-installed-bank-geometry-p ' not in text:
   anchor=min((event(text,'defun',n) for n in ('fn2-run-install','fn2-run-install-physical')),key=lambda n:n.start);text=lr.write(text,[(anchor.start,anchor.start,DATA['helpers']+'\n')])
  for name,condition in (
   ('fn2-run-install','(and (natp r) (fn2-run-installed-bank-geometry-p fn2-run-installed) (< r (fn2-run-installed-resident-limit fn2-run-installed)))'),
   ('fn2-run-install-filter','(and (natp r) (fn2-run-installed-bank-geometry-p fn2-run-installed) (< r (fn2-run-installed-resident-limit fn2-run-installed)))'),
   ('fn2-run-install-units','(and (natp r) (fn2-run-installed-bank-geometry-p fn2-run-installed) (< r (fn2-run-installed-resident-limit fn2-run-installed)))'),
   ('fn2-run-retired-next','(and (natp r) (fn2-run-installed-bank-geometry-p fn2-run-installed) (< r (fn2-run-installed-resident-limit fn2-run-installed)))'),
   ('fn2-run-install-physical','(or (fn2-run-installed-bank-row-p 0 r fn2-run-installed) (fn2-run-installed-bank-row-p 1 r fn2-run-installed))'),
   ('fn2-run-free-physical','(or (fn2-run-installed-bank-row-p 0 r fn2-run-installed) (fn2-run-installed-bank-row-p 1 r fn2-run-installed))')):
   a=event(text,'defun',name);src=text[a.start:a.end]
   old='(and (natp r) (< r (fn2-run-installed-rows fn2-run-installed))'
   new='(and '+condition+' (natp r) (< r (fn2-run-installed-rows fn2-run-installed))'
   out=once(src,old,new);text=lr.write(text,[(a.start,a.end,out)])
  return text
 if book=='machines-c':
  old='(fn2-run-installed-init (+ (fn2-b-capacity :identity-runs 64 profile) (fn2-b-capacity :extent-slots 16 profile)) fn2-run-installed)'
  new='(fn2-run-installed-init-configured (fn2-b-capacity :identity-runs 64 profile) (fn2-b-capacity :extent-slots 16 profile) fn2-run-installed)'
  text=once(text,old,new)
  old='(unsigned-byte-p 32 (+ (fn2-b-capacity :identity-runs 64 profile) (fn2-b-capacity :extent-slots 16 profile)))'
  new='(and (posp (fn2-b-capacity :extent-slots 16 profile)) (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile)) (unsigned-byte-p 32 (fn2-run-installed-row-count (fn2-b-capacity :identity-runs 64 profile) (fn2-b-capacity :extent-slots 16 profile))))'
  if new in text:return text
  if old in text:return once(text,old,new)
  # Older actual C profile declarations checked R alone. Add the SAME new
  # canonical R+2E admission; do not silently retain the weaker old guard.
  f=event(text,'defun','fn2-idc-profilep');part=text[f.start:f.end]
  anchor='(unsigned-byte-p 32 (fn2-b-capacity :identity-runs 64 profile))'
  if part.count(anchor)!=1:raise ValueError('actual resident profile guard')
  return lr.write(text,[(f.start,f.end,part.replace(anchor,anchor+'\n      '+new,1))])
 if book=='sealer':
  for name in ('fn2-seal-free-rows','fn2-seal-free-row','fn2-seal-retired-row'):
   a=event(text,'defun',name);src=text[a.start:a.end]
   old='(< r (fn2-run-installed-rows fn2-run-installed))'
   new='(and (< r (fn2-run-installed-rows fn2-run-installed)) (< r (fn2-run-installed-resident-limit fn2-run-installed)))'
   out=once(src,old,new);text=lr.write(text,[(a.start,a.end,out)])
  a=event(text,'defun','fn2-seal-install-run');src=text[a.start:a.end]
  out=once(src,'(rows (fn2-run-installed-rows fn2-run-installed))','(rows (fn2-run-installed-resident-limit fn2-run-installed))')
  return lr.write(text,[(a.start,a.end,out)])
 if book=='checkpoint-summary-apply':
  text=once(text,'(<= (fn2-checkpoint-summary-count 0 fn2-checkpoint-summary) (fn2-run-installed-rows fn2-run-installed))','(and (fn2-run-installed-bank-geometry-p fn2-run-installed) (= (fn2-checkpoint-summary-bank 0 fn2-checkpoint-summary) 0) (<= (fn2-checkpoint-summary-count 0 fn2-checkpoint-summary) (fn2-run-installed-bank-capacity fn2-run-installed)))')
  text=once(text,'(r (nfix (- rank 1)))','(r (+ (fn2-run-installed-bank-start 0 fn2-run-installed) (nfix (- rank 1))))')
  text=once(text,'(< r (fn2-run-installed-rows fn2-run-installed))','(fn2-run-installed-bank-row-p 0 r fn2-run-installed)')
  return text
 if book in ('range','sealer-unit'):
  edits=[]
  for m in lr.match('(fn2-run-installed-init ?resident fn2-run-installed)',lr.parse(text).forms,deep=True):
   arg=m.captures['resident'];resident=text[arg.start:arg.end]
   edits.append((m.node.start,m.node.end,'(fn2-run-installed-init-configured '+resident+' 1 fn2-run-installed)'))
  return lr.write(text,edits)
 raise ValueError(book)
def project_row_count(book,text):
 if book=='run-geometry':
  return once(text,'(include-book "format-base")','(include-book "format-base")\n(include-book "run-installed-geometry")')
 names={'runs':('fn2-run-installed-bank-geometry-p','fn2-run-installed-init-configured'),'machines-c':('fn2-idc-profilep',)}.get(book,())
 edits=[]
 for name in names:
  f=event(text,'defun',name)
  for m in lr.match('(+ ?resident (* 2 ?capacity))',[f],deep=True):
   r=m.captures['resident'];e=m.captures['capacity']
   edits.append((m.node.start,m.node.end,'(fn2-run-installed-row-count '+text[r.start:r.end]+' '+text[e.start:e.end]+')'))
 return lr.write(text,edits)
def project(book,text):
 if book=='run-geometry':return project_row_count(book,text)
 return project_row_count(book,_project_banks(book,text))
if __name__=='__main__':
 for book in ('run-geometry','runs','machines-c','sealer','range'):
  p=Path(__file__).resolve().parents[1]/'books'/(book+'.lisp');text=p.read_text();p.write_text(project(book,text))
 p=Path(__file__).resolve().parents[1]/'tests/sealer-unit.lisp';text=p.read_text();p.write_text(project('sealer-unit',text))
