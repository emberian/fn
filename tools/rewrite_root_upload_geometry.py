#!/usr/bin/env python3
"""Extract ROOT's actual forms, never the cold donor's 12KiB policy.

Run once from the unmodified 07e40b063 source. Production forms are selected
through lisp_rewrite and moved byte-for-byte; the receipt retains originals.
"""
from pathlib import Path
import hashlib,json,re
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]

def atom(n): return n.text.lower() if isinstance(n,lr.Atom) else ''
def raw(n,src): return src.text[n.start:n.end]

def extract():
    paths=['books/upload-kind.lisp','books/article-manifest.lisp','books/upload.lisp','books/ordered.lisp']
    sources={p:lr.parse(ROOT/p) for p in paths}; edits={p:[] for p in paths}
    receipt={'baseline':'07e40b063','moves':[],'rewrites':[],'physical_geometry':[]}
    def move(path,head,name=None,needle=None):
        hits=[n for n in sources[path].forms if isinstance(n,lr.Lst) and n.items and atom(n.items[0])==head
              and (name is None or len(n.items)>1 and atom(n.items[1])==name)
              and (needle is None or needle in raw(n,sources[path]))]
        if len(hits)!=1:raise ValueError((path,head,name,needle,len(hits)))
        n=hits[0];form=raw(n,sources[path]);edits[path].append((n.start,n.end,''))
        receipt['moves'].append({'source':path,'target':target,'head':head,'name':name,'needle':needle,
                                'form':form,'sha256':hashlib.sha256(form.encode()).hexdigest()})
        return form
    target='books/source-manifest-codec.lisp';codec=[]
    for name in ['*fn2-am-block-bytes*','*fn2-am-header-max*','*fn2-am-entry-max*','*fn2-am-entries-per-unit*','*fn2-am-stored-max*']:
        codec.append(move(paths[0],'defconst',name))
    codec.append(move(paths[0],'assert-event',needle='(equal *fn2-am-stored-max* 380928)'))
    for name in ['*fn2-am-header-fields*','*fn2-am-entry-fields*']:codec.append(move(paths[1],'defconst',name))
    for needle in ['(equal *fn2-am-entries-per-unit* 31)','(<= *fn2-am-entry-max* *fn2-commit-unit-bytes*)']:
        codec.append(move(paths[1],'assert-event',needle=needle))
    for head,name in [('defun','fn2-am-blocks'),('defun','fn2-am-units'),('defthm','fn2-am-units-natp'),
                      ('defun','fn2-am-manifestp'),('defun','fn2-am-fits')]:codec.append(move(paths[1],head,name))
    codec.append(move(paths[1],'assert-event',needle='(fn2-am-fits *fn2-am-stored-max*)'))
    for head,name in [('defun','fn2-am-entry-at'),('defthm','fn2-am-entry-at-natp'),('defthm','fn2-am-entry-at-bound')]:
        codec.append(move(paths[1],head,name))
    codec.append(move(paths[1],'in-theory',needle='fn2-am-blocks fn2-am-units'))
    codec.append('(local (in-theory (disable fn2-fields-rows fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-pool-rows)))')
    for prefix in ['entry','header']:
        name='fn2-am-get-'+prefix
        for head,n in [('defun',name),('fn2-fc-shape',name+'-shape'),('defthm',name+('-naturals' if prefix=='entry' else '-natp'))]:
            codec.append(move(paths[1],head,n))
        codec.append(move(paths[1],'in-theory',needle='(disable '+name+')'))
    (ROOT/target).write_text('; Actual ROOT source-manifest geometry and readers, shared below C and D.\n'
                           '; The physical 64KiB manifest threshold is unchanged.\n(in-package "ACL2")\n'
                           '(include-book "commit-format")\n(fn2-book-layer :b)\n\n'+'\n\n'.join(codec)+'\n')
    target='books/upload-page-geometry.lisp';page=[move(paths[3],'defconst','*fn2-article-location-hashes-max*')]
    for name in ['*fn2-upload-chunk-class*','*fn2-upload-article-max*','*fn2-upload-digest-octets*',
                 '*fn2-upload-mid-field-octets*','*fn2-upload-mid-template*','*fn2-upload-mid-close*','*fn2-upload-op-mid-template*']:
        page.append(move(paths[0],'defconst',name))
    page.append(move(paths[0],'assert-event',needle='(<= (length *fn2-upload-op-mid-template*)'))
    page.append(move(paths[0],'defconst','*fn2-upload-mid-line-max*'))
    page.append(move(paths[0],'assert-event',needle='(equal (- *fn2-upload-mid-line-max*'))
    page.append(move(paths[0],'assert-event',needle='(<= (+ *fn2-upload-article-max*'))
    for name in ['*fn2-upload-page-stored-source*','*fn2-upload-page-location-hashes*','*fn2-upload-page-stage*',
                 '*fn2-upload-page-hash*','*fn2-upload-page-manifest*','*fn2-upload-head-bytes*','*fn2-upload-entry-bytes*']:
        page.append(move(paths[2],'defconst',name))
    page.append(move(paths[2],'defun','fn2-upload-page-bytes'))
    helpers='''; These scalar decisions are consumed by the actual input configuration
; and upload producer as well as resource admission.
(defun fn2-upload-profile-article-max (profile)
 (declare (xargs :guard t))
 (let ((max (fn2-profile-get :article-max profile)))
  (if (unsigned-byte-p 32 max) max *fn2-upload-article-max*)))
(defun fn2-upload-input-bound (article-max cap0 cap1)
 (declare (xargs :guard t))
 (min (nfix article-max) (nfix (- (+ (nfix cap0) (nfix cap1)) (+ 1 *fn2-upload-digest-octets*)))))
(defun fn2-upload-article-profilep (profile)
 (declare (xargs :guard t))
 (or (null (fn2-profile-get :article-max profile))
     (and (natp (fn2-profile-get :article-max profile))
          (<= (+ (fn2-profile-get :article-max profile) *fn2-upload-mid-line-max*) *fn2-am-stored-max*))))
'''
    (ROOT/target).write_text('; Shared actual ROOT upload sizing; no cold payload-policy change.\n(in-package "ACL2")\n'
                           '(include-book "profile")\n(include-book "source-manifest-codec")\n(fn2-book-layer :b)\n\n'
                           +'\n\n'.join(page)+'\n\n'+helpers)
    for path,src in sources.items():(ROOT/path).write_text(lr.write(src.text,edits[path]))
    changes={paths[2]:[('fn2-upload-bound',
      [('(min (nfix max) (nfix (- (+ (nfix cap0) (nfix cap1)) (+ 1 *fn2-upload-digest-octets*))))','(fn2-upload-input-bound max cap0 cap1)')])],
     paths[0]:[('fn2-input-config-profilep',[(
      '(or (null (fn2-profile-get :article-max profile))\n           (and (natp (fn2-profile-get :article-max profile))\n                (<= (+ (fn2-profile-get :article-max profile) *fn2-upload-mid-line-max*) *fn2-am-stored-max*)))',
      '(fn2-upload-article-profilep profile)')]),
      ('fn2-input-config-from',[
       ('\n         (max (fn2-profile-get :article-max profile))',''),
       ('(if (unsigned-byte-p 32 max) max *fn2-upload-article-max*)','(fn2-upload-profile-article-max profile)')])]}
    for path,rows in changes.items():
        src=lr.parse(ROOT/path);replacements=[]
        for name,swaps in rows:
            hit=lr.match('_',src.forms,deep=True,head='defun',name=name)
            if len(hit)!=1:raise ValueError(name)
            old=raw(hit[0].node,src);new=old
            for a,b in swaps:
                if new.count(a)!=1:raise ValueError((name,a))
                new=new.replace(a,b)
            receipt['rewrites'].append({'book':path,'name':name,'original':old,'sha256':hashlib.sha256(old.encode()).hexdigest(),'substitutions':swaps})
            replacements.append((hit[0].start,hit[0].end,new))
        (ROOT/path).write_text(lr.write(src.text,replacements))
    for path,include in [(paths[0],'upload-page-geometry'),(paths[1],'source-manifest-codec'),(paths[2],'upload-page-geometry'),(paths[3],'upload-page-geometry')]:
        p=ROOT/path;s=p.read_text();at=s.index('(fn2-book-layer')
        s=s[:at]+'(include-book "'+include+'")\n'+s[at:];p.write_text(s)
    for path in paths:
        p=ROOT/path
        p.write_text(re.sub(r'\n{3,}', '\n\n', p.read_text()).rstrip()+'\n')
    for path,name in [('books/commit-geometry.lisp','*fn2-commit-extent-bytes*'),('books/format-base.lisp','*fn2-storage-extent-bytes*'),('books/format-base.lisp','*fn2-format-page-size*')]:
        src=lr.parse(ROOT/path);hit=lr.match('_',src.forms,deep=False,head='defconst',name=name)
        if len(hit)!=1:raise ValueError(name)
        form=raw(hit[0].node,src);receipt['physical_geometry'].append({'book':path,'name':name,'form':form,'sha256':hashlib.sha256(form.encode()).hexdigest()})
    (ROOT/'tools/fixtures/root-upload-geometry-extraction.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt
if __name__=='__main__':
    r=extract();print('moved',len(r['moves']),'original ROOT forms; rewrote',len(r['rewrites']),'actual producer functions')
