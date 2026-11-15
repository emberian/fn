"""Read exact fetch-closure source/cache coordinates without launching ACL2.

Remote mode validates candidate metadata/payload integrity beneath ten supplied keys.
It does not install, publish, synchronize, resolve pairs, or submit a job.
"""
from pathlib import Path
import argparse
import json
import shlex
import subprocess
import certs
ROOT=Path(__file__).resolve().parents[1]
BASE='a1dba5a1c7bd303ba6085c589b9020c357624079'
TID='8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c'
REMOTE=r'''import json,sys
from pathlib import Path
cache=Path(sys.argv[1]);root=Path(sys.argv[2]);tid=sys.argv[3]
sys.path.insert(0,str(root/'tools'));import certs
rows=json.load(sys.stdin);out=[]
for row in rows:
 key=row['plain_closure_key']
 es=certs.cached_entries(cache,key,lambda m:m.get('toolchain_identity')==tid and bool(m.get('fasl_sha256')) and certs.usable_origin(m,str(root)))
 chosen=certs.choose_entry(es,str(root));selected=None
 if chosen:
  path,m=chosen
  selected={k:m.get(k) for k in ['toolchain_identity','origin_root','origin_kind','published_at','cert_sha256','fasl_sha256','key_version']}
  selected['coordinate']=str(path)
 out.append(dict(book=row['book'],plain_closure_key=key,key_directory_exists=(cache/key).is_dir(),selected=selected))
print(json.dumps(dict(cache_root_exists=cache.is_dir(),tools_root=str(root),rows=out)))'''


def inventory(root=ROOT):
 required=certs.closure(root,'books/pool-digest')
 rows=[]
 for book in sorted(required):
  key,listing=certs.closure_key(root,book)
  rows.append(dict(book=book,source_sha256=required[book],form_sha256=certs.form_hash(root/(book+'.lisp')),plain_closure_key=key,local_include_count=len(listing)))
 return dict(base=BASE,scope='plain-world exact local closure; cache inventory only, no ACL2/pair-alist/install qualification',books=rows)

def local(rows):
 cache=certs.cache_directory();out=[]
 for row in rows:
  entries=[];base=cache/row['plain_closure_key']
  if base.is_dir():
   for path in sorted(base.iterdir()):
    if not path.is_dir():continue
    m=certs.read_meta(path)
    if not m:continue
    e={k:m.get(k) for k in ['toolchain_identity','origin_root','origin_kind','published_at','cert_sha256','fasl_sha256','key_version']}
    e.update(coordinate=str(path.relative_to(cache)),integrity_hashes_match=certs.entry_matches_meta(path,m),portable_origin_usable=certs.usable_origin(m,str(ROOT)))
    entries.append(e)
  out.append(dict(book=row['book'],plain_closure_key=row['plain_closure_key'],entries=entries))
 return dict(cache=str(cache),entries=out)

def remote(rows,host,cache,tools_root):
 command='python3 -c '+shlex.quote(REMOTE)+' '+shlex.quote(cache)+' '+shlex.quote(tools_root)+' '+shlex.quote(TID)
 try:
  p=subprocess.run(['ssh','-o','BatchMode=yes','-o','ConnectTimeout=5',host,command],input=json.dumps(rows),text=True,capture_output=True,timeout=20)
  if p.returncode:return dict(error=p.stderr.strip(),returncode=p.returncode)
  result=json.loads(p.stdout)
  return dict(cache=cache,cache_root_exists=result['cache_root_exists'],entries=result['rows'],tools_root=result['tools_root'],validation='certs.cached_entries metadata/payload integrity and origin candidate selection only; no install or pair probe')
 except (subprocess.TimeoutExpired,ValueError) as e:return dict(error=str(e))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--remote',action='store_true');p.add_argument('--output',type=Path);p.add_argument('--remote-tools-root',default='/build/lanes/ticket-frontier-3b62')
 a=p.parse_args();r=inventory();r['local_cache']=local(r['books'])
 if a.remote:
  r['record_caches']={'forge':remote(r['books'],'fn@forge','/home/fn/.cache/fn-certs',a.remote_tools_root)}
 text=json.dumps(r,indent=2)+'\n'
 if a.output:a.output.write_text(text)
 else:print(text,end='')
