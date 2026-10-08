"""Read-only train-31 control for the lock gate; no checkout or baseline edit."""
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools'))
import lock_discipline_check as check
read=Path.read_text
cache={}
def from_train(path,*args,**kwargs):
 try: rel=path.resolve().relative_to(ROOT).as_posix()
 except ValueError: return read(path,*args,**kwargs)
 if rel not in cache:
  r=subprocess.run(['git','show','4976a4b53:'+rel],cwd=ROOT,text=True,capture_output=True,timeout=10)
  cache[rel]=r.stdout if r.returncode==0 else None
 return cache[rel] if cache[rel] is not None else read(path,*args,**kwargs)
Path.read_text=from_train
sys.exit(check.main())
