from pathlib import Path
import json,subprocess,sys,tempfile,unittest
ROOT=Path(__file__).resolve().parents[1]
class Geometry(unittest.TestCase):
 def test_scoped_and_idempotent(self):
  f=json.loads((ROOT/'tools/fixtures/successor_geometry.json').read_text())
  with tempfile.TemporaryDirectory() as temp:
   root=Path(temp)
   for p,s in f['before'].items():
    dest=root/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(s)
   for repeat in range(2):
    subprocess.run([sys.executable,str(ROOT/'tools/rewrite_successor_geometry.py')],cwd=root,check=True,capture_output=True)
    for p,s in f['after'].items():self.assertEqual((root/p).read_text(),s,p)
 def test_actual_root_replay(self):
  base='c2d28dd9677757a24847763a3e8a9893de464eec'
  names=['machines-c.lisp','machines-c-successor.lisp','successor-workspace-geometry.lisp','successor-schema-geometry.lisp']
  with tempfile.TemporaryDirectory() as temp:
   root=Path(temp);(root/'books').mkdir()
   for name in names[:2]:
    (root/'books'/name).write_bytes(subprocess.check_output(['git','show',base+':books/'+name],cwd=ROOT))
   for repeat in range(2):
    subprocess.run([sys.executable,str(ROOT/'tools/rewrite_successor_geometry.py')],cwd=root,check=True,capture_output=True)
    for name in names:
     current=(ROOT/'books'/name).read_text()
     follow=ROOT/'tools/fixtures/identity-workspace-profile-extraction.json'
     if follow.exists():
      paired=json.loads(follow.read_text())
      if 'books/'+name in paired['books']:
       self.assertEqual(current.count(paired['new']),1)
       current=current.replace(paired['new'],paired['old'])
       if name=='machines-c.lisp':
        self.assertEqual(current.count(paired['include']),1)
        current=current.replace(paired['include'],'',1)
     self.assertEqual((root/'books'/name).read_text(),current,name)
if __name__=='__main__':unittest.main()
