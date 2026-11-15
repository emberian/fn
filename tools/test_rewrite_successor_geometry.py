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
if __name__=='__main__':unittest.main()
