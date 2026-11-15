"""Pin the SAME actual rolling producer sizing and explicit policy change."""
from pathlib import Path
import hashlib,json,unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def get(text,head,name=None,needle=None):
    nodes=[n for n in lr.parse(text).forms if isinstance(n,lr.Lst) and n.items and getattr(n.items[0],'text','').lower()==head]
    if name:nodes=[n for n in nodes if len(n.items)>1 and getattr(n.items[1],'text','')==name]
    if needle:nodes=[n for n in nodes if needle in text[n.start:n.end]]
    assert len(nodes)==1,(head,name,needle,len(nodes));n=nodes[0];return text[n.start:n.end]
class StreamPage(unittest.TestCase):
 def test_actual_moved_forms_exact(self):
    r=json.loads((ROOT/'tools/fixtures/upload-stream-page-composition.json').read_text())
    self.assertEqual(r['actual_producer'],'522e12181')
    for row in r['moves']:
        self.assertEqual(hashlib.sha256(row['form'].encode()).hexdigest(),row['sha256'])
        self.assertEqual(get((ROOT/row['target']).read_text(),row['head'],row['name'],row['needle']),row['form'])
 def test_policy_changes_are_explicit_and_upper_bound_matches(self):
    r=json.loads((ROOT/'tools/fixtures/upload-stream-page-composition.json').read_text())
    for row in r['policies']:
        self.assertNotEqual(row['old'],row['new'])
        self.assertEqual(get((ROOT/row['book']).read_text(),row['head'],row['name']),row['new'])
        if row['name']=='fn2-upload-input-bound':
            self.assertEqual(len(lr.match('(nfix max)',lr.parse(row['actual_upper']).forms,deep=True)),1)
            self.assertIn('(nfix article-max)',row['new'])
    old=r['previous_policy_fixture']
    self.assertEqual(hashlib.sha256(old['source'].encode()).hexdigest(),old['sha256'])
    self.assertIn('(not (fn2-am-manifestp 12289))',old['source'])
 def test_f_consumes_same_stream_sizing_and_profile_bound(self):
    s=(ROOT/'books/checkpoint-service-geometry.lisp').read_text()
    self.assertIn('(fn2-upload-stream-page-bytes (+ bound *fn2-upload-mid-line-max*))',s)
    self.assertIn('(fn2-upload-input-bound (fn2-upload-profile-article-max profile) capacity0 capacity1)',s)
    f=(ROOT/'tests/root-upload-geometry-unit.lisp').read_text()
    for needle in ['(not (fn2-am-manifestp 12288))','(fn2-am-manifestp 12289)',
                   '(fn2-upload-input-bound 40000 8192 8192) 40000',
                   '(fn2-upload-stream-page-bytes 33032)']:
        self.assertIn(needle,f)
if __name__=='__main__':unittest.main()
