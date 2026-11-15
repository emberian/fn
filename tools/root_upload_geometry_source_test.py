#!/usr/bin/env python3
"""Pin the ROOT producer expressions AND physical manifest policy after move."""
from pathlib import Path
import hashlib,json,unittest
import lisp_rewrite as lr
import ledger
ROOT=Path(__file__).resolve().parents[1]
RECEIPT=ROOT/'tools/fixtures/root-upload-geometry-extraction.json'
def atom(n):return n.text.lower() if isinstance(n,lr.Atom) else ''
def unique(source,head,name=None,needle=None,deep=False):
    parsed=lr.parse(source)
    if name is not None:
        hits=lr.match('_',parsed.forms,deep=deep,head=head,name=name)
        nodes=[h.node for h in hits]
    else:
        nodes=[n for n in parsed.forms if isinstance(n,lr.Lst) and n.items and atom(n.items[0])==head]
    nodes=[n for n in nodes if needle is None or needle in source[n.start:n.end]]
    if len(nodes)!=1:raise AssertionError((head,name,needle,len(nodes)))
    n=nodes[0];return source[n.start:n.end],n,parsed
class RootGeometry(unittest.TestCase):
    def setUp(self):self.receipt=json.loads(RECEIPT.read_text())
    def test_every_original_form_moved_once_without_copies(self):
        self.assertEqual(self.receipt['baseline'],'07e40b063')
        self.assertEqual(len(self.receipt['moves']),48)
        for row in self.receipt['moves']:
            with self.subTest(name=row['name'],needle=row['needle']):
                self.assertEqual(hashlib.sha256(row['form'].encode()).hexdigest(),row['sha256'])
                target_path=row['target']
                follow=ROOT/'tools/fixtures/upload-window-root-composition.json'
                if follow.exists():
                    for move in json.loads(follow.read_text())['moves']:
                        if row['name']==move['symbol']:
                            self.assertEqual(move['source'],row['target'])
                            self.assertEqual(move['form'],row['form'])
                            self.assertEqual(move['sha256'],row['sha256'])
                            self.assertNotIn(move['form'],(ROOT/move['source']).read_text())
                            target_path=move['target']
                target=(ROOT/target_path).read_text()
                form,_,_=unique(target,row['head'],row['name'],row['needle'])
                policy_path=ROOT/'tools/fixtures/upload-stream-page-composition.json'
                policies=json.loads(policy_path.read_text())['policies'] if policy_path.exists() else []
                policy=next((p for p in policies if p['book']==target_path and p['name']==row['name']),None)
                if policy:
                    self.assertEqual(policy['old'],row['form'])
                    self.assertEqual(form,policy['new'])
                else:self.assertEqual(form,row['form'])
                old=(ROOT/row['source']).read_text()
                if row['name'] is not None:
                    self.assertEqual(lr.match('_',lr.parse(old).forms,deep=True,head=row['head'],name=row['name']),[])
                else:self.assertNotIn(row['form'],old)
    def test_actual_input_and_upload_consumers_only_substitute_shared_expressions(self):
        page=(ROOT/'books/upload-page-geometry.lisp').read_text()
        for row in self.receipt['rewrites']:
            form,_,_=unique((ROOT/row['book']).read_text(),'defun',row['name'],deep=True)
            for old,new in reversed(row['substitutions']):
                if new:
                    self.assertEqual(form.count(new),1)
                    form=form.replace(new,old)
                else:
                    # Restore the removed pure max binding at its original spot.
                    before='(fn2-input-config (fn2-input-config-init 1 fn2-input-config))'
                    self.assertEqual(form.count(before),1)
                    form=form.replace(before,before+old,1)
            self.assertEqual(form,row['original'])
            self.assertEqual(hashlib.sha256(form.encode()).hexdigest(),row['sha256'])
        rows={r['name']:r for r in self.receipt['rewrites']}
        form,node,parsed=unique(page,'defun','fn2-upload-input-bound')
        actual=parsed.text[node.items[-1].start:node.items[-1].end]
        expected=rows['fn2-upload-bound']['substitutions'][0][0].replace('(nfix max)','(nfix article-max)')
        policy_path=ROOT/'tools/fixtures/upload-stream-page-composition.json'
        if policy_path.exists():
            policy=next(p for p in json.loads(policy_path.read_text())['policies'] if p['name']=='fn2-upload-input-bound')
            self.assertEqual(policy['old'].splitlines()[-1].strip(),expected+')')
            self.assertEqual(ledger.canonical_text(actual),ledger.canonical_text('(nfix article-max)'))
        else:self.assertEqual(ledger.canonical_text(actual),ledger.canonical_text(expected))
        form,node,parsed=unique(page,'defun','fn2-upload-article-profilep')
        actual=parsed.text[node.items[-1].start:node.items[-1].end]
        self.assertEqual(ledger.canonical_text(actual),ledger.canonical_text(rows['fn2-input-config-profilep']['substitutions'][0][0]))
        form,node,parsed=unique(page,'defun','fn2-upload-profile-article-max')
        actual=parsed.text[node.items[-1].start:node.items[-1].end]
        normal=rows['fn2-input-config-from']['substitutions'][1][0]
        self.assertEqual(ledger.canonical_text(actual),ledger.canonical_text('(let ((max (fn2-profile-get :article-max profile))) '+normal+')'))
    def test_manifest_wrapper_callees_and_physical_64k_policy(self):
        for row in self.receipt['physical_geometry']:
            form,_,_=unique((ROOT/row['book']).read_text(),'defconst',row['name'])
            self.assertEqual(form,row['form'])
            self.assertEqual(hashlib.sha256(form.encode()).hexdigest(),row['sha256'])
        codec=(ROOT/'books/source-manifest-codec.lisp').read_text()
        manifest,_,_=unique(codec,'defun','fn2-am-manifestp')
        self.assertIn('(< *fn2-upload-raw-bytes* (nfix total))',manifest)
        self.assertNotIn('fn2-upload-payload',codec)
        for name in ['fn2-am-blocks','fn2-am-units','fn2-am-manifestp']:
            self.assertEqual(sum(1 for r in self.receipt['moves'] if r['name']==name),1)
        fixture=(ROOT/'tests/root-upload-geometry-unit.lisp').read_text()
        for needle in ['(not (fn2-am-manifestp 12288))','(fn2-am-manifestp 12289)',
                       '(fn2-am-manifestp 65537)','(fn2-upload-page-bytes 33032)']:
            self.assertIn(needle,fixture)
if __name__=='__main__':unittest.main()
