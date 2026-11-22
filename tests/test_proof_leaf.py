"""Lifecycle controls use fake proof APIs; no ACL2 or farm allocation."""
import json
from pathlib import Path
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch, Mock
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import proof_leaf as leaf
import certify_books
import proof_repl


class Lifecycle(unittest.TestCase):
    def test_local_include_requires_cache_without_global_import(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'books').mkdir()
            for name,body in {'private':'', 'parent':'(local (include-book "private"))',
                              'direct-private':'', 'target':'(include-book "parent")\n(local (include-book "direct-private"))'}.items():
                (root/('books/'+name+'.lisp')).write_text('(in-package "ACL2")\n'+body+'\n')
            parents=set(leaf.certs.closure(root,'books/target'))-{'books/target'}
            self.assertEqual(parents,{'books/parent','books/private','books/direct-private'})
            imports,exports=leaf.entry_for_leaf(root,'books/target',parents,proof_repl)
            self.assertEqual(imports,['books/parent'])
            self.assertEqual(exports,{'books/parent'})
            self.assertTrue(exports < parents)

    def test_selected_metadata_identity_is_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);plan={'books':{'books/p':{'key':'k','sha256':'s'}}}
            good={'book':'books/p','closure_key':'k','source_sha256':'s'}
            for field in good:
                with self.subTest(field=field), patch.object(leaf.certs,'cached_entries',return_value=[]), \
                     patch.object(leaf.certs,'choose_entry',return_value=(root,dict(good,**{field:'wrong'}))), \
                     self.assertRaisesRegex(ValueError,'metadata identity'):
                    leaf.check_cache(root,plan,{'books/p'},root,'t')

    def test_stop_waits_for_actual_delayed_child(self):
        child=leaf.subprocess.Popen([sys.executable,'-c','import time; time.sleep(0.15)'])
        def identity(pid):
            self.assertEqual(pid,child.pid)
            return ('original','S') if child.poll() is None else None
        began=time.monotonic()
        try:
            with patch.object(leaf,'process_identity',side_effect=identity):
                leaf.require_stopped([{'pid':child.pid,'start_ticks':'original'}],time.time()+2)
            self.assertGreaterEqual(time.monotonic()-began,0.1)
            self.assertEqual(child.wait(timeout=1),0)
        finally:
            if child.poll() is None: child.kill(); child.wait()

    def test_stop_does_not_confuse_reused_pid_or_zombie_with_absence(self):
        handles=[{'pid':123,'start_ticks':'original'}]
        with patch.object(leaf,'process_identity',return_value=('other','S')):
            leaf.require_stopped(handles,time.time()+1)
        with patch.object(leaf,'process_identity',return_value=('original','Z')), \
             self.assertRaisesRegex(ValueError,"123, 'Z'"):
            leaf.require_stopped(handles,time.time())
        with patch.object(leaf,'process_identity',side_effect=[('original','Z'),None]):
            leaf.require_stopped(handles,time.time()+1)

    def test_record_miss_filter_distinguishes_root_from_parent(self):
        self.assertEqual(certify_books.uncached_parent_books(['books/root'], ['books/root']), [])
        self.assertEqual(certify_books.uncached_parent_books(['books/root', 'books/parent'], ['books/root']), ['books/parent'])

    def run_case(self, fail=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan = root / 'plan.json'
            plan.write_text(json.dumps({'source': 'pinned', 'toolchain': 'toolchain', 'books': {}}))
            args = SimpleNamespace(book='books/target', plan=plan, output=root/'result',
                                   deadline=time.time()+60, memory_bytes=1024,
                                   event_steps=2000000, event_seconds=20)
            repl = SimpleNamespace(ROOT=root, normalize_book=lambda x:x,
                exported_include_graph=lambda r,b: {b:['books/parent']},
                warm_entry_books=lambda r,p: (['books/parent'], {'books/parent'}),
                read_state=lambda n: {}, lock_holder=lambda n: {})
            calls=[]
            def command(self, label, arguments, cleanup=False):
                calls.append((label,arguments,cleanup))
                if label == fail: raise RuntimeError('actual refusal')
            with patch.object(leaf,'checked_scope',return_value='/scope'), \
                 patch.object(leaf.acl2_slots,'acl2_environment',return_value={}), \
                 patch.object(leaf.acl2_toolchain,'fingerprint',return_value=SimpleNamespace(qualified=True,identity='toolchain')), \
                 patch.dict(leaf.os.environ, FN_ACL2='/launcher', FN_CERT_CACHE='/cache'), \
                 patch.object(leaf,'check_sources',return_value={'books/parent','books/target'}), \
                 patch.object(leaf,'check_cache',return_value={}) as cache, \
                 patch.object(leaf,'session_handles',return_value=[]), \
                 patch.object(leaf,'verify_record',return_value='manifest'), \
                 patch.object(leaf.Commands,'run',command):
                rc=leaf.qualify(args,repl)
            return rc,calls,json.loads((args.output/'receipt.json').read_text()),cache.call_args_list

    def test_success_orders_whole_author_stop_then_strict_record(self):
        rc,calls,receipt,cache=self.run_case()
        self.assertEqual(rc,0)
        self.assertEqual([c[0] for c in calls],['install','start','source-directory','author','stop','record'])
        self.assertIn('--cached-only',calls[1][1])
        root = Path(receipt['entry']['path']).parent.parent
        self.assertEqual(calls[2][1][3], f'(set-cbd "{root}/books/")')
        self.assertIn('--per-event-steps',calls[3][1])
        self.assertNotIn('--from',calls[3][1])
        self.assertIn('--cached-parents',calls[5][1])
        self.assertNotIn('--skip-includes',calls[3][1])
        self.assertEqual(receipt['status'],'qualified')
        self.assertEqual(cache[0].args[2],{'books/parent'})
        self.assertEqual(cache[-1].args[2],{'books/parent','books/target'})

    def test_first_refusal_cleans_session_without_record(self):
        for stage in ('start','source-directory','author'):
            with self.subTest(stage=stage):
                rc,calls,receipt,_=self.run_case(stage)
                self.assertEqual(rc,1)
                self.assertEqual(calls[-1][0],'cleanup')
                self.assertNotIn('record',[c[0] for c in calls])
                self.assertEqual(receipt['status'],'refused')

    def test_record_refusal_does_not_restart_author(self):
        rc,calls,_,_=self.run_case('record')
        self.assertEqual(rc,1)
        self.assertEqual([c[0] for c in calls],['install','start','source-directory','author','stop','record'])

    def test_deadline_reaps_only_its_actual_child(self):
        with tempfile.TemporaryDirectory() as directory:
            receipt={'commands':[]}
            runner=leaf.Commands(Path(directory),Path(directory),time.time()+0.1,receipt,lambda:None)
            with self.assertRaises(leaf.subprocess.TimeoutExpired):
                runner.run('bounded-child',['-c','import time; time.sleep(10)'])
            child=receipt['commands'][0]
            self.assertLess(child['returncode'],0)
            with self.assertRaises(ProcessLookupError):leaf.os.kill(child['pid'],0)

    def test_expired_deadline_never_starts_process(self):
        runner=leaf.Commands(Path('.'),Path('.'),time.time()-1,{'commands':[]},lambda:None)
        with patch.object(leaf.subprocess,'Popen') as start, self.assertRaises(TimeoutError):
            runner.run('author',[])
        start.assert_not_called()

    def test_missing_or_corrupt_parent_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);plan={'books':{'books/p':{'key':'k','sha256':'source'}}}
            with patch.object(leaf.certs,'cached_entries',return_value=[]), \
                 patch.object(leaf.certs,'choose_entry',return_value=None),self.assertRaisesRegex(ValueError,'no cold replay'):
                leaf.check_cache(root,plan,{'books/p'},root,'toolchain')
            (root/'book.cert').write_bytes(b'wrong')
            meta={'book':'books/p','closure_key':'k','source_sha256':'source','cert_sha256':'bad','fasl_sha256':'bad'}
            with patch.object(leaf.certs,'cached_entries',return_value=[]), \
                 patch.object(leaf.certs,'choose_entry',return_value=(root,meta)),self.assertRaisesRegex(ValueError,'payload changed'):
                leaf.check_cache(root,plan,{'books/p'},root,'toolchain')

    def test_changed_record_manifest_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'run').mkdir()
            (root/'record.log').write_text('Certification run: run\n')
            good=dict(status='passed',runner_unchanged=True,source_digests_sha256={'x':'a'},
                      source_digests_sha256_after={'x':'a'},acl2_toolchain_identity='t',roots=['books/p'])
            for change in ({}, {'runner_unchanged':False}, {'source_digests_sha256_after':{'x':'b'}}, {'roots':['books/other']}):
                (root/'run/manifest.json').write_text(json.dumps(dict(good,**change)))
                if change:
                    with self.assertRaises(ValueError):leaf.verify_record(root,root,'books/p','t')
                else:self.assertTrue(leaf.verify_record(root,root,'books/p','t').endswith('manifest.json'))

    def test_source_key_change_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'books').mkdir();(root/'books/p.lisp').write_text('(in-package "ACL2")')
            plan={'books':{'books/p':{'sha256':leaf.digest(root/'books/p.lisp'),'key':'old'}}}
            with patch.object(leaf.certs,'closure',return_value={'books/p':'hash'}), \
                 patch.object(leaf.certs,'closure_key',return_value=('new',[])), self.assertRaisesRegex(ValueError,'source/key changed'):
                leaf.check_sources(root,plan,'books/p')

if __name__=='__main__': unittest.main()
