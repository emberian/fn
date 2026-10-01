import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

SPEC=importlib.util.spec_from_file_location('book_navigator',Path(__file__).resolve().parents[1]/'tools/book_navigator.py')
nav=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(nav)


class BookNavigatorTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        subprocess.run(['git','init','-q',str(self.root)],check=True)
        self.write('Makefile','ACL2_BOOKS = books/runtime books/unknown\n')
        self.write('docs/prefixes.md','| `fn-run-` | `runtime` | Current runtime boundary |\n')
        self.write('docs/books/catalog.json',json.dumps({'subsystems':[{'name':'Runtime','patterns':['runtime'],'responsibility':'Actual runtime seam'}],'extra_roots':[],'book_notes':{}}))
        self.write('planning/proofs.json','{"proofs":[]}')
        self.write('planning/proof-events.json','{"targets":[]}')
        self.write('books/shared.lisp','(in-package "ACL2")\n(defun fn-shared (x) x)')
        self.write('books/proof-only.lisp','(in-package "ACL2")\n(defthm proof-helper (equal x x))')
        self.write('books/runtime.lisp','(in-package "ACL2")\n(include-book "shared")\n(local (include-book "proof-only"))\n(defun fn-run (x) (fn-shared x))')
        self.write('books/test-only.lisp','(in-package "ACL2")\n(defun fn-fixture (x) x)')
        self.write('books/generation.lisp','(in-package "ACL2")\n(defun fn-generation (x) x)')
        self.write('books/unknown.lisp','(in-package "ACL2")\n(defun fn-unknown (x) x)')
        self.write('host/native/build.lisp','(include-book "books/runtime")\n(defun fnn-entry (x) (acl2::fn-run x))')
        self.write('host/interfaces.lisp','(definterface fn-run :class :common-lisp-compliant :root :extract)')
        self.write('tests/acl2/scenario.lisp','(include-book "../../books/test-only")')
        self.write('tools/extract/loader.lisp','(include-book "../../books/generation")')
        self.track()
        subprocess.run(['git','-c','commit.gpgsign=false','-c','core.hooksPath=/dev/null','-c','user.email=test@example.invalid','-c','user.name=Fixture','commit','-qm','fixture'],cwd=self.root,check=True)

    def write(self,path,text):
        p=self.root/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)

    def track(self): subprocess.run(['git','add','.'],cwd=self.root,check=True)
    def rows(self,data): return {b['path']:b for b in data['books']}

    def test_tracked_canonical_only_and_untracked_dependency_explicit(self):
        self.write('books/runtime.lisp',(self.root/'books/runtime.lisp').read_text()+'\n(include-book "wip")')
        self.write('books/wip.lisp','(defun fn-wip (x) x)')
        data=nav.build(self.root);rows=self.rows(data)
        self.assertNotIn('books/wip.lisp',rows)
        self.assertTrue(any(w['kind']=='missing-or-untracked-include' and w['target']=='books/wip.lisp' for w in data['warnings']))
        self.assertFalse(data['inventory_complete'])

    def test_role_boundaries_reverse_dependencies_and_package_qualified_host(self):
        data=nav.build(self.root);rows=self.rows(data)
        self.assertIn('served/reference',rows['books/runtime.lisp']['roles'])
        self.assertIn('host-reference',rows['books/runtime.lisp']['uses'])
        self.assertEqual(rows['books/proof-only.lisp']['roles'],['proof-support'])
        self.assertEqual(rows['books/test-only.lisp']['roles'],['test-only'])
        self.assertIn('generation-support',rows['books/generation.lisp']['roles'])
        self.assertEqual(rows['books/unknown.lisp']['roles'],['unknown'])
        self.assertTrue(rows['books/unknown.lisp']['certification_root'])
        self.assertIn('books/runtime.lisp',rows['books/shared.lisp']['included_by'])
        self.assertEqual(next(x for x in rows['books/runtime.lisp']['dependencies'] if x['path']=='books/proof-only.lisp')['kind'],'local/proof')
        self.assertFalse(any(w['kind']=='unresolved-root' and w['target'].startswith(('host/','tests/')) for w in data['warnings']))

    def test_registry_keystone_and_reference_support_are_roots(self):
        self.write('books/reference.lisp','(include-book "shared")\n(defthm fn-reference-bridge (equal x x))')
        self.write('planning/proof-events.json','{"targets":[{"id":"PRF-TEST","events":[{"name":"fn-reference-bridge"}]}]}')
        self.track();rows=self.rows(nav.build(self.root))
        self.assertIn('proof-support',rows['books/reference.lisp']['roles'])
        self.assertEqual(rows['books/reference.lisp']['proof_ids'],['PRF-TEST'])
        self.assertIn('proof-support',rows['books/shared.lisp']['roles'])

    def test_dynamic_root_override_requires_provenance_and_does_not_mean_obsolete(self):
        config=json.loads((self.root/'docs/books/catalog.json').read_text())
        config['extra_roots']=[{'path':'books/unknown.lisp','category':'generation','source':'tools/computed-loader.py','reason':'Computed selected root; maintained source contract'}]
        self.write('docs/books/catalog.json',json.dumps(config))
        self.assertIn('generation-support',self.rows(nav.build(self.root))['books/unknown.lisp']['roles'])
        config['extra_roots'][0].pop('reason');self.write('docs/books/catalog.json',json.dumps(config))
        with self.assertRaises(ValueError):nav.build(self.root)

    def test_superseded_requires_replacement_and_evidence(self):
        config=json.loads((self.root/'docs/books/catalog.json').read_text())
        config['book_notes']={'books/unknown.lisp':{'role':'superseded'}}
        self.write('docs/books/catalog.json',json.dumps(config))
        with self.assertRaises(ValueError):nav.build(self.root)
        config['book_notes']['books/unknown.lisp'].update(replacement='books/runtime.lisp',evidence='Explicit source contract, not age')
        self.write('docs/books/catalog.json',json.dumps(config))
        self.assertEqual(self.rows(nav.build(self.root))['books/unknown.lisp']['roles'],['unknown','superseded'])

    def test_exact_body_candidate_is_not_a_deletion_claim(self):
        body='(if (natp x) (+ x '+ ' '.join(['1']*100)+') (if (consp x) (car x) nil))'
        self.write('books/copy-a.lisp','(defun fn-copy-a (x) '+body+')')
        self.write('books/copy-b.lisp','(defun fn-copy-b (x) '+body+')')
        self.track();data=nav.build(self.root)
        candidate=next(c for c in data['candidates'] if len(c['definitions'])==2)
        self.assertIn('not a semantic/refinement or deletion proof',candidate['uncertainty'])
        self.assertTrue(all(self.rows(data)[p]['roles']==['unknown'] for p in ['books/copy-a.lisp','books/copy-b.lisp']))

    def test_html_embedding_is_safe_and_freshness_ignores_only_git_coordinate(self):
        data=nav.build(self.root);data['limitations'].append('</script><script>bad</script>')
        rendered=nav.render_html(data)
        payload=rendered.split('<script id="data" type="application/json">',1)[1].split('</script>',1)[0]
        decoded=json.loads(payload)
        self.assertEqual(decoded['limitations'],data['limitations'])
        self.assertNotIn('</script>',payload)
        changed=dict(data,source_revision='unrelated-commit')
        self.assertEqual(nav.comparable(changed),nav.comparable(data))
        changed['canonical_count']=99
        self.assertNotEqual(nav.comparable(changed),nav.comparable(data))

    def test_cli_generated_navigation_and_stale_input_detection(self):
        self.assertEqual(nav.main(['--root',str(self.root),'--write']),0)
        self.assertEqual(nav.main(['--root',str(self.root),'--check']),0)
        self.write('books/unknown.lisp','(defun fn-new-purpose (x) x)')
        self.assertEqual(nav.main(['--root',str(self.root),'--check']),1)

if __name__=='__main__': unittest.main()
