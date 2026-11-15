"""SOURCE controls: original formula identity, actual caller and closed links."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr
import reader_foundation_batch as rw
import checkpoint_reader_contract_rewrite as transform

BASE = '7778c95d517b33d3fd1dc8d9a7ff37d64dd8df95'
REGISTRY = 'fa8d24704aee8407a57b63f20dbb265a8cf0172f'


class ReaderContracts(unittest.TestCase):
    def test_original_metadata_and_exact_transform(self):
        old = rw.source(ROOT, BASE, 'books/checkpoint.lisp')
        node = rw.unique(old, transform.PATTERN)
        fixture = (ROOT / 'tools/fixtures/checkpoint-reader-contract-before.lisp').read_text()
        self.assertEqual(old[node.start:node.end] + '\n', fixture)
        now = (ROOT / 'books/checkpoint.lisp').read_text()
        self.assertEqual(transform.prepare_interfaces(transform.transform(old)), now)
        self.assertEqual(transform.transform(now), now)
        # Inputs/specs/H remain canonical. Only three result positions select
        # unresolved old facts; all other generated DEFTHM forms pass unchanged.
        self.assertIn('(hyps (fn2-columns-carrier-hyps carriers))', now)
        self.assertIn('(specs (fn2-columns-carrier-specs carriers))', now)
        self.assertIn('(facts (fn2-columns-preservation-facts name (cons name args) specs hyps hints))', now)
        self.assertIn('((4 . fn2-checkpoint-reader-checker-domain-removal-check)', now)
        self.assertIn('(5 . fn2-checkpoint-reader-hasher-domain-removal-check)', now)
        self.assertIn('(8 . fn2-checkpoint-reader-digests-domain-removal-check)', now)
        self.assertIn('(defthm-owed ,(cadr fact) ,args ,(caddr fact)', now)

    def test_all_existing_bodies_guards_declarations_unchanged(self):
        for path in ('books/checkpoint.lisp', 'books/boot.lisp'):
            before = rw.definitions(rw.source(ROOT, BASE, path))
            after = rw.definitions((ROOT / path).read_text())
            for name, node in before.items():
                self.assertEqual(rw.norm(node), rw.norm(after[name]), (path, name))

    def test_current_registry_is_exact_provider(self):
        for path in ('books/declare.lisp', 'books/owed.lisp',
                     'books/assurance-completion.lisp', 'books/owed-report.lisp'):
            self.assertEqual((ROOT / path).read_text(), rw.source(ROOT, REGISTRY, path))

    def test_fixture_uses_same_setup_and_actual_arguments(self):
        source = (ROOT / 'tests/checkpoint-reader-scalar-domain-unit.lisp').read_text()
        now = (ROOT / 'tests/checkpoint-reader-refutation-unit.lisp').read_text()
        self.assertEqual(now, transform.refutation_unit(source))
        control = rw.unique(source, '(defun-nx fn2-checkpoint-reader-scalar-domain-check ?*body)')
        arguments = rw.unique(now, '(defun-nx fn2-checkpoint-reader-refutation-arguments ?*body)')
        original_bindings = control.items[-1].items[1].items
        n = next(i for i, item in enumerate(original_bindings) if rw.atom(item.items[0]) == 'whole-h')
        self.assertEqual(tuple(map(rw.plain, arguments.items[-1].items[1].items[:n])),
                         tuple(map(rw.plain, original_bindings[:n])))
        call = next(item.items[1] for item in original_bindings if rw.atom(item.items[0]) == 'answer')
        self.assertEqual(tuple(map(rw.plain, arguments.items[-1].items[2].items[1:])),
                         tuple(map(rw.plain, call.items[1:])))

    def test_each_refutation_binds_exact_live_statement_and_closed_call(self):
        text = (ROOT / 'tests/checkpoint-reader-refutation-unit.lisp').read_text()
        for case in ('checker', 'hasher', 'digests'):
            for facet in ('type', 'wfp'):
                name = f'fn2-checkpoint-check-step-{case}-{facet}'
                theorem = rw.unique(text, f'(defthm {name}-refuted-instance ?*body)')
                conclusion = theorem.items[2]
                self.assertEqual(rw.atom(conclusion.items[0]), 'not')
                call = conclusion.items[1]
                self.assertEqual(rw.atom(call.items[0]), name + '$owed')
                self.assertEqual(len(call.items)-1, 20)
                for i, arg in enumerate(call.items[1:]):
                    self.assertEqual(rw.plain(arg), rw.plain(lr.parse(
                        f'(nth {i} (fn2-checkpoint-reader-refutation-arguments :{case}))').forms[0]))
                link = rw.unique(text, f'(defsquare-refuted {name} ?*body)')
                self.assertEqual(rw.atom(link.items[2]), name + '-refuted-instance')
                self.assertEqual(rw.atom(link.items[3]), name + '-under-guard')
        self.assertIn('(subsetp-eq names (fn2-owed-names (w state)))', text)
        self.assertIn('(fn2-columns-guard-domain-specs (fn2-columns-carrier-specs carriers))', text)

    def test_actual_boot_face_consumes_guarded_interface(self):
        old = rw.source(ROOT, BASE, 'books/boot.lisp')
        now = (ROOT / 'books/boot.lisp').read_text()
        self.assertEqual(now, transform.boot_bridge(old))
        self.assertEqual(now, transform.boot_bridge(now))
        contracts = rw.unique(now, '(defcolumns-guarded-contracts fn2-boot-checkpoint-descriptor-pool ?*body)')
        text = now[contracts.start:contracts.end]
        self.assertIn('(fn2-fc 4 :prefix "-CHECKER")', text)
        self.assertIn('(fn2-b3 6 :prefix "-HASHER")', text)
        self.assertIn('(fn2-digests 9 :prefix "-DIGESTS")', text)
        self.assertIn('fn2-checkpoint-check-step fn2-checkpoint-restore-load-hash', text)

    def test_prepare_uses_existing_frames_and_named_getters(self):
        now = (ROOT / 'books/checkpoint.lisp').read_text()
        self.assertEqual(transform.prepare_interfaces(now), now)
        provider = rw.source(ROOT, transform.PREPARE_SOURCE, 'books/checkpoint.lisp')
        pattern = '(defcolumns-guarded-contracts fn2-checkpoint-copy-expected ?*body)'
        self.assertEqual(rw.plain(rw.unique(now, pattern)), rw.plain(rw.unique(provider, pattern)))
        for name in ('fn2-checkpoint-prepare-body', 'fn2-checkpoint-prepare', 'fn2-checkpoint-prepare-owned'):
            pattern = '(fn2-checkpoints-preserves '+name+' ?*body)'
            self.assertEqual(rw.plain(rw.unique(now, pattern)), rw.plain(rw.unique(provider, pattern)))

    def test_predicate_evidence_uses_canonical_closed_domain_path(self):
        self.assertEqual((ROOT / 'books/square-evidence.lisp').read_text(),
                         rw.source(ROOT, '4d86318352248e5e22d4bdaec8b6de7475ed1090',
                                   'books/square-evidence.lisp'))
        text = (ROOT / 'tests/checkpoint-reader-refutation-unit.lisp').read_text()
        helper = rw.unique(text, '(local (defun fn2-checkpoint-reader-evidence-events ?*body))')
        source = text[helper.start:helper.end]
        self.assertIn('(fn2-evidence-hypothesis-cut hyp guard)', source)
        self.assertIn('(equal count 1)', source)
        self.assertIn('(fn2-square-predicate-evidence-events-with-hints', source)
        self.assertIn(':kind :hypothesis-removal :remove guard', source)
        self.assertIn('(fn2-checkpoint-reader-evidence-bindings args :positive 0)', source)
        self.assertIn('(fn2-checkpoint-reader-evidence-bindings args case 0)', source)
        self.assertIn('`(fn2-assert-square-evidence ,claim)', source)
        # Bindings are actual closed constructor terms in translated grammar;
        # they are never host-computed quotations of mutable reader snapshots.
        self.assertIn("`(nth ',i (fn2-checkpoint-reader-refutation-arguments ',which))", text)
        hint = rw.unique(text, '(local (defun fn2-checkpoint-reader-evidence-hints ?*body))')
        self.assertIn(':use ,ground', text[hint.start:hint.end])
        self.assertIn('(fn2-checkpoint-check-step)', text[hint.start:hint.end])


if __name__ == '__main__':
    unittest.main()
