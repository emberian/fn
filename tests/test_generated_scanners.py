"""Generated definitions stay visible without reading or evaluating ACL2 output."""
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import callgraph
import ledger
import reach_check

LOOP = '''(def-loop fn-scan (xs buffer) :over xs :stobjs buffer :elt e
  :let ((value (fn-read e buffer))) :keep (fn-good value)
  :while (fn-more xs) :stop (fn-stop value) :stop-value (fn-stop-result xs)
  :tail (fn-tail xs) :body (fn-line value)
  :guard-hints (("Goal" :in-theory (enable fn-proof-only))))'''
HELPERS = '\n'.join(f'(defun {name} (x) x)' for name in
                    ('fn-read', 'fn-good', 'fn-more', 'fn-stop', 'fn-stop-result',
                     'fn-tail', 'fn-line', 'fn-proof-only'))


class GeneratedScannerTests(unittest.TestCase):
    def test_callgraph_wrapper_loop_and_all_runtime_terms(self):
        forms = ledger.Reader(LOOP + '\n' + HELPERS).top_level()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'toy.lisp'
            path.write_text(LOOP + '\n' + HELPERS)
            graph = callgraph.build([(path, 'books/toy.lisp')])
        self.assertIn('fn-scan', graph.definitions)
        self.assertIn('fn-scan-loop', graph.definitions)
        self.assertIn('fn-scan-loop', graph.edges['fn-scan'])
        for name in ('fn-read', 'fn-good', 'fn-more', 'fn-stop', 'fn-stop-result',
                     'fn-tail', 'fn-line'):
            self.assertIn(name, graph.edges['fn-scan-loop'])
        self.assertNotIn('fn-proof-only', graph.reach('fn-scan'))
        self.assertEqual(graph.definitions['fn-scan-loop'][0].line, forms[0][1])
        # Disabling record plumbing must not disable loop definitions.
        self.assertIn('fn-scan-loop', {d.name for d in callgraph.collect(forms, 'toy', records=False)})

    def test_reach_graph_fixture_has_host_chain_through_generated_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'books').mkdir()
            (root / 'host/native').mkdir(parents=True)
            (root / 'tools').mkdir()
            (root / 'books/toy.lisp').write_text(LOOP + '\n' + HELPERS +
                '\n(defthm clean (equal (fn-scan xs buffer) nil))')
            (root / 'host/native/build.lisp').write_text('(load "host/native/toy.lisp")')
            (root / 'host/native/toy.lisp').write_text(
                "(defun fnn-entry (xs buffer) (fnn-core 'fn-scan xs buffer))")
            loaded = reach_check.loaded_host_files(root=root)
            with patch.object(reach_check, 'ROOT', root), \
                    patch.object(reach_check, 'loaded_host_files', return_value=loaded):
                graph = reach_check.Graph()
                self.assertIn('fn-scan', graph.reachable)
                self.assertIn('fn-scan-loop', graph.reachable)
                self.assertIn('fn-read', graph.reachable)
                self.assertIn('fn-scan', graph.host_chain('fn-read'))
                theorems = reach_check.theorem_forms(graph.books)
                self.assertIn('fn-scan-loop-is-revappend', theorems)
                self.assertTrue(reach_check.Subject(graph, 'clean', theorems['clean'][1]).hosted(graph))

    def test_existing_record_and_protocol_expansions_are_shared_unchanged(self):
        forms = ledger.Reader('''
          (fn-defrecord fn-r :constructor (fn-r-make a)
                        :fields ((fn-r-a natp)))
          (fn-defrecord-export fn-r-rules :records (fn-r))
          (defprotocol test (:x :arms (:pinned (fn-arm x))))
        ''').top_level()
        mirrors = (ledger.defrecord_expansion, ledger.defrecord_export_expansion,
                   ledger.defprotocol_expansion)
        for (form, _), mirror in zip(forms, mirrors):
            self.assertEqual(ledger.generated_expansion(form), mirror(form))
        defs = {d.name: d for d in callgraph.collect(forms, 'toy')}
        self.assertEqual(defs['fn-rp'].kind, 'record')
        self.assertEqual(defs['fn-nntp-command-dispatch'].kind, 'macro')
        self.assertIn('fn-arm', callgraph.symbols(defs['fn-nntp-command-dispatch'].form))
        self.assertNotIn('fn-rp', {d.name for d in callgraph.collect(forms, 'toy', records=False)})

    def test_shared_events_do_not_admit_templates_or_refused_events(self):
        forms = ledger.Reader('''
          '(def-loop quoted (xs) :body (car xs))
          (defmacro template () '(def-loop phantom (xs) :body (car xs)))
          (must-fail (def-loop refused (xs) :body (car xs)))
          (local (def-loop local-loop (xs) :body (car xs)))
        ''').top_level()
        events = list(ledger.source_events(forms, include_local=False))
        self.assertEqual([ledger.head(form) for form, _ in events], ['defmacro'])
        self.assertIsNone(ledger.generated_expansion(ledger.read_forms('(unknown x)')[0]))

    def test_guard_and_shape_readers_see_both_definitions(self):
        from tools import interface_kinds, host_shape_check
        source = interface_kinds.read_source([('books/toy.lisp', LOOP)])
        self.assertEqual(set(source.definitions), {'fn-scan', 'fn-scan-loop'})
        self.assertEqual(source.verified, {'fn-scan', 'fn-scan-loop'})
        definitions = []
        for form, _ in host_shape_check.ledger.Reader(LOOP).top_level():
            host_shape_check.definitions_in(form, 'toy:1', False, definitions)
        self.assertEqual({d.name for d in definitions}, {'fn-scan', 'fn-scan-loop'})

    def test_hot_path_reader_preserves_generated_guard_verification(self):
        import hot_path_check
        tree = hot_path_check.Tree()
        scan = hot_path_check.FileScan('books/toy.lisp', False, False, tree)
        scan.scan(hot_path_check.ledger.Reader(LOOP).top_level())
        for name in ('fn-scan', 'fn-scan-loop'):
            self.assertIn(name, tree.definitions)
            self.assertTrue(tree.definitions[name].verified)

    def test_exported_generated_theorem_and_local_bridge(self):
        import interface_emit
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'books').mkdir()
            (root / 'books/toy.lisp').write_text(LOOP + '''
              (def-loop put (xs buffer) :shape :into :into buffer
                :write append-byte :map mapped :body (car xs))
              (local (defthm hidden t))
              (must-fail (defthm refused nil))''')
            self.assertEqual(interface_emit.tree_theorems(root), {'put-is-append'})

    def test_loop_bodies_preserve_tail_recursion_and_elt_substitution(self):
        declaration = ledger.read_forms('''(def-loop mapped (xs) :elt e
              :body (f e 'e "e") :tail (tail xs))''')[0]
        events = ledger.generated_expansion(declaration)
        expected = ledger.read_forms('''
          (if (consp xs) (mapped-loop (cdr xs) (cons (f (car xs) 'e "e") acc))
              (revappend acc (tail xs)))
          (mbe :logic (if (consp xs) (cons (f (car xs) 'e "e") (mapped (cdr xs))) (tail xs))
               :exec (mapped-loop xs nil))''')
        self.assertEqual(events[0][-1], expected[0])
        self.assertEqual(events[1][-1], expected[1])

    def test_coverage_span_names_both_generated_definitions(self):
        import callers
        text = "; header\n" + LOOP + "\n(defun ordinary (x) x)\n"
        spans = callers.definitions(text)
        for name in ('fn-scan', 'fn-scan-loop'):
            self.assertIn((name, 2, 6), spans)
        self.assertNotIn('fn-read', {name for name, _, _ in spans})

    def test_generated_names_reach_book_and_protocol_indexes(self):
        import build_lists_check
        import protocol_emit
        import protocol_rows
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'books').mkdir()
            (root / 'books/toy.lisp').write_text(LOOP)
            index = build_lists_check.BookIndex(root)
            self.assertIn('fn-scan-loop', index.defs('books/toy.lisp'))
            with patch.object(protocol_emit, 'ROOT', root):
                self.assertIn('fn-scan-loop', protocol_emit.defined_functions())
        rows = protocol_rows.capability_lines({'toy': '(def-loop fn-capabilities (xs) '
                    ':body (fn-nntp-string-octets "READER"))'})
        self.assertEqual(rows, [('toy', 'READER')])

    def test_proof_controller_lookup_sees_generated_loop(self):
        import proof_repl
        form = proof_repl.find_definition('fn-scan-loop', [LOOP])
        self.assertEqual(form[:2], ['defun', 'fn-scan-loop'])
        self.assertEqual(form[2], ['xs', 'buffer', 'acc'])

    def test_literal_theorem_spelling_is_preserved(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / 'toy.lisp'
            source = '(defthm rational (implies (< x 1/2) (p |a b| x)))'
            path.write_text(source)
            with patch.object(reach_check, 'ROOT', root):
                self.assertEqual(reach_check.theorem_forms([path])['rational'][1], source)

    def test_other_loop_shapes_have_executable_bodies(self):
        cases = [
          ('(def-loop take-n (n xs) :shape :take :over xs :count n :body (car xs))',
           '(if (not (zp n)) (take-n-loop (- n 1) (cdr xs) (cons (car xs) acc)) (revappend acc nil))'),
          ('(def-loop take-b (n xs) :shape :take :over xs :count n :base (done n) :body (car xs))',
           '(if (done n) (revappend acc nil) (take-b-loop (- n 1) (cdr xs) (cons (car xs) acc)))'),
          ('(def-loop map-b (xs) :base (atom-ish xs) :keep (ok (car xs)) :tail (tl xs) :body (car xs))',
           '(if (atom-ish xs) (revappend acc (tl xs)) '
           '(if (ok (car xs)) (map-b-loop (cdr xs) (cons (car xs) acc)) (map-b-loop (cdr xs) acc)))'),
          ('(def-loop sum (xs) :shape :sum :elt e :body (f e))',
           '(if (consp xs) (sum-loop (cdr xs) (+ (f (car xs)) acc)) acc)'),
          ('(def-loop cat (xs) :shape :concat :body (f (car xs)))',
           '(if (consp xs) (cat-loop (cdr xs) (revappend (f (car xs)) acc)) (revappend acc nil))'),
          ('(def-loop put (buffer xs) :shape :into :into buffer :write put-byte :map mapped :body (car xs))',
           '(if (consp xs) (let ((buffer (put-byte (car xs) buffer))) (put buffer (cdr xs))) buffer)')]
        for declaration, expected in cases:
            with self.subTest(declaration=declaration):
                event = ledger.generated_expansion(ledger.read_forms(declaration)[0])[0]
                self.assertEqual(event[-1], ledger.read_forms(expected)[0])


if __name__ == '__main__':
    unittest.main()
