import unittest
from pathlib import Path
from tools.owner_carrier.families import publication, GLOBALS, composition_events


class FamilyTransformationTests(unittest.TestCase):
    def test_all_ten_reads_and_writes_move_together(self):
        for old, field in GLOBALS.items():
            with self.subTest(global_name=old):
                source = f"(f-put-global '{old} (fn-owner-sco-global '{old} state) state)"
                result = publication(source)
                self.assertNotIn(old, result)
                self.assertIn(f'(fn-opub-get {field} (fn-ost-publication state))', result)
                self.assertIn(f'(fn-opub-put {field}', result)
                self.assertEqual(publication(result), result)

    def test_quotes_comments_strings_and_unrelated_calls_are_unchanged(self):
        source = '''; (f-get-global 'fn-owner-sco-base state)
'(f-put-global 'fn-owner-sco-base nil state)
(defun f () "(f-get-global 'fn-owner-sco-base state)")
(f-put-global 'fn-owner-other nil state)'''
        self.assertEqual(publication(source), source)

    def test_nested_effect_refuses_instead_of_evaluating_state_twice(self):
        source = "(f-put-global 'fn-owner-sco-base x (f-put-global 'fn-owner-sco-inflight y state))"
        with self.assertRaises(ValueError):
            publication(source)

    def test_layout_outside_calls_is_preserved(self):
        source = "(let ((state (f-put-global 'fn-owner-sco-base x state))) ; retained\n state)"
        self.assertIn('; retained\n state)', publication(source))

    def test_composition_equations_are_generated_and_cover_all_ten_fields(self):
        root = Path(__file__).resolve().parents[1]
        generated = composition_events()
        self.assertTrue((root / "books/owner-publication-composition.lisp").read_text().endswith(generated))
        for field in GLOBALS.values():
            self.assertIn(f"(fn-opub-get {field} r)", generated)

    def test_served_wrappers_use_the_carried_transitions(self):
        from tools import lisp_rewrite as lr
        root = Path(__file__).resolve().parents[1]
        text = (root / "host/owner-host.lisp").read_text()
        forms = lr.parse(text).forms
        for host, pure in [
            ("catalog-root-reserve", "fn-ocr-reserve"),
            ("catalog-root-current", "fn-ocr-current"),
            ("sco-due", "fn-opub-due"), ("sco-request", "fn-opub-request"),
            ("sco-capture", "fn-opub-capture-context"),
            ("sco-publication-done", "fn-opub-done"),
            ("sco-publication-abandoned", "fn-opub-abandoned")]:
            match = lr.match(None, forms, head="defun", name="fn-owner-" + host, deep=False)[0]
            self.assertIn("(" + pure + " ", text[match.start:match.end].replace("\n", " "))
        from tools.owner_globals_check import globals_of
        self.assertEqual(set(GLOBALS).intersection(globals_of(text)), set())


class ReclaimLiveCarrierTests(unittest.TestCase):
    def test_budget_installs_and_both_requests_read_the_same_carried_flag(self):
        from tools import lisp_rewrite as lr
        from tools.owner_globals_check import globals_of
        root = Path(__file__).resolve().parents[1]
        text = (root / 'host/owner-host.lisp').read_text()
        forms = lr.parse(text).forms
        def body(name):
            m = lr.match(None, forms, head='defun', name=name, deep=False)[0]
            return text[m.start:m.end]
        self.assertIn('(fn-ost-install-admission (fn-oadm-configure-reclaim live) state)',
                      body('fn-owner-connection-budget'))
        self.assertIn('(fn-oadm-reclaim-live (fn-ost-admission state))',
                      body('fn-owner-reclaim-live-p'))
        readers = [n for n in forms if isinstance(n, lr.Lst)
                   and n.items and isinstance(n.items[0], lr.Atom)
                   and n.items[0].low == 'defun'
                   and '(fn-owner-reclaim-live-p state)' in text[n.start:n.end]]
        self.assertEqual(len(readers), 2)
        for directory in ('host', 'books'):
            for path in (root / directory).rglob('*.lisp'):
                source = path.read_text()
                if 'fn-owner-reclaim-live' in source:
                    self.assertNotIn('fn-owner-reclaim-live', globals_of(source), str(path))


class RecordFamilyTransformationTests(unittest.TestCase):
    fields = {'fn-owner-account-carries': ':carries',
              'fn-owner-account-root-state': ':root',
              'fn-owner-canonical-state': ':canonical'}

    def transform(self, source):
        from tools.owner_carrier.families import record_family
        return record_family(source, self.fields, 'fn-oauth', 'authority')

    def test_all_fields_and_both_quote_forms(self):
        for key, field in self.fields.items():
            for quoted in ["'"+key, '(quote '+key+')']:
                source = f'(and (boundp-global {quoted} state) (f-get-global {quoted} state))'
                getter = f'(fn-oauth-get {field} (fn-ost-authority state))'
                self.assertEqual(self.transform(source), getter)
                self.assertIn(f'(fn-oauth-put {field} {getter}', self.transform(
                    f'(f-put-global {quoted} {source} state)'))
                self.assertEqual(self.transform(getter), getter)

    def test_nil_default_and_consp_selector(self):
        for key, field in self.fields.items():
            getter = f'(fn-oauth-get {field} (fn-ost-authority state))'
            self.assertEqual(self.transform(
                f"(if (boundp-global '{key} state) (f-get-global '{key} state) nil)"), getter)
            self.assertEqual(self.transform(
                f"(and (f-boundp-global '{key} state) (consp (f-get-global '{key} state)))"),
                f'(consp {getter})')

    def test_quoted_forms_and_comments_and_strings_are_preserved(self):
        source = '''; (f-get-global 'fn-owner-account-carries state)
'(f-get-global 'fn-owner-account-carries state)
(quote (f-put-global 'fn-owner-canonical-state nil state))
(f "(f-get-global 'fn-owner-account-root-state state)")'''
        self.assertEqual(self.transform(source), source)

    def test_lone_boundness_and_nested_state_effects_refuse(self):
        for source in ["(boundp-global 'fn-owner-canonical-state state)",
                       "(f-put-global 'fn-owner-canonical-state nil (mutate state))"]:
            with self.assertRaises(ValueError):
                self.transform(source)


class AuthorityCarrierTests(unittest.TestCase):
    def test_all_old_global_readers_and_writers_move_to_the_record(self):
        from tools.owner_globals_check import globals_of
        root = Path(__file__).resolve().parents[1]
        old = set(RecordFamilyTransformationTests.fields)
        found = {}
        for directory in ('books', 'host'):
            for path in (root / directory).rglob('*.lisp'):
                source = path.read_text()
                if any(key in source for key in old):
                    keys = set(globals_of(source)) & old
                    if keys:
                        found[str(path.relative_to(root))] = keys
        self.assertEqual(found, {'books/owner-authority-state.lisp': {'fn-owner-canonical-state'}})
        host = (root / 'host/owner-host.lisp').read_text()
        self.assertIn('(fn-oauth-publication (fn-ost-authority state) full4', host)
        for path, field in [('consumer-account-carries-state', ':carries'),
                            ('consumer-account-state', ':root'),
                            ('owner-canonical-read-state', ':canonical')]:
            self.assertIn(f'(fn-oauth-get {field} (fn-ost-authority state))',
                          (root / 'books' / (path + '.lisp')).read_text())


class ReadersCarrierTests(unittest.TestCase):
    def test_all_reader_wrappers_use_the_carried_pair(self):
        from tools.owner_globals_check import globals_of
        root = Path(__file__).resolve().parents[1]
        old = {'fn-owner-reader-views', 'fn-owner-access-cache'}
        found = {}
        for directory in ('books', 'host'):
            for path in (root / directory).rglob('*.lisp'):
                source = path.read_text()
                if any(key in source for key in old):
                    keys = set(globals_of(source)) & old
                    if keys:
                        found[str(path.relative_to(root))] = keys
        self.assertEqual(found, {'books/owner-readers-state.lisp': {'fn-owner-reader-views'}})
        for filename in ('index-connection-pins-host', 'index-connection-repin-prepare-host'):
            self.assertIn('(fn-ordr-index-kind (fn-ost-readers state))',
                          (root / 'host' / (filename+'.lisp')).read_text())
        source = (root / 'host/owner-host.lisp').read_text()
        self.assertIn('(fn-ordr-capture (fn-ost-readers state) event', source)
        self.assertIn('(fn-ordr-cache-install (fn-ost-readers state) cache)', source)
