"""tools/spec_cite_check.py: a spec cannot cite a name the tree no longer defines (PKT-312)."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import spec_cite_check as scc  # noqa: E402

DEFINED = {"fn-bpn-limits-compose-at-the-codec-widths", "fn-sn-step"}
SPEC = ("specs/bp.md",
        "D-9: raised only with `fn-bpn-limits-compose`.\n"
        "Now `fn-bpn-limits-compose-at-the-codec-widths` and `FN-SN-STEP`.\n"
        "Prose: `fn-bpn`, `fn-bpn-*`, `fn-<rec>-shapep`, `fn-hybrid-v1`, "
        "`(fn-sn-step s)`, `books/x.lisp`.\n")


class SpecCiteCheckTests(unittest.TestCase):
    def test_a_retired_theorem_name_is_undefined_and_fails(self):
        result = scc.check(DEFINED, [SPEC], {})
        self.assertEqual(result.unlisted, {"fn-bpn-limits-compose": ["specs/bp.md:1"]})
        self.assertFalse(result.ok)
        self.assertEqual(result.resolved, 2)  # case-insensitive
        self.assertEqual(result.ruled, {"template": 2, "short": 1, "tag": 1})
        self.assertEqual(result.checked, 7)  # the call form and the path are not names

    def test_a_listed_stale_citation_is_counted_not_failed_and_only_in_its_file(self):
        listing = {"stale": {"PKT-446": {"fn-bpn-limits-compose": ["specs/bp.md"]}}}
        result = scc.check(DEFINED, [SPEC], listing)
        self.assertTrue(result.ok)
        self.assertEqual(result.stale, {"fn-bpn-limits-compose": ["specs/bp.md:1"]})
        other = ("docs/new.md", "see `fn-bpn-limits-compose`\n")
        result = scc.check(DEFINED, [SPEC, other], listing)
        self.assertEqual(result.unlisted, {"fn-bpn-limits-compose": ["docs/new.md:1"]})

    def test_a_repaired_citation_makes_its_entry_unused(self):
        listing = {"stale": {"PKT-446": {"fn-bpn-limits-compose": ["specs/bp.md"]}},
                   "exemptions": {"fn-gone-name": "was prose"}}
        repaired = ("specs/bp.md", "`fn-bpn-limits-compose-at-the-codec-widths`\n")
        result = scc.check(DEFINED, [repaired], listing)
        self.assertFalse(result.ok)
        self.assertEqual(len(result.unused), 2)

    def test_an_exemption_needs_its_reason_and_resolves(self):
        listing = {"exemptions": {"fn-bpn-limits-compose": "a historical name in a changelog"}}
        result = scc.check(DEFINED, [SPEC], listing)
        self.assertTrue(result.ok)
        self.assertEqual(result.exempted, {"fn-bpn-limits-compose": 1})

    def test_a_slash_abbreviation_resolves_only_when_every_expansion_does(self):
        self.assertEqual(scc.abbreviated("fnn-metadata-frontier-frame/-decode/-next"),
                         ["fnn-metadata-frontier-frame", "fnn-metadata-frontier-decode",
                          "fnn-metadata-frontier-next"])
        defined = {"fn-a-frame", "fn-a-decode"}
        good = ("specs/x.md", "`fn-a-frame/-decode`\n")
        bad = ("specs/x.md", "`fn-a-frame/-decode/-next`\n")
        self.assertTrue(scc.check(defined, [good], {}).ok)
        self.assertEqual(list(scc.check(defined, [bad], {}).unlisted),
                         ["fn-a-frame/-decode/-next"])

    def test_a_record_name_is_defined(self):
        # (fn-defrecord fn-node-state ...) in books/node.lisp: prose names the
        # record kind, which no defun spells.
        self.assertIn("fn-node-state", scc.defined_names())

    def test_a_macro_generated_name_is_defined(self):
        template = """(defmacro fn-rpf-define-buffer ()
  `(defstobj fn-recovery-profile-buffer
     (fn-rpf-bytes :type (array (unsigned-byte 8)
                               (,(nth 7 (fn-recovery-profile-envelope))))
                   :initially 0)
     :inline t))
"""
        self.assertEqual(scc.macro_generated_definitions(
            template + "(fn-rpf-define-buffer)\n"), {"fn-recovery-profile-buffer"})
        self.assertEqual(scc.macro_generated_definitions(template), set())
        self.assertEqual(scc.macro_generated_definitions("""
(defmacro fn-define-buffer (name)
  `(defstobj ,name (bytes :initially 0)))
(fn-define-buffer fn-buffer)
"""), set())
        self.assertIn("fn-recovery-profile-buffer", scc.defined_names())

    def test_a_def_buffer_stobj_is_defined(self):
        # books/native-control-buffer.lisp: (def-buffer fn-octets-ctl)
        self.assertIn("fn-octets-ctl", scc.defined_names())

    def test_concatenated_definer_names_come_only_from_emitted_definitions(self):
        source = """
(defconst *model-definitions* '(model-invp model-step))
(defun instance-name (prefix original)
  (intern-in-package-of-symbol
    (concatenate 'string (symbol-name prefix) "-"
      (subseq (symbol-name original) 6 (length (symbol-name original)))) prefix))
(defun instance-events (prefix originals)
  (if (endp originals) nil
    (cons `(defun ,(instance-name prefix (car originals)) (x)
             ;; Merely calling a constructed name does not define it.
             (,(instance-name prefix 'model-referenced-only) x))
          (instance-events prefix (cdr originals)))))
(defmacro define-instance (prefix)
  `(make-event (cons 'progn (instance-events ',prefix *model-definitions*))))
(define-instance fn-first)
(define-instance fn-second)
; (define-instance fn-comment)
'(define-instance fn-quoted)
(defun unused-example () (define-instance fn-unexecuted))
"""
        names = scc.concatenated_macro_definitions(source)
        self.assertEqual(names, {"fn-first-invp", "fn-first-step",
                                 "fn-second-invp", "fn-second-step"})
        result = scc.check(names, [("docs/example.md",
            "`fn-first-invp` `fn-second-step` `fn-first-never-built` "
            "`fn-first-referenced-only` `fn-comment-invp` "
            "`fn-quoted-invp` `fn-unexecuted-invp`")], {})
        self.assertEqual(result.resolved, 2)
        self.assertEqual(set(result.unlisted), {
            "fn-first-never-built", "fn-first-referenced-only",
            "fn-comment-invp", "fn-quoted-invp", "fn-unexecuted-invp"})

    def test_unknown_definer_condition_cannot_admit_either_branch(self):
        source = """
(defmacro define-choice (prefix)
  (if (unmodelled-condition)
      `(defun ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name prefix) "-yes") prefix) () t)
    `(defun ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name prefix) "-no") prefix) () nil)))
(define-choice fn-choice)
"""
        self.assertEqual(scc.concatenated_macro_definitions(source), set())

    def test_definer_conditions_distinguish_strings_from_symbols(self):
        source = """
(defmacro define-choice (prefix)
  (let ((suffix (if (equal "nil" 'nil) "-wrong"
                  (if "nil" "-truth" "-also-wrong"))))
    `(defun ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name prefix) suffix) prefix) () t)))
(define-choice fn-choice)
"""
        self.assertEqual(scc.concatenated_macro_definitions(source), {"fn-choice-truth"})

    def test_definer_keyword_conditions_use_the_actual_first_value(self):
        source = """
(defmacro define-view (prefix &key view)
  (let ((name (intern-in-package-of-symbol
                (concatenate 'string (symbol-name prefix) "-view") prefix)))
    `(progn ,@(and view `((defthm ,name t))))))
(define-view fn-visible :view t)
(define-view fn-hidden :view nil :view t)
(define-view fn-bad-call :view t :unknown t)
(define-view fn-odd-call :view t :view)
"""
        self.assertEqual(scc.concatenated_macro_definitions(source), {"fn-visible-view"})

    def test_runtime_layer_definer_resolves_both_actual_prefixes(self):
        from ledger import Reader, head
        source = (ROOT / "books/runtime-contract-layer.lisp").read_text()
        calls = [form for path in (ROOT / "books/runtime-contract-echo.lisp",
                                   ROOT / "books/post-transaction-layer.lisp")
                 for form, _ in Reader(path.read_text()).top_level()
                 if head(form) == "fn-rtc-def-layer"]
        names = scc.concatenated_macro_definitions(source, calls)
        for prefix in ("fn-rcl", "fn-ptl"):
            self.assertIn(prefix + "-invp", names)
            self.assertIn(prefix + "-x-deliver-types", names)
            self.assertIn(prefix + "-host-landing-is-the-contract-step", names)
            self.assertNotIn(prefix + "-never-built", names)
            # The machine's supplied init is referenced, not renamed/defined.
            self.assertNotIn(prefix + "-m-init", names)

    def test_a_def_generic_export_is_defined(self):
        # books/payload-arena.lisp: (def-generic fn-arena ... :exports
        # ((:update fn-arena-seal-buffer :logic fn-arena$a-seal-buffer) ...))
        self.assertIn("fn-arena-seal-buffer", scc.defined_names())
        self.assertNotIn("fn-arena-seal-no-such-export", scc.defined_names())

    def test_the_tree_is_green_under_strict(self):
        self.assertEqual(scc.main(["--summary", "--strict"]), 0)

    def test_no_citation_is_filed_stale(self):
        # BM08: the listing is repaired prose or a reasoned exemption, never a parked debt.
        import json
        listing = json.loads((Path(scc.__file__).resolve().parent / "spec_cite_exemptions.json").read_text())
        self.assertEqual(listing["stale"], {})


if __name__ == "__main__":
    unittest.main()
