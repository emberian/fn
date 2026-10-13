"""Execute the actual prepare adapters with already-decided core replies.

The constructor and recognizer are fixture seams, not models of their policy.
Entering the interner, prepare, or install on a refusal fails this probe. The
constructor's codec decisions have separate ACL2 teeth in store-node-tests.
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_source import forms, read_all


def actual(path, name, kind="defun"):
    matches = [form for form in forms((ROOT / path).read_text())
               if re.match(r"\(" + kind + r"\s+" + re.escape(name) + r"\s", form, re.I)]
    if len(matches) != 1:
        raise AssertionError((path, name, len(matches)))
    # ACL2's declaration describes its stobjs/mode; the adapter body is exact.
    form = matches[0]
    if kind == "defun":
        declaration = next((node for node in read_all(form)[0].items
                            if form[node.start:node.end].startswith("(declare (xargs")), None)
        if declaration:
            form = form[:declaration.start] + form[declaration.end:]
    return form


def guard_probe_source():
    """ACL2 probe with image flags, real budget code and live fixture stobjs.

    Constructor/context seams select the already-decided refusal. The actual
    budget and its callees are loaded from books; the memory-gate body is exact.
    Unlike the SBCL adapter test, all host xargs declarations are retained.
    Execute this driver only through tools/proof_repl.py.
    """
    def declared(path, name):
        return next(f for f in forms((ROOT / path).read_text())
                    if f.startswith("(defun " + name + " "))

    # Live fixtures replace the representation owners, never a budget guard.
    names = {
        "fn-octets": "fn-l18-octets", "fn-arena": "fn-l18-arena",
        "fn-cat": "fn-l18-cat", "fn-hist": "fn-l18-hist",
    }
    fixtures = {
        "fn-owner-store": ("state", "(f-get-global 'fn-l18-word state)", "state"),
        "fn-owner-core": ("state", "nil", "state"),
        "fn-own-clock": ("o", "nil", ""),
        "fn-store-groups-from-codes": ("codes groups", "'(\"fn.test\")", ""),
        "fn-store-octets->string": ("xs", "(fn-record-octets-string xs)", ""),
        "fn-pfld-article-inputsp": ("mid size groups id subject evidence charge", "t", ""),
        "fn-store-existing-action": ("mid payload groups s fn-l18-arena", "nil", "fn-l18-arena"),
        "fn-pidx-existing-action-cat": ("mid fn-l18-octets groups o fn-l18-arena fn-l18-cat", "nil", "fn-l18-octets fn-l18-arena fn-l18-cat"),
        "fn-adm-handle-room-p": ("count n", "t", ""),
        "fn-arena-count": ("fn-l18-arena", "0", "fn-l18-arena"),
        "fn-octets-list": ("fn-l18-octets", "nil", "fn-l18-octets"),
        "fn-octets-len": ("fn-l18-octets", "0", "fn-l18-octets"),
        "fn-sn-article-record": ("s obs mid payload groups id subject evidence charge", "s", ""),
        "fn-owner-record-octets": ("fn-l18-hist state", "(mv 0 fn-l18-hist state)", "fn-l18-hist state"),
        "fn-owner-record-debt": ("fn-l18-hist state", "(mv 0 fn-l18-hist state)", "fn-l18-hist state"),
        "fn-owner-record-totals": ("fn-l18-hist state", "(mv nil fn-l18-hist state)", "fn-l18-hist state"),
        "fn-owner-profile-carry": ("state", "nil", "state"),
        "fn-owner-store-profile": ("state", "nil", "state"),
        "fn-owner-ocfg": ("state", "nil", "state"),
        "fn-owner-parse-carry": ("state", "nil", "state"),
        "fn-owner-retain-carry": ("state", "nil", "state"),
        "fn-prc-refresh": ("carry ledger", "nil", ""),
        "fn-pout-prepare-article": ("before row budget carry", "(mv :prepared before)", ""),
        "fn-ppc-pout-prepare-article-cat": ("before row budget carry fn-l18-arena fn-l18-cat", "(mv :prepared before)", "fn-l18-arena fn-l18-cat"),
        "fn-owner-retain-carry-put": ("carry state", "state", "state"),
        "fn-owner-install-ocfg": ("before state", "state", "state"),
        "fn-store-sn-domain": ("state", "nil", "state"),
        "fn-psrv-store-prepare-next": ("cfg s record count", "s", ""),
        "fn-psrv-store-refusal-kind": ("cfg s record", ":refused", ""),
        "fn-adm-article-word": ("word profile img cfg limit count bytes record debt tot row", "word", ""),
        "fn-adm-memory-admitp": ("profile img cfg limit tot row", "nil", ""),
        "fn-owner-config": ("state", "nil", "state"),
        "fn-cfg-value": ("cfg", "nil", ""),
        "fn-owner-memory-cfg": ("v tls trigger pub live cold profile window server config", "nil", ""),
        "fn-oag-agent": ("cfg", "nil", ""),
        "fn-adm-cfg-at": ("cfg cap", "nil", ""),
        "fn-mm-cfg-connections": ("cfg", "0", ""),
    }
    for name in fixtures:
        names[name] = "fn-l18-seam-" + name.removeprefix("fn-")

    def rewrite(form):
        # Symbols only: never rewrite prose or a source literal.
        from lisp_source import tokens
        for kind, start, end in reversed(list(tokens(form))):
            if kind == "atom" and form[start:end] in names:
                form = form[:start] + names[form[start:end]] + form[end:]
        return form

    source = '''(in-package "ACL2")
(include-book "../../../books/store-profile-carried")
(defstobj fn-l18-octets (l18-octets-cell :initially nil))
(defstobj fn-l18-arena (l18-arena-cell :initially nil))
(defstobj fn-l18-cat (l18-cat-cell :initially nil))
(defstobj fn-l18-hist (l18-hist-cell :initially nil))
'''
    for name, (args, body, stobjs) in fixtures.items():
        declaration = " :stobjs (" + stobjs + ")" if stobjs else ""
        used = set(re.findall(r"[A-Za-z0-9-]+", body))
        ignored = [arg for arg in args.split() if arg not in used]
        ignore = " (declare (ignore " + " ".join(ignored) + "))" if ignored else ""
        source += f"(defun {names[name]} ({args}) (declare (xargs :mode :program :guard t{declaration})){ignore} {body})\n"
    source += '''(defun fn-l18-seam-apc-intern-row-at (record keyring generation h carry)
 (declare (xargs :mode :program :guard (and (fn-record-p record) (fn-prin-keyringp keyring) (natp generation) (natp h))))
 (declare (ignore record keyring generation h carry))
 (hard-error 'fn-l18-guard-probe "Refusal reached the interner" nil))
'''
    names["fn-apc-intern-row-at"] = "fn-l18-seam-apc-intern-row-at"
    source += rewrite(declared("host/owner-host.lisp", "fn-owner-memory-gate")) + "\n"
    for path, name in [("host/owner-host.lisp", "fn-owner-prepare"),
                       ("host/owner-host.lisp", "fn-owner-prepare-buffer"),
                       ("host/store-node-host.lisp", "fn-store-sn-prepare")]:
        source += rewrite(declared(path, name)) + "\n"
    source += '''(defun fn-l18-guard-probe (words fn-l18-octets fn-l18-arena fn-l18-cat fn-l18-hist state)
 (declare (xargs :mode :program :stobjs (fn-l18-octets fn-l18-arena fn-l18-cat fn-l18-hist state)))
 (if (endp words)
     (mv nil fn-l18-octets fn-l18-arena fn-l18-cat fn-l18-hist state)
   (let ((state (f-put-global 'fn-l18-word (car words) state)))
    (mv-let (erp word fn-l18-arena fn-l18-hist state)
      (fn-owner-prepare '(60 97 64 120 62) '(65) '(0) '(105) '(115) '(101) 1 fn-l18-arena fn-l18-hist state)
      (if (or erp (not (equal word (car words)))) (hard-error 'fn-l18-guard-probe "Owner refused incorrectly" nil)
       (mv-let (erp word fn-l18-arena fn-l18-hist state)
         (fn-owner-prepare-buffer '(60 97 64 120 62) '(0) '(105) '(115) '(101) 1 fn-l18-octets fn-l18-arena fn-l18-cat fn-l18-hist state)
         (if (or erp (not (equal word (car words)))) (hard-error 'fn-l18-guard-probe "Buffer refused incorrectly" nil)
          (let ((state (f-put-global 'fn-store-sn (car words) state)))
           (mv-let (erp word fn-l18-arena state)
             (fn-store-sn-prepare '(60 97 64 120 62) '(65) '(0) '(105) '(115) '(101) 1 nil fn-l18-arena state)
             (if (or erp (not (equal word (car words)))) (hard-error 'fn-l18-guard-probe "Store refused incorrectly" nil)
              (prog2$ (cw "GUARD-T ALL-THREE ~x0 budget=~x1 memory=~x2~%" word
                           (fn-pvc-article-budget-carried nil nil 0 0 word 0)
                           (fn-owner-memory-gate state))
                (fn-l18-guard-probe (cdr words) fn-l18-octets fn-l18-arena fn-l18-cat fn-l18-hist state))))))))))))
(defun fn-l18-guard-probe-local (state)
 (declare (xargs :mode :program :stobjs state))
 (with-local-stobj fn-l18-octets
  (mv-let (erp fn-l18-octets state)
   (with-local-stobj fn-l18-arena
    (mv-let (erp fn-l18-octets fn-l18-arena state)
     (with-local-stobj fn-l18-cat
      (mv-let (erp fn-l18-octets fn-l18-arena fn-l18-cat state)
       (with-local-stobj fn-l18-hist
        (mv-let (erp fn-l18-octets fn-l18-arena fn-l18-cat fn-l18-hist state)
         (fn-l18-guard-probe *fn-sn-article-record-refusals* fn-l18-octets fn-l18-arena fn-l18-cat fn-l18-hist state)
         (mv erp fn-l18-octets fn-l18-arena fn-l18-cat state)))
       (mv erp fn-l18-octets fn-l18-arena state)))
     (mv erp fn-l18-octets state)))
   (mv erp state))))
(set-check-invariant-risk t)
(with-guard-checking-event t
 (value-triple (cw "IMAGE GUARD=~x0 INVARIANT-RISK=~x1~%" (@ guard-checking-on) (@ check-invariant-risk))))
(with-guard-checking-event t
 (make-event
  (mv-let (erp state)
    (fn-l18-guard-probe-local state)
    (if erp (er soft 'fn-l18-guard-probe "Guard probe returned an error")
      (value '(value-triple :guards-passed))))))
'''
    for message in ("Owner refused incorrectly", "Buffer refused incorrectly", "Store refused incorrectly"):
        error = f'(hard-error \'fn-l18-guard-probe "{message}" nil)'
        source = source.replace(error, "(mv " + error + " fn-l18-octets fn-l18-arena fn-l18-cat fn-l18-hist state)")
    return source


@unittest.skipUnless(shutil.which("sbcl"), "SBCL needed for host adapter probe")
class OwnerPrepareRefusals(unittest.TestCase):
    def test_guard_probe_keeps_the_image_flags_and_real_budget(self):
        source = guard_probe_source()
        read_all(source, strict=True)
        self.assertIn("(with-guard-checking-event t", source)
        self.assertIn("(set-check-invariant-risk t)", source)
        self.assertNotIn("with-guard-checking-event :none", source)
        self.assertNotIn("(defun fn-pvc-article-budget-carried", source)
        self.assertIn("(fn-l18-guard-probe *fn-sn-article-record-refusals*", source)
        for name in ("fn-owner-prepare", "fn-owner-prepare-buffer", "fn-store-sn-prepare"):
            self.assertIn("(defun " + name, source)
        # The real budget entry's domain admits every constructor keyword.
        self.assertIn("(xargs :guard t)", next(
            form for form in forms((ROOT / "books/store-profile-carried.lisp").read_text())
            if form.startswith("(defun fn-pvc-article-budget-carried ")))

    def test_constructor_refusals_return_by_name_without_interning(self):
        sources = "\n".join([
            actual("books/store-node.lisp", "*fn-sn-article-record-refusals*", "defconst"),
            actual("host/owner-host.lisp", "fn-owner-prepare"),
            actual("host/owner-host.lisp", "fn-owner-prepare-buffer"),
            actual("host/store-node-host.lisp", "fn-store-sn-prepare"),
            actual("host/native/owner.lisp", "fnn-owner-prepare-refusal-word"),
        ])
        prefix = r'''
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defmacro defconst (name value) `(defparameter ,name ,value))
(defmacro mv (&rest xs) `(values ,@xs))
(defmacro mv-let (vars form &body body) `(multiple-value-bind ,vars ,form ,@body))
(defun len (x) (length x))
'''
        prefix += r'''
(defvar *reply*)
(defvar *expected-charge*)
(defvar *constructor-calls* 0)
(defvar *interns* 0)
(defvar *prepares* 0)
(defvar *installs* 0)
(defun fn-record-p (x) (equal x '(:record)))
(defun fn-sn-article-record (s obs mid payload groups id subject evidence charge)
 (declare (ignore s obs mid payload groups id subject evidence))
 (assert (= charge *expected-charge*))
 (incf *constructor-calls*) *reply*)
(defun fn-store-octets->string (xs) (coerce (mapcar #'code-char xs) 'string))
(defun fn-store-groups-from-codes (codes domain) (declare (ignore codes domain)) '("fn.test"))
(defun fn-octet-listp (xs) (and (listp xs) (every (lambda (x) (typep x '(unsigned-byte 8))) xs)))
(defun fn-pfld-article-inputsp (&rest args) (declare (ignore args)) t)
(defun fn-store-existing-action (&rest args) (declare (ignore args)) nil)
(defun fn-pidx-existing-action-cat (&rest args) (declare (ignore args)) nil)
(defun fn-adm-handle-room-p (&rest args) (declare (ignore args)) t)
(defun fn-octets-list (buffer) (declare (ignore buffer)) '(65))
(defun fn-octets-len (buffer) (declare (ignore buffer)) 1)
(defun fn-owner-record-octets (hist state) (values 0 hist state))
(defun fn-owner-record-debt (hist state) (values 0 hist state))
(defun fn-owner-record-totals (hist state) (values nil hist state))
(defun fn-owner-memory-gate (state) (declare (ignore state)) '(0 0 0))
(defun fn-apc-intern-row-at (record &rest args)
 (declare (ignore args)) (assert (fn-record-p record)) (incf *interns*) :row)
(defun fn-pout-prepare-article (&rest args)
 (declare (ignore args)) (incf *prepares*) (values :prepared :next))
(defun fn-ppc-pout-prepare-article-cat (&rest args)
 (declare (ignore args)) (incf *prepares*) (values :prepared :next))
(defun fn-owner-install-ocfg (next state)
 (declare (ignore next)) (incf *installs*) state)
(defun fn-psrv-store-prepare-next (&rest args)
 (declare (ignore args)) (incf *prepares*) :next)
(defun f-put-global (key next state)
 (declare (ignore key next)) (incf *installs*) state)
(defun f-get-global (key state) (declare (ignore key state)) :store)
(defun fn-adm-article-word (word &rest args) (declare (ignore args)) word)
(defun fn-owner-retain-carry-put (carry state) (declare (ignore carry)) state)
(defun fn-record-payload (record) (assert (fn-record-p record)) '(65))
(defun fnn-fault (&rest args) (error "Unknown prepare word: ~s" args))
'''
        for name in ("fn-owner-store", "fn-state-groups", "fn-node-acceptance", "fn-sn-node",
                     "fn-own-clock", "fn-owner-core", "fn-pvc-article-budget-carried",
                     "fn-owner-profile-carry", "fn-owner-store-profile", "fn-sf-records-count",
                     "fn-sn-files", "fn-owner-ocfg", "fn-sn-keyring", "fn-sn-keyring-generation",
                     "fn-arena-count", "fn-owner-parse-carry", "fn-adm-memory-admitp", "fn-prc-refresh",
                     "fn-owner-retain-carry", "fn-node-retention", "fn-sbud-count", "fn-store-sn-domain"):
            prefix += f"(defun {name} (&rest args) (declare (ignore args)) 0)\n"
        suffix = r'''
(defun probe (reply charge)
 (let ((*reply* reply) (*expected-charge* charge)
       (*constructor-calls* 0) (*interns* 0) (*prepares* 0) (*installs* 0))
   (let ((results
          (list
           (multiple-value-list (fn-owner-prepare '(60 97 64 120 62) '(65) '(0) '(105) '(115) '(101) charge :arena :hist :state))
           (multiple-value-list (fn-owner-prepare-buffer '(60 97 64 120 62) '(0) '(105) '(115) '(101) charge :octets :arena :cat :hist :state))
           (multiple-value-list (fn-store-sn-prepare '(60 97 64 120 62) '(65) '(0) '(105) '(115) '(101) charge :clock :arena :state)))))
     (assert (= *constructor-calls* 3))
     (if (fn-record-p reply)
         (progn
          (assert (equal (mapcar #'second results) '((:seal (65)) :seal-buffer (:seal (65)))))
          (assert (= *interns* 2)) (assert (= *prepares* 3)) (assert (= *installs* 4)))
         (progn
          (assert (equal results (list (list nil reply :arena :hist :state)
                                       (list nil reply :arena :hist :state)
                                       (list nil reply :arena :state))))
          (assert (eq (fnn-owner-prepare-refusal-word reply) reply))
          (assert (zerop *interns*)) (assert (zerop *prepares*)) (assert (zerop *installs*))
          (format t "NAMED-NOT-INTERNED ~s charge=~d~%" reply charge))))))
(dolist (word *fn-sn-article-record-refusals*) (probe word (expt 2 64)))
(probe '(:record) 1)
(assert (eq (fnn-owner-prepare-refusal-word :invalid) :malformed))
(assert (eq (fnn-owner-prepare-refusal-word :unaffordable) :unaffordable))
(assert (handler-case (progn (fnn-owner-prepare-refusal-word :unknown) nil) (error () t)))
(write-line "OWNER-PREPARE-REFUSALS-PASS")
'''
        path = ROOT / "build/codex/l-seq/host-refusal-unit-probe.lisp"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(prefix + sources + suffix)
        completed = subprocess.run(
            ["sbcl", "--noinform", "--disable-debugger", "--script", str(path)],
            cwd=ROOT, capture_output=True, text=True, timeout=30)
        (path.parent / "host-refusal-unit-sbcl.log").write_text(completed.stdout + completed.stderr)
        self.assertEqual(completed.returncode, 0, completed.stderr[-12000:])
        self.assertIn("NAMED-NOT-INTERNED :CHARGE-INVALID charge=18446744073709551616", completed.stdout)
        self.assertIn("OWNER-PREPARE-REFUSALS-PASS", completed.stdout)


if __name__ == "__main__":
    unittest.main()
