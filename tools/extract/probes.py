#!/usr/bin/env python3
"""tools/extract/probes.py -- the boundary differential (lane extract-2, e1).

Each probe calls a host entry (a function host/native/*.lisp calls through
fnn-call) with fixed arguments, some violating the entry's guard.  The same
probe runs twice:
  * SBCL: the developer image evaluates (fnn-call 'ENTRY ARGS...): the host's
    entry guard (arity, the guard's KIND conjuncts), then the entry's *1*
    counterpart under guard-checking t (its WHOLE guard), then the entry;
  * CHICKEN: the extracted program's boundary procedure |b:ENTRY| (the
    extractor's rule, tools/extract/chicken.py boundary_def).
Each side prints one line per probe:
    PROBE LABEL host-entry-guard MESSAGE   refused by fnn-entry-guard (its message)
    PROBE LABEL fault MESSAGE              a store fault: the entry's *1* guard check
                                           halted ("ACL2 error in ENTRY: ACL2 Halted")
    PROBE LABEL returned VALUE             accepted; VALUE printed (integers, lists)
    PROBE LABEL other TEXT                 anything else
and the lines must be byte-identical.  ACL2's own guard-violation text
(the untranslated guard and the arguments, through ACL2's printer) is the
diagnostic on the side, not the refusal, and is not compared.

  probes.py scheme OUT.scm      the probes as Scheme (compiled into the binary)
  probes.py sbcl OUT.lisp       the probes as --eval forms for the image
  probes.py run-sbcl IMAGE OUT  run them in the developer image IMAGE, output to OUT
  probes.py compare A B         compare the two outputs; exit 1 naming the first difference
  probes.py sig-vectors LIB OUT the ML-DSA-65 vectors (sig-vectors.json) from the committed carrier
"""
import json
import os
import sys

SECRET = [7] * 32

# A-SIG-NATIVE's vectors (tools/extract/sig-vectors.json, made once by
# `probes.py sig-vectors LIBRARY OUT' from the committed OpenSSL-3.5-signed
# carrier tests/fixtures/dregg-e1/signed.eml): an ML-DSA-65 public key, the
# signed preimage and its signature, which the image's realizer of
# fn-sig-verify (host/native/signatures.lisp) and the program's
# (tools/extract/native.scm) must answer alike, with each mutation.
SIG_VECTORS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sig-vectors.json")


def sig_probes():
    v = json.load(open(SIG_VECTORS))
    pk, m, sig = (list(bytes.fromhex(v[k])) for k in ("public_key", "message", "signature"))
    flip = lambda xs, i: xs[:i] + [xs[i] ^ 1] + xs[i + 1:]  # noqa: E731
    return [
        ("sig-verifies", "FN-SIG-VERIFY", [pk, m, sig]),
        ("sig-flipped-signature", "FN-SIG-VERIFY", [pk, m, flip(sig, 1000)]),
        ("sig-flipped-message", "FN-SIG-VERIFY", [pk, flip(m, len(m) // 2), sig]),
        ("sig-flipped-key", "FN-SIG-VERIFY", [flip(pk, 5), m, sig]),
        ("sig-short-signature", "FN-SIG-VERIFY", [pk, m, sig[:-1]]),
        ("sig-long-key", "FN-SIG-VERIFY", [pk + [0], m, sig]),
        ("sig-non-octet-key", "FN-SIG-VERIFY", [pk[:-1] + [256], m, sig]),
        ("sig-non-list-message", "FN-SIG-VERIFY", [pk, 7, sig]),
        ("sig-empty-message", "FN-SIG-VERIFY", [pk, [], sig]),
    ]


# Probes of a realizer the extracted code calls in place of a function with no
# ACL2 body: the image's fnn-call of the function against the program's
# procedure (chicken.py SHIMS), which every call site in served.scm names.
SHIM_PROBES = {"FN-SIG-VERIFY": "a-native-sig-verify"}
# (label, entry, args); an arg is an int, a list (nested), ("arena",), ("state",),
# or ("u8vec", [...]) (the host's own byte vector).
PROBES = [
    ("chunk-handle", "FN-READER-CHUNK", [7, ("arena",), ("state",)]),
    ("chunk-vector", "FN-READER-CHUNK", [("u8vec", [1, 1]), ("arena",), ("state",)]),
    ("chunk-arity", "FN-READER-CHUNK", [[1, 2]]),
    ("render-ok", "FN-NS-FILE-RENDER", [[1, [97, 98], SECRET]]),
    ("render-short-secret", "FN-NS-FILE-RENDER", [[1, [97, 98], [7, 7]]]),
    ("render-handle", "FN-NS-FILE-RENDER", [7]),
    ("render-arity", "FN-NS-FILE-RENDER", []),
    ("intern-generation", "FN-INTERN-EVENTS", [[], [], -1, ("arena",)]),
    ("intern-keyring", "FN-INTERN-EVENTS", [[], 7, 0, ("arena",)]),
    ("intern-empty", "FN-INTERN-EVENTS", [[], [], 0, ("arena",)]),
] + sig_probes()


def flat_ints(a):
    return isinstance(a, list) and a and all(isinstance(x, int) for x in a)


def scm_arg(a):
    if isinstance(a, int):
        return str(a)
    if flat_ints(a):
        return "'(%s)" % " ".join(map(str, a))
    if isinstance(a, list):
        return "(list %s)" % " ".join(scm_arg(x) for x in a) if a else "'()"
    if a[0] == "arena":
        return "arena"
    if a[0] == "state":
        return "acl2-state"
    if a[0] == "u8vec":
        return "(u8vector %s)" % " ".join(map(str, a[1]))
    raise ValueError(a)


def lisp_arg(a):
    if isinstance(a, int):
        return str(a)
    if flat_ints(a):
        return "'(%s)" % " ".join(map(str, a))
    if isinstance(a, list):
        return "(list %s)" % " ".join(lisp_arg(x) for x in a) if a else "nil"
    if a[0] == "arena":
        return "(fnn-live-arena)"
    if a[0] == "state":
        return "*the-live-state*"
    if a[0] == "u8vec":
        return "(make-array %d :element-type '(unsigned-byte 8) :initial-contents '(%s))" % (
            len(a[1]), " ".join(map(str, a[1])))
    raise ValueError(a)


def scheme(out):
    with open(out, "w") as h:
        h.write(";;; generated by tools/extract/probes.py: the boundary probes\n")
        h.write("(define (boundary-probes arena)\n  (list\n")
        for label, entry, args in PROBES:
            h.write('   (list "%s" "%s" (lambda () (%s %s)))\n' % (
                label, entry, SHIM_PROBES.get(entry, "|b:ACL2::%s|" % entry),
                " ".join(scm_arg(a) for a in args)))
        h.write("))\n")


# The value printer both sides share: integers and lists of them, NIL, else "value".
LISP_PRINTER = """(defun xt-probe-value (v)
  (labels ((p (x) (cond ((integerp x) (format nil "~d" x))
                        ((null x) "NIL")
                        ((and (consp x) (null (cdr (last x))))
                         (format nil "(~{~a~^ ~})" (mapcar #'p x)))
                        (t "value"))))
    (p v)))"""

LISP_PROBE = """(format t "~&PROBE ~a ~a~%" "{label}"
  (handler-case (format nil "returned ~a" (xt-probe-value (first (fnn-call '{entry}{args}))))
    (fnn-entry-guard-fault (c) (format nil "host-entry-guard ~a" (fnn-message c)))
    (fnn-store-fault (c) (format nil "fault ~a" (fnn-message c)))
    (serious-condition (c) (format nil "other ~a" c))))"""


def sbcl(out):
    with open(out, "w") as h:
        h.write('(in-package "ACL2")\n')
        h.write(LISP_PRINTER + "\n")
        for label, entry, args in PROBES:
            h.write(LISP_PROBE.replace("{label}", label).replace("{entry}", entry).replace(
                "{args}", "".join(" " + lisp_arg(a) for a in args)) + "\n")


def run_sbcl(image, out):
    """Evaluate the probes in the developer image's saved core, in place of its
    entry (tests/test_native_entry_guard.py's image_command)."""
    import os
    import shlex
    import subprocess
    from pathlib import Path
    root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(root))
    from tests.test_native_entry_guard import image_command  # noqa: E402
    import tests.test_native_entry_guard as eg
    eg.IMAGE = Path(image)
    forms_file = Path(out + ".lisp")
    sbcl(str(forms_file))
    argv, env = image_command(['(load "%s")' % forms_file.resolve()])
    r = subprocess.run(argv, env=env, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       timeout=600, check=False)
    Path(out).write_bytes(r.stdout)
    return r.returncode


def compare(a, b):
    la = [l for l in open(a).read().splitlines() if l.startswith("PROBE ")]
    lb = [l for l in open(b).read().splitlines() if l.startswith("PROBE ")]
    if len(la) != len(PROBES) or len(lb) != len(PROBES):
        print("probes: expected %d lines, have %d (sbcl) and %d (chicken)" % (len(PROBES), len(la), len(lb)))
        return 1
    bad = 0
    for x, y in zip(la, lb):
        if x != y:
            bad += 1
            print("DIFFER\n  sbcl:    %s\n  chicken: %s" % (x, y))
    kinds = {}
    for x in la:
        k = x.split(" ")[2]
        kinds[k] = kinds.get(k, 0) + 1
    print("probes: %d of %d identical; sbcl outcomes %s" % (len(la) - bad, len(la), kinds))
    return 1 if bad else 0


def sig_vectors(library, out):
    """The committed carrier's ML-DSA-65 (key, preimage, signature) triple that
    LIBRARY verifies (tests/mldsa65_interop.py's extraction: a wrong parse
    cannot verify), written to OUT."""
    from pathlib import Path
    root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(root))
    from tests.mldsa65_interop import Seam, carrier_candidates  # noqa: E402
    seam = Seam(library)
    data = (root / "tests/fixtures/dregg-e1/signed.eml").read_bytes()
    for found in carrier_candidates(data):
        for (pk, msg, sig), _ in found:
            if seam.lib.fn_mldsa65_verify(sig, len(sig), msg, len(msg), pk) == 0:
                Path(out).write_text(json.dumps({
                    "about": "an OpenSSL-3.5-made ML-DSA-65 signature over fn's signed preimage, from the "
                             "committed carrier tests/fixtures/dregg-e1/signed.eml (probes.py sig-vectors)",
                    "public_key": pk.hex(), "message": msg.hex(), "signature": sig.hex()}, indent=1) + "\n")
                return 0
    print("sig-vectors: no carrier triple verifies under %s" % library)
    return 1


if __name__ == "__main__":
    verb = sys.argv[1]
    if verb == "sig-vectors":
        sys.exit(sig_vectors(sys.argv[2], sys.argv[3]))
    if verb == "scheme":
        scheme(sys.argv[2])
    elif verb == "sbcl":
        sbcl(sys.argv[2])
    elif verb == "run-sbcl":
        sys.exit(run_sbcl(sys.argv[2], sys.argv[3]))
    elif verb == "compare":
        sys.exit(compare(sys.argv[2], sys.argv[3]))
    else:
        sys.exit(__doc__)
