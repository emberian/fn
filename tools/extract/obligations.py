#!/usr/bin/env python3
"""tools/extract/obligations.py -- X1's obligations O2 (closure and initialization) and O3 (entry
conditions), checked by running the same forms in the reference image and in fn-core.
EXTRACTION-PROGRAM-20261007.md section 7 states the four obligations.

O2: every extracted global (a `var:' unit: a defconst, defparameter or defvar the closure reads), every
ACL2 state global the closure reads (a `global:' unit) and every value core-world.lisp sets holds the
same value in fn-core as in the image, before fn starts; so does every world global the snapshot
carries (fgetprop NAME 'global-value; closure_why.py --check-props keeps that list complete).
O3: every root the host calls (edges.tsv `#root' lines naming a function) has the same entry-guard
specification in both processes: host/native/io.lisp's own fnn-entry-guard-spec (arity, formals'
recognizers and kinds, read from the world in the image and from the carried snapshot in fn-core) and
fnn-trailing-kind (the live stobjs before a trailing state).

Each side prints one line per item, `OB KIND NAME TEXT`, where TEXT comes from one canonical printer
that both sides evaluate.  It is a single line and the same in both processes: symbols are
package-qualified, uninterned ones print as #:, cycles and depth are bounded, numeric arrays over
4096 elements print as a dimension list and an order-sensitive hash.  The lines must be identical,
item for item, apart from the reviewed exclusions in EXCLUDED, each with its reason.

  obligations.py forms OUT_DIR CORE_OUT     write OUT_DIR/obligations.lisp from CORE_OUT's manifest and edges
  obligations.py run-image IMAGE OUT_DIR    evaluate them in the image (at *ld-level* 1, as probes.py does)
  obligations.py run-core CORE OUT_DIR      evaluate them in fn-core (`--xl-load')
  obligations.py compare OUT_DIR            compare OUT_DIR/image.out with OUT_DIR/core.out; exit 1 naming each difference
"""
import os
import re
import subprocess
import sys
from pathlib import Path

# Items whose value legitimately differs between a saved ACL2 image and fn-core, each with the reason.
# An entry is (KIND, NAME); NAME is package::name as printed.  Keep this list short and reviewed.
EXCLUDED = {
    ("VAR", "ACL2::*AOKP*"): "ACL2's ld binds it while a command runs (the image is sampled inside ld-fn); "
                             "both sides are non-NIL, the only test ACL2 makes of it (attachments allowed)",
    ("VAR", "ACL2::*FIND-PACKAGE-CACHE*"): "a one-entry cache of ACL2's last find-package; contents depend on history",
    ("VAR", "ACL2::*PACKAGE-ALIST*"): "ACL2's package-name cache, filled on demand; contents depend on history",
    ("VAR", "ACL2::*USER-STOBJ-ALIST*"): "fn-core keeps its live stobjs in clruntime's *xl-user-stobj-alist*; the one "
                                         "emitted reader, REPLACE-LIVE-STOBJS-IN-LIST, only renders a guard-violation message",
}

PRINTER = r"""
(defun xt-ob-text (x)
  (let ((seen (make-hash-table :test 'eq)))
    (with-output-to-string (s)
      (labels ((sym (y) (if (symbol-package y)
                            (format s "~a::~a" (package-name (symbol-package y)) (symbol-name y))
                            (write-string "#:" s)))
               (p (y d)
                 (cond ((> d 200) (write-string "#deep" s))
                       ((symbolp y) (sym y))
                       ((integerp y) (format s "~d" y))
                       ((rationalp y) (format s "~d/~d" (numerator y) (denominator y)))
                       ((floatp y) (format s "~a" (multiple-value-list (integer-decode-float y))))
                       ((complexp y) (write-string "#C(" s) (p (realpart y) d) (write-string " " s) (p (imagpart y) d) (write-string ")" s))
                       ((characterp y) (format s "#\\~d" (char-code y)))
                       ((stringp y) (format s "\"~{~d~^,~}\"" (map 'list #'char-code y)))
                       ((consp y)
                        ;; SEEN holds the conses on the current path only: shared structure prints in full
                        ;; (the image keeps sharing that fn-core's printed-and-read constants do not), a true
                        ;; cycle prints #cycle
                        (if (gethash y seen) (write-string "#cycle" s)
                            (let ((path nil))
                              (write-string "(" s)
                              (loop for tail = y then (cdr tail)
                                    for i from 0
                                    while (consp tail)
                                    do (when (gethash tail seen) (write-string " . #cycle" s) (return))
                                       (when (> i 0) (write-string " " s))
                                       (setf (gethash tail seen) t) (push tail path)
                                       (p (car tail) (1+ d))
                                    finally (when tail (write-string " . " s) (p tail (1+ d))))
                              (dolist (c path) (remhash c seen))
                              (write-string ")" s))))
                       ((arrayp y)
                        (let ((n (array-total-size y)))
                          (format s "#A~a~a(" (array-dimensions y) (if (typep y '(array t)) "" (prin1-to-string (array-element-type y))))
                          (if (and (> n 4096) (not (typep y '(array t))))
                              (let ((h 0)) (dotimes (i n) (setq h (mod (+ (* h 1000003) (sxhash (row-major-aref y i))) 2305843009213693951)))
                                (format s "hash ~d" h))
                              (dotimes (i (min n 4096)) (when (> i 0) (write-string " " s)) (p (row-major-aref y i) (1+ d))))
                          (when (and (> n 4096) (typep y '(array t))) (write-string " ..." s))
                          (write-string ")" s)))
                       ((hash-table-p y) (format s "#HT(~a ~d)" (hash-table-test y) (hash-table-count y)))
                       ((functionp y) (write-string "#<FUNCTION>" s))
                       (t (format s "#<~a>" (let ((ty (type-of y))) (if (symbolp ty) (symbol-name ty) "OBJECT")))))))
        (p x 0)))))
(defmacro xt-ob (kind name form)
  `(format t "~&OB ~a ~a ~a~%" ,kind ,name
           (handler-case ,form (serious-condition (c) (format nil "#ERROR ~a" (type-of c))))))
"""


def manifest_items(core_out):
    """(vars, globals, roots): the symbols of `var:' and `global:' units, and every #root function."""
    vars_, globals_, roots = [], [], []
    for line in (Path(core_out) / "manifest.tsv").read_text(encoding="latin-1").splitlines():
        if line.startswith("#") or not line.strip():
            continue
        uid = line.split("\t", 1)[0]
        kind, _, sym = uid.partition(":")
        if kind == "var":
            vars_.append(sym)
        elif kind == "global":
            globals_.append(sym)
    for line in (Path(core_out) / "edges.tsv").read_text(encoding="latin-1").splitlines():
        if line.startswith("#root\t"):
            uid = line.split("\t", 1)[1].strip()
            kind, _, sym = uid.partition(":")
            if kind == "raw":
                roots.append(sym)
    world = (Path(core_out) / "core-world.lisp").read_text(encoding="latin-1")
    for m in re.finditer(r"^\(DEFPARAMETER (\S+)", world, re.M):
        vars_.append(m.group(1) if "::" in m.group(1) else "ACL2::" + m.group(1))
    for m in re.finditer(r"^\(XL-SET-GLOBAL \(QUOTE (\S+)\)", world, re.M):
        globals_.append(m.group(1) if "::" in m.group(1) else "ACL2::" + m.group(1))
    dedupe = lambda xs: list(dict.fromkeys(xs))  # noqa: E731
    return dedupe(vars_), dedupe(globals_), dedupe(roots)


def world_globals(core_out):
    """The world globals the snapshot carries (rows with GLOBAL-VALUE)."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from closure_why import snapshot_props
    rows = snapshot_props((Path(core_out) / "core-world.lisp").read_text(encoding="latin-1"))
    return sorted(s for s, props in rows.items() if "ACL2::GLOBAL-VALUE" in props)


def forms(out_dir, core_out):
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    vars_, globals_, roots = manifest_items(core_out)
    lines = ['(in-package "ACL2")', PRINTER]
    for v in vars_:
        lines.append('(xt-ob "VAR" "%s" (if (boundp \'%s) (xt-ob-text (symbol-value \'%s)) "#UNBOUND"))' % (v, v, v))
    for g in globals_:
        lines.append('(xt-ob "GLOBAL" "%s" (if (boundp-global \'%s *the-live-state*) '
                     '(xt-ob-text (f-get-global \'%s *the-live-state*)) "#UNBOUND"))' % (g, g, g))
    worlds = world_globals(core_out)
    for g in worlds:
        lines.append('(xt-ob "WORLD" "%s" (xt-ob-text (fgetprop \'%s \'global-value :none (w *the-live-state*))))' % (g, g))
    for r in roots:
        lines.append('(xt-ob "ENTRY" "%s" (xt-ob-text (list (fnn-entry-guard-spec \'%s) (fnn-trailing-kind \'%s))))'
                     % (r, r, r))
    total = len(vars_) + len(globals_) + len(worlds) + len(roots)
    lines.append('(format t "~&OB-END ~d~%%" %d)' % total)
    (out_dir / "obligations.lisp").write_text("\n".join(lines) + "\n", encoding="latin-1")
    (out_dir / "expected.count").write_text("%d\n" % total)
    print("obligations: %d globals, %d state globals, %d world globals, %d entries"
          % (len(vars_), len(globals_), len(worlds), len(roots)))
    return 0


def run_image(image, out_dir):
    root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(root))
    import tests.test_native_entry_guard as eg  # noqa: E402
    eg.IMAGE = Path(image)
    f = (Path(out_dir) / "obligations.lisp").resolve()
    argv, env = eg.image_command(['(let ((acl2::*ld-level* 1)) (load "%s"))' % f])
    r = subprocess.run(argv, env=env, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       timeout=1800, check=False)
    (Path(out_dir) / "image.out").write_bytes(r.stdout)
    # the image's source tree (IMAGE is TREE/build/fn-host-*): book paths in the world name it
    (Path(out_dir) / "image.root").write_text(str(Path(image).resolve().parent.parent))
    return r.returncode


def run_core(core, out_dir):
    f = (Path(out_dir) / "obligations.lisp").resolve()
    r = subprocess.run([core, "--xl-load", str(f)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       timeout=1800, check=False)
    (Path(out_dir) / "core.out").write_bytes(r.stdout)
    # fn-core's extraction tree (CORE is TREE/build/<out>/fn-core): the world it was exported from names it
    (Path(out_dir) / "core.root").write_text(str(Path(core).resolve().parent.parent.parent))
    return r.returncode


def encoded(text):
    """TEXT as the canonical printer prints a string's characters."""
    return ",".join(str(ord(c)) for c in text)


def parse(path, root=None):
    """{(KIND, NAME): TEXT}; a string that begins with ROOT/ (a book path in the world, which names the
    checkout the world was certified in) has that prefix replaced by ROOT/, so the two sides' different
    checkouts do not differ."""
    items, end = {}, None
    prefix = (encoded(root.rstrip("/") + "/"), encoded("ROOT/")) if root else None
    for line in Path(path).read_text(encoding="latin-1").splitlines():
        if line.startswith("OB "):
            _, kind, name, text = line.split(" ", 3)
            if prefix:
                text = text.replace('"' + prefix[0], '"' + prefix[1])
            items[(kind, name)] = text
        elif line.startswith("OB-END "):
            end = int(line.split()[1])
    return items, end


def compare(out_dir):
    out_dir = Path(out_dir)
    want = int((out_dir / "expected.count").read_text())
    root = lambda side: (out_dir / (side + ".root")).read_text().strip() if (out_dir / (side + ".root")).exists() else None  # noqa: E731
    a, ea = parse(out_dir / "image.out", root("image"))
    b, eb = parse(out_dir / "core.out", root("core"))
    bad = []
    if ea != want or eb != want or len(a) != want or len(b) != want:
        bad.append("incomplete: expected %d items; image printed %d (end %s), core %d (end %s)"
                   % (want, len(a), ea, len(b), eb))
    counts = {}
    for key in sorted(set(a) | set(b)):
        if key in EXCLUDED:
            print("EXCLUDED %s %s: %s" % (key[0], key[1], EXCLUDED[key]))
            continue
        counts[key[0]] = counts.get(key[0], 0) + 1
        if a.get(key) != b.get(key):
            bad.append("%s %s: image %s | core %s" % (key[0], key[1], (a.get(key) or "-")[:160], (b.get(key) or "-")[:160]))
    for line in bad[:60]:
        print("DIFFER " + line)
    print("obligations: %d items compared (%s), %d excluded, %d differ"
          % (sum(counts.values()), ", ".join("%s %d" % kv for kv in sorted(counts.items())), len(EXCLUDED), len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    verb = sys.argv[1] if len(sys.argv) > 1 else ""
    if verb == "forms":
        sys.exit(forms(sys.argv[2], sys.argv[3]))
    if verb == "run-image":
        sys.exit(run_image(sys.argv[2], sys.argv[3]))
    if verb == "run-core":
        sys.exit(run_core(sys.argv[2], sys.argv[3]))
    if verb == "compare":
        sys.exit(compare(sys.argv[2]))
    sys.exit(__doc__)
