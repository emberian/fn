#!/usr/bin/env python3
"""tools/extract/debug_keep.py CORE_EXE [KEEP] -- the debug-keep gate (EXTRACTION-PROGRAM-20261007.md item 8).

fn-core is compiled at (debug 0) except the functions listed in tools/extract/debug-keep.txt (NAME FILE per
line; core-main.lisp recompiles them at debug 1).  This runs the built core's `--xl-load' on a probe and
refuses (exit 1, naming each) a listed function that is absent, inlined, not a compiled function, or has no
block (code-location) debug-info, which is what (debug 1) keeps and (debug 0) drops."""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

KEEP = Path(__file__).resolve().parent / "debug-keep.txt"


def keep_names(path=KEEP):
    """The names of the keep file, in order (comment lines and blanks skipped)."""
    names = []
    for line in Path(path).read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            names.append(line.split()[0].lower())
    return names


PROBE = r'''
(dolist (n '(%s))
  (let* ((sym (find-symbol (string-upcase n) "ACL2"))
         (f (and sym (fboundp sym) (fdefinition sym)))
         (status
           (cond ((null f) "absent")
                 ((member (sb-int:info :function :inlinep sym) '(inline maybe-inline)) "inlined")
                 ((not (typep f 'compiled-function)) "not-compiled")
                 (t (let* ((df (sb-di:fun-debug-fun f))
                           (cdf (and (typep df 'sb-di::compiled-debug-fun) (sb-di::compiled-debug-fun-compiler-debug-fun df)))
                           (blocks (and cdf (funcall (find-symbol "COMPILED-DEBUG-FUN-BLOCKS" "SB-C") cdf))))
                      (if (and blocks (plusp (length blocks))) "ok" "no-blocks"))))))
    (format t "DEBUG-KEEP ~a ~a~%" n status)))
'''


def problems(report, names):
    """Refusals from a probe's stdout REPORT for NAMES: each name must report ok, exactly once."""
    got = {}
    for m in re.finditer(r"(?m)^DEBUG-KEEP (\S+) (\S+)$", report):
        got[m.group(1).lower()] = m.group(2)
    out = []
    for n in names:
        s = got.get(n.lower())
        if s is None:
            out.append("%s: the probe reported nothing" % n)
        elif s != "ok":
            out.append("%s: %s (a debug-keep function must be a compiled, non-inlined function with block debug-info)" % (n, s))
    return out


def check(core_exe, names):
    with tempfile.TemporaryDirectory() as d:
        probe = Path(d) / "probe.lisp"
        probe.write_text(PROBE.replace("%s", " ".join(names), 1))
        r = subprocess.run([str(core_exe), "--xl-load", str(probe)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           text=True, errors="replace", timeout=300)
    if r.returncode != 0:
        return ["the probe exited %d: %s" % (r.returncode, r.stderr.strip()[-300:])]
    return problems(r.stdout, names)


def main(argv):
    if not 2 <= len(argv) <= 3:
        print(__doc__, file=sys.stderr)
        return 2
    names = keep_names(argv[2] if len(argv) == 3 else KEEP)
    bad = check(argv[1], names)
    for p in bad:
        print("debug_keep: %s" % p, file=sys.stderr)
    if not bad:
        print("debug_keep: %d functions keep their debug info" % len(names))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
