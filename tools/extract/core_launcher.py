#!/usr/bin/env python3
"""Render the bare SBCL product's launcher in the native packaging contract.

The saved core starts SBCL's normal option dispatcher; the launcher's explicit
XL-TOPLEVEL call starts fn. This permits the existing runtime/core identity
probe to exit before fn runs, and preserves --fn arguments and runtime overrides.

A start decides its heap per command, as the image's launcher does (ruling
2026-10-09, ADMISSION-RESERVES-NOT-REOPEN): the launcher carries packaging/fn's
fn_decide_heap and packaging/launcher-decide.sh, so `fn-core --fn ARGV' with no
caller figure first runs `fn-core --fn heap -- ARGV' (the core's own,
ACL2-decided figure, at the core's size plus two nurseries) and starts at the
heap and control stack it prints, or stops with its refusal.  The exec line's
heap and stack are what a start that names no command (or `heap' itself) runs
at.  The decision finds the core as "$0.core", so the launcher and its core are
NAME and NAME.core side by side (tools/extract/core.sh).
"""
import argparse
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
BEGIN, END = "# BEGIN fn_decide_heap", "# END fn_decide_heap"


def decision_prelude(root=ROOT):
    """The shell lines a launcher runs before its exec: packaging/fn's
    fn_decide_heap and packaging/launcher-decide.sh, verbatim."""
    lines = Path(root, "packaging/fn").read_text().splitlines(keepends=True)
    starts = [i for i, line in enumerate(lines) if line.startswith(BEGIN)]
    ends = [i for i, line in enumerate(lines) if line.startswith(END)]
    if len(starts) != 1 or len(ends) != 1 or ends[0] < starts[0]:
        raise ValueError("packaging/fn has no single fn_decide_heap block")
    return "".join(lines[starts[0]:ends[0] + 1]) + Path(root, "packaging/launcher-decide.sh").read_text()


def launcher(runtime, home, core, heap, stack, tls=None, prelude=None):
    # The freeze/install scripts deliberately accept this generated shell form.
    # Refuse shell syntax rather than accepting a path their parser misreads.
    for path in (runtime, home, core):
        if not re.fullmatch(r"/[A-Za-z0-9_./+:-]+", str(path)):
            raise ValueError("unsupported native launcher path: %r" % str(path))
    for name, value in (("heap", heap), ("stack", stack)):
        if not re.fullmatch(r"[0-9]+(?:KB|MB|GB)?", str(value)):
            raise ValueError("invalid %s runtime option" % name)
    if tls is not None and not re.fullmatch(r"[0-9]+", str(tls)):
        raise ValueError("invalid TLS runtime option")
    options = (" --tls-limit " + str(tls)) if tls is not None else ""
    return ("#!/bin/sh\n# fn extracted SBCL product; no ACL2 restart or world\n"
            + (decision_prelude() if prelude is None else prelude)
            + "export SBCL_HOME='%s'\n" % home
            + 'exec "%s"%s --dynamic-space-size %s --control-stack-size %s --disable-ldb '
              '--core "%s" --noinform ${SBCL_USER_ARGS} --end-runtime-options '
              "--no-userinit --no-sysinit --eval '(cl-user::xl-toplevel)' "
              '--disable-debugger --end-toplevel-options "$@"\n' % (runtime, options, heap, stack, core))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    for name in ("runtime", "home", "core", "heap", "stack"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--tls")
    args = parser.parse_args()
    if Path(args.core).resolve() != Path(str(args.output) + ".core").resolve():
        parser.error("the core must be OUTPUT.core (the decision reads \"$0.core\")")
    text = launcher(args.runtime, args.home, args.core, args.heap, args.stack, args.tls)
    args.output.write_text(text)
    args.output.chmod(0o755)


if __name__ == "__main__":
    main()
