#!/usr/bin/env python3
"""Render the bare SBCL product's launcher in the native packaging contract.

The saved core starts SBCL's normal option dispatcher; the launcher's explicit
XL-TOPLEVEL call starts fn. This permits the existing runtime/core identity
probe to exit before fn runs, and preserves --fn arguments and runtime overrides.
"""
import argparse
from pathlib import Path
import re


def launcher(runtime, home, core, heap, stack, tls=None):
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
            "export SBCL_HOME='%s'\n" % home
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
    text = launcher(args.runtime, args.home, args.core, args.heap, args.stack, args.tls)
    args.output.write_text(text)
    args.output.chmod(0o755)


if __name__ == "__main__":
    main()
