#!/usr/bin/env python3
"""tools/extract/core_build.py -- the host half of the Common Lisp product,
read from the selected native build script so it is what the image loads: the body of
its `(progn! (set-raw-mode t) ...)' block (the raw host files in order and
the calls between them).  `core_build.py TREE OUT.lisp [BUILD]' writes that body; BUILD defaults to
host/native/build.lisp."""
import re
import sys
from pathlib import Path

START = "(progn! (set-raw-mode t)"


def raw_block(tree, build="host/native/build.lisp"):
    text = (tree / build).read_text()
    i = text.index(START) + len(START)
    depth, j, n = 1, i, len(text)
    in_str = False
    while j < n and depth:
        c = text[j]
        if in_str:
            if c == "\\":
                j += 1
            elif c == '"':
                in_str = False
        elif c == ";":
            j = text.index("\n", j)
        elif c == '"':
            in_str = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        j += 1
    return text[i:j - 1]


# What the image's raw block does that only an ACL2 image can do; the product leaves it out, by name.
# A bare-SBCL core has no ACL2 world, LD or banner (EXTRACTION-PROGRAM-20261007.md section 6).
IMAGE_ONLY_LOADS = {
    # `fn acl2 session' runs ACL2's LD over the image's world (ld-fn: ACL2's evaluator);
    # its `raw-traps' subcommand goes with it, so fn-core has no `acl2' developer verb.
    "host/native/acl2-session.lisp": "ACL2's read-eval-print loop over the image's world",
    # `fn operator CONFIG eval' (the developer image's evaluator): admits ACL2 events through
    # ld-fn and the prover over the image's world, in an owner quantum (RP-1: no fn-deval- or
    # fnn-dev- function reaches the core; closure_why.py's BANNED_PREFIXES refuses their units)
    "host/native/developer-eval.lisp": "ACL2 event admission (LD and the prover) over the image's world",
}
IMAGE_ONLY_FORMS = {
    "(setq *print-startup-banner* nil)": "ACL2's startup banner variable",
}


def product_raw_block(tree, build="host/native/build.lisp"):
    """raw_block without IMAGE_ONLY_LOADS and IMAGE_ONLY_FORMS.  A build may omit an image-only
    load (build-dtn.lisp has no developer-eval) but never repeat one; every image-only form must be there once."""
    body = raw_block(tree, build)
    for rel in IMAGE_ONLY_LOADS:
        pat = re.compile(r'(?m)^[ \t]*\(load "' + re.escape(rel) + r'"\)[ \t]*\n')
        if len(pat.findall(body)) > 1:
            raise ValueError("image-only load is loaded more than once by %s: %s" % (build, rel))
        body = pat.sub("", body)
    for form in IMAGE_ONLY_FORMS:
        if body.count(form) != 1:
            raise ValueError("image-only form is not in %s exactly once: %s" % (build, form))
        body = body.replace(form, "")
    return body


def host_files(tree, build="host/native/build.lisp"):
    """The raw host files the product loads, in order."""
    return re.findall(r'\(load "(host/native/[^"]+\.lisp)"\)', product_raw_block(tree, build))


def product_block(tree, build="host/native/build.lisp"):
    """Install genuine participants only in the isolated bare SBCL builder.

    The native ACL2 world loads helper source without changing workers/hooks.
    This builder captures the SAME gate before ImagePrepare. It supplies no
    qualifier or accepted admission.
    """
    body = product_raw_block(tree, build)
    prepare = list(re.finditer(
        r"(?im)^([ \t]*)\(fnn-runtime-bootstrap-image-prepare\)[ \t]*(?:;[^\n]*)?$", body))
    if not prepare:
        if re.search(r"(?im)^[ \t]*\(fnn-runtime-bootstrap-image-prepare\b", body):
            raise ValueError("unsupported runtime bootstrap preparation form")
        return body
    if len(prepare) != 1:
        raise ValueError("duplicate runtime bootstrap image preparation")
    cut = prepare[0].start()
    loads = []
    for name in ("runtime-participants", "runtime-image-policy", "runtime-profile-envelope", "runtime-bootstrap"):
        matches = list(re.finditer(
            r'(?im)^[ \t]*\(load "host/native/' + name + r'\.lisp"\)', body))
        if len(matches) != 1 or matches[0].start() >= cut:
            raise ValueError("bootstrap helper load must precede image preparation: " + name)
        loads.append(matches[0].end())
    if loads != sorted(loads):
        raise ValueError("bootstrap helper order must be participants, image policy, profile envelope, bootstrap")
    # Only this image-builder form installs actual participants and policy.
    # The native source world has no such side effects. Both receive the SAME
    # live pool, and ImagePrepare captures their actual objects afterwards.
    hooks = ("(let* ((pool (fnn-live-page-read-pool))\n"
             "       (gate (cl-user::fnn-runtime-participants-install-for-image pool))\n"
             "       (policy (cl-user::fnn-runtime-image-policy-prepare pool gate)))\n"
             "  (fnn-runtime-profile-envelope-image-prepare pool policy))\n"
             "(cl-user::fnn-runtime-image-policy-register-image-hook)\n"
             "(cl-user::fnn-runtime-participants-register-image-hooks)\n")
    setup_names = ("fnn-runtime-participants-install-for-image",
                   "fnn-runtime-participants-register-image-hooks",
                   "fnn-runtime-image-policy-prepare",
                   "fnn-runtime-image-policy-register-image-hook",
                   "fnn-runtime-profile-envelope-image-prepare")
    present = [len(re.findall(r"(?<![\w-])" + name + r"\b", body, re.I))
               for name in setup_names]
    if any(present):
        pos = body.find(hooks)
        if (present != [1, 1, 1, 1, 1] or pos < max(loads) or
                pos + len(hooks) > cut):
            raise ValueError("partial, repeated or mismatched bootstrap policy setup")
        return body
    return body[:cut] + hooks + body[cut:]


if __name__ == "__main__":
    tree, out = Path(sys.argv[1]), Path(sys.argv[2])
    build = sys.argv[3] if len(sys.argv) > 3 else "host/native/build.lisp"
    out.write_text(";;; generated by tools/extract/core_build.py from " + build + "\n"
                   + "(in-package \"ACL2\")\n(progn\n" + product_block(tree, build) + "\n)\n")
    print("core_build: %d host files" % len(host_files(tree, build)))
