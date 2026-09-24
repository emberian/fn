#!/usr/bin/env python3
"""The DTN image loads every host file the default image loads, or says why not.

`host/native/build.lisp` and `host/native/build-dtn.lisp` keep two `ld`
lists.  On 2026-09-23 (`be7397c8`) `fn-store-checkpoint-clone-fence-name`
moved into `host/checkpoint-host.lisp`; build.lisp gained the `ld`,
build-dtn.lisp did not, and `host/native/io.lisp` calls that name when any
Store opens.  Both DTN images built, and both refused `store init` with
"ACL2 executable counterpart missing" (native-subsets-6c0626c5, failure 2).
Nothing static saw it: the raw modules name ACL2 functions as quoted symbols
resolved at call time.

The two lists stay separate on purpose: the DTN image omits the NNTP reader,
the writable owner and the operator surfaces, and its build script is the
declaration `tools/proof_artifacts.py --profile dtn` reads.  This check makes
the difference explicit instead:

  omitted     every host file in build.lisp's transitive `ld` closure and not
              in build-dtn.lisp's is a key of DTN_OMITTED, with a reason;
  stale       every key of DTN_OMITTED is in fact omitted;
  reached     no name an omitted file defines is spelled as a quoted symbol
              (`'name`, how `fnn-core` and its siblings name a counterpart) in
              a raw module build-dtn.lisp loads, or called from a host file in
              its closure, unless DTN_OMITTED lists that name with the reason
              the DTN image cannot reach the reference.

Static, no ACL2.  It does not follow the books an omitted host file includes,
and it cannot see a counterpart name computed at run time.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BUILD = "host/native/build.lisp"
DTN_BUILD = "host/native/build-dtn.lisp"

# host file -> (why the DTN image omits it, {referenced name: why unreachable})
DTN_OMITTED: dict[str, tuple[str, dict[str, str]]] = {
    "host/anchor-wire-host.lisp": (
        "only host/native/anchor.lisp uses it; the DTN image does not load anchor.lisp", {}),
    "host/anchor-server-host.lisp": (
        "only host/native/anchor.lisp uses it; the DTN image does not load anchor.lisp", {}),
    "host/reader-host.lisp": (
        "the NNTP reader; its book books/served is left out of the DTN image by design",
        {name: "io.lisp's `reader` verb; the DTN image has no NNTP reader by design "
               "(build-dtn.lisp header)"
         for name in ("fn-reader-chunk", "fn-reader-outcome", "fn-reader-reset",
                      "fn-reader-set-posting", "fn-reader-use-seed",
                      "fn-reader-use-store")}),
    "host/native/reader-model-host.lisp": (
        "the differential reader model over books/served, left out by design",
        {"fn-reader-model-octets": "io.lisp's `model` verb faults on the missing "
                                   "counterpart, as the build-dtn.lisp header says"}),
    "host/native-config-host.lisp": (
        "native configuration files; used by config.lisp, operator.lisp and owner.lisp, none loaded", {}),
    "host/native-auth-host.lisp": (
        "NNTP credential transport; used only by auth.lisp, not loaded", {}),
    "host/native-auth-admin-host.lisp": (
        "credential administration; used only by auth-admin.lisp, not loaded", {}),
    "host/feed-filename-host.lisp": (
        "outbound feed file names; used only by feed-filename.lisp, not loaded", {}),
    "host/native-operator-host.lisp": (
        "the public operator surface; used only by operator.lisp, not loaded", {}),
    "host/native-control-host.lisp": (
        "control socket; used by control/hybrid-control/operator/topic-local/consumer-local, none loaded", {}),
    "host/native-hybrid-control-host.lisp": (
        "hybrid authoring control; used by control.lisp and hybrid-control.lisp, not loaded", {}),
    "host/hybrid-signature-host.lisp": (
        "ML-DSA/Ed25519 signatures; the DTN image loads no crypto (signatures.lisp, owner.lisp)", {}),
    "host/topic-history-metadata-host.lisp": (
        "includes books/topic-history-authorship for topic-local.lisp, not loaded; defines nothing", {}),
    "host/bp-release-owner-host.lisp": (
        "the owner-mode workflow journal; owner.lisp is not loaded",
        {name: "workflow.lisp selects it only for an owner-mode journal, which only "
               "bp-node.lisp and bp-obligation.lisp open; neither is loaded"
         for name in ("fn-owner-workflow-apply-record", "fn-owner-workflow-install-replay",
                      "fn-owner-workflow-preflight-record", "fn-owner-workflow-reset")}),
    "host/bp-native-app-host.lisp": (
        "the BP application handoff into the NNTP owner; owner.lisp is not loaded",
        {"fn-owner-bp-tcpcl-ingress": "bp-service.lisp calls it only with a non-NIL owner "
                                      "and channel; bp.lisp's service loop passes NIL NIL, "
                                      "and bp-node.lisp, the caller that passes an owner, "
                                      "is not loaded"}),
}

LD = re.compile(r'^\s*\(ld\s+"([^"]+)"', re.M)
LOAD = re.compile(r'\(load\s+"([^"]+)"')
DEF = re.compile(r'^\s*\((?:defun|defund|defmacro|defconst|defabbrev)\s+([^\s()]+)', re.M | re.I)


def strip_comments(text: str) -> str:
    return re.sub(r";[^\n]*", "", text)


def ld_closure(root: Path, build_text: str) -> list[str]:
    """Host files a session script `ld`s, transitively, relative to each file."""
    seen: list[str] = []

    def walk(text: str, base: str) -> None:
        for target in LD.findall(strip_comments(text)):
            path = os.path.normpath(os.path.join(base, target))
            if path not in seen:
                seen.append(path)
                walk((root / path).read_text(encoding="utf-8"), os.path.dirname(path))

    walk(build_text, ".")
    return seen


def findings(root: Path = ROOT, default_text: str | None = None,
             dtn_text: str | None = None,
             omitted: dict[str, tuple[str, dict[str, str]]] | None = None) -> list[str]:
    default_text = default_text if default_text is not None else (root / DEFAULT_BUILD).read_text()
    dtn_text = dtn_text if dtn_text is not None else (root / DTN_BUILD).read_text()
    omitted = DTN_OMITTED if omitted is None else omitted
    default = ld_closure(root, default_text)
    dtn = ld_closure(root, dtn_text)
    out: list[str] = []
    for path in default:
        if path not in dtn and path not in omitted:
            out.append(f"omitted: {path} is loaded by {DEFAULT_BUILD} and not by "
                       f"{DTN_BUILD}, and DTN_OMITTED gives no reason")
    for path in omitted:
        if path not in default or path in dtn:
            out.append(f"stale: DTN_OMITTED lists {path}, which is not a default-only host file")
    corpus = {path: strip_comments((root / path).read_text(encoding="utf-8"))
              for path in LOAD.findall(strip_comments(dtn_text))}
    host = {path: strip_comments((root / path).read_text(encoding="utf-8")) for path in dtn}
    provided = {name.lower() for text in host.values() for name in DEF.findall(text)}
    for path in default:
        if path in dtn:
            continue
        allowed = omitted.get(path, ("", {}))[1]
        names = {n.lower() for n in DEF.findall((root / path).read_text(encoding="utf-8"))}
        for name in sorted(names - provided):
            if name in allowed:
                continue
            quoted = re.compile(r"'" + re.escape(name) + r"(?![\w\-*+$!?%&<>=/.:])", re.I)
            called = re.compile(r"\(" + re.escape(name) + r"(?![\w\-*+$!?%&<>=/.:])", re.I)
            for user, text in corpus.items():
                if quoted.search(text):
                    out.append(f"reached: {user} names '{name}, defined only in {path}, "
                               f"which {DTN_BUILD} does not load")
            for user, text in host.items():
                if called.search(text):
                    out.append(f"reached: {user} calls {name}, defined only in {path}, "
                               f"which {DTN_BUILD} does not load")
    return out


def main() -> int:
    found = findings()
    for line in found:
        print(f"build-lists: {line}")
    default = ld_closure(ROOT, (ROOT / DEFAULT_BUILD).read_text())
    dtn = ld_closure(ROOT, (ROOT / DTN_BUILD).read_text())
    print(f"build-lists: default ld closure {len(default)}, DTN {len(dtn)}, "
          f"omitted with reasons {len(DTN_OMITTED)}; {len(found)} finding(s)")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
