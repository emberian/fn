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
              the DTN image cannot reach the reference;
  raw         the same for the raw side: no raw module build-dtn.lisp loads
              calls or `#'`-names a function defined only in a raw module that
              build.lisp loads and build-dtn.lisp does not, unless
              DTN_RAW_REACH gives the reason the call cannot run there.  The
              first fix for the store-init failure loaded checkpoint-host and
              the image then failed on `fnn-checkpoint-name-result`, which
              io.lisp called and only checkpoint.lisp defined;
  included    every `fn-` name a host file in build-dtn.lisp's `ld` closure
              calls or names in `:stobjs` that a book defines is defined in a
              book the DTN image has included by the time that file is `ld`ed
              (build-dtn.lisp's includes before the `ld`, the includes of the
              host files `ld`ed so far and the file's own, each closed over
              the books' non-local includes).  At 32842f50 build.lisp included
              books/octets-stobj and books/poster-bytes-buffer for
              host/owner-host.lisp's fn-owner-prepare-buffer and
              build-dtn.lisp did not, so the DTN image failed to build.

Static, no ACL2.  It does not follow the books an omitted host file includes,
and it cannot see a counterpart name computed at run time.  `included` reads
definitions by pattern (defun, define, defstobj, defabsstobj and kin), so a
name a macro defines is invisible to it, and it skips names some book the
image has included already defines.
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
    "host/native-auth-host.lisp": (
        "NNTP credential transport; used only by auth.lisp, not loaded", {}),
    "host/native-auth-admin-host.lisp": (
        "credential administration; used only by auth-admin.lisp, not loaded", {}),
    "host/native-control-host.lisp": (
        "control socket; used by control/hybrid-control/operator/topic-local/consumer-local; "
        "the DTN image loads only operator.lisp of these",
        {name: "operator.lisp's `post` executor and live-owner admin arm; the DTN "
               "image names :nntp-service and :control in *fnn-image-omitted-surfaces*, "
               "so the operator refuses `post` (exit 5) and never takes the live arm"
         for name in ("fn-native-control-host-status-class",
                      "fn-native-control-host-status-exit-code",
                      "fn-native-control-host-refusal-status")}),
    "host/peer-invite-host.lisp": (
        "peering invitations (PRF-097); used only by host/native/peer-invite.lisp, "
        "which build-dtn.lisp does not load: the operator refuses `peer "
        "genesis|invite|accept|confirm` on an image that omits :control", {}),
    "host/native-hybrid-control-host.lisp": (
        "hybrid authoring control; used by control.lisp and hybrid-control.lisp, not loaded", {}),
    "host/topic-history-metadata-host.lisp": (
        "includes books/topic-history-authorship for topic-local.lisp, not loaded; defines nothing", {}),
}

# (raw module that calls, raw function defined only outside the DTN image) -> why
DTN_RAW_REACH: dict[tuple[str, str], str] = {
    ("host/native/owner.lisp", "fnn-anchor-csprng-nonce"):
        "only in fnn-owner-topic-local-serialized, which only control.lisp calls; "
        "control.lisp is not loaded",
    **{("host/native/operator.lisp", name):
       "operator.lisp's `run` executor (the NNTP service), `post` executor and "
       "live-owner admin arm; build-dtn.lisp names :nntp-service and :control in "
       "*fnn-image-omitted-surfaces*, so the operator refuses `run` and `post` "
       "(exit 5) and never takes the live arm"
       for name in ("fnn-control-admin", "fnn-control-live-status", "fnn-control-owner-run-normalized",
                    "fnn-control-socket-path-p", "fnn-control-submit",
                    "fnn-feed-service-close", "fnn-feed-service-start",
                    "fnn-feed-service-wake", "fnn-native-auth-startup-hook")},
    ("host/native/operator.lisp", "fnn-pinv-execute"):
        "operator.lisp's peering executor; fnn-operator-dispatch-plan maps :peering "
        "to the :control surface, which build-dtn.lisp names in "
        "*fnn-image-omitted-surfaces*, so the DTN operator refuses it (the usage exit) "
        "before this call",
    ("host/native/operator.lisp", "fnn-native-auth-admin-execute"):
        "operator.lisp's `principal` executor; build-dtn.lisp names :credentials in "
        "*fnn-image-omitted-surfaces*, so the operator refuses it (exit 5)",
}

LD = re.compile(r'^\s*\(ld\s+"([^"]+)"', re.M)
LOAD = re.compile(r'\(load\s+"([^"]+)"')
DEF = re.compile(r'^\s*\((?:defun|defund|defmacro|defconst|defabbrev)\s+([^\s()]+)', re.M | re.I)


def strip_comments(text: str) -> str:
    return re.sub(r";[^\n]*", "", text)


def strip_code(text: str) -> str:
    """Raw Lisp without comments, strings or #| |# blocks (character literals kept)."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == "#" and text.startswith("#\\", i):
            out.append(text[i:i + 3]); i += 3
        elif c == "#" and text.startswith("#|", i):
            j = text.find("|#", i + 2); i = n if j < 0 else j + 2
        elif c == ";":
            j = text.find("\n", i); i = n if j < 0 else j
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1; out.append('""')
        else:
            out.append(c); i += 1
    return "".join(out)


RAW_DEF = re.compile(r"\((?:defun|defmacro)\s+([^\s()]+)", re.I)
RAW_USE = re.compile(r"(?:\(|#')(fnn-[^\s()']+)", re.I)


def raw_findings(root: Path, default_text: str, dtn_text: str,
                 reach: dict[tuple[str, str], str]) -> list[str]:
    default_raw = LOAD.findall(strip_comments(default_text))
    dtn_raw = LOAD.findall(strip_comments(dtn_text))
    code = {path: strip_code((root / path).read_text(encoding="utf-8"))
            for path in set(default_raw) | set(dtn_raw)}
    present = {name.lower() for path in dtn_raw for name in RAW_DEF.findall(code[path])}
    absent: dict[str, str] = {}
    for path in default_raw:
        if path not in dtn_raw:
            for name in RAW_DEF.findall(code[path]):
                absent.setdefault(name.lower(), path)
    out = []
    for user in dtn_raw:
        for name in sorted({use.lower() for use in RAW_USE.findall(code[user])}):
            if name in absent and name not in present and (user, name) not in reach:
                out.append(f"raw: {user} calls {name}, defined only in {absent[name]}, "
                           f"which {DTN_BUILD} does not load")
    return out


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
             omitted: dict[str, tuple[str, dict[str, str]]] | None = None,
             reach: dict[tuple[str, str], str] | None = None) -> list[str]:
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
    out.extend(raw_findings(root, default_text, dtn_text,
                            DTN_RAW_REACH if reach is None else reach))
    out.extend(include_findings(root, dtn_text))
    return out


INCLUDE = re.compile(r'\(include-book\s+"([^"]+)"([^)]*)\)', re.I)
LOCAL_INCLUDE = re.compile(r'\(local\s+\(include-book\s+"([^"]+)"', re.I)
BOOK_DEF = re.compile(r"\((?:defun|defund|defun-sk|define|defmacro|defabbrev|defconst|"
                      r"defstobj|defabsstobj|defun-inline|defund-inline|defun-nx|"
                      r"defund-nx|defstub|encapsulate\s+\(\s*\()\s*\(?([^\s()]+)", re.I)
HOST_CALL = re.compile(r"\((fn-[^\s()'`,]+)", re.I)
HOST_STOBJS = re.compile(r":stobjs\s+(\([^)]*\)|[^\s()]+)", re.I)
ORDER = re.compile(r'^\s*\((include-book|ld)\s+"([^"]+)"([^\n]*)', re.M)


class BookIndex:
    """Non-local include closures and definitions of the repository's books."""

    def __init__(self, root: Path):
        self.root = root
        self._includes: dict[str, list[str]] = {}
        self._defs: dict[str, set[str]] = {}
        self.owner: dict[str, set[str]] = {}
        for path in sorted((root / "books").rglob("*.lisp")):
            rel = path.relative_to(root).as_posix()
            for name in self.defs(rel):
                self.owner.setdefault(name, set()).add(rel)

    def _code(self, rel: str) -> str:
        return strip_code_keep_strings((self.root / rel).read_text(encoding="utf-8"))

    def includes(self, rel: str) -> list[str]:
        if rel not in self._includes:
            out: list[str] = []
            if (self.root / rel).exists():
                text = self._code(rel)
                text = LOCAL_INCLUDE.sub("", text)
                for target, rest in INCLUDE.findall(text):
                    if ":dir" in rest.lower():
                        continue
                    out.append(os.path.normpath(os.path.join(os.path.dirname(rel), target))
                               + ".lisp")
            self._includes[rel] = out
        return self._includes[rel]

    def defs(self, rel: str) -> set[str]:
        if rel not in self._defs:
            self._defs[rel] = {n.lower() for n in BOOK_DEF.findall(self._code(rel))}
        return self._defs[rel]

    def close(self, books: set[str], start: list[str]) -> None:
        stack = list(start)
        while stack:
            book = stack.pop()
            if book in books:
                continue
            books.add(book)
            stack.extend(self.includes(book))


def strip_code_keep_strings(text: str) -> str:
    """Lisp without comments or #| |# blocks; string literals kept (include targets)."""
    text = re.sub(r"#\|.*?\|#", "", text, flags=re.S)
    return re.sub(r';[^\n]*', "", text)


def host_uses(text: str) -> set[str]:
    code = strip_code(text)
    names = {n.lower() for n in HOST_CALL.findall(code)}
    for group in HOST_STOBJS.findall(code):
        names.update(n.lower() for n in re.findall(r"[^\s()]+", group))
    return names


def include_findings(root: Path, dtn_text: str, index: BookIndex | None = None) -> list[str]:
    index = index or BookIndex(root)
    available: set[str] = set()
    out: list[str] = []
    seen: set[str] = set()

    def visit(text: str, base: str) -> None:
        for kind, target, rest in ORDER.findall(strip_code_keep_strings(text)):
            if kind.lower() == "include-book":
                if ":dir" not in rest.lower():
                    index.close(available, [os.path.normpath(os.path.join(base, target))
                                            + ".lisp"])
                continue
            path = os.path.normpath(os.path.join(base, target))
            if path in seen:
                continue
            seen.add(path)
            host_text = (root / path).read_text(encoding="utf-8")
            host_dir = os.path.dirname(path)
            index.close(available, [os.path.normpath(os.path.join(host_dir, t)) + ".lisp"
                                    for t, r in INCLUDE.findall(
                                        LOCAL_INCLUDE.sub("", strip_code_keep_strings(host_text)))
                                    if ":dir" not in r.lower()])
            local = {n.lower() for n in DEF.findall(strip_comments(host_text))}
            defined_so_far = set().union(*(index.defs(b) for b in available if (root / b).exists()))
            for name in sorted(host_uses(host_text) - local - defined_so_far):
                books = index.owner.get(name)
                if books:
                    out.append(f"included: {path} uses {name}, defined in "
                               f"{', '.join(sorted(books))}, which {DTN_BUILD} has not "
                               f"included when it loads {path}")
            visit(host_text, host_dir)

    visit(dtn_text, ".")
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
