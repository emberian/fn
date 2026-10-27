#!/usr/bin/env python3
"""Find the theorems whose subject no host line can reach.

AGENTS.md's first assurance rule says "The theorem subject is the function the
host calls", and "Say which host line calls the subject."  That rule has been
prose with nothing behind it, and the defect it names has been our most
expensive one.  Five instances surfaced on 2026-09-21 alone, every one found
by someone driving the wire and none by a check:

* K3's duplicate suppression (`fn-peer-history-is-have-at-offer`) was proved
  of `fn-peer-decide-offer`, which answered from the node pinned when the
  connection OPENED.  The certified refusal sat behind a branch the running
  server could not reach while the wire answered `335`, and a streaming peer
  paid for the whole article twice.
* `fn-peer-capability-lines` renders the transit capability list, has a
  block-text lemma and five assertions.  `fn-auth-step` answers `CAPABILITIES`
  itself before it ever delegates, so the arm never runs.
* `fn-own-feed-durable-records` existed with no caller, so the outbound queue
  lived in memory and an article accepted while a peer was down did not
  survive the process that accepted it.
* `fn-feed-lost` had no live caller: a socket that died left its entry `:sent`
  until a restart.
* `fn-cpc-validp` validates a checkpoint and no host line calls it.

Each was true, proved, certified, and irrelevant to the running server.

    python3 tools/reach_check.py              # findings
    python3 tools/reach_check.py --summary    # the line `make check` prints
    python3 tools/reach_check.py --strict     # non-zero on an UNBASELINED orphan
    python3 tools/reach_check.py --baseline   # rewrite the baseline (deliberate)
    python3 tools/reach_check.py --lower-stale  # shrink-only: drop rows whose event is now hosted or gone

WHAT IT MEASURES.  The call graph over `books/*.lisp' and `host/*.lisp',
seeded from every function a LOADED host file defines (one the image
builds, host/native/build.lisp and build-dtn.lisp, or the extraction world
tools/extract/world-host.lisp `ld' or `load'; a host file no build loads
seeds nothing, PKT-412, and tools/host_check.py --loaded refuses it), every book
symbol a loaded host file names.  Python development and checking tools
seed nothing: their book-symbol mentions are not served host lines.
A `defabsstobj' export is a function whose body is its :logic and
:exec functions, and `(attach-stobj GENERIC IMPL)' makes each GENERIC export
reach IMPL's export with the same :logic (the node's `fn-arena' runs
`fn-arena-paged''s pages); a live stobj's creator and recognizer run
whenever one of its exports does.

A registry event is HOSTED when its SUBJECT is (the keystone audit of
2026-09-27 found 16 events hosted by something else; AGENTS.md: "The subject
is the function the host calls"):
* the subject is the book functions its CONCLUSION calls (nested `implies'
  unfolded), less the stobj names (`fn-arena', `fn-cat', `state': a stobj is
  threaded, never the subject) and less the predicate each hypothesis
  conjunct applies (in `(implies (inv s) (inv (step s)))' the subject is
  `step').  Hints never count.  A conclusion that calls nothing takes its
  subject from the hypotheses;
* a hosted subject counts only where it is applied to arguments no MODEL
  computed: under `(let ((m (model-run evs))) (host-f (views m)))' host-f is
  applied to the model's state, and the event is about the model;
* a row's generated `keystone_subjects' map (tools/keystone_emit.py, lane
  defkeystone: {"<registry keystone>": "<subject function>"}) DECLARES the
  subject: the event is hosted exactly when a host line reaches that
  function, and the conclusion is not read;
* `NAME{correspondence}' and `NAME{preserved}' are about the export NAME;
  a correspondence also counts when a reached export of the SAME stobj has
  a correspondence theorem explicitly using it, with matching logic/exec
  conclusions, and its exec directly calls NAME's exec.  This is named
  proof-dependency attribution, not equality of the exports or their effects;
  both the listing and `--explain' name the linking correspondence;
* failing that, a NAMED equality in books/ ties an unhosted subject U to a
  hosted H: a conclusion `(equal (U ..) (H x ..))' whose H side applies H to
  variables and constants only (not a commutation, not an unfolding into a
  constructor), or a refinement square `(equal (H .. (A x) ..) (A (U x ..)))'
  (store-log-kernel-concrete's fn-lgc-*-refines), or the square read with
  the abstraction the other way, `(equal (A .. (C ..) ..) (L .. (A ..) ..))'
  (A of what the hosted C leaves is L of A of the state before; the page
  store's pgs-x-commit-refines-commit), or a structural output projection
  `(equal (A (C x ..)) (L x ..))' over identical plain inputs: A only selects
  and reconstructs fields of C's answer (PKT-413's receiver result).
  `--explain' names it.  This last bridge covers the projected result, not
  the rest of C's output or effects.

WHAT IT CANNOT SEE.  A function reached only through a macro this reader
does not expand, or named in a Python string it does not recognize as a
symbol, and reachability is transitive: a book function a hosted function
calls is executed, so a keystone over a component (fn-cat-complete inside
the host's fn-sca-finish) is hosted even when the host-level theorem is a
different event.  The one macro it does expand is `fn-defrecord'
(books/defrecord.lisp): its generated recognizer is a definition here, whose
body is the record's `:fields' types, `:extra' conjuncts and
`:recognizer-formals' (PKT-394).  It also sees through a proof-only
ABBREVIATION in a statement: an unreached, non-recursive, branch-free
definition (or backquote macro) is read as the composition it names, so an
event over `fn-osi-live-store' is about `fn-own-store' of the owner the host
runs (PKT-376); a let-bound abbreviation is a model state only when what it
abbreviates is.  `$' and braces are symbol constituents
(before 2026-09-27 `(defun fn-arena$lcorr ...)' read as a definition of
`fn-arena').

A flag is a question for a human, never a verdict.  Being unreachable is not
by itself a defect: a book can legitimately run ahead of its host.  What the
baseline does is stop the number growing silently.
"""
from __future__ import annotations
import argparse
import collections
import json
import pathlib
import re
import subprocess
import sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import callgraph  # noqa: E402
import lisp_source  # noqa: E402
from lisp_source import code_only, forms, read_sexp  # noqa: E402,F401
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
from tools import ratchet  # noqa: E402
ROOT = pathlib.Path(__file__).resolve().parent.parent
# ---------------------------------------------------------------- file memo
#
# Every scan below reads a book's top-level forms, and theorem_forms parses
# each book again with the ledger's reader: ~3,000 files, five or six times
# over, every run (X17: reach --strict was 11 minutes of a train pass).
# Both are functions of the file's bytes, so they are memoised by content:
# FILE_MEMO holds, under the digest of (this file, tools/ledger.py, the
# Python, the kind, the path and the text), what the scan computed.  An
# edited book is re-read; the rest are not.  One pickle, read once and
# rewritten when something new was computed, keeping only what this run
# used.  Under build/cache/, which tools/check_steps.py never keys a step
# on.  FN_REACH_CACHE=0 turns it off; a path moves it.
FILE_MEMO = ROOT / "build" / "cache" / "reach" / "files.pickle.z"
_TEXT: dict = {}
_MEMO: dict | None = None
_MEMO_USED: dict = {}
_MEMO_SALT: bytes | None = None
def _memo_path():
    import os
    setting = os.environ.get("FN_REACH_CACHE", "")
    if setting == "0":
        return None
    return pathlib.Path(setting) if setting else FILE_MEMO


def file_text(path) -> str:
    """PATH's text, read once per process (OSError propagates, as read_text)."""
    key = str(path)
    if key not in _TEXT:
        _TEXT[key] = pathlib.Path(path).read_text(encoding="utf-8", errors="replace")
    return _TEXT[key]


def memoised(kind: str, rel: str, text: str, compute):
    """COMPUTE() for this KIND of scan over REL's TEXT, from the memo when an
    earlier run computed it over the same bytes with the same code."""
    global _MEMO, _MEMO_SALT
    import hashlib
    where = _memo_path()
    if where is None:
        return compute()
    if _MEMO is None:
        import atexit
        import pickle
        import zlib
        try:
            _MEMO = pickle.loads(zlib.decompress(where.read_bytes()))
            if not isinstance(_MEMO, dict):
                _MEMO = {}
        except Exception:
            _MEMO = {}
        atexit.register(_memo_save)
    if _MEMO_SALT is None:
        salt = hashlib.sha256(b"fn-reach-file-memo-1\0" + sys.version.encode())
        for source in (pathlib.Path(__file__), pathlib.Path(callgraph.ledger.__file__),
                       pathlib.Path(lisp_source.__file__)):
            salt.update(source.resolve().read_bytes())
        _MEMO_SALT = salt.digest()
    digest = hashlib.sha256(_MEMO_SALT)
    digest.update(kind.encode() + b"\0" + rel.encode() + b"\0" + text.encode("utf-8", "surrogatepass"))
    key = digest.hexdigest()
    if key in _MEMO:
        value = _MEMO[key]
    else:
        value = compute()
        _MEMO[key] = value
        _MEMO_USED["dirty"] = True
    _MEMO_USED[key] = True
    return value


def _memo_save() -> None:
    import os
    import pickle
    import zlib
    where = _memo_path()
    if where is None or _MEMO is None:
        return
    used = {k: v for k, v in _MEMO.items() if k in _MEMO_USED}
    if not _MEMO_USED.get("dirty") and len(used) == len(_MEMO):
        return
    try:
        where.parent.mkdir(parents=True, exist_ok=True)
        temporary = where.with_name(".{}.{}.tmp".format(where.name, os.getpid()))
        # zlib level 1: the memo is mostly book text (~50 MB raw, ~10 MB packed).
        temporary.write_bytes(zlib.compress(pickle.dumps(used, protocol=pickle.HIGHEST_PROTOCOL), 1))
        os.replace(temporary, where)
    except OSError:
        pass  # a memo that cannot be written is a slower run, never a wrong one


# The builds whose loads are the running server's host lines, each with the
# directory ACL2 runs it from: the two images, and the extraction world the
# served product (the SBCL core) is extracted from, which loads the image's
# host files (tools/extract/world.py).  A host file no build loads is not a host line
# and seeds nothing (PKT-412); tools/host_check.py --loaded refuses one (Q7k).
IMAGE_BUILDS = {"host/native/build.lisp": ".",
                "host/native/build-dtn.lisp": ".",
                "tools/extract/world-host.lisp": "tools/extract"}
# A test image's build: what it loads is loaded (host_check --loaded), but a
# test image is not the server, so it seeds nothing here.
TEST_IMAGE_BUILDS = {"host/native/build-store-test.lisp": "."}
RAW_LOAD = re.compile(r'\(load\s+"([^"]+\.lisp)"')
RAW_LOAD_BESIDE = re.compile(r'\(load\s+\(merge-pathnames\s+"([^"]+\.lisp)"')
def loaded_host_files(builds=IMAGE_BUILDS, root: pathlib.Path = ROOT) -> set[str]:
    """Every host file BUILDS (a sequence of root-run builds, or a mapping of
    build to the directory it runs from) load, root-relative: the build script,
    each `ld' host file (an ld inside one in place: host_check.ld_sequence)
    and each raw file it `load's, following a raw file's own loads (a
    root-relative string, or a `merge-pathnames' beside the loading file)."""
    import host_check
    found: set[str] = set()
    work: list[str] = []
    for build in builds:
        if not (root / build).is_file():
            continue
        work.append(build)
        cbd = builds.get(build, ".") if isinstance(builds, dict) else "."
        work += host_check.ld_sequence(build, root, cbd=cbd)
    while work:
        relative = work.pop()
        if relative in found or not (root / relative).is_file():
            continue
        found.add(relative)
        text = (root / relative).read_text(encoding="utf-8", errors="replace")
        text = re.sub(r";[^\n]*", "", text)
        work += RAW_LOAD.findall(text)
        beside = pathlib.PurePosixPath(relative).parent
        work += [str(beside / name) for name in RAW_LOAD_BESIDE.findall(text)]
    return found


NESTED_DEFTHM = re.compile(r"\((?:defthm|defthmd)\s+([a-zA-Z0-9<>=/*+${}-]+)")
def theorem_forms(paths) -> dict:
    """name -> (file, form) for every `defthm'/`defthmd', including those
    inside an `encapsulate', `local', `defsection' or `progn' (a top-level
    only scan left such events unresolved, which passed them silently)."""
    found = {}
    for path in paths:
        try:
            text = file_text(path)
        except OSError:
            continue
        rel = str(path.relative_to(ROOT))
        for name, form in memoised("theorems", rel, text,
                                   lambda: _file_theorems(text)):
            if name not in found:
                found[name] = (rel, form)
    return found


def _file_theorems(text: str) -> list:
    """[(name, form)] of one file's theorems, in theorem_forms' order of
    preference: the lexical reader's nested spelling first, then the shared
    reader's events (a name already seen keeps its first form)."""
    import ledger
    out, seen = [], set()
    # Preserve literal theorem spelling for this checker's lexical term
    # reader (including rationals and escaped symbols). Only generated
    # events need the shared mirror's printable form.
    for form in forms(text):
        for match in NESTED_DEFTHM.finditer(form):
            name = match.group(1).lower()
            if name in seen:
                continue
            inner = forms(form[match.start():])
            if inner:
                seen.add(name)
                out.append((name, inner[0]))
    try:
        parsed = ledger.Reader(text).top_level()
    except ledger.ReadError:
        return out
    for form, _ in ledger.source_events(parsed):
        if ledger.head(form) in ("defthm", "defthmd") and len(form) >= 3:
            name = str(form[1])
            if name not in seen:
                seen.add(name)
                out.append((name, ledger.source_text(form)))
    return out


