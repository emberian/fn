#!/usr/bin/env python3
"""Native verdicts without rebuilding the image: overlay a published image set.

A host edit's native verdict used to need a full image cycle: certify,
acquire, validate, host-ld and four image builds, 25 to 70 minutes on hbox
before the first test ran (planning/loops-2026-10-04.md).  An OVERLAY keeps
the published set's certified world and applies only what changed since its
commit, form by form, and then saves a derived core:

    python3 tools/native_overlay.py plan BASE [REV] [--out DIR]   # static, anywhere
    python3 tools/native_overlay.py build DIR --image-set PATH --tree T --images LIST
    tools/hbox_native.sh --image-set BASE --overlay REV tests.test_native_owner

`plan` reads `git diff BASE REV` (REV `.`, the default, is this working tree
with uncommitted and untracked files).  It sorts each changed file against
what the images load (host/native/build.lisp and build-dtn.lisp: their `ld`
host files, their raw `load` files and the books their worlds include), and
diffs each loaded file's top-level forms by (head, name).  A form that only
changes a definition's body is applied.  A change that a definition swap
cannot carry is REFUSED, by name, and nothing is built:

  - an image input: a build script, a C library, VERSION, an image-world
    umbrella, raw-trap.lisp (the dispatch table is sealed at build);
  - a layout or a value captured by callers: a changed defstobj,
    defabsstobj, attach-stobj, defstruct, defclass, define-condition,
    defmacro, defconst, defconstant, defparameter, defvar, declaim, an
    inline function, a table or definterface event, or a head this tool
    does not know (a project macro such as def-carried may expand to any
    of these);
  - a top-level form with a load-time effect (pushnew of a hook, a
    registration call), changed, added or deleted;
  - a definition run at IMAGE BUILD: a changed function some build-time
    form calls, transitively (a defparameter's initializer, a
    registration call, the build script's own raw block), whose result
    the saved core already holds;
  - a deleted definition something in the images still names;
  - a book outside the image's world that the change includes;
  - an ACL2 change for a stripped image (production, dtn): their worlds
    hold no prover state, so only a raw-only plan overlays them, and a
    module that reads FN_NATIVE_HOST is refused at launch otherwise.

What `build` checks in the image itself before it saves (each a refusal):
a changed ACL2 function that is a raw-dispatch target (D40: its trap holds
the captured object, so a swapped body would never run); every
raw-dispatch trap still intact afterwards (fnn-raw-dispatch-traps-intact);
every :raw-with declaration's theorems still about the loaded world
(fn-di-raw-with-problem).  ACL2 forms load with redefinition allowed, and
every unchanged defthm of the images' ACL2 host files or the changed books
that names a changed function is proved again under a fresh name, so a
definition change that breaks a theorem refuses the overlay as host-ld
would refuse the image.

A green overlay run is a lane's verdict on behaviour at these bytes over
the base set's world.  It is not an image: the image cycle (certify,
host-ld, the four builds) stays the integrator's, once per batch, and its
record names the overlay (OVERLAY.json beside each core: the base set,
the source, the plan's digest and every applied form).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# image -> (build script, launcher name, world flavour)
IMAGES = {
    "developer": ("host/native/build.lisp", "fn-host-developer", "full"),
    "production": ("host/native/build.lisp", "fn-host", "stripped"),
    "dtn-developer": ("host/native/build-dtn.lisp", "fn-host-dtn-developer", "full"),
    "dtn": ("host/native/build-dtn.lisp", "fn-host-dtn", "stripped"),
}
BUILD_SCRIPTS = ("host/native/build.lisp", "host/native/build-dtn.lisp")

# Inputs of an image that no form swap reaches.
IMAGE_INPUTS = re.compile(r"""^(host/native/build[^/]*\.lisp|host/native/[^/]*\.c|lib/.*|VERSION
    |books/image-world[^/]*\.lisp|host/native/raw-trap\.lisp|host/native/strip-world\.lisp
    |tools/build_native_host\.sh|tools/build_[a-z0-9]+\.sh)$""", re.VERBOSE)

RAW_CHANGE_OK = {"defun", "defmethod"}
RAW_NEW_OK = RAW_CHANGE_OK | {"defmacro", "defvar", "defparameter", "defconstant", "defstruct",
                              "defclass", "define-condition", "defgeneric"}
ACL2_CHANGE_OK = {"defun", "defund", "defthm", "defthmd", "defrule", "defruled", "verify-guards",
                  "in-theory", "mutual-recursion", "define", "defun-sk"}
ACL2_NEW_OK = ACL2_CHANGE_OK | {"defmacro", "defconst", "defabbrev", "include-book", "encapsulate"}
# Changed forms inside an encapsulate: the same rule as at top level.
THEOREM_HEADS = {"defthm", "defthmd", "defrule", "defruled"}
DEFINING_HEADS = {"defun", "defund", "defmethod", "define", "defun-sk", "defmacro", "defabbrev"}
INERT_HEADS = {"in-package"} | THEOREM_HEADS | {"verify-guards", "in-theory", "declaim"}

TOKEN = re.compile(r'''
    (?P<comment>;[^\n]*)              |
    (?P<block>\#\|.*?\|\#)            |
    (?P<string>"(?:\\.|[^"\\])*")     |
    (?P<open>[(])                     |
    (?P<close>[)])                    |
    (?P<quote>'|`|,@|,|\#\.|\#')      |
    (?P<atom>\#\\.[^\s()"';]*|\|[^|]*\|[^\s()"';]*|[^\s()"';]+)
''', re.VERBOSE | re.DOTALL)


class Form:
    __slots__ = ("text", "line", "head", "name", "norm", "tokens", "calls", "fnrefs")

    def __init__(self, text: str, line: int):
        self.text = text
        self.line = line
        toks = [(m.lastgroup, m.group()) for m in TOKEN.finditer(text)
                if m.lastgroup not in ("comment", "block")]
        self.norm = " ".join(t for _, t in toks).lower()
        atoms = [t.lower() for kind, t in toks if kind == "atom"]
        self.tokens = set(atoms)
        # call position (an atom right after an open paren) and #'NAME
        self.calls = {toks[i + 1][1].lower() for i in range(len(toks) - 1)
                      if toks[i][0] == "open" and toks[i + 1][0] == "atom"}
        self.fnrefs = {toks[i + 1][1].lower() for i in range(len(toks) - 1)
                       if toks[i][1] == "#'" and toks[i + 1][0] == "atom"}
        lead = [t for kind, t in toks if kind != "quote"]
        # #+linux (defun ...) reads as one form; its head is the form's.
        while lead and lead[0].startswith(("#+", "#-")):
            lead = lead[1:]
        self.head = lead[1].lower() if len(lead) > 1 and lead[0] == "(" else None
        self.name = None
        if self.head and len(lead) > 2 and lead[2] not in ("(", ")"):
            if self.head.startswith("def") or self.head in ("mutual-recursion",):
                self.name = lead[2].lower()
        if self.head in ("defstruct", "defclass") and len(lead) > 3 and lead[2] == "(":
            self.name = lead[3].lower()
        if self.head == "mutual-recursion":
            self.name = "mutual-recursion:" + ",".join(sorted(self.defined()))

    def key(self) -> tuple:
        if self.name:
            return (self.head, self.name)
        return ("form", self.norm)

    def defined(self) -> set[str]:
        """Names a definition form introduces (mutual-recursion: each defun's)."""
        found = re.findall(r"\(\s*(?:defun|defund)\s+([^\s()]+)", self.text, re.IGNORECASE)
        if self.head in ("defun", "defund", "defmethod", "define", "defun-sk", "defmacro",
                         "defabbrev", "defvar", "defparameter", "defconstant", "defconst"):
            found.append(self.name or "")
        return {f.lower() for f in found if f}


def read_forms(text: str) -> list[Form]:
    """Top-level forms, comments dropped, a #+/#- prefix glued to its form."""
    out: list[Form] = []
    depth = 0
    start = None
    prefix = None
    for m in TOKEN.finditer(text):
        kind = m.lastgroup
        if kind in ("comment", "block"):
            continue
        if depth == 0:
            if kind == "quote":
                prefix = prefix if prefix is not None else m.start()
                continue
            if kind == "atom" and m.group().startswith(("#+", "#-")):
                prefix = prefix if prefix is not None else m.start()
                continue
            if kind == "open":
                start = prefix if prefix is not None else m.start()
                depth = 1
            elif kind in ("atom", "string"):
                begin = prefix if prefix is not None else m.start()
                out.append(Form(text[begin:m.end()], text.count("\n", 0, begin) + 1))
            elif kind == "close":
                raise ValueError(f"unmatched ) at line {text.count(chr(10), 0, m.start()) + 1}")
            prefix = None
            continue
        if kind == "open":
            depth += 1
        elif kind == "close":
            depth -= 1
            if depth == 0:
                out.append(Form(text[start:m.end()], text.count("\n", 0, start) + 1))
                start = None
                prefix = None
    if depth:
        raise ValueError("unbalanced: a top-level form is still open at end of file")
    return out


# --- the plan (static; runs where git is) ---------------------------------

class Source:
    """File text at a revision (`.` = the working tree)."""

    def __init__(self, rev: str):
        self.rev = rev
        self.cache: dict[str, str | None] = {}
        self.batch = None

    def text(self, path: str) -> str | None:
        if path not in self.cache:
            if self.rev == ".":
                p = ROOT / path
                self.cache[path] = p.read_text(encoding="utf-8") if p.is_file() else None
            else:
                if self.batch is None:
                    self.batch = subprocess.Popen(["git", "-C", str(ROOT), "cat-file", "--batch"],
                                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE)
                self.batch.stdin.write(f"{self.rev}:{path}\n".encode())
                self.batch.stdin.flush()
                header = self.batch.stdout.readline().decode().split()
                if len(header) == 3 and header[1] == "blob":
                    data = self.batch.stdout.read(int(header[2]) + 1)[:-1]
                    self.cache[path] = data.decode("utf-8")
                else:
                    self.cache[path] = None
        return self.cache[path]


def changed_files(base: str, rev: str) -> list[str]:
    if rev == ".":
        out = subprocess.run(["git", "-C", str(ROOT), "diff", "--name-only", base, "--", "."],
                             check=True, capture_output=True, text=True).stdout.split()
        out += subprocess.run(["git", "-C", str(ROOT), "ls-files", "--others", "--exclude-standard"],
                              check=True, capture_output=True, text=True).stdout.split()
    else:
        out = subprocess.run(["git", "-C", str(ROOT), "diff", "--name-only", base, rev],
                             check=True, capture_output=True, text=True).stdout.split()
    return sorted(set(out))


LOAD = re.compile(r'\((ld|load)\s+"([^"]+)"', re.IGNORECASE)
INCLUDE = re.compile(r'\(\s*include-book\s+"([^"]+)"([^)]*)\)', re.IGNORECASE)


def build_loads(src: Source, script: str) -> tuple[list[str], list[str]]:
    """(the `ld` host files, the raw `load` files) of a build script, in order."""
    text = src.text(script) or ""
    lds, raws = [], []
    for form in read_forms(text):
        for kind, path in LOAD.findall(form.text):
            (lds if kind.lower() == "ld" else raws).append(path)
    return lds, raws


def world_books(src: Source, script: str, lds: list[str]) -> list[str]:
    """Every repository book the script and its ld files include, closure order."""
    seen: dict[str, None] = {}

    def visit(path: str, stack: set[str]) -> None:
        if path in seen or path in stack:
            return
        text = src.text(path)
        if text is None:
            return
        stack.add(path)
        base = Path(path).parent
        for target, rest in INCLUDE.findall(text):
            if ":dir" in rest.lower():
                continue
            for root in (base, Path(".")):
                book = os.path.normpath((root / target).as_posix()) + ".lisp"
                if src.text(book) is not None:
                    visit(book, stack)
                    break
        stack.discard(path)
        if path.startswith("books/"):
            seen[path] = None

    for path in [script] + lds:
        visit(path, set())
    return list(seen)


def diff_forms(old: list[Form], new: list[Form]):
    """[(action, form)] in NEW's order (changed/added), then deletions."""
    old_by = {}
    for f in old:
        old_by.setdefault(f.key(), []).append(f)
    new_keys = set()
    out = []
    for f in new:
        k = f.key()
        new_keys.add(k)
        olds = old_by.get(k)
        if not olds:
            out.append(("added", f))
        elif all(o.norm != f.norm for o in olds):
            out.append(("changed", f))
    for f in old:
        if f.key() not in new_keys:
            out.append(("deleted", f))
    return out


class Plan:
    def __init__(self, base: str, rev: str, old=None, new=None, files=None):
        self.base, self.rev = base, rev
        self.old, self.new = old or Source(base), new or Source(rev)
        self.refusals: list[str] = []
        self.notes: list[str] = []
        self.images: dict[str, dict] = {}
        self.forms: dict[str, list[tuple[str, Form]]] = {}  # file -> applied forms
        self.rechecks: dict[str, list[Form]] = {}           # file -> theorems re-proved
        self.changed_names: set[str] = set()
        self.deleted: list[tuple[str, Form]] = []
        self.files = files if files is not None else changed_files(base, rev)

    def refuse(self, why: str) -> None:
        self.refusals.append(why)

    def make(self) -> "Plan":
        loads = {}
        for script in BUILD_SCRIPTS:
            lds, raws = build_loads(self.new, script)
            loads[script] = (lds, raws, world_books(self.new, script, lds))
        image_files: dict[str, str] = {}  # path -> "acl2" | "raw" | "book"
        for lds, raws, books in loads.values():
            for p in lds:
                image_files[p] = "acl2"
            for p in raws:
                image_files[p] = "raw"
            for p in books:
                image_files.setdefault(p, "book")
        # the build scripts' own raw statements run at image build
        build_time: list[tuple[str, Form]] = []
        for script in BUILD_SCRIPTS:
            for form in read_forms(self.new.text(script) or ""):
                if form.head not in ("include-book", "ld", "load", "in-package") and not LOAD.match(form.text.strip()):
                    build_time.append((script, form))
        outside = []
        for path in self.files:
            if IMAGE_INPUTS.match(path):
                self.refuse(f"{path}: an image input (build script, C library, VERSION, world "
                            "umbrella or sealed dispatch table); rebuild the image set")
                continue
            kind = image_files.get(path)
            if kind is None:
                outside.append(path)
                continue
            self.diff_file(path, kind)
        if outside:
            self.notes.append(f"{len(outside)} changed file(s) no image loads (the tree runs them): "
                              + ", ".join(outside[:12]) + (" ..." if len(outside) > 12 else ""))
        # what the images load at these bytes, for the reference and staleness scans
        corpus: dict[str, list[Form]] = {}
        acl2_changed = any(image_files.get(p) != "raw" for p in self.forms)
        for path, kind in image_files.items():
            if kind == "book" and not acl2_changed:
                continue  # a book cannot call a raw host function
            text = self.new.text(path)
            if text is not None:
                try:
                    corpus[path] = read_forms(text)
                except ValueError:
                    pass
        self.check_build_time(corpus, build_time, image_files)
        self.check_deleted(corpus)
        self.add_rechecks(corpus, image_files)
        for image, (script, launcher, world) in IMAGES.items():
            lds, raws, books = loads[script]
            order = [p for p in books if p in self.forms] + [p for p in lds if p in self.forms]
            raw_order = [p for p in raws if p in self.forms]
            entry = {"launcher": launcher, "world": world, "acl2": order, "raw": raw_order}
            acl2_here = bool(order) or any(p in self.rechecks for p in books + lds)
            if world == "stripped" and acl2_here:
                entry["refused"] = ("ACL2 events change (" + ", ".join(order[:4]) + "): a stripped "
                                    "world holds no prover state to admit them")
            self.images[image] = entry
        return self

    def diff_file(self, path: str, kind: str) -> None:
        old_text, new_text = self.old.text(path), self.new.text(path)
        try:
            old = read_forms(old_text or "")
            new = read_forms(new_text or "")
        except ValueError as error:
            self.refuse(f"{path}: does not read ({error})")
            return
        if new_text is None:
            self.refuse(f"{path}: deleted, but an image loads it")
            return
        applied = []
        raw = kind == "raw"
        inline = set()
        if raw:
            for f in old + new:
                if f.head == "declaim" and "inline" in f.tokens:
                    inline |= f.tokens - {"declaim", "inline"}
        for action, form in diff_forms(old, new):
            where = f"{path}:{form.line}"
            label = f"{form.head or 'form'} {form.name or ''}".strip()
            if form.head == "in-package":
                continue
            if action == "deleted":
                if form.name and form.head in DEFINING_HEADS | {"defvar", "defparameter",
                                                                 "defconstant", "defconst"}:
                    self.deleted.append((path, form))
                elif form.head in THEOREM_HEADS | {"in-theory", "verify-guards"}:
                    self.notes.append(f"{where}: {label} deleted (stays in the overlay's world)")
                else:
                    self.refuse(f"{where}: {label} deleted: a form with a load-time effect "
                                "already ran in the base image")
                continue
            ok = (RAW_CHANGE_OK if action == "changed" else RAW_NEW_OK) if raw else \
                 (ACL2_CHANGE_OK if action == "changed" else ACL2_NEW_OK)
            if form.head not in ok:
                if form.name is None and form.head is not None and not form.head.startswith("def"):
                    why = "a top-level form with a load-time effect"
                elif form.head in ("defstobj", "defabsstobj", "attach-stobj", "defstruct",
                                   "defclass", "define-condition"):
                    why = "a layout change: never mix obsolete stobj or struct layouts"
                elif form.head in ("defmacro", "defabbrev", "defconst", "defconstant",
                                   "defparameter", "defvar", "declaim"):
                    why = "its callers were compiled with the old expansion or value"
                elif form.head in ("table", "definterface", "defattach"):
                    why = "a table the image sealed or read at build"
                else:
                    why = f"{form.head!s} is not a head this tool can swap (its expansion is unknown)"
                self.refuse(f"{where}: {action} {label}: {why}")
                continue
            if form.head == "encapsulate":
                bad = form.tokens & {"defstobj", "defabsstobj", "attach-stobj", "defattach",
                                     "table", "defmacro", "defconst"}
                if bad:
                    self.refuse(f"{where}: {action} encapsulate holds {', '.join(sorted(bad))}")
                    continue
            if raw and form.name in inline:
                self.refuse(f"{where}: {action} {label}: declared inline; its callers hold the old body")
                continue
            if form.head == "include-book":
                self.notes.append(f"{where}: new include-book (the build checks it is in the world)")
            applied.append((action, form))
            if action == "changed":
                self.changed_names |= form.defined()
        if applied:
            self.forms[path] = applied

    def callers(self, corpus: dict[str, list[Form]], names: set[str]) -> set[str]:
        """NAMES and every function whose body names one of them, transitively."""
        # a body's edges: every atom it names (calls, #', quoted entry names
        # handed to fnn-core): an over-approximation, so a caller is never missed
        defs = [(f.defined(), f.tokens) for forms in corpus.values() for f in forms
                if f.head in DEFINING_HEADS or f.head == "mutual-recursion"]
        reached = set(names)
        grew = True
        while grew:
            grew = False
            for defined, tokens in defs:
                if defined - reached and tokens & reached:
                    reached |= defined
                    grew = True
        return reached

    def check_build_time(self, corpus, build_time, image_files) -> None:
        if not self.changed_names:
            return
        reached = self.callers(corpus, self.changed_names)
        sites = list(build_time)
        for path, forms in corpus.items():
            for f in forms:
                if f.head in DEFINING_HEADS or f.head in INERT_HEADS or f.head == "mutual-recursion":
                    continue
                if f.head in ("include-book", "ld", "local", "encapsulate", "defstobj",
                              "defabsstobj", "progn") and image_files.get(path) == "book":
                    continue
                sites.append((path, f))
        # A site matters when it CALLS into a changed definition at build (an
        # atom in call position reaching one), or captures a changed
        # function's object (#'NAME): a symbol it stores resolves at each
        # call and reaches the new body.
        seen = set()
        for path, f in sites:
            called = sorted((f.calls - {f.head}) & reached) if f.head in DEFINING_HEADS else sorted(f.calls & reached)
            captured = sorted(f.fnrefs & self.changed_names)
            if (called or captured) and (path, f.line) not in seen:
                seen.add((path, f.line))
                label = f"{f.head or 'form'} {f.name or ''}".strip()
                why = (f"calls {', '.join(called[:3])} (reaching a changed definition)" if called
                       else f"captures the function object of {', '.join(captured[:3])}")
                self.refuse(f"{path}:{f.line}: {label} runs at image build and {why}: the saved "
                            "core holds what it made then")

    def check_deleted(self, corpus) -> None:
        for path, form in self.deleted:
            name = form.name
            users = [f"{p}:{f.line}" for p, forms in corpus.items() for f in forms
                     if name in f.tokens and name not in f.defined()]
            if users:
                self.refuse(f"{path}:{form.line}: {form.head} {name} deleted but still named at "
                            f"{', '.join(users[:3])}: the base image would keep serving it")
            else:
                self.notes.append(f"{path}:{form.line}: {form.head} {name} deleted (unreferenced; "
                                  "stays defined in the overlay)")

    def add_rechecks(self, corpus, image_files) -> None:
        """Unchanged theorems naming a changed function, in the images' ACL2
        host files and the changed books: proved again under a fresh name."""
        if not self.changed_names:
            return
        for path, forms in corpus.items():
            kind = image_files.get(path)
            if kind == "raw" or (kind == "book" and path not in self.forms):
                continue
            applied = {f.key() for _, f in self.forms.get(path, [])}
            for f in forms:
                if f.head in THEOREM_HEADS and f.key() not in applied and f.tokens & self.changed_names:
                    self.rechecks.setdefault(path, []).append(f)

    # -- output --
    def write(self, out: Path) -> dict:
        out.mkdir(parents=True, exist_ok=True)
        files = {}
        for n, (path, applied) in enumerate(sorted(self.forms.items())):
            body = ['(in-package "ACL2")']
            for action, form in applied:
                body.append(f";; {action} {path}:{form.line}\n{form.text}")
            for form in self.rechecks.get(path, []):
                fresh = f"fn-overlay-recheck-{form.name}"
                renamed = re.sub(re.escape(form.name), fresh, form.text, count=1, flags=re.IGNORECASE)
                body.append(f";; recheck {path}:{form.line}\n{renamed}")
            name = f"overlay-{n:03d}.lisp"
            (out / name).write_text("\n\n".join(body) + "\n", encoding="utf-8")
            files[path] = name
        for path, forms in sorted(self.rechecks.items()):
            if path not in files:
                n = len(files)
                body = ['(in-package "ACL2")']
                for form in forms:
                    fresh = f"fn-overlay-recheck-{form.name}"
                    renamed = re.sub(re.escape(form.name), fresh, form.text, count=1, flags=re.IGNORECASE)
                    body.append(f";; recheck {path}:{form.line}\n{renamed}")
                name = f"overlay-{n:03d}.lisp"
                (out / name).write_text("\n\n".join(body) + "\n", encoding="utf-8")
                files[path] = name
        images = {}
        for image, entry in self.images.items():
            images[image] = dict(entry,
                                 acl2=[files[p] for p in entry["acl2"] if p in files]
                                 + [files[p] for p in self.rechecks if p in files
                                    and p not in entry["acl2"] and self.image_has(image, p)],
                                 raw=[files[p] for p in entry["raw"]],
                                 sources={files[p]: p for p in entry["acl2"] + entry["raw"]})
        record = {
            "base": self.base, "rev": self.rev, "source": source_id(self.rev),
            "refusals": self.refusals, "notes": self.notes, "images": images,
            "changed_names": sorted(self.changed_names),
            "forms": {p: [{"action": a, "head": f.head, "name": f.name, "line": f.line}
                          for a, f in applied] for p, applied in self.forms.items()},
            "rechecks": {p: [f.name for f in forms] for p, forms in self.rechecks.items()},
        }
        digest = hashlib.sha256()
        for name in sorted(files.values()):
            digest.update(name.encode() + b"\0" + (out / name).read_bytes())
        record["digest"] = digest.hexdigest()
        (out / "plan.json").write_text(json.dumps(record, indent=1) + "\n")
        return record

    def image_has(self, image: str, path: str) -> bool:
        script = IMAGES[image][0]
        lds, _ = build_loads(self.new, script)
        return path in lds


def source_id(rev: str) -> str:
    if rev == ".":
        head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                              capture_output=True, text=True).stdout.strip()
        dirty = subprocess.run(["git", "-C", str(ROOT), "diff", "--quiet", "HEAD"]).returncode
        return f"worktree {head}{'+dirty' if dirty else ''}"
    full = subprocess.run(["git", "-C", str(ROOT), "rev-parse", rev],
                          capture_output=True, text=True).stdout.strip()
    return f"commit {full}"


def cmd_plan(args) -> int:
    base = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--verify", args.base + "^{commit}"],
                          capture_output=True, text=True)
    if base.returncode:
        print(f"native_overlay: no commit {args.base}", file=sys.stderr)
        return 2
    plan = Plan(base.stdout.strip(), args.rev).make()
    out = Path(args.out) if args.out else ROOT / "build" / "native-overlay" / "plan"
    if out.exists():
        shutil.rmtree(out)
    record = plan.write(out)
    for note in record["notes"]:
        print(f"note: {note}")
    for path, forms in record["forms"].items():
        for f in forms:
            print(f"apply: {path}:{f['line']} {f['action']} {f['head']} {f['name'] or ''}")
    for path, names in record["rechecks"].items():
        print(f"recheck: {path}: {len(names)} theorem(s) naming a changed function")
    for image, entry in record["images"].items():
        state = entry.get("refused") or (f"{len(entry['acl2'])} ACL2 file(s), {len(entry['raw'])} raw file(s)"
                                          if entry["acl2"] or entry["raw"] else "unchanged")
        print(f"image {image}: {state}")
    for why in record["refusals"]:
        print(f"REFUSED: {why}")
    print(f"native_overlay: plan {record['digest'][:12]} {record['source']} over {record['base'][:12]} "
          f"-> {out}" + (f"; {len(record['refusals'])} refusal(s): this change needs an image build"
                         if record["refusals"] else ""))
    return 3 if record["refusals"] else 0


# --- the build (on the box; needs only this file and the plan) ------------

ERROR_MARKS = ("ACL2 Error", "HARD ACL2 ERROR", "ABORTING from raw Lisp", "debugger invoked",
               "Unhandled ", "FN_OVERLAY_REFUSED")


def overlay_script(plan_dir: Path, entry: dict, changed: list[str], out_core: Path) -> str:
    """The session: ACL2 events first (as build.lisp's lds precede its raw
    block), then the raw forms, the image's own checks, then save-exec."""
    lines = []
    if entry["world"] == "full":
        names = " ".join(changed)
        lines.append(f"(value-triple (prog2$ (cw \"FN_OVERLAY_BEGIN~%\") :begin))")
        lines.append("(defttag :fn-native-host)")
        # D40: a raw-dispatched target's trap holds the captured object.
        lines.append("(progn! (set-raw-mode t) (let ((hit (remove-if-not (lambda (n) (member n '("
                     + names + ") :test 'eq)) (append (fnn-raw-dispatch-names) (mapcar 'fnn-raw-dispatch-target (fnn-raw-dispatch-names)))))) "
                     "(when hit (format t \"~&FN_OVERLAY_REFUSED raw-dispatch target redefined: ~(~{~a~^ ~}~)~%\" hit))))")
        if entry["acl2"]:
            lines.append("(set-ld-redefinition-action '(:doit! . :overwrite) state)")
            for name in entry["acl2"]:
                lines.append(f'(ld "{plan_dir / name}" :ld-error-action :error)')
            lines.append("(set-ld-redefinition-action nil state)")
        for name in entry["raw"]:
            lines.append(f'(progn! (set-raw-mode t) (load "{plan_dir / name}"))')
        lines.append(":q")
    else:
        # A stripped world holds no prover state, but its loop still starts:
        # restart through it (as every saved core is restarted) and leave it.
        lines += [":q", '(in-package "ACL2")']
        for name in entry["raw"]:
            lines.append(f'(load "{plan_dir / name}")')
    lines += [
        # every trap intact; every :raw-with declaration still holds in this world
        "(acl2::fnn-raw-dispatch-traps-intact)",
    ]
    if entry["world"] == "full":
        lines.append(
            "(let ((wrld (acl2::w acl2::*the-live-state*)) (bad nil)) "
            "(dolist (e (acl2::table-alist 'acl2::fn-interfaces wrld)) "
            "(let ((th (cadr (acl2::assoc-keyword :raw-with (cdr e))))) "
            "(when th (let ((p (acl2::fn-di-raw-with-problem (car e) (cdr e) wrld))) (when p (push (list (car e) p) bad)))))) "
            "(when bad (format t \"~&FN_OVERLAY_REFUSED raw-with declarations no longer hold: ~s~%\" bad) (sb-ext:exit :code 3 :abort t)))")
    if entry["acl2"]:
        # A changed ACL2 entry's guard spec is recomputed from this world at
        # its first call; every other cached spec (the build filled some) stays.
        lines.append("(when (boundp 'acl2::*fnn-entry-guard-specs*) (dolist (n '("
                     + " ".join(changed) + ")) (remhash n acl2::*fnn-entry-guard-specs*)))")
    lines += [
        "(format t \"~&FN_OVERLAY_READY~%\")",
        f'(acl2::save-exec "{out_core}" "fn native overlay" :return-from-lp \'(acl2::fn-native-entry acl2::state) '
        ':inert-args t :host-lisp-args "--noinform" :toplevel-args "--disable-debugger")',
    ]
    return "\n".join(lines) + "\n"


def launcher_command(launcher_text: str) -> tuple[list[str], str]:
    """The base launcher's sbcl argv up to its toplevel options, and its env line."""
    exec_line = next(l for l in launcher_text.splitlines() if l.startswith("exec "))
    env_line = next((l for l in launcher_text.splitlines() if l.startswith("export SBCL_HOME")), "")
    return exec_line, env_line


def cmd_build(args) -> int:
    plan_dir = Path(args.plan).resolve()
    record = json.loads((plan_dir / "plan.json").read_text())
    if record["refusals"]:
        print("native_overlay: the plan has refusals; nothing built:", file=sys.stderr)
        for why in record["refusals"]:
            print(f"  {why}", file=sys.stderr)
        return 3
    image_set = Path(args.image_set)
    build = Path(args.tree).resolve() / "build"
    build.mkdir(parents=True, exist_ok=True)
    wanted = [w for w in args.images.split(",") if w]
    status = 0
    for image in wanted:
        entry = record["images"][image]
        launcher = entry["launcher"]
        base_launcher = image_set / launcher
        if entry.get("refused"):
            print(f"native_overlay: {image}: REFUSED: {entry['refused']}")
            # no stale image under the overlay's name: a module reading it is refused
            for suffix in ("", ".core"):
                place = build / f"{launcher}{suffix}"
                if place.is_symlink() or place.exists():
                    place.unlink()
            status = status or 3
            continue
        text = base_launcher.read_text()
        exec_line, env_line = launcher_command(text)
        base_core = re.search(r'--core "([^"]+)"', exec_line).group(1)
        out_core = build / f"{launcher}.core"
        for place in (build / launcher, out_core):
            if place.is_symlink() or place.exists():
                place.unlink()
        if not entry["acl2"] and not entry["raw"]:
            # unchanged for this image: the base core itself
            out_core.symlink_to(base_core)
        else:
            m = re.match(r'exec "([^"]+)" (.*) --core "[^"]+" (.*?) --end-runtime-options', exec_line)
            sbcl, runtime_a, runtime_b = m.group(1), m.group(2), m.group(3).replace("${SBCL_USER_ARGS}", "")
            runtime = (runtime_a + " " + runtime_b).split()
            # the session's own control stack: the deployed 1 MiB is a thread figure, not ACL2's
            runtime = [("64MB" if prev == "--control-stack-size" else a)
                       for prev, a in zip([""] + runtime, runtime)]
            # Restart as the saved launcher does (acl2::sbcl-restart), with the
            # loop reading this session instead of running fn-native-entry.  A
            # core saved without that restart differed: tests.test_native_
            # state_checkpoint's running-owner compaction lost its race to the
            # stop on a no-op re-save of the published production core,
            # 3 of 3, and passed 3 of 3 on the published core itself.
            toplevel = ["--eval", "(progn (setq acl2::*return-from-lp* nil) (acl2::sbcl-restart))"]
            script = overlay_script(plan_dir, entry, record["changed_names"], out_core.with_suffix(""))
            (plan_dir / f"session-{image}.lisp").write_text(script)
            env = dict(os.environ)
            home = re.search(r"SBCL_HOME='([^']+)'", env_line)
            if home:
                env["SBCL_HOME"] = home.group(1)
            # save-exec writes its own launcher at OUT; the base's replaces it below
            argv = [sbcl, *runtime, "--core", base_core, "--end-runtime-options", "--no-userinit",
                    *toplevel, "--disable-debugger", "--end-toplevel-options"]
            log = plan_dir / f"session-{image}.log"
            with open(log, "w") as handle:
                proc = subprocess.run(argv, input=script,
                                      stdout=handle, stderr=subprocess.STDOUT, text=True,
                                      env=env, cwd=args.tree, timeout=args.timeout)
            output = log.read_text(errors="replace")
            marks = [m for m in ERROR_MARKS if m in output]
            if proc.returncode or marks or "FN_OVERLAY_READY" not in output or not out_core.is_file():
                for place in (out_core, out_core.with_suffix("")):
                    if place.exists():
                        place.unlink()
                refused = re.findall(r"FN_OVERLAY_REFUSED [^\n]*", output)
                print(f"native_overlay: {image}: REFUSED (exit {proc.returncode}; "
                      f"{', '.join(refused or marks) or 'no FN_OVERLAY_READY'}); log {log}")
                for line in [l for l in output.splitlines() if "Error" in l or "REFUSED" in l][:8]:
                    print(f"   | {line}")
                status = status or 3
                continue
        (build / launcher).write_text(text.replace(f'--core "{base_core}"', f'--core "{out_core}"'))
        (build / launcher).chmod(0o755)
        lib = build / "lib"
        if not lib.exists() and (image_set / "lib").is_dir():
            lib.symlink_to(image_set / "lib")
        (build / f"{launcher}.catalog").write_text("old\n")
        sums = hashlib.sha256(out_core.read_bytes()).hexdigest() if out_core.is_file() else None
        (build / f"{launcher}.overlay.json").write_text(json.dumps({
            "base_set": str(image_set), "base": record["base"], "source": record["source"],
            "plan": record["digest"], "image": image, "core_sha256": sums,
            "applied": {entry["sources"].get(n, n): n for n in entry["acl2"] + entry["raw"]},
        }, indent=1) + "\n")
        print(f"native_overlay: {image}: {'base core (unchanged)' if not entry['acl2'] and not entry['raw'] else 'overlay core'} "
              f"-> {build / launcher}")
    return status


# --- the live owner --------------------------------------------------------

def cmd_live(args) -> int:
    """Start an owner from IMAGE on a scratch store with the developer REPL,
    detached; print its socket, port and config.  `fn_dev.py repl --socket`
    attaches; `stop` ends it."""
    import socket as socketlib
    import time
    root = Path(args.root).resolve()
    if root.exists() and any(root.iterdir()) and not (root / "fn.toml").is_file():
        print(f"native_overlay: {root} exists and is not a live root", file=sys.stderr)
        return 2
    root.mkdir(parents=True, exist_ok=True)
    image = Path(args.image).resolve()
    config = root / "fn.toml"
    if not config.is_file():
        with socketlib.socket() as sock:
            sock.bind(("127.0.0.1", 0))
            port = sock.getsockname()[1]
        config.write_text(f'[store]\npath = "{root}/store"\n[listener]\nhost = "127.0.0.1"\n'
                          f'port = {port}\n[control]\npath = "{root}/control.sock"\n')
        init = subprocess.run([str(image), "--fn", "operator", str(config), "init", "--budget",
                               str(args.budget), "fn.test"], capture_output=True, text=True, timeout=120)
        (root / "init.log").write_text(init.stdout + init.stderr)
        if init.returncode:
            print(f"native_overlay: init exit {init.returncode}; {root / 'init.log'}", file=sys.stderr)
            return 1
    port = re.search(r"port = (\d+)", config.read_text()).group(1)
    sock = root / "dev.sock"
    if sock.exists():
        print(f"native_overlay: {sock} exists: an owner is live (stop it first)", file=sys.stderr)
        return 2
    env = dict(os.environ, FN_NATIVE_DEV_REPL=str(sock))
    log = open(root / "owner.log", "a")
    started = time.monotonic()
    owner = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], env=env,
                             stdout=log, stderr=log, start_new_session=True)
    (root / "owner.pid").write_text(f"{owner.pid}\n")
    while not sock.exists():
        if owner.poll() is not None:
            print(f"native_overlay: owner exited {owner.returncode} before its REPL listened; "
                  f"{root / 'owner.log'}", file=sys.stderr)
            return 1
        if time.monotonic() - started > args.timeout:
            print("native_overlay: owner REPL did not appear", file=sys.stderr)
            return 1
        time.sleep(0.05)
    print(f"native_overlay: owner pid {owner.pid} live in {time.monotonic() - started:.1f}s; "
          f"nntp 127.0.0.1:{port}; config {config}; repl {sock}")
    print(f"  attach: python3 tools/fn_dev.py repl --socket {sock}")
    return 0


def cmd_stop(args) -> int:
    import signal
    import time
    root = Path(args.root).resolve()
    try:
        pid = int((root / "owner.pid").read_text())
    except (OSError, ValueError):
        print(f"native_overlay: no owner.pid in {root}", file=sys.stderr)
        return 2
    try:
        os.kill(pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    for _ in range(400):
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            break
        time.sleep(0.05)
    (root / "owner.pid").unlink(missing_ok=True)
    print(f"native_overlay: owner {pid} stopped")
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("plan", help="classify the change since BASE; refuse what an overlay cannot carry")
    p.add_argument("base")
    p.add_argument("rev", nargs="?", default=".")
    p.add_argument("--out")
    p.set_defaults(run=cmd_plan)
    p = sub.add_parser("build", help="on the box: derive overlay cores from a published set")
    p.add_argument("plan")
    p.add_argument("--image-set", required=True, help="the published set's directory")
    p.add_argument("--tree", required=True, help="the tree whose build/ receives the overlay images")
    p.add_argument("--images", default="developer")
    p.add_argument("--timeout", type=int, default=1800)
    p.set_defaults(run=cmd_build)
    p = sub.add_parser("live", help="start a developer owner with its REPL on a scratch store")
    p.add_argument("--image", required=True)
    p.add_argument("--root", required=True)
    p.add_argument("--budget", type=int, default=2048)
    p.add_argument("--timeout", type=float, default=60)
    p.set_defaults(run=cmd_live)
    p = sub.add_parser("stop", help="stop a live owner")
    p.add_argument("--root", required=True)
    p.set_defaults(run=cmd_stop)
    args = parser.parse_args(argv)
    return args.run(args)


if __name__ == "__main__":
    sys.exit(main())
