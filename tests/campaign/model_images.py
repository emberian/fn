"""The campaign's differential check against the byte-level crash model.

Crash model v2 §5.1: after the kill, before the reopen, import the case
directory as a byte-store image, ask ACL2 for the model state at that cut,
and require that what the host recovered is one of the images the model
admits there.  Until this module the campaign compared the recovered state
with a *reference run*: it could see that recovery had gone somewhere wrong,
but not that it had gone somewhere the model does not allow, and the
`fn-sf-crash` choice column of `cuts.py` was prose.

What is checked, per cut:

1. the model state `bs_k` after the program prefix up to that cut, from
   `fn-bs-run` over the program constant of `books/byte-store-programs.lisp`
   applied to the imported *template* store;
2. the set of durable `transactions/` name sets, and of frontier file
   contents, over every crash choice of `bs_k`'s pending list -- writes
   whole or lost, entry operations applied or dropped.  That is a superset
   of the model's images at the level the kernel predicate constrains: a
   torn *staging* write cannot change a durable authority name, which is
   what K1 says and what this enumeration therefore need not reproduce
   byte by byte;
3. the recovered record count of the reopened store is the size of one of
   those name sets.

A recovered count outside the set is a counterexample to K1/K2 and is
reported with `bs_k`'s pending list, not swallowed.

This is the enumeration a decision procedure would replace:
`fn-bs-image-admissiblep` and its `-iff-crash-imagep` are still open (P1
residual), so the check enumerates the choices instead of deciding
membership, and says so rather than claiming the exact form.
"""
from __future__ import annotations

import itertools
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import run_store  # noqa: E402

# The store layout as the model names it (tools/run_store.py).
DIRECTORY_IDS = {
    ".": ":root",
    "transactions": ":transactions",
    "staging": ":staging",
}

# (component, host function) -> (model program constructor, its arguments).
# The arguments are the ones the template store makes the program's own:
# a staging name, the next transaction name, and the frame octets are
# supplied per case by the caller.
PROGRAM_OF = {
    ("store", "advance_frontier"): "fn-bs-frontier-program",
    ("store", "publish"): "fn-bs-record-program",
    ("store", "recover"): "fn-bs-recover-program",
}


# The program constant arguments.  Only the SHAPE of the pending list at a
# cut decides the admissible name sets, so the staging name, the final name
# and the frame octets are placeholders: the durable half of the state comes
# from the imported template, not from these.  What is NOT checked here is
# the record's octets, which needs fn-bs-scan-store (K1, open).
PROGRAM_ARGUMENTS = {
    "fn-bs-frontier-program": '".allocation-campaign" \'(1)',
    "fn-bs-record-program": '".stage-campaign" "campaign.txn" \'(10 11 12 13)',
    "fn-bs-recover-program": "",
}


def program_form(program: str, point: str) -> str:
    return "({} {})".format(program, PROGRAM_ARGUMENTS[program]).replace(" )", ")")


def cut_index(program: str, point: str, occurrence: int = 1,
              book: str = "byte-store-programs.lisp") -> int:
    """The index in fn-bs-run's pair list of the cut named POINT.

    fn-bs-run returns one pair per step, so the pair after the (:cut NAME)
    step is at the step's own index.
    """
    text = (ROOT / "books" / book).read_text()
    start = text.index("(defun {} ".format(program))
    end = text.find("\n(", start + 1)
    body = text[start:end if end > 0 else len(text)]
    index = -1
    seen = 0
    steps = {":cut", ":create", ":write-all", ":write", ":fsync-file",
             ":fsync-dir", ":link", ":rename", ":unlink", ":mkdir",
             ":observe"}
    for step in __import__("re").finditer(
            r"\(list (:[a-z-]+)(?:\s+\"([^\"]*)\")?", body):
        if step.group(1) not in steps:
            continue
        index += 1
        if step.group(1) == ":cut" and step.group(2) == point:
            seen += 1
            if seen == occurrence:
                return index
    raise ModelError("{} has no :cut {!r} occurrence {}".format(
        program, point, occurrence))


class ModelError(RuntimeError):
    pass


@dataclass
class ModelImages:
    """What the model admits at one cut."""
    pending: str
    record_counts: tuple[int, ...]


class ModelBridge:
    """An ACL2 process holding books/byte-store-programs, nothing else."""

    def __init__(self):
        env = os.environ.copy()
        env["ACL2_CUSTOMIZATION"] = "NONE"
        env["ACL2_BOOK_HASH_ALISTP"] = "NIL"
        self.proc = subprocess.Popen(
            [env.get("FN_ACL2", "acl2")], cwd=ROOT, env=env,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT)
        run_store.read_prompt(self.proc, run_store.ACL2_START_TIMEOUT_SECONDS)
        self.call('(include-book "books/byte-store-programs")')

    def call(self, form: str, timeout: float = 120.0) -> str:
        self.proc.stdin.write((form + "\n").encode("ascii"))
        self.proc.stdin.flush()
        output = run_store.read_prompt(self.proc, timeout)
        text = output.decode("ascii", "replace")
        if "ACL2 Error" in text or "HARD ACL2 ERROR" in text:
            raise ModelError(text[-2000:])
        return text

    def value(self, form: str, timeout: float = 120.0) -> str:
        """The printed value of FORM, with the echoed prompt removed."""
        text = self.call(form, timeout)
        body = text.rsplit("ACL2 !>", 1)[0]
        return body.strip()

    def close(self) -> None:
        if self.proc is not None:
            try:
                self.proc.stdin.close()
            except Exception:
                pass
            self.proc.wait(timeout=10)
            if self.proc.stdout is not None:
                self.proc.stdout.close()
            self.proc = None


def import_image(store_root: Path, unit: int = 4096) -> str:
    """The case directory as an ACL2 byte-store form: no pending operations.

    Regular files are inodes keyed by `st_ino`; the three store directories
    are the keyword ids the programs use.  A crash image has an empty
    pending list by construction, which is what makes it an image.
    """
    inodes: dict[int, bytes] = {}
    dirs: dict[str, list[tuple[str, str]]] = {}
    for relative, dir_id in DIRECTORY_IDS.items():
        directory = store_root if relative == "." else store_root / relative
        entries: list[tuple[str, str]] = []
        if directory.is_dir():
            for child in sorted(directory.iterdir()):
                if child.is_dir():
                    child_id = DIRECTORY_IDS.get(child.name)
                    if child_id is not None:
                        entries.append((child.name, child_id))
                    continue
                if not child.is_file():
                    continue
                ino = child.stat().st_ino
                inodes[ino] = child.read_bytes()
                entries.append((child.name, str(ino)))
        dirs[dir_id] = entries
    inode_forms = " ".join(
        "({} . ({}))".format(ino, " ".join(str(b) for b in octets))
        if octets else "({})".format(ino)
        for ino, octets in sorted(inodes.items()))
    dir_forms = " ".join(
        "({} . ({}))".format(
            dir_id,
            " ".join('("{}" . {})'.format(name, value) for name, value in entries))
        if entries else "({})".format(dir_id)
        for dir_id, entries in dirs.items())
    next_ino = (max(inodes) + 1) if inodes else 0
    return "'(:byte-store {} ({}) ({}) nil {})".format(
        unit, inode_forms, dir_forms, next_ino)


def choice_vectors(pending: list[str]) -> list[str]:
    """Every whole-or-lost choice over a pending list, as ACL2 choice lists.

    A `:write` is offered whole (a full `:new` selector list, which the
    reader of this enumeration should note is not every torn selection) or
    lost (no selectors); an entry operation is `:apply` or `:drop`.  The
    torn selections are what the §5.2 variant injector produces on disk;
    this enumeration is the namespace-level envelope the kernel predicate
    speaks about.
    """
    per_op = []
    for op in pending:
        if op.startswith("(:WRITE") or op.startswith("(:write"):
            per_op.append(("(:NEW :NEW :NEW :NEW :NEW :NEW :NEW :NEW)", "NIL"))
        else:
            per_op.append((":APPLY", ":DROP"))
    return ["(" + " ".join(vector) + ")"
            for vector in itertools.product(*per_op)] if per_op else ["NIL"]


def images_at_cut(bridge: ModelBridge, template_store: Path, program_form: str,
                  cut_index: int, unit: int = 4096) -> ModelImages:
    """The model's admissible record counts at one cut of one program."""
    template = import_image(template_store, unit)
    bridge.call("(defconst *fn-campaign-template* {})".format(template))
    bridge.call("(defconst *fn-campaign-program* {})".format(program_form))
    bridge.call(
        "(defconst *fn-campaign-run*"
        " (fn-bs-run *fn-campaign-template* (fn-sf-initial-state)"
        " *fn-campaign-program* nil nil nil))")
    bridge.call(
        "(defconst *fn-campaign-bs* (car (nth {} *fn-campaign-run*)))".format(
            cut_index))
    pending = bridge.value("(fn-bs-pending *fn-campaign-bs*)")
    operations = [line for line in pending.split("(:") if line.strip()]
    counts = []
    for vector in choice_vectors(["(:" + op for op in operations]):
        printed = bridge.value(
            "(len (strip-cars (cdr (assoc-equal :transactions"
            " (fn-bs-dirs (fn-bs-crash *fn-campaign-bs* '{}))))))".format(vector))
        counts.append(int(printed.split()[-1]))
    for name in ("*fn-campaign-bs*", "*fn-campaign-run*", "*fn-campaign-program*",
                 "*fn-campaign-template*"):
        bridge.call("(u)")
    return ModelImages(pending=pending, record_counts=tuple(sorted(set(counts))))
