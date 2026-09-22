"""Native developer-image fault cuts and their byte-program coordinates."""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent.parent


@dataclass(frozen=True)
class NativeCut:
    name: str
    program: str
    candidate: str
    outcome: str = "kill"
    # The program whose run completes before `program` begins, when the cut's
    # program is not itself a whole write path.  Its coordinate is then
    # `follows` run to its end, then `program` up to the cut.
    follows: str | None = None


POST_CUTS = (
    NativeCut("frontier-staged-durable", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-replaced", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-attempted", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-durable", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-reserved", "fn-bs-frontier-program", "absent"),
    NativeCut("record-staged-durable", "fn-bs-record-program", "absent"),
    NativeCut("record-linked", "fn-bs-record-program", "either"),
    NativeCut("record-attempted", "fn-bs-record-program", "present"),
    NativeCut("record-durable", "fn-bs-record-program", "present"),
    NativeCut("record-completing", "fn-bs-record-program", "present"),
    NativeCut("record-staging-cleaned", "fn-bs-record-program", "present"),
    NativeCut("finish-consumed", "fn-bs-finish-program", "present"),
    NativeCut("finish-durable", "fn-bs-finish-program", "present"),
)
# Recovery writes no record, so the candidate column is n/a: the prior is
# unchanged and a staging orphan is either swept or left for the next open.
# `recover-barrier' names five sites of fn-bs-recover-program; a store fault
# fires at the first one reached.  The staging sweep runs only after
# fn-bs-recover-program's fifth barrier has reached :ready (host/native/io.lisp
# `fnn-recover'), once per orphan, so `recovery-stage-unlinked' is at the end
# of fn-bs-recover-program followed by one fn-bs-recover-stage-cleanup-program.
RECOVERY_CUTS = (
    NativeCut("recover-replayed", "fn-bs-recover-program", "n/a"),
    NativeCut("recover-barrier", "fn-bs-recover-program", "n/a"),
    NativeCut("recovery-stage-unlinked", "fn-bs-recover-stage-cleanup-program", "n/a",
              follows="fn-bs-recover-program"),
)
ALL_CUTS = POST_CUTS + RECOVERY_CUTS

# Checkpoint publication and selection are driven by their ACL2 phase machines.
# Reclamation has one repeated unlink boundary per covered name and a final
# transaction-directory barrier.  Runtime tests select repeated unlink cuts by
# 1-based occurrence, matching fn-bs-pack-reclaim-steps order.
CHECKPOINT_CUTS = (
    NativeCut("candidate-file", "fn-cpp-publication-step", "absent"),
    NativeCut("candidate-link", "fn-cpp-publication-step", "either"),
    NativeCut("candidate-directory", "fn-cpp-publication-step", "present"),
    NativeCut("selection-file", "fn-cpp-marker-step", "absent"),
    NativeCut("selection-replace", "fn-cpp-marker-step", "present"),
    NativeCut("selection-directory", "fn-cpp-marker-step", "present"),
    NativeCut("pack-reclaim-unlink", "fn-bs-pack-reclaim-program", "either"),
    NativeCut("pack-reclaim-directory", "fn-bs-pack-reclaim-program", "n/a"),
)


def native_declared_cut_names(parameter: str) -> tuple[str, ...]:
    source = (ROOT / "host/native/io.lisp").read_text()
    match = re.search(r"\(defparameter \+{}\+\s+'\((.*?)\)\)".format(parameter),
                      source, re.S)
    if not match:
        raise AssertionError("native cut declaration not found: {}".format(parameter))
    keywords = re.findall(r":([a-z-]+)", match.group(1))
    strings = re.findall(r'"([a-z-]+)"', match.group(1))
    return tuple(keywords or strings)


def developer_selectors() -> tuple[str, ...]:
    """The environment selectors host/native/io.lisp registers for its gate."""
    source = (ROOT / "host/native/io.lisp").read_text()
    match = re.search(r"\(defparameter \+fnn-developer-selectors\+\s+'\((.*?)\)\)",
                      source, re.S)
    if not match:
        raise AssertionError("developer selector table not found")
    return tuple(re.findall(r'"(FN_NATIVE_[A-Z_]+)"', match.group(1)))


def model_cut_names(program: str, book: str = "byte-store-programs.lisp") -> tuple[str, ...]:
    source = (ROOT / "books" / book).read_text()
    start = source.index("(defun {} ".format(program))
    next_def = source.find("\n(defun ", start + 1)
    body = source[start:next_def if next_def >= 0 else len(source)]
    return tuple(re.findall(r'\(list :cut "([^"]+)"\)', body))


def verify_native_cut_map() -> None:
    declared = tuple(c.name for c in POST_CUTS)
    actual = native_declared_cut_names("fnn-post-model-cuts")
    if declared != actual:
        raise AssertionError("native/model post cuts differ: declared={!r} actual={!r}".format(
            declared, actual))
    recovery = native_declared_cut_names("fnn-recovery-model-cuts")
    if tuple(c.name for c in RECOVERY_CUTS) != recovery:
        raise AssertionError("native/model recovery cuts differ")
    for cut in ALL_CUTS:
        if cut.name not in model_cut_names(cut.program):
            raise AssertionError("{} absent from {}".format(cut.name, cut.program))
    verify_recovery_order()


def host_function(source: str, name: str) -> str:
    start = source.index("(defun {} ".format(name))
    following = source.find("\n(defun ", start + 1)
    return source[start:following if following >= 0 else len(source)]


def verify_recovery_order() -> None:
    """The host reaches the recovery cuts in the order the coordinates say.

    `fnn-recover' runs fn-bs-recover-program's cuts (replay, then each
    barrier) and only then the sweep, whose unlink carries the cleanup
    program's cut.  A `follows' coordinate is false if the host sweeps first.
    """
    source = (ROOT / "host/native/io.lisp").read_text()
    recover = host_function(source, "fnn-recover")
    order = [recover.index("(fnn-at store :recover-replayed)"),
             recover.index("(fnn-at store :recover-barrier)"),
             recover.index("(fnn-sweep-staging store)")]
    if order != sorted(order):
        raise AssertionError("fnn-recover no longer sweeps after its barriers")
    sweep = host_function(source, "fnn-sweep-staging")
    if sweep.index("(fnn-unlink ") > sweep.index("(fnn-at store :recovery-stage-unlinked)"):
        raise AssertionError("recovery-stage-unlinked precedes its unlink")
    for cut in RECOVERY_CUTS:
        if cut.follows is not None:
            program = model_cut_names(cut.follows)
            if not program or program[-1] != "recover-barrier":
                raise AssertionError("{} does not end at its fifth barrier".format(
                    cut.follows))


def verify_checkpoint_cut_map() -> None:
    native = (ROOT / "host/native/checkpoint.lisp").read_text()
    for cut in CHECKPOINT_CUTS:
        hook = '(fnn-checkpoint-test-stop "{}")'.format(cut.name)
        if hook not in native:
            raise AssertionError("native checkpoint cut absent: {}".format(cut.name))
    reclaim = model_cut_names("fn-bs-pack-reclaim-steps",
                              "byte-store-compaction-correspondence.lisp")
    for name in ("pack-reclaim-unlink", "pack-reclaim-directory"):
        if name not in reclaim:
            raise AssertionError("{} absent from reclaim model".format(name))
