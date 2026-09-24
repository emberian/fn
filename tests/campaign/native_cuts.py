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
    model_name: str | None = None
    occurrence: int = 1


# frontier-created/-written, record-created/-written and record-stage-unlinked
# were model sites with no host cut until lane p10-k0 (campaign 1a9dd747,
# "the coverage runs one way only"); host/native/io.lisp now has an `fnn-at'
# at each (fnn-write-staged-at, and inside fnn-publish's best-effort cleanup).
POST_CUTS = (
    NativeCut("frontier-created", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-written", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-staged-durable", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-replaced", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-attempted", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-durable", "fn-bs-frontier-program", "absent"),
    NativeCut("frontier-reserved", "fn-bs-frontier-program", "absent"),
    NativeCut("record-created", "fn-bs-record-program", "absent"),
    NativeCut("record-written", "fn-bs-record-program", "absent"),
    NativeCut("record-staged-durable", "fn-bs-record-program", "absent"),
    NativeCut("record-linked", "fn-bs-record-program", "either"),
    NativeCut("record-attempted", "fn-bs-record-program", "present"),
    NativeCut("record-durable", "fn-bs-record-program", "present"),
    NativeCut("record-completing", "fn-bs-record-program", "present"),
    NativeCut("record-stage-unlinked", "fn-bs-record-program", "present"),
    NativeCut("record-staging-cleaned", "fn-bs-record-program", "present"),
    NativeCut("finish-consumed", "fn-bs-finish-program", "present"),
    NativeCut("finish-durable", "fn-bs-finish-program", "present"),
)
# Recovery writes no record, so the candidate column is n/a: the prior is
# unchanged and a staging orphan is either swept or left for the next open.
# Each `recover-barrier-N' selects its ordinal site of fn-bs-recover-program.
# The staging sweep runs only after
# fn-bs-recover-program's fifth barrier has reached :ready (host/native/io.lisp
# `fnn-recover'), once per orphan, so `recovery-stage-unlinked' is at the end
# of fn-bs-recover-program followed by one fn-bs-recover-stage-cleanup-program.
RECOVERY_CUTS = (
    NativeCut("recover-replayed", "fn-bs-recover-program", "n/a"),
    *(NativeCut("recover-barrier-{}".format(i), "fn-bs-recover-program", "n/a",
                model_name="recover-barrier", occurrence=i) for i in range(1, 6)),
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
    strings = re.findall(r'"([a-z0-9-]+)"', match.group(1))
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


# The byte-program step kinds (books/byte-store-programs.lisp, the step table
# at its head).  `observe' and `cut' issue no syscall.
STEP_KINDS = ("observe", "cut", "create", "write-all", "fsync-file", "fsync-dir",
              "rename", "link", "unlink")
SYSCALL_KINDS = frozenset(STEP_KINDS[2:])


@dataclass(frozen=True)
class ModelStep:
    kind: str
    args: tuple[str, ...]

    @property
    def directory(self) -> str | None:
        """The directory the step acts in: the target of a rename or link."""
        if self.kind in ("rename", "link"):
            return self.args[2]
        return self.args[0] if self.kind in SYSCALL_KINDS else None


def model_steps(program: str, book: str = "byte-store-programs.lisp") -> tuple[ModelStep, ...]:
    """The program's steps in order, read from its `(list :kind ...)' forms.

    An inner `(list :core-completion ...)' is an observation's argument, not
    a step; only the step kinds above are kept.
    """
    source = (ROOT / "books" / book).read_text()
    start = source.index("(defun {} ".format(program))
    next_def = source.find("\n(defun ", start + 1)
    body = source[start:next_def if next_def >= 0 else len(source)]
    steps = []
    for kind, rest in re.findall(r"\(list :([a-z-]+)([^\n]*)", body):
        if kind not in STEP_KINDS:
            continue
        if kind == "cut":
            args = tuple(re.findall(r'"([^"]+)"', rest)[:1])
        else:
            args = tuple(re.findall(r'(:[a-z-]+|\*[a-z-]+\*|"[^"]*"|[a-z][a-z-]*)',
                                    rest.split(";")[0]))
        steps.append(ModelStep(kind, args))
    return tuple(steps)


def cut_step_index(cut: NativeCut) -> int:
    """The index in model_steps(cut.program) of the cut's own `:cut' step."""
    seen = 0
    for index, step in enumerate(model_steps(cut.program)):
        if step.kind == "cut" and step.args == (cut.model_name or cut.name,):
            seen += 1
            if seen == cut.occurrence:
                return index
    raise AssertionError("{} occurrence {} absent from {}".format(
        cut.name, cut.occurrence, cut.program))


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
        model_names = model_cut_names(cut.program)
        if model_names.count(cut.model_name or cut.name) < cut.occurrence:
            raise AssertionError("{} occurrence {} absent from {}".format(
                cut.name, cut.occurrence, cut.program))
    verify_recovery_order()
    verify_swallowed_cuts()


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
             recover.index('(fnn-at store (intern (format nil "RECOVER-BARRIER-~d" ordinal) :keyword))'),
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


# The post cut whose EIO the host swallows: a cut between two best-effort
# staging steps after the record's directory barrier (P-RECORD's `970 best
# effort', `971 best effort').  `post_arm' in native_nntp_post_probe derives
# the arm from the model coordinate; this checks the host agrees: the
# `fnn-at' of every such cut, and of no other post cut, lies inside the
# `ignore-errors' form of fnn-publish.
def swallowed_cut(cut: NativeCut) -> bool:
    steps = model_steps(cut.program)
    index = cut_step_index(cut)
    published = [j for j, s in enumerate(steps)
                 if s.kind in ("rename", "link") and s.directory != ":staging"]
    if not published:
        return False
    barrier = next((j for j, s in enumerate(steps)
                    if j > published[0] and s.kind == "fsync-dir"
                    and s.directory == steps[published[0]].directory), None)
    before = [j for j, s in enumerate(steps[:index]) if s.kind in SYSCALL_KINDS]
    after = [j for j, s in enumerate(steps) if j > index and s.kind in SYSCALL_KINDS]
    return (barrier is not None and bool(before) and bool(after)
            and before[-1] > barrier
            and steps[before[-1]].directory == ":staging"
            and steps[after[0]].directory == ":staging")


def swallowed_post_cuts() -> tuple[str, ...]:
    return tuple(cut.name for cut in POST_CUTS if swallowed_cut(cut))


def verify_swallowed_cuts(source: str | None = None) -> None:
    if source is None:
        source = (ROOT / "host/native/io.lisp").read_text()
    publish = host_function(source, "fnn-publish")
    start = publish.index("(ignore-errors")
    depth, end = 0, start
    for end in range(start, len(publish)):
        depth += {"(": 1, ")": -1}.get(publish[end], 0)
        if depth == 0:
            break
    inside = publish[start:end + 1]
    swallowed = set(swallowed_post_cuts())
    for cut in POST_CUTS:
        site = "(fnn-at store :{})".format(cut.name)
        if (site in inside) != (cut.name in swallowed):
            raise AssertionError("{}: model says swallowed={}, host ignore-errors "
                                 "says {}".format(cut.name, cut.name in swallowed,
                                                  site in inside))
