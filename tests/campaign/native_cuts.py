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
    # The book whose `(defun PROGRAM ...)' holds the cut.
    book: str = "byte-store-programs.lisp"


# The committed-history marker program (lane p10-marker-model).
MARKER_BOOK = "byte-store-marker-program.lisp"
# The programs of one commit, in the order the host runs them: every post
# cut's coordinate is the earlier programs run to their ends, then its own
# program up to the cut.
POST_PROGRAMS = ("fn-bs-frontier-program", "fn-bs-record-program",
                 "fn-bs-marker-program", "fn-bs-finish-program")

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
    # fnn-mark-committed, run after fnn-publish returned :durable and before
    # fnn-finish at every commit site (verify_commit_order): the record is
    # durable at every marker cut.
    *(NativeCut(name, "fn-bs-marker-program", "present", book=MARKER_BOOK)
      for name in ("marker-created", "marker-written", "marker-staged-durable",
                   "marker-replaced", "marker-durable")),
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

# The offline profile upgrade (`operator CONFIG store upgrade-profile P' and
# the developer `store ROOT upgrade-profile P'), fn-bs-profile-program in
# books/byte-store-profile-program.lisp, selected by FN_NATIVE_PROFILE_FAULT.
# The candidate column is the profile the next open must read: the old one
# before the rename, the new one after the root barrier, either at the
# rename.  At every cut the store opens with one of the two profiles and
# never a torn one (fn-bs-profile-program-crash-is-old-or-new), and its
# budget is the old or the new one (-crash-budget-is-old-or-new).
PROFILE_BOOK = "byte-store-profile-program.lisp"
PROFILE_CUTS = (
    NativeCut("profile-created", "fn-bs-profile-program", "old", book=PROFILE_BOOK),
    NativeCut("profile-written", "fn-bs-profile-program", "old", book=PROFILE_BOOK),
    NativeCut("profile-staged-durable", "fn-bs-profile-program", "old", book=PROFILE_BOOK),
    NativeCut("profile-replaced", "fn-bs-profile-program", "either", book=PROFILE_BOOK),
    NativeCut("profile-durable", "fn-bs-profile-program", "new", book=PROFILE_BOOK),
)

# The exact-state checkpoint (P3): `operator CONFIG store checkpoint' and the
# developer `store ROOT checkpoint' write fn-bs-scp-program, selected by
# FN_NATIVE_STATE_CHECKPOINT_FAULT.  The candidate column is the checkpoint
# the next open reads: the old one (or none) before the rename, the new one
# after the root barrier, either at the rename.  At every cut the open reads
# one of the two whole files, never a torn one
# (fn-bs-scp-program-crash-is-old-or-new), and either opens to the
# full-replay state (fn-sn-recover-from-checkpoint-equals-full-recover).
STATE_CHECKPOINT_BOOK = "byte-store-state-checkpoint-program.lisp"
STATE_CHECKPOINT_CUTS = tuple(
    NativeCut(name, "fn-bs-scp-program", candidate, book=STATE_CHECKPOINT_BOOK)
    for name, candidate in (("state-checkpoint-created", "old"),
                            ("state-checkpoint-written", "old"),
                            ("state-checkpoint-staged-durable", "old"),
                            ("state-checkpoint-replaced", "either"),
                            ("state-checkpoint-durable", "new")))

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
    NativeCut("pack-retire-unlink", "fn-cprt-retire-program", "either",
              book="checkpoint-pack-retire.lisp"),
    NativeCut("pack-retire-directory", "fn-cprt-retire-program", "n/a",
              book="checkpoint-pack-retire.lisp"),
)
# The two entries that reach every CHECKPOINT_CUTS site on a pack: the
# developer `checkpoint' verb (`pack ROOT select', then `pack-reclaim ROOT',
# then `pack-retire ROOT') and the public `operator CONFIG store compact'
# (host/native/checkpoint.lisp `fnn-compact-steps', which carries out
# books/store-compact-verb.lisp `*fn-cverb-pack-steps*').  Since the
# chained-packs join (735614d6) the :pack arm extends the chain
# (`fnn-pack-extend-chain'), which publishes and selects each link, so the
# :select arm calls nothing: its function is called inside the pack arm's.
COMPACT_ENTRY_STEPS = (
    ("pack", "fnn-pack-extend-chain"),
    ("select", None),
    ("reclaim", "fnn-pack-prefix-reclaim"),
    ("retire", "fnn-pack-retire-older-generations"),
)
# The one link of a chain, in fn-cpp-publication-step then fn-cpp-marker-step
# order: the candidate's publication, then the selection of it.
COMPACT_CHAIN_LINK = ("fnn-pack-publish-generation", "fnn-pack-select")


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
    for index, step in enumerate(model_steps(cut.program, cut.book)):
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
        model_names = model_cut_names(cut.program, cut.book)
        if model_names.count(cut.model_name or cut.name) < cut.occurrence:
            raise AssertionError("{} occurrence {} absent from {}".format(
                cut.name, cut.occurrence, cut.program))
    verify_recovery_order()
    verify_swallowed_cuts()
    verify_profile_cut_map()
    verify_state_checkpoint_cut_map()
    verify_marker_cut_map()


def verify_profile_cut_map() -> None:
    """The host's profile cuts are the model program's, in its order.

    The host reaches them in `fnn-upgrade-profile-write' in the program's
    order: the two staging cuts inside fnn-write-staged-at, then the three
    `fnn-at' sites around the rename and the root barrier.
    """
    declared = tuple(c.name for c in PROFILE_CUTS)
    if declared != native_declared_cut_names("fnn-profile-model-cuts"):
        raise AssertionError("native/model profile cuts differ")
    if declared != model_cut_names("fn-bs-profile-program", PROFILE_BOOK):
        raise AssertionError("profile cuts are not fn-bs-profile-program's")
    source = (ROOT / "host/native/io.lisp").read_text()
    write = host_function(source, "fnn-upgrade-profile-write")
    order = [write.index(":profile-created :profile-written"),
             write.index("(fnn-at store :profile-staged-durable)"),
             write.index("(fnn-replace stage (fnn-config-path store))"),
             write.index("(fnn-at store :profile-replaced)"),
             write.index("(fnn-fsync-dir (fnn-store-root store))"),
             write.index("(fnn-at store :profile-durable)")]
    if order != sorted(order):
        raise AssertionError("fnn-upgrade-profile-write is out of the program's order")
    for cut in PROFILE_CUTS:
        steps = model_steps(cut.program, cut.book)
        index = cut_step_index(cut)
        renamed = any(s.kind == "rename" for s in steps[:index])
        fenced = any(s.kind == "fsync-dir" for s in steps[:index])
        expected = "new" if fenced else ("either" if renamed else "old")
        if cut.candidate != expected:
            raise AssertionError("{}: candidate {} but the program says {}".format(
                cut.name, cut.candidate, expected))


def verify_state_checkpoint_cut_map() -> None:
    """The host's state-checkpoint cuts are fn-bs-scp-program's, in its order,
    reached by `fnn-state-checkpoint-write' as the profile writer reaches its own."""
    declared = tuple(c.name for c in STATE_CHECKPOINT_CUTS)
    if declared != native_declared_cut_names("fnn-state-checkpoint-model-cuts"):
        raise AssertionError("native/model state-checkpoint cuts differ")
    if declared != model_cut_names("fn-bs-scp-program", STATE_CHECKPOINT_BOOK):
        raise AssertionError("state-checkpoint cuts are not fn-bs-scp-program's")
    source = (ROOT / "host/native/io.lisp").read_text()
    write = host_function(source, "fnn-state-checkpoint-write")
    order = [write.index(":state-checkpoint-created :state-checkpoint-written"),
             write.index("(fnn-at store :state-checkpoint-staged-durable)"),
             write.index("(fnn-replace stage (fnn-state-checkpoint-path store))"),
             write.index("(fnn-at store :state-checkpoint-replaced)"),
             write.index("(fnn-fsync-dir (fnn-store-root store))"),
             write.index("(fnn-at store :state-checkpoint-durable)")]
    if order != sorted(order):
        raise AssertionError("fnn-state-checkpoint-write is out of the program's order")
    for cut in STATE_CHECKPOINT_CUTS:
        steps = model_steps(cut.program, cut.book)
        index = cut_step_index(cut)
        renamed = any(s.kind == "rename" for s in steps[:index])
        fenced = any(s.kind == "fsync-dir" for s in steps[:index])
        expected = "new" if fenced else ("either" if renamed else "old")
        if cut.candidate != expected:
            raise AssertionError("{}: candidate {} but the program says {}".format(
                cut.name, cut.candidate, expected))


def program_book(program: str) -> str:
    """The book whose defun holds PROGRAM, from the cut table."""
    return next((c.book for c in ALL_CUTS + PROFILE_CUTS + STATE_CHECKPOINT_CUTS
                 if c.program == program),
                "byte-store-programs.lisp")


def marker_fate(cut: NativeCut) -> str:
    """What committed-history.json holds after a death at CUT: the prior
    post's marker ("old"), this post's ("new"), or "either".

    Derived from the coordinate: a cut of an earlier program leaves the old
    marker, a later program's the new one; inside fn-bs-marker-program the
    rename onto the root makes it either and the root barrier new
    (books/byte-store-marker-program.lisp fn-bs-marker-crash-is-the-history-table).
    """
    program = POST_PROGRAMS.index(cut.program)
    marker = POST_PROGRAMS.index("fn-bs-marker-program")
    if program != marker:
        return "old" if program < marker else "new"
    steps = model_steps(cut.program, cut.book)
    index = cut_step_index(cut)
    renamed = any(s.kind == "rename" for s in steps[:index])
    fenced = any(s.kind == "fsync-dir" for s in steps[:index])
    return "new" if fenced else ("either" if renamed else "old")


def verify_marker_cut_map() -> None:
    """The marker cuts are ACL2's table, in the program's order, and every
    commit site runs publish, then the marker, then finish.

    fn-hm-marker-cut-names (books/store-history-marker.lisp) is the table
    the developer selector validates against; fn-bs-marker-program's cuts are
    the model's.  fnn-command-post, fnn-command-probe (host/native/io.lisp)
    and fnn-owner-publish-prepared (host/native/owner.lisp) call fnn-publish,
    fnn-mark-committed and fnn-finish in that source order, which is the
    order POST_PROGRAMS gives the model.
    """
    declared = tuple(c.name for c in POST_CUTS if c.program == "fn-bs-marker-program")
    if declared != model_cut_names("fn-bs-marker-program", MARKER_BOOK):
        raise AssertionError("marker cuts are not fn-bs-marker-program's")
    book = (ROOT / "books/store-history-marker.lisp").read_text()
    table = re.findall(r'"([a-z-]+)"', host_function(book, "fn-hm-marker-cut-names"))
    if tuple(table) != declared:
        raise AssertionError("marker cuts are not fn-hm-marker-cut-names")
    if tuple(c.program for c in POST_CUTS) != tuple(sorted(
            (c.program for c in POST_CUTS), key=POST_PROGRAMS.index)):
        raise AssertionError("POST_CUTS is out of POST_PROGRAMS order")
    io = (ROOT / "host/native/io.lisp").read_text()
    owner = (ROOT / "host/native/owner.lisp").read_text()
    for source, name in ((io, "fnn-command-post"), (io, "fnn-command-probe"),
                         (owner, "fnn-owner-publish-prepared")):
        body = host_function(source, name)
        order = [body.index("(fnn-publish store"),
                 body.index("(fnn-mark-committed store"),
                 body.index("(fnn-finish store)")]
        if order != sorted(order):
            raise AssertionError("{} does not publish, mark, then finish".format(name))
    mark = host_function(io, "fnn-mark-committed")
    order = [mark.index(":marker-created :marker-written"),
             mark.index("(fnn-at store :marker-staged-durable)"),
             mark.index("(fnn-replace stage (fnn-history-marker-path store))"),
             mark.index("(fnn-at store :marker-replaced)"),
             mark.index("(fnn-fsync-dir (fnn-store-root store))"),
             mark.index("(fnn-at store :marker-durable)")]
    if order != sorted(order):
        raise AssertionError("fnn-mark-committed is out of the program's order")


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
             recover.index("(fnn-sweep-staging store)"),
             # D31: the marker catch-up (fn-bs-marker-program, the same
             # host cuts as a commit's) after the barriers and the sweep,
             # before the open returns.
             recover.index("(fnn-mark-committed store nil frame)"),
             recover.index("(setf (fnn-store-fenced store) nil)")]
    if order != sorted(order):
        raise AssertionError("fnn-recover no longer sweeps and catches up after its barriers")
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
    # The theorem subjects of books/checkpoint-compaction-preservation are
    # the functions the reclaim and the next open call.
    reclaim_host = host_function(native, "fnn-pack-prefix-reclaim")
    if "(fnn-core 'fn-bs-pack-reclaim-plan observed limit lower)" not in reclaim_host:
        raise AssertionError("pack-reclaim no longer calls fn-bs-pack-reclaim-plan")
    order = [reclaim_host.index("(fnn-unlink "),
             reclaim_host.index('(fnn-checkpoint-test-stop "pack-reclaim-unlink")'),
             reclaim_host.index("(fnn-fsync-dir (fnn-transactions store))"),
             reclaim_host.index('(fnn-checkpoint-test-stop "pack-reclaim-directory")')]
    if order != sorted(order):
        raise AssertionError("fnn-pack-prefix-reclaim is out of fn-bs-pack-reclaim-steps order")
    retire = model_cut_names("fn-cprt-retire-steps", "checkpoint-pack-retire.lisp")
    for name in ("pack-retire-unlink", "pack-retire-directory"):
        if name not in retire:
            raise AssertionError("{} absent from retire model".format(name))
    verify_compact_entries(native)
    bridge = (ROOT / "host/checkpoint-host.lisp").read_text()
    for wrapper, subject in (
            ("fn-store-compact-decide", "fn-cverb-decide"),
            ("fn-store-checkpoint-compaction-observe", "fn-ccp-observe-framed"),
            ("fn-store-checkpoint-compaction-coverage", "fn-ccp-coverage-framed")):
        body = host_function(bridge, wrapper)
        if "({} ".format(subject) not in body:
            raise AssertionError("{} does not call {}".format(wrapper, subject))


def native_reachable_functions(native: str, root: str) -> tuple[str, ...]:
    """The host/native/checkpoint.lisp functions ROOT reaches by a call or a
    `#'' reference, ROOT first (functions of other files are not followed)."""
    defined = set(re.findall(r"^\(defun (fnn-[a-z0-9-]+) ", native, re.M))
    seen, queue = [root], [root]
    while queue:
        body = host_function(native, queue.pop(0))
        for name in re.findall(r"(?:\(|#')(fnn-[a-z0-9-]+)[\s)]", body):
            if name in defined and name not in seen:
                seen.append(name)
                queue.append(name)
    return tuple(seen)


def verify_compact_entries(native: str) -> None:
    """Both compaction entries reach the checkpoint cuts through one code path.

    `fnn-compact-steps' asks exactly one decision, host/checkpoint-host.lisp
    `fn-store-compact-decide' (books/store-compact-verb.lisp
    `fn-cverb-decide', whose steps are `*fn-cverb-pack-steps*'), through
    `fnn-compact-decide': once, and again before every further chain link
    (the :admit of `fnn-pack-extend-chain'), and it asks nothing else.  The
    pack publication passes the checkpoint candidate observer (the
    candidate-* cuts), the pack and checkpoint selections share
    `fnn-marker-replace' (the selection-* cuts), the operator verb's step
    arms call the same functions the developer verb calls, ACL2's step list
    names exactly those arms in that order, and every process-death cut the
    compaction path can take is a CHECKPOINT_CUTS model program cut: a native
    compaction cut with no model crash point fails here.
    """
    publish = host_function(native, "fnn-pack-publish-generation")
    if ":observer #'fnn-checkpoint-candidate-observer" not in publish:
        raise AssertionError("pack publication does not reach the candidate cuts")
    for caller in ("fnn-pack-select", "fnn-checkpoint-select"):
        if "(fnn-marker-replace " not in host_function(native, caller):
            raise AssertionError("{} does not share the marker loop".format(caller))
    decide = host_function(native, "fnn-compact-decide")
    if re.findall(r"\(fnn-core '([a-z0-9-]+)", decide) != ["fn-store-compact-decide"]:
        raise AssertionError("fnn-compact-decide does not ask exactly fn-store-compact-decide")
    steps = host_function(native, "fnn-compact-steps")
    if "(fnn-core " in steps:
        raise AssertionError("fnn-compact-steps asks a decision other than fnn-compact-decide")
    asks = [m.start() for m in re.finditer(r"\(fnn-compact-decide store records\)", steps)]
    pack_arm = re.search(r"\(:pack\s", steps)
    admit = steps.find(":admit ")
    if (len(asks) != 2 or not pack_arm or admit < pack_arm.start()
            or not asks[0] < pack_arm.start() < admit < asks[1]):
        raise AssertionError("fnn-compact-steps does not ask fn-store-compact-decide first "
                             "and again in the pack arm's :admit")
    positions = []
    for keyword, function in COMPACT_ENTRY_STEPS:
        arm = re.search(r"\(:{}\s".format(keyword), steps)
        if not arm or (function is not None
                       and not re.search(r"\({}\s".format(function), steps)):
            raise AssertionError("compact step {} does not call {}".format(keyword, function))
        positions.append(arm.start())
    if positions != sorted(positions):
        raise AssertionError("fnn-compact-steps arms are out of step order")
    chain = host_function(native, "fnn-pack-extend-chain")
    found = [re.search(r"\(funcall admit\s", chain)] + [
        re.search(r"\({}\s".format(f), chain) for f in COMPACT_CHAIN_LINK]
    order = [m.start() if m else -1 for m in found]
    if min(order) < 0 or order != sorted(order):
        raise AssertionError("fnn-pack-extend-chain does not admit, publish and select "
                             "each link in that order")
    book = (ROOT / "books/store-compact-verb.lisp").read_text()
    match = re.search(r"\(defconst \*fn-cverb-pack-steps\* '\(([^)]*)\)\)", book)
    if not match or tuple(re.findall(r":([a-z]+)", match.group(1))) != tuple(
            k for k, _ in COMPACT_ENTRY_STEPS):
        raise AssertionError("*fn-cverb-pack-steps* is not the host's step order")
    model = {cut.name for cut in CHECKPOINT_CUTS}
    taken = []
    for function in native_reachable_functions(native, "fnn-compact-steps"):
        taken += re.findall(r'\(fnn-checkpoint-test-stop "([a-z0-9-]+)"\)',
                            host_function(native, function))
    unmodelled = sorted(set(taken) - model)
    if unmodelled:
        raise AssertionError("native compaction cuts with no model program cut: {}".format(
            ", ".join(unmodelled)))
    if set(taken) != model:
        raise AssertionError("model compaction cuts the native path does not take: {}".format(
            ", ".join(sorted(model - set(taken)))))
    command = host_function(native, "fnn-checkpoint-command")
    for word, function in (('"pack"', "fnn-checkpoint-command-pack"),
                           ('"pack-reclaim"', "fnn-checkpoint-command-pack-reclaim"),
                           ('"pack-retire"', "fnn-checkpoint-command-pack-retire")):
        if word not in command or function not in command:
            raise AssertionError("developer checkpoint verb lacks {}".format(word))


# The post cut whose EIO the host swallows: a cut between two best-effort
# staging steps after the record's directory barrier (P-RECORD's `970 best
# effort', `971 best effort').  `post_arm' in native_nntp_post_probe derives
# the arm from the model coordinate; this checks the host agrees: the
# `fnn-at' of every such cut, and of no other post cut, lies inside the
# `ignore-errors' form of fnn-publish.
def swallowed_cut(cut: NativeCut) -> bool:
    steps = model_steps(cut.program, cut.book)
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
