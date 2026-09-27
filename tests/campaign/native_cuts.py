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

# `store import DIR' (host/native/io.lisp `fnn-command-store-import'):
# books/store-import-publication.lisp fn-bs-imp-program, selected by
# FN_NATIVE_IMPORT_FAULT.  The program is its parts in IMPORT_PROGRAMS order;
# a repeated cut (per subdirectory, per file) is selected at its first
# occurrence.  The candidate column is whether ROOT holds the imported store
# after a death at the cut: absent before the no-replace rename, either at
# it, present once ROOT's parent is fenced.
IMPORT_BOOK = "store-import-publication.lisp"
IMPORT_PROGRAMS = ("fn-bs-imp-stage-steps", "fn-bs-imp-subdir-steps",
                   "fn-bs-imp-file-steps", "fn-bs-imp-fence-steps",
                   "fn-bs-imp-seal-steps", "fn-bs-imp-publication-program")
IMPORT_CUTS = tuple(
    NativeCut(name, program, candidate, book=IMPORT_BOOK)
    for name, program, candidate in (
        ("import-stage-created", "fn-bs-imp-stage-steps", "absent"),
        ("import-subdir-created", "fn-bs-imp-subdir-steps", "absent"),
        ("import-file-created", "fn-bs-imp-file-steps", "absent"),
        ("import-file-written", "fn-bs-imp-file-steps", "absent"),
        ("import-file-durable", "fn-bs-imp-file-steps", "absent"),
        ("import-subdir-durable", "fn-bs-imp-fence-steps", "absent"),
        ("import-staged-durable", "fn-bs-imp-seal-steps", "absent"),
        ("import-validated", "fn-bs-imp-publication-program", "absent"),
        ("import-published", "fn-bs-imp-publication-program", "either"),
        ("import-durable", "fn-bs-imp-publication-program", "present")))

# The suffixes of the publication program's cuts, in its order.
PUBLICATION_SUFFIXES = tuple(c.name[len("import-"):] for c in IMPORT_CUTS)

# `operator CONFIG init' (host/native/io.lisp `fnn-command-init-published',
# PKT-647): books/store-init-publication.lisp fn-bs-init-pub-program, the
# import's program with init's cut names, selected by FN_NATIVE_INIT_FAULT.
INIT_PUB_BOOK = "store-init-publication.lisp"
INIT_PUB_CUTS = tuple(
    NativeCut("init-" + c.name[len("import-"):], "fn-bs-init-pub-program", c.candidate,
              book=INIT_PUB_BOOK)
    for c in IMPORT_CUTS)

# The chained-packs program (lane pack-chain-cut, PKT-459).
CHAIN_BOOK = "checkpoint-pack-chain.lisp"

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
    # Between two links of a chain (fnn-pack-extend-chain): after the link's
    # selection returned :durable, before the next link's admit.  The chain
    # program's cut (books/checkpoint-pack-chain.lisp fn-ccc-chain-program;
    # fn-ccc-chain-link-cut-walks-the-extended-chain and
    # fn-ccc-chain-link-cut-reopens-to-the-history): links 1..N published
    # and selected, the marker naming link N.
    NativeCut("pack-chain-link", "fn-ccc-chain-program", "present",
              book=CHAIN_BOOK),
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
# The one link of a chain, in fn-ccc-chain-program order (:publish, :select,
# then the pack-chain-link cut): the candidate's publication
# (fn-cpp-publication-step), the selection of it (fn-cpp-marker-step), then
# the between-links stop hook.
COMPACT_CHAIN_LINK = ("fnn-pack-publish-generation", "fnn-pack-select",
                      '(fnn-checkpoint-test-stop "pack-chain-link")')


# The record log (lane w6-log-core; books/store-log-programs.lisp).  Each cut
# is a named point of one log program, hosted by one function of
# host/native/io.lisp (LOG_PROGRAM_HOSTS); the candidate is the batch's fate
# at the cut: at log-written a crash image scans to the committed records and
# a prefix of the batch (T2, "either"); at log-fenced the batch is committed;
# the recovery cuts keep the scanned records ("present": the zeroing write
# lies past the frontier).
LOG_BOOK = "store-log-programs.lisp"
LOG_PROGRAM_HOSTS = {
    "fn-lg-append-program": "fnn-log-append",
    "fn-lg-fence-program": "fnn-log-fence",
    "fn-lg-recover-program": "fnn-log-recover",
    # The segment's extension (lane log-2, PKT-COL-4).
    "fn-lg-extend-program": "fnn-log-ensure-extent",
}
LOG_EXTEND_BOOK = "store-log-extend.lisp"
LOG_PROGRAM_BOOKS = {"fn-lg-extend-program": LOG_EXTEND_BOOK}
LOG_CUTS = (
    NativeCut("log-written", "fn-lg-append-program", "either", book=LOG_BOOK),
    NativeCut("log-fenced", "fn-lg-fence-program", "present",
              follows="fn-lg-append-program", book=LOG_BOOK),
    NativeCut("log-truncated", "fn-lg-recover-program", "present", book=LOG_BOOK),
    NativeCut("log-recovered", "fn-lg-recover-program", "present", book=LOG_BOOK),
    # A death during the extension (at rest: no batch in flight) leaves the
    # committed records exactly (fn-lg-extension-written-crash-reads-the-
    # committed-records); no member is in the log's batch yet.
    NativeCut("log-extended", "fn-lg-extend-program", "present", book=LOG_EXTEND_BOOK),
    NativeCut("log-extent-fenced", "fn-lg-extend-program", "present", book=LOG_EXTEND_BOOK),
)
# The host primitive that performs each log step kind, and its cut call.
LOG_STEP_HOST = {"write-at": "(fnn-log-pwrite ", "fence": "(fnn-log-fdatasync ",
                 "extend-to": "(fnn-log-preallocate "}

# The served commit on a format-9 store (lane commit-onto-log): P-BATCH as the
# owner's commit quantum runs it (host/native/owner.lisp
# fnn-owner-commit-queued-locked).  Each member's finish (fnn-finish: cuts
# finish-consumed, finish-durable) is its in-memory completion, in order,
# BEFORE the batch's append and barrier (fnn-log-commit-open-batch, `fnn-at'
# after each program's host call); no member's reply leaves the owner before
# log-fenced.  So a process death at a finish cut of a served POST leaves its
# record unwritten (absent), at log-written a prefix of the batch (either),
# from log-fenced on the whole batch (present).  A batch of one outside a
# quantum (fnn-log-publish: the control socket's post, retention, identity,
# consumer and topic events) runs append and barrier first and its finish
# cuts are then present: POST_LOG_ONE_CANDIDATE.
POST_LOG_CUTS = (
    NativeCut("finish-consumed", "fn-bs-finish-program", "absent"),
    NativeCut("finish-durable", "fn-bs-finish-program", "absent"),
    NativeCut("log-written", "fn-lg-append-program", "either", book=LOG_BOOK),
    NativeCut("log-fenced", "fn-lg-fence-program", "present",
              follows="fn-lg-append-program", book=LOG_BOOK),
)
POST_LOG_ONE_CANDIDATE = {"log-written": "either", "log-fenced": "present",
                          "finish-consumed": "present", "finish-durable": "present"}
# The host's order for the batch's two programs: the program's host call,
# then the `fnn-at' of its cut.
POST_LOG_HOST = (("(fnn-log-append ", "(fnn-at store :log-written)"),
                 ("(fnn-log-fence ", "(fnn-at store :log-fenced)"))

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
              "rename", "link", "unlink",
              # books/store-import-publication.lisp's two directory steps.
              "mkdir", "rename-dir-noreplace",
              # books/store-log-programs.lisp's positioned write and barrier.
              "write-at", "fence",
              # books/store-log-extend.lisp's zero extension.
              "extend-to")
SYSCALL_KINDS = frozenset(STEP_KINDS[2:])


@dataclass(frozen=True)
class ModelStep:
    kind: str
    args: tuple[str, ...]

    @property
    def directory(self) -> str | None:
        """The directory the step acts in: the target of a rename or link."""
        if self.kind in ("rename", "link", "rename-dir-noreplace"):
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
    verify_state_checkpoint_cut_map()
    verify_marker_cut_map()
    verify_import_cut_map()


def verify_state_checkpoint_cut_map() -> None:
    """The host's state-checkpoint cuts are fn-bs-scp-program's, in its order,
    reached by `fnn-state-checkpoint-write' in the program's order."""
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


def verify_import_cut_map() -> None:
    """The host's import cuts are fn-bs-imp-program's, in its order: the
    declared names are the program's cuts, fn-bs-imp-program runs its parts in
    IMPORT_PROGRAMS order, `fnn-command-store-import' reaches the cuts, the
    no-replace rename and the parent fence in that order (the three file cuts
    inside `fnn-import-write-file', between its open, write and fence), and
    the candidate column is the one the program's steps give."""
    declared = tuple(c.name for c in IMPORT_CUTS)
    if declared != native_declared_cut_names("fnn-import-model-cuts"):
        raise AssertionError("native/model import cuts differ")
    program_cuts = tuple(name for program in IMPORT_PROGRAMS
                         for name in model_cut_names(program, IMPORT_BOOK))
    if declared != program_cuts:
        raise AssertionError("import cuts are not fn-bs-imp-program's: {!r}".format(
            program_cuts))
    for cut in IMPORT_CUTS:
        if cut.name not in model_cut_names(cut.program, cut.book):
            raise AssertionError("{} absent from {}".format(cut.name, cut.program))
    book = (ROOT / "books" / IMPORT_BOOK).read_text()
    staging = host_function(book, "fn-bs-imp-staging-program")
    order = [staging.index("(fn-bs-imp-stage-steps "),
             staging.index("(fn-bs-imp-subdir-steps "),
             staging.index("(fn-bs-imp-files-steps "),
             staging.index("(fn-bs-imp-fence-steps "),
             staging.index("(fn-bs-imp-seal-steps)")]
    whole = host_function(book, "fn-bs-imp-program")
    if (order != sorted(order)
            or whole.index("(fn-bs-imp-staging-program ")
            > whole.index("(fn-bs-imp-publication-program ")):
        raise AssertionError("fn-bs-imp-program no longer runs its parts in order")
    if "(fn-bs-imp-file-steps (car files))" not in host_function(book, "fn-bs-imp-files-steps"):
        raise AssertionError("fn-bs-imp-files-steps no longer runs fn-bs-imp-file-steps")
    source = (ROOT / "host/native/io.lisp").read_text()
    body = host_function(source, "fnn-command-store-import")
    if "(fnn-core 'fn-bs-imp-classify" not in host_function(source, "fnn-import-classify"):
        raise AssertionError("fnn-import-classify does not call fn-bs-imp-classify")
    if not (body.index("(fnn-import-leftover-stage root-path)")
            < body.index("(fnn-staged-publication\n         \"import\"")):
        raise AssertionError("fnn-command-store-import does not classify before publishing")
    verify_staged_publication(source, "import", declared)
    _import_candidates()


def verify_staged_publication(source: str, kind: str, declared: tuple) -> None:
    """`fnn-staged-publication' reaches fn-bs-imp-program's steps and cuts in
    its order (the three file cuts inside `fnn-import-write-file', between its
    open, write and fence), each cut named KIND-SUFFIX, and publishes with a
    no-replace rename only."""
    if declared != tuple("{}-{}".format(kind, s) for s in PUBLICATION_SUFFIXES):
        raise AssertionError("{} cuts are not the publication program's".format(kind))
    body = host_function(source, "fnn-staged-publication")
    at = '(fnn-pub-at stage kind "{}")'.format
    order = [body.index("(fnn-publication-lock root-path)"),
             body.index("(fnn-mkdir stage-root #o700)"),
             body.index(at("stage-created")),
             body.index("(fnn-mkdir (fnn-join stage-root sub) #o700)"),
             body.index(at("subdir-created")),
             body.index("(fnn-import-write-file stage (car file) (cdr file) kind)"),
             body.index("(fnn-fsync-dir (fnn-join stage-root sub))"),
             body.index(at("subdir-durable")),
             body.index("(fnn-fsync-dir stage-root)"),
             body.index(at("staged-durable")),
             body.index("(fnn-open-live-store stage-root t)"),
             body.index(at("validated")),
             body.index("(fnn-rename-no-replace stage-root root-path)"),
             body.index(at("published")),
             body.index("(fnn-fsync-dir parent)"),
             body.index(at("durable")),
             body.index("(fnn-publication-unlock lock)")]
    if order != sorted(order):
        raise AssertionError("fnn-staged-publication is out of fn-bs-imp-program's order")
    if "(fnn-replace " in body:
        raise AssertionError("fnn-staged-publication publishes with a replacing rename")
    write = host_function(source, "fnn-import-write-file")
    order = [write.index("(fnn-open path"),
             write.index('(fnn-pub-at store kind "file-created")'),
             write.index("(fnn-write-all fd"),
             write.index('(fnn-pub-at store kind "file-written")'),
             write.index("(fnn-fsync-file fd)"),
             write.index('(fnn-pub-at store kind "file-durable")')]
    if order != sorted(order):
        raise AssertionError("fnn-import-write-file is out of fn-bs-imp-file-steps order")
    if "sb-posix:o-excl" not in write:
        raise AssertionError("fnn-import-write-file does not create exclusively")


def init_publication_cut_names() -> dict:
    """books/store-init-publication.lisp *fn-bs-init-pub-cut-names*: each
    fn-bs-imp-program cut to init's name for it."""
    book = (ROOT / "books" / INIT_PUB_BOOK).read_text()
    table = book[book.index("(defconst *fn-bs-init-pub-cut-names*"):]
    table = table[:table.index("\n\n")]
    return dict(re.findall(r'\("([a-z-]+)" \. "([a-z-]+)"\)', table))


def verify_init_publication_cut_map() -> None:
    """`operator init' (fnn-command-init-published) runs the import's
    program with init's cut names: the host's +fnn-init-publication-cuts+ are
    *fn-bs-init-pub-cut-names* applied to fn-bs-imp-program's cuts in order,
    fn-bs-init-pub-program renames the cuts of fn-bs-imp-program, the host
    asks ACL2's admission before publishing through fnn-staged-publication,
    and the candidate column is the import's."""
    declared = tuple(c.name for c in INIT_PUB_CUTS)
    if declared != native_declared_cut_names("fnn-init-publication-cuts"):
        raise AssertionError("native/model init publication cuts differ")
    renamed = init_publication_cut_names()
    if declared != tuple(renamed[c.name] for c in IMPORT_CUTS):
        raise AssertionError("init cuts are not the import program's, renamed")
    book = (ROOT / "books" / INIT_PUB_BOOK).read_text()
    program = host_function(book, "fn-bs-init-pub-program")
    if "(fn-bs-init-pub-rename-cuts\n   (fn-bs-imp-program " not in program:
        raise AssertionError("fn-bs-init-pub-program is not fn-bs-imp-program renamed")
    if tuple(c.candidate for c in INIT_PUB_CUTS) != tuple(c.candidate for c in IMPORT_CUTS):
        raise AssertionError("init candidates differ from the import program's")
    source = (ROOT / "host/native/io.lisp").read_text()
    body = host_function(source, "fnn-command-init-published")
    order = [body.index('(fnn-import-leftover-stage root-path "init")'),
             body.index("(fnn-import-classify leftover root-path)"),
             body.index("(fnn-core 'fn-bs-init-pub-admission"),
             body.index('(fnn-staged-publication\n       "init"')]
    if order != sorted(order):
        raise AssertionError("fnn-command-init-published publishes before ACL2 admits")
    operator = (ROOT / "host/native/operator.lisp").read_text()
    # The call, whitespace collapsed: the root, the groups, the profile and
    # (since batch AS's merge of store-mount-identity) the mission's
    # durability policy.
    if "(fnn-command-init-published root groups profile" not in " ".join(host_function(
            operator, "fnn-operator-execute-init").split()):
        raise AssertionError("operator init does not run the publication program")
    verify_staged_publication(source, "init", declared)


def _import_candidates() -> None:
    for cut in IMPORT_CUTS:
        own = IMPORT_PROGRAMS.index(cut.program)
        before = [step for program in IMPORT_PROGRAMS[:own]
                  for step in model_steps(program, IMPORT_BOOK)]
        before += list(model_steps(cut.program, cut.book)[:cut_step_index(cut)])
        kinds = [step.kind for step in before]
        renamed = "rename-dir-noreplace" in kinds
        fenced = renamed and "fsync-dir" in kinds[kinds.index("rename-dir-noreplace"):]
        expected = "present" if fenced else ("either" if renamed else "absent")
        if cut.candidate != expected:
            raise AssertionError("{}: candidate {} but the program says {}".format(
                cut.name, cut.candidate, expected))


def program_book(program: str) -> str:
    """The book whose defun holds PROGRAM, from the cut table."""
    return next((c.book for c in ALL_CUTS + STATE_CHECKPOINT_CUTS + IMPORT_CUTS
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


def book_function(name: str) -> tuple:
    """The one book under books/ that defines NAME, and the definition.

    A source test that follows a host call into ACL2 by the callee's name,
    so a renamed or re-homed definition does not need a new literal line.
    """
    found = [(path, host_function(path.read_text(encoding="utf-8"), name))
             for path in sorted((ROOT / "books").glob("*.lisp"))
             if "(defun {} ".format(name) in path.read_text(encoding="utf-8")]
    if len(found) != 1:
        raise AssertionError("{} is defined in {} books, not one".format(name, len(found)))
    return found[0]


def calls_through_book(body: str, callee: str, arguments: str) -> list:
    """The functions BODY calls over ARGUMENTS that are CALLEE or reach it.

    CALLEE counts when BODY calls it over ARGUMENTS itself, or calls over
    ARGUMENTS the one book function whose definition calls CALLEE: a host
    line that routes the same open through an ACL2 wrapper keeps the check.
    """
    heads = re.findall(r"\((fn-[a-z0-9-]+) {}\)".format(re.escape(arguments)), body)
    return [head for head in heads
            if head == callee
            or "({} ".format(callee) in book_function(head)[1]]


def host_reach(source: str, name: str) -> str:
    """NAME's definition and those of the functions in SOURCE it calls.

    One level: a verb split into a handler and its body keeps the calls its
    source tests look for, while a call moved out of the verb's reach fails.
    """
    body = host_function(source, name)
    callees = sorted(set(re.findall(r"\((fnn?-[a-z0-9-]+)[\s)]", body)) - {name})
    return body + "".join(host_function(source, callee) for callee in callees
                          if "(defun {} ".format(callee) in source)


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
        re.search(re.escape(f) if f.startswith("(") else r"\({}\s".format(f), chain)
        for f in COMPACT_CHAIN_LINK]
    order = [m.start() if m else -1 for m in found]
    if min(order) < 0 or order != sorted(order):
        raise AssertionError("fnn-pack-extend-chain does not admit, publish, select and "
                             "stop at pack-chain-link for each link in that order")
    # The model's link is :publish, :select, then its one cut, and nothing the
    # host does between the selection and the hook touches the disk.
    if model_cut_names("fn-ccc-chain-program", CHAIN_BOOK) != ("pack-chain-link",):
        raise AssertionError("fn-ccc-chain-program's cuts are not (pack-chain-link)")
    program = host_function((ROOT / "books" / CHAIN_BOOK).read_text(), "fn-ccc-chain-program")
    kinds = [program.index(k) for k in ("(list :publish ", "(list :select ",
                                         '(list :cut "pack-chain-link")')]
    if kinds != sorted(kinds):
        raise AssertionError("fn-ccc-chain-program is not :publish, :select, then the cut")
    between = chain[found[2].end():found[3].start()]
    if re.search(r"\(fnn-(?!pack-select\b)[a-z0-9-]+", between):
        raise AssertionError("fnn-pack-extend-chain calls the host between the selection "
                             "and pack-chain-link: the cut is not the selection's state")
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


def verify_log_cut_map() -> None:
    """The host's log cuts are the log programs', in their order: the declared
    names (+fnn-log-model-cuts+) are LOG_CUTS's and the programs' cuts in
    LOG_PROGRAM_HOSTS order; each hosting function performs its program's
    steps (fnn-log-pwrite for :write-at, fnn-log-fdatasync for :fence, and
    `(fnn-log-at :NAME)' for each cut) in the program's order, and every
    `fnn-log-at' in it is one of the program's cuts."""
    declared = tuple(c.name for c in LOG_CUTS)
    if declared != native_declared_cut_names("fnn-log-model-cuts"):
        raise AssertionError("native/model log cuts differ")
    program_cuts = tuple(name for program in LOG_PROGRAM_HOSTS
                         for name in model_cut_names(
                             program, LOG_PROGRAM_BOOKS.get(program, LOG_BOOK)))
    if declared != program_cuts:
        raise AssertionError("log cuts are not the log programs': {!r}".format(program_cuts))
    source = (ROOT / "host/native/io.lisp").read_text()
    for program, host in LOG_PROGRAM_HOSTS.items():
        book = LOG_PROGRAM_BOOKS.get(program, LOG_BOOK)
        body = host_function(source, host)
        at, order = 0, []
        for step in model_steps(program, book):
            needle = ("(fnn-log-at :{})".format(step.args[0]) if step.kind == "cut"
                      else LOG_STEP_HOST[step.kind])
            found = body.find(needle, at)
            if found < 0:
                raise AssertionError("{}: {} {} missing or out of order".format(
                    host, step.kind, step.args))
            order.append(found)
            at = found + len(needle)
        cuts = set(re.findall(r"\(fnn-log-at :([a-z-]+)\)", body))
        if cuts != set(model_cut_names(program, book)):
            raise AssertionError("{} cuts {} are not {}'s".format(host, sorted(cuts), program))
        for kind, needle in LOG_STEP_HOST.items():
            if body.count(needle) != sum(1 for s in model_steps(program, book)
                                         if s.kind == kind):
                raise AssertionError("{}: {} count differs from {}".format(host, kind, program))
    for cut in LOG_CUTS:
        cut_step_index(cut)


# The log's segment programs (lane log-recovery; books/store-log-segments.lisp):
# the rotation at a checkpoint's capture and the drop after its install.
SEGMENT_BOOK = "store-log-segments.lisp"
SEGMENT_PROGRAM_HOSTS = {
    "fn-lgs-rotate-program": "fnn-log-rotate",
    "fn-lgs-drop-program": "fnn-log-drop",
}
SEGMENT_STEP_HOST = {"create": "(fnn-open path", "fsync-file": "(fnn-fsync-file ",
                     "fsync-dir": "(fnn-fsync-dir ", "unlink": "(fnn-unlink "}


def verify_log_segment_cut_map() -> None:
    """Each segment program's hosting function performs its steps in the
    program's order (the syscall's call, then `(fnn-log-at :NAME)' for each
    cut), and every `fnn-log-at' in it is one of the program's cuts."""
    source = (ROOT / "host/native/io.lisp").read_text()
    for program, host in SEGMENT_PROGRAM_HOSTS.items():
        body = host_function(source, host)
        at = 0
        for step in model_steps(program, SEGMENT_BOOK):
            needle = ("(fnn-log-at :{})".format(step.args[0]) if step.kind == "cut"
                      else SEGMENT_STEP_HOST[step.kind])
            found = body.find(needle, at)
            if found < 0:
                raise AssertionError("{}: {} {} missing or out of order".format(
                    host, step.kind, step.args))
            at = found + len(needle)
        cuts = set(re.findall(r"\(fnn-log-at :([a-z-]+)\)", body))
        if cuts != set(model_cut_names(program, SEGMENT_BOOK)):
            raise AssertionError("{} cuts {} are not {}'s".format(host, sorted(cuts), program))


def verify_post_log_cut_map() -> None:
    """The served log route's cuts: the declared names (+fnn-post-log-model-
    cuts+) are POST_LOG_CUTS's; the log programs' own cuts are its last two,
    in order; fnn-log-commit-open-batch calls fnn-log-append then cuts
    log-written, then fnn-log-fence then cuts log-fenced; fnn-finish holds the
    two finish cuts; a batch of one (fnn-log-publish) is committed before the
    record's place is observed; and the commit quantum drains its members
    (their finishes) before it commits the batch, and delivers their replies
    only after."""
    declared = tuple(c.name for c in POST_LOG_CUTS)
    if declared != native_declared_cut_names("fnn-post-log-model-cuts"):
        raise AssertionError("native/model post-log cuts differ")
    program_cuts = (model_cut_names("fn-lg-append-program", LOG_BOOK)
                    + model_cut_names("fn-lg-fence-program", LOG_BOOK))
    if declared[2:] != program_cuts:
        raise AssertionError("post-log cuts are not the log programs': {!r}".format(program_cuts))
    source = (ROOT / "host/native/io.lisp").read_text()
    body = host_function(source, "fnn-log-commit-open-batch")
    at = 0
    for call, cut in POST_LOG_HOST:
        for needle in (call, cut):
            found = body.find(needle, at)
            if found < 0:
                raise AssertionError("fnn-log-commit-open-batch: {} missing or out of order".format(needle))
            at = found + len(needle)
    publish = host_function(source, "fnn-log-publish")
    commit, order = publish.find("(fnn-log-commit-open-batch "), publish.find("(fnn-observe store :log-order)")
    if not (0 <= commit < order):
        raise AssertionError("fnn-log-publish observes the record's place before a batch of one is fenced")
    finish = host_function(source, "fnn-finish")
    for name in declared[:2]:
        if "(fnn-at store :{})".format(name) not in finish:
            raise AssertionError("fnn-finish lacks the {} cut".format(name))
    # The pipelined commit (lane log-2): SEAL is P-BATCH's append and its
    # cut, SYNC its barrier and cut, in the log's own functions.
    for name, (call, cut) in (("fnn-log-seal-open-batch", POST_LOG_HOST[0]),
                              ("fnn-log-sync-sealed-batch", POST_LOG_HOST[1])):
        body = host_function(source, name)
        if not (0 <= body.find(call) < body.find(cut)):
            raise AssertionError("{}: {} then {} missing or out of order".format(name, call, cut))
    owner = (ROOT / "host/native/owner.lisp").read_text()
    # START drains its members, then seals; COMPLETE acknowledges, then
    # delivers; the inline quantum runs START, SYNC, COMPLETE; the committer
    # collects the syncer's word before COMPLETE, and seals the next batch
    # only after the replies of the batch in flight.
    start = host_function(owner, "fnn-owner-commit-start-locked")
    if not (0 <= start.find("(fnn-owner-drain-one ") < start.find("(fnn-log-seal-open-batch ")):
        raise AssertionError("START does not drain its members before the seal")
    complete = host_function(owner, "fnn-owner-commit-complete-locked")
    if not (0 <= complete.find("(fnn-log-batch-finish ") < complete.rfind("(fnn-owner-deliver ")):
        raise AssertionError("COMPLETE does not acknowledge before it delivers")
    quantum = host_function(owner, "fnn-owner-commit-queued-locked")
    order = [quantum.find(x) for x in ("(fnn-owner-commit-start-locked ",
                                       "(fnn-owner-commit-sync ",
                                       "(fnn-owner-commit-complete-locked ")]
    if not (0 <= order[0] < order[1] < order[2]):
        raise AssertionError("the inline commit quantum's order is not START, SYNC, COMPLETE")
    pipeline = host_function(owner, "fnn-owner-commit-pipeline")
    order = [pipeline.find(x) for x in ("(fnn-owner-start-syncer ",
                                        "(sb-thread:join-thread syncer",
                                        "(fnn-owner-commit-complete-locked service members nil deferred)",
                                        "(fnn-log-seal-open-batch store)")]
    if not (0 <= order[0] < order[1] < order[2] < order[3]):
        raise AssertionError("the committer's order is not SYNC, collect, COMPLETE, seal the next batch")
    for cut in POST_LOG_CUTS[2:]:
        cut_step_index(cut)


# The record-log route's arms (lane log-2; books/store-log-route-programs.lisp).
# Each per-file host function above has a format-9 arm, `(when (fnn-store-logp
# store) ...)', that calls the log route instead; tools/native_program_check.py
# reads the per-file route and checks each arm here: the arm's callee's
# durable steps and process-death cuts, in source order, are its programs'
# steps.  Host steps: fnn-log-pwrite is a :write-at, fnn-log-fdatasync and a
# recovery barrier thunk are a :fence, `(fnn-at store :NAME)' and
# `(fnn-log-at :NAME)' are the cut NAME (the log's own and the store's
# injection at one point are one cut), the recovery barrier loop runs once per
# thunk of fnn-store-recovery-barriers.  Calls into LOG_ROUTE_EXPAND are read
# from the callee's own defun; any other call is not a step (fnn-log-take's
# :full arm commits at the operator's bound, a runtime arm; fnn-log-ensure-
# extent's growth is PKT-COL-4's).
LOG_ROUTE_BOOK = "store-log-route-programs.lisp"
LOG_ROUTE_ARMS = {
    "fnn-advance-frontier": ("fnn-log-reserve", (("fn-lg-reserve-program", LOG_ROUTE_BOOK),)),
    "fnn-publish": ("fnn-log-publish", (("fn-lg-append-program", LOG_BOOK),
                                        ("fn-lg-fence-program", LOG_BOOK),
                                        ("fn-lg-order-program", LOG_ROUTE_BOOK))),
    "fnn-mark-committed": (None, ()),
    "fnn-recover": ("fnn-recover-log", (("fn-lg-open-program", LOG_ROUTE_BOOK),)),
}
# fnn-log-scan-segments (lane log-recovery): the multi-segment open reads the
# closed segments only (no step) and recovers the active one through
# fnn-log-recover; a rotation it completes is P-ROTATE's, not the open's.
LOG_ROUTE_EXPAND = ("fnn-log-commit-open-batch", "fnn-log-append", "fnn-log-fence",
                    "fnn-log-recover", "fnn-log-scan-segments")
_LOG_ROUTE_TOKEN = re.compile(
    r"\((fnn-log-pwrite|fnn-log-fdatasync|fnn-log-commit-open-batch|fnn-log-append|"
    r"fnn-log-fence|fnn-log-recover|fnn-log-scan-segments)[\s)]"
    r"|\(fnn-at store :([a-z0-9-]+)\)|\(fnn-log-at :([a-z0-9-]+)\)"
    r"|\(funcall barrier\)|RECOVER-BARRIER-")


def _strip_lisp_text(body: str) -> str:
    """BODY without comments and string literals (a docstring may name a call)."""
    out, i, n = [], 0, len(body)
    while i < n:
        c = body[i]
        if c == ";":
            j = body.find("\n", i)
            i = n if j < 0 else j
        elif c == '"':
            j = i + 1
            while j < n and body[j] != '"':
                j += 2 if body[j] == "\\" else 1
            if body[i:j].startswith('"RECOVER-BARRIER-'):
                out.append("RECOVER-BARRIER-")
            i = j + 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def _recovery_barrier_count(source: str) -> int:
    body = _strip_lisp_text(host_function(source, "fnn-store-recovery-barriers"))
    at = body.index("(list") + len("(list")
    depth, count = 0, 0
    for c in body[at:]:
        if c == "(":
            if depth == 0:
                count += 1
            depth += 1
        elif c == ")":
            if depth == 0:
                break
            depth -= 1
    return count


def log_route_host_steps(source: str, name: str) -> list:
    body = _strip_lisp_text(host_function(source, name))
    steps: list = []
    barrier = None
    for m in _LOG_ROUTE_TOKEN.finditer(body):
        call, cut_store, cut_log = m.group(1), m.group(2), m.group(3)
        text = m.group(0)
        if call in LOG_ROUTE_EXPAND:
            steps.extend(log_route_host_steps(source, call))
        elif call == "fnn-log-pwrite":
            steps.append(("write",))
        elif call == "fnn-log-fdatasync":
            steps.append(("fence",))
        elif text == "(funcall barrier)":
            barrier = len(steps)
            steps.append(("fence",))
        elif text == "RECOVER-BARRIER-":
            steps.append(("cut", "recover-barrier"))
            if barrier is not None:
                loop = steps[barrier:]
                steps.extend(loop * (_recovery_barrier_count(source) - 1))
                barrier = None
        else:
            cut = ("cut", cut_store or cut_log)
            if not (steps and steps[-1] == cut):
                steps.append(cut)
    return steps


def verify_log_route_arms(source: str | None = None) -> list:
    """Each format-9 arm's host steps equal its log programs' steps; returns
    the mismatches (empty when every arm matches).  SOURCE: io.lisp's text
    (a test's mutation), the file by default."""
    if source is None:
        source = (ROOT / "host/native/io.lisp").read_text()
    problems = []
    for host, (callee, programs) in LOG_ROUTE_ARMS.items():
        body = host_function(source, host)
        arm = re.search(r"\(when \(fnn-store-logp store\)\s*\(return-from {}\s*(\S*)".format(
            re.escape(host)), body)
        if not arm:
            problems.append("{}: no format-9 arm".format(host))
            continue
        called = arm.group(1).strip("()")
        if callee is None:
            if called not in ("nil", ""):
                problems.append("{}: the arm calls {}, expected nothing".format(host, called))
            continue
        if called != callee:
            problems.append("{}: the arm calls {}, expected {}".format(host, called, callee))
            continue
        model = []
        for program, book in programs:
            for step in model_steps(program, book):
                if step.kind == "write-at":
                    model.append(("write",))
                elif step.kind == "fence":
                    model.append(("fence",))
                elif step.kind == "cut":
                    model.append(("cut", step.args[0]))
        hosted = log_route_host_steps(source, callee)
        if hosted != model:
            problems.append("{} -> {}: host {} is not {} {}".format(
                host, callee, hosted, [p for p, _ in programs], model))
    return problems
