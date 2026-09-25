# The laptop hard-crash of 2026-09-25 ~03:08 UTC — cause and the cap

## What happened

At about 03:08 UTC (23:08 local) the laptop stopped responding under the
wave of ten lanes and was force-powered-off (the reset diagnostic
`ResetCounter-2026-09-24-230936.diag` records `btn_rst, finger_reset
force_off`: a button reset, not a kernel panic). The jetsam report written
at 23:11 local is a post-boot snapshot (74 GB free, largest process iTerm2)
and does not name the process; the lanes' local load logs lived in the
session scratchpad under `/private/tmp` and did not survive the reboot. So
the record below is the mechanism, established from the launcher, the pool
and the transcripts, not a process snapshot.

## The mechanism

- Every ACL2 started on the laptop is the Homebrew `saved_acl2`, which
  launches SBCL with `--dynamic-space-size 32000` (32 GB) per process.
- The slot pool (`tools/acl2_slots.py`) allowed eight ACL2 processes, and a
  bare `acl2 < driver.lsp` takes no slot at all (its docstring has said so
  since 2026-09-19).
- The laptop has 96 GB and no swap. Three such processes at full heap
  exhaust it; nothing on macOS kills them before the machine hangs.
- At 02:42 UTC two lanes (bounds-p1, bounds-p4) started local REPL sessions
  through `tools/proof_repl.py`. From 02:43 the SHA-256 representation lane
  loaded `books/sha256-stobj.lisp` on the laptop through its own `ld.sh`
  (a bare `acl2`, 500 s timeout), reported the load "stuck in a
  long-running event" at 02:55, and then re-issued the whole load about
  every thirty seconds until 03:04 while editing the bit-vector guard
  lemmas (`logand` masks over `unsigned-byte-p 32`, the class of proof that
  builds enormous terms when the recognizer is opened). The last transcript
  entries of every lane are between 03:00 and 03:07 UTC.

## What changed

`tools/acl2_slots.py` now caps the heap of every ACL2 the tools start:
`heap_cap_user_args()` exports `SBCL_USER_ARGS=--dynamic-space-size 8000`
on darwin (the Homebrew launcher splices that variable after its own size,
and SBCL takes the last), `FN_ACL2_DYNAMIC_SPACE_MB` overrides, and the
farm boxes get nothing added because their launchers carry their own sizes
(persvati 8,192 MB; hbox's certify workers 4 GB, its images 32,000 MB under
cgroup caps). The pool's darwin default is six slots: six times 8,000 MB is
48 GB, half the machine. `tools/acl2`, `tools/certify_books.py` and the two
host checks that start ACL2 themselves apply the cap; the certification
manifest records the value. Verified: `tools/acl2 < probe` reports a
dynamic space of 8,000 MB where it reported 32,000 before.

A runaway proof now dies inside its own process with "heap exhausted" (the
launcher's `--disable-ldb` makes that an exit), and the slot and the
machine survive it.

## What remains a footgun

A bare `acl2 <` in a shell bypasses both the pool and the cap. The one-line
fix is `export SBCL_USER_ARGS="${SBCL_USER_ARGS:---dynamic-space-size 8000}"`
in the login environment (ember's `~/.zshenv` is a synced dotfile, so that
is ember's edit). Until then the rule for lanes is: laptop ACL2 only through
`tools/acl2` or `tools/proof_repl.py`; everything else on the farm.
