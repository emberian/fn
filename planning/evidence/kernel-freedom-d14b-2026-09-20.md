# D14-b: the recovery freedom, certification evidence (2026-09-20)

Lane `w10/kernel-freedom`, worktree `build/lanes/w10-kernel-freedom`, branch
from `dev` at `f730c24`, merged `dev` at `6fba627` and again at `e5e6218`.

## Tool versions and invocation

* ACL2 8.7 on SBCL, persvati, `$HOME/fn-tools/acl2-8.7/saved_acl2`, driven by
  `python3 tools/farm.py submit persvati --jobs 4 --remote-root
  /home/ember/fn-lanes/w10-kernel-freedom --affected-by books/store-files.lisp
  --closure`, then `wait`. `ACL2_BOOK_HASH_ALISTP=NIL` and
  `ACL2_CUSTOMIZATION=NONE` are set by the runner, so every certificate is
  content hashed.
* ACL2 8.7 from Homebrew on the laptop, one process at a time through
  `tools/acl2 --timeout 600`, for three `ld` probes of `books/store-files`
  and `books/store-files-invariants` while the shape was being settled. No
  laptop run is cited as certification evidence.

## Runs

| run | tree | scope | result |
| --- | --- | --- | --- |
| `run-20260920T211812Z-1f0a` | the FIRST shape: `fn-sf-crash-imagep` itself widened | `--affected-by books/store-files.lisp --closure`, 122 roots | **23 failed**, 272.2 s. One genuine proof failure, `fn-snt-admissible-crash-image-is-recoverable` (`books/store-node-traces.lisp:678`); the other 22 are includes of it. Kept as the measurement behind decision D14-b. |
| `run-20260920T213023Z-4804` | the shipped shape, before merging dev `e5e6218` | same, 122 roots | **7 failed**, 306.8 s, and **none of the seven is in the `fn-sf-crash-imagep` closure**: `books/peer-feed-invariants` fails at `fn-feed-apply-record-preserves-peer`, a book whose include closure is `peer-feed` -> `scheduler`, `frame`, `frame-invariants` and which has no path to `books/store-files` at all; `books/owner{,-config,-feed}` and `tests/acl2/owner-tests` are includes of it; `tests/acl2/checkpoint-codec-tests` fails an `assert-event` about `fn-cpc-validp` on a bad-generation record, also outside the closure. Both were already failing in the first run, under a different kernel. |
| `run-20260920T213846Z-bd4f` | the shipped shape, after merging dev `e5e6218`, which carries `w6/peering-feed-4`'s fix for `books/peer-feed-invariants` | same, 129 roots | **125 passed, 4 failed**, 286.9 s; evidence `build/acl2/certify-20260920T213853Z-3576178`. `books/owner-invariants` is open at `fn-own-advanced-session-is-bounded`, an auth/peer session theorem in a book this lane does not touch -- `git diff dev...HEAD -- books/owner-invariants.lisp books/owner.lisp books/owner-config.lisp` is empty -- and `books/owner-config` and `tests/acl2/owner-tests` are includes of it. `tests/acl2/checkpoint-codec-tests` is the same out-of-closure failure as above. Every store root passed, including `tests/acl2/store-observed-traces-tests`, which carries the kernel half of the counterexample. |
| `run-20260920T214551Z-90a4` | the FINAL tree | `--affected-by books/store-files.lisp --affected-by books/byte-store-scan.lisp --closure`, 129 roots | **125 passed, 4 failed**, 269.9 s; evidence `build/acl2/certify-20260920T214556Z-3646511`. The same four pre-existing failures as the run above, and every root of the `fn-sf-crash-imagep` closure passed. |

## What the runs establish, and what they do not

They establish that the books certify with the two recognizers in place, and
that `fn-sf-crash-imagep` being unchanged leaves every one of the eleven
theorems that take it, and their proofs, untouched.

They do not establish `specs/crash-model-v2.md` K2, which is open: K2 rests on
K1's three remaining clauses and on the frontier sub-case K2f, both recorded
in the handoff. No claim here is a claim about a platform.

## Diagnosis method for the two out-of-closure failures

Not by `git stash` and not by comparison with a remembered baseline: by
reading the failing books' `include-book` forms. `books/peer-feed-invariants`
includes `peer-feed` only, and `peer-feed` includes `scheduler`, `frame` and
`frame-invariants`; none of them reaches `books/store-files`, so no change to
the kernel can reach that theorem. `tests/acl2/checkpoint-codec-tests`
includes `books/checkpoint-codec` only. Both books enter the run because
`--affected-by ... --closure` selects over every Makefile root, not because
they depend on the change.
