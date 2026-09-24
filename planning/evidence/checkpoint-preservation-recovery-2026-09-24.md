# Selected-pack preservation and retirement, 2026-09-24

The ACL2 retirement plan permits deletion only of pack generations strictly
older than the selected generation.  `fn-cprt-selected-survives-retirement-cut`
assumes the selected generation is present and issued unlinks are a prefix of
that plan; it preserves selected authority under arbitrary survival of issued
unlinks.  `fn-cprt-next-after-retirement-is-above-selected` assumes a valid
increasing namespace, selected membership, and remaining generation capacity;
it prevents reuse of a retired name.  The test book has a three-generation
crash witness and explicit counterexamples to each keystone premise.

The native `checkpoint pack-retire ROOT` caller first reopens and validates
selected authority under an exclusive Store lock.  It invokes the ACL2 plan,
unlinks each issued older name, and barriers the packs directory.  A process
death after each unlink or after the barrier reopens under the surviving
selected pack; retirement can be retried.  The updated recovery-only auxiliary
diagnostic compares the exact-history replay with historical verdicts,
keyring snapshots, dense sequence, E2 consumer projection, topic projection,
and the rebuilt consumer event index.  It does not install this diagnostic
projection as the served Store state.

Scoped certification ran on `persvati` with ACL2 8.7, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
via `python3 tools/farm.py --jobs 2 submit persvati books/checkpoint-pack-retire
tests/acl2/checkpoint-pack-retire-tests books/checkpoint-auxiliary
tests/acl2/checkpoint-auxiliary-tests`.  The final source-matched closure
manifest is `planning/evidence/manifests/certify-20260924T055055Z-857709.json`:
all four roots were installed at their exact current bytes from prior passing
scoped runs, with 93/93 dependencies installed.  The substantive fresh runs
were `certify-20260924T054434Z-796217.json` for the retirement book/test,
`certify-20260924T054805Z-830303.json` for the strengthened retirement test,
and `certify-20260924T054113Z-763692.json` for the auxiliary book/test (those
two passed; an earlier retirement draft failed in that same manifest and was
fixed).  Source SHA-256 values in the final manifest are:

| Source | SHA-256 |
| --- | --- |
| `books/checkpoint-pack-retire.lisp` | `9ec4ea094233ca591adbfdc7de1527b5387e598c22d24da458ec6717a9c31f14` |
| `tests/acl2/checkpoint-pack-retire-tests.lisp` | `1c7ed7453dfd61e9250e2d7eb660507e32f1a89e7eb40923476fd7ba7126f995` |
| `books/checkpoint-auxiliary.lisp` | `7d2ef24d58e90be94a275ac8703bef95c9fcd3ee9d1680fd031ecf2aa1ab1e58` |
| `tests/acl2/checkpoint-auxiliary-tests.lisp` | `15ada01453d2587ac8b77c1a1be1e22caf07b578f73bd4b9d926e76d052efbcb` |

`make check` and Python syntax compilation passed in the isolated lane.
The native SIGKILL/reopen, active-reader, and exact-source assertions are
source-present in `tests/test_native_checkpoint.py`; they require a new
source-matched saved image.  Certification does not prove host syscall
behavior or power-loss ordering.  Retirement recovers duplicate-pack space
only.  Exact retained events and protected article objects are not pruned;
the 4096-generation namespace and 4096-event/4-MiB pack bound remain finite.

## Native cut audit and bounded capacity follow-up

The native sequence in `fnn-pack-retire-older-generations` matches the model
as follows: opening/validating selected authority and computing a plan make no
pack deletion; an empty plan returns without a barrier; each `fnn-unlink`
attempt maps to one `:unlink :packs` transition (including a possibly applied
attempt that returned an ambiguous OS error); the matching `pack-retire-unlink`
hook is after each successful call; `fnn-fsync-dir` maps to `:fsync-dir :packs`
and `pack-retire-directory` follows its success.  A failed unlink or barrier
fences mutation and requires reopen.  The model now returns an empty program
for the no-op plan, matching the actual native early return.  The native test
will kill after both first and second unlinks, and after the directory barrier;
its no-op case arms the directory stop hook and requires normal completion.

The new `fn-cprt-retirement-never-increases-namespace-count` and
`fn-cprt-issued-unretained-name-frees-one-slot` theorems state the bounded
resource effect: a surviving deletion lowers the number of pack generation
names, while an interrupted deletion that reappears does not.  This does not
grant permission to delete retained Store events or article objects, and does
not make the finite generation number wrap.  The additional source-matched
scoped manifests are `certify-20260924T055821Z-924910.json` for the changed
book and its previous test bytes and `certify-20260924T055927Z-936158.json`
for the final ACL2 test bytes; both passed on the same toolchain.  Native
execution is part of the combined image qualification handoff, not these
manifests.
