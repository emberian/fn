# K0 corollaries (T16 model side), 2026-09-25

Lane `k0-corollaries`, branch `lane/k0-corollaries` from dev `9458fcd4`
(merged dev after the keystone rename to `fn-bs-step-preserves-k0-coverage`).

## What changed

1. **Coverage hypothesis dropped.** `fn-bs-step-preserves-k0-coverage`
   (`books/byte-store-k0-step.lisp`) now has one hypothesis,
   `(fn-bs-k0-step-inputp bs ks step outcome)`. Every kind's precondition
   carries the relation, or for the root barrier the marker-pending
   coverage, so the old `(fn-bs-k0-coveredp bs ks)` was implied.
2. **The record program's two `:ok` observations are step kinds.**
   `fn-sf-record-file-result-ok-preserves-store-relation` and
   `fn-sf-record-link-result-ok-preserves-store-relation` (same book): from
   any related byte state, `(:record-file :ok)` and `(:record-link :ok)`
   keep the relation. They need no byte-state premise. `:record-staged` and
   `:record-data-durable` admit the same crash images, and so do
   `:record-data-durable` and `:record-attempted`, and neither transition
   changes whether a pending link is allowed. `fn-bs-k0-observation-inputp`
   now admits both, so every step of `fn-bs-record-program` is a step kind of
   the keystone.
3. **Per-cut theorems as corollaries**
   (`books/byte-store-k0-step-bridge-marker.lisp` for the marker program and the generic lemmas, `books/byte-store-k0-step-bridge.lisp` for frontier and record; both new). Each `-by-step` theorem
   restates a per-cut theorem and proves it the same way. It discharges
   `fn-bs-k0-step-inputp` at the pair before the cut's step and
   instantiates the keystone there, using the generic lemma
   `fn-bs-k0b-cut-after-step`. A covered pair with no committed-history
   rename pending is then related
   (`fn-bs-k0b-covered-without-root-marker-is-related`). The per-cut
   theorems stay where they are, and the registry still cites them.

   | per-cut theorem | corollary | predecessor relation from |
   | --- | --- | --- |
   | `fn-bs-k0-marker-cuts-relation` (pairs 1, 3, 5, 9 and the dropped resolution at 7) | `fn-bs-k0-marker-cuts-relation-by-step` | the entry pair alone: `fn-bs-k0b-marker-pairs-by-step` chains the keystone through all five marker steps |
   | `fn-bs-k0-marker-replaced-cut-relation` | `fn-bs-k0-marker-replaced-cut-relation-by-step` | the same chain; crash images from `fn-bs-k0-covered-crash-image-is-a-related-image` |
   | `fn-bs-k0-frontier-replaced-cut-relation` | `fn-bs-k0-frontier-replaced-cut-relation-by-step` | `fn-bs-k0-frontier-staged-durable-cut-relation` |
   | `fn-bs-k0-frontier-attempted-cut-relation` | `fn-bs-k0-frontier-attempted-cut-relation-by-step` | the replaced corollary |
   | `fn-bs-k0-frontier-reserved-cut-relation` | `fn-bs-k0-frontier-reserved-cut-relation-by-step` | `fn-bs-k0-frontier-durable-cut-relation` |
   | `fn-bs-k0-record-attempted-cut-establishes-relation` | `fn-bs-k0-record-attempted-cut-relation-by-step` | `fn-bs-k0-record-linked-cut-relation` (uses item 2's link observation) |
   | `fn-bs-k0-record-durable-cut-relation` | `fn-bs-k0-record-durable-cut-relation-by-step` | the attempted corollary |
   | `fn-bs-k0-record-completing-cut-relation` | `fn-bs-k0-record-completing-cut-relation-by-step` | the durable corollary |
   | `fn-bs-k0-record-cleanup-cut-relation` | `fn-bs-k0-record-cleanup-cut-relation-by-step` | the completing corollary, then its own pair 16 |

   Each non-marker corollary still takes shape facts about its program pair
   (lookups, the kernel phase, pending entries, whether the pair is
   reachable) from the existing per-program lemmas. Only the step's effect
   on the relation comes from the keystone.
4. **Marker error arms, universally.**
   `fn-bs-step-at-marker-pairs-preserves-k0-coverage` assumes a related
   state in the completion window (`fn-bs-finish-inputp`), a string stage
   absent from `:staging`, typed non-empty octets, and a file-barrier
   outcome that is `:ok` or a well-formed crash selection of the stage's
   writes (`fn-bs-k0b-marker-fsync-outcomep`). At each of the five marker
   steps (create, write-all, fsync-file, rename onto
   `committed-history.json`, fsync-dir `:root`), taken at its program pair,
   and for every outcome, the result is covered. Its kernel is the entry
   kernel, which is still `:completing`. So no `:emit-success` has been
   observed, and the transaction stays fenced. The run stops at the first
   error (`fn-bs-run-stops-at-first-error-by-definition`), so no finish
   step follows. This replaces the example-only evidence of
   `k0-general-step-2026-09-25.md`.

## Teeth (`tests/acl2/byte-store-k0-step-bridge-tests.lisp`)

- Record `:ok` observations: reachable witnesses at the K5 fixture's record
  run, at file-barrier pair 4 (`:record-staged` to `:record-data-durable`)
  and linked pair 8 (`:record-data-durable` to `:record-attempted`, with a
  link pending). Each witness checks the lemma and `bsks-ok` for the
  observe step. The one hypothesis, the relation, has a `must-fail`: the
  initial byte image under the same kernel.
- Marker theorem: the witness is the K5 completing pair and the marker run
  from it. It checks the hypotheses for `:ok` and `(:eio)`, and the
  conclusion for `:ok`, `(:eio)`, a short write `(:eio . 3)`, and issued
  and unissued failed renames. There is one `must-fail` for each of these
  hypotheses: the relation (initial image), the completion window (the
  related record-attempted pair 10), the string stage (`7`), the absent
  stage (the marker run's own created pair 1), and typed octets (`(300)`).
  Two hypotheses have no `must-fail`. `(consp octets)` is used only by the
  run-shape lemma. `fn-bs-k0b-marker-fsync-outcomep` is the keystone's
  environment premise for the file barrier. The staged marker file is not
  an authority inode, so a torn selection of its writes plausibly stays
  covered, and neither hypothesis is shown to be needed for this
  conclusion.

## Not derived, and what each would take

- `fn-bs-k0-frontier-durable-cut-relation`: the root barrier over a pending
  frontier rename (`:fsync-dir :root` in `:frontier-attempted`) is not a
  step-input kind. Covering it needs a stand-alone lemma for that fence
  from any related state, like `fn-bs-k8-pending-link-fence-preserves-relation`
  for transactions, and its `:ok` arm in `fn-bs-k0-step-inputp`.
- `fn-bs-k0-frontier-created-and-written-cut-relation`,
  `-frontier-staged-durable-`, `-record-created-and-written-`,
  `-record-staged-durable-`: each needs its program's run prefix as
  explicit states, as `fn-bs-marker-run-shape` gives for the marker (the
  record prefix is exactly `fn-bs-marker-b1..b3` with the frame). Each also
  needs a stage-level version of `fn-bs-k0b-marker-pairs-by-step`, whose
  hypotheses are the relation, a quiet root and transactions directory,
  and no recovery window, in place of `fn-bs-finish-inputp`.
- `fn-bs-k0-record-linked-cut-relation`: the link's inputs at pair 6 must
  be discharged. Those inputs are the next transaction name as the
  candidate's sequence, the fenced and allocated source, the durable record
  of the staged frame as the candidate, and the destination absent.
  `fn-bs-k6-file-cut-source-is-fenced-frame` and
  `fn-bs-k0-file-cut-has-new-inode` give the first-order facts; the name
  and absence facts are not exported.

## Step kinds still uncovered by the keystone

- `:mkdir` and `:link-eexist`. These are initialization only, and
  `fn-bs-init-program-establishes-relation` covers the init program as a
  whole. Covering them needs a relation-shaped invariant for the
  pre-initialization store, which the relation does not describe (no
  config entry).
- The error outcomes of the `:staging` and `:transactions` barriers.
  `:staging` needs a lemma that a crash selection of staging-only entry
  operations keeps the relation; staging is not authority, so this is the
  staging-extension argument of `byte-store-k0-staging`. `:transactions`
  is the K7 pair-11 EIO run (`:apply` and `:drop`); lifting it to an
  arbitrary related state is the missing lemma.
- The root barrier over a pending frontier rename (above).
- Every step in the recovery window (`fn-bs-replay-visiblep`). Covering it
  needs the replay-scan arm of the relation (`fn-bs-replay-matches-scan`)
  preserved per step, which is the P-RECOVER cut work named open in
  `byte-store-k0.lisp`.

## Certification

ACL2 8.7 w25 `acl2-literal`, on persvati, 2 jobs, 300 s timeout, no `--closure`.

- `run-20260925T051603Z-e055`, manifest
  [certify-20260925T051619Z-858822](manifests/certify-20260925T051619Z-858822.json),
  source `2486918c`. Certified: `books/byte-store-k0-step` in 7.4 s,
  `tests/acl2/byte-store-k0-step-tests` in 6.5 s, and the combined bridge
  in 10.9 s, which was over the 10 s limit, so it was split. The same
  run recertified the dependencies at the merged dev bytes: `byte-store-k0`
  14.7 s, `-k0-staging` 12.6 s, `-k0-marker` 11.4 s, `-k0-step-lemmas`
  11.1 s. These timings are under this run's load; the previous lane
  measured the lemmas book at 8.2 s. `tests/acl2/byte-store-k0-step-bridge-tests`
  failed: a guard violation in a witness that passed a short write as an
  outcome to the file barrier. Those witnesses were dropped.
- `run-20260925T051908Z-51f1`, manifest
  [certify-20260925T051927Z-895517](manifests/certify-20260925T051927Z-895517.json),
  source `2b3f29f8`, passed: `books/byte-store-k0-step-bridge-marker` 6.3 s,
  `books/byte-store-k0-step-bridge` 8.8 s, and
  `tests/acl2/byte-store-k0-step-bridge-tests` 5.2 s.
- Proof development used a persvati `proof_repl` session over
  `books/byte-store-k0-marker`, with the step books loaded from source.
- The ledger (`planning/ledger.*`) was not regenerated.
