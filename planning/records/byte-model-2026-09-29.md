# byte-model: durable acceptance at every crash point (2026-09-29)

Lane byte-model (Fable 5.1), row Q3b of `build/coordinator/COMPLETE-BEFORE-6.6.0.md`
(K0 and log byte-model remainder: PKT-043/050/086/215/216/682/747/832) and the
resource contract's D4 row (`docs/resource-contract.md`). Branch `lane/byte-model`.

## 0. The result

- PRF-936, `books/store-log-durable.lisp` (prefix `fn-lgu-`): KEYSTONE
  `fn-lgu-acknowledged-article-is-recoverable-at-every-crash-point`. An
  article the node acknowledged as accepted (a member of the aligned owner
  layer's `acked` list, `fn-owb-alignedp`) is held by the kernel recovered
  (`fn-lgk-recover`) from the durable content of every admissible crash image
  (`fn-bs-crash-imagep`) of every crash point `fn-lgu-crash-point-p` names:
  every cut state of `fn-lg-append-program`, of `fn-lg-fence-program` with the
  barrier `:ok` or failed after landing an admissible selection, and of
  `fn-lg-extend-program`, run from a related state (R). Its recovery half,
  `fn-lgu-acknowledged-article-is-recoverable-at-every-cut-of-recovery`, covers
  every cut of `fn-lg-recover-program` from the recovered layer.
- No trailer assumption. `fn-lgu-committed-record-is-read-from-every-crash-image`
  composes the shift lemma (`fn-bs-crash-of-aligned-append`: the tear keeps the
  prefix below the frontier) with `fn-lg-scan-of-complete-append` (the scan reads
  a complete prefix's entries before whatever the tear left). A-CRYPTO-TRAILER
  decides only what the scan reads after the committed records (T2, PRF-244).
- The subject is the host's functions: `tools/native_program_check.py` now lists
  the four log programs with their cuts (`tests/campaign/native_cuts.py`
  `log_program_cut_map`), checked step by step against `host/native/io.lisp`:

      fn-lg-append-program <- fnn-log-append: 1 cut: log-written
      fn-lg-fence-program <- fnn-log-fence: 1 cut: log-fenced
      fn-lg-recover-program <- fnn-log-recover: 2 cuts: log-truncated, log-recovered
      fn-lg-extend-program <- fnn-log-ensure-extent: 2 cuts: log-extended, log-extent-fenced
      log programs: PASS (4 programs, 6 cuts)

  Teeth: `tests/test_native_program_check.py LogProgramListingTests` (a cut
  removed, an extension fenced before its write: FAIL).

## 1. The six theorems the row names

| the row's item | theorem | book | status |
| --- | --- | --- | --- |
| T7, a failed barrier recovers to a prefix | `fn-owb-uncertain-batch-recovers-to-a-prefix` | owner-batch | on dev (PRF-253's book); cited |
| the log shift lemma | `fn-bs-crash-of-aligned-append` | store-log-crash | on dev (PRF-244); cited, and the composition's first half |
| the P-BATCH step for the segment extension | `fn-lg-extend-program-keeps-the-relation` (cuts `log-extended`, `log-extent-fenced`) | store-log-extend | on dev (PRF-268, lane log-2); cited; the keystone covers its cuts |
| the administrative publication's byte program | none | host/native/admin.lisp `fnn-admin-publish` through `fnn-immutable-publish-effect` into the config directory | NOT DELIVERED (section 4) |
| the whole-file range read over the host loop | `fn-bs-read-ranges-read-the-whole-file`, `fn-bs-read-ranges-is-the-range` | byte-store-range-read | NEW: `fnn-state-checkpoint-plan`'s consecutive reads on one descriptor (`fn-bs-exclusive-chainp` under A-HOST-EXCLUSIVE-READ, a state per read `fn-bs-states-cover-p`) are one range of the first state's content; from offset 0 to the file's length, the content. Model-only (the loop is the host's): `planning/reach-baseline.json` |
| covered files ruled out by proof | `fn-lgs-open-plan-scan-ignores-covered` (+ `fn-lgw-segment-drop-preserves-the-open`) | store-log-segments, store-log-stream | on dev (PRF-270); the host's open takes the plan from ACL2's `fn-lgs-open-plan` (`fnn-log-covered-indices`); no host check of covered segments remains |

## 2. The keystone's shape and hypotheses

- Per cut theorem (`fn-lgu-committed-record-survives-every-cut-of-the-append`,
  `-the-fence`, `-a-failed-fence`, `-the-extension`,
  `fn-lgu-record-read-at-open-survives-every-cut-of-recovery`): from R and a
  record in the kernel's committed list, for every pair of the program's run
  (`fn-lg-run` / `fn-lg-extend-run` record the state after every step, the
  `:cut` steps included) and every crash image of its store, the record is read
  by the scan of the image's content. The append's and the fence's cuts keep R
  (`fn-lg-append-program-keeps-the-relation`, `fn-lg-fence-program-keeps-the-
  relation`); the failed fence leaves the crash image of the environment's
  selection with nothing of the segment pending; the extension's written state
  is the shift lemma's shape (the whole content as the prefix) and its fenced
  state is related (`fn-lg-extension-keeps-the-relation`); recovery's zeroing
  write lies at the frontier (T3) and its fence establishes R
  (`fn-lgk-recover-establishes-relation`).
- The extension arm requires `(natp next)`, a unit-aligned `next` past the
  content; the host's target satisfies it (`fn-olr-extension-target-is-an-extent`).
- The failed-fence arm requires the environment's selection admissible
  (`fn-bs-crash-choicesp`) and an errno that is not `:ok`.
- The recovery half carries the recovery program's own hypotheses: the segment's
  content unit-aligned, a digest genesis, no pending write of the segment and
  the owner's sole-pending-writer obligation (`fn-assume-log-sole-pending-writer`,
  an fn obligation, not a platform assumption).
- `fn-lgu-recovered-kernel-is-the-recover-by-definition`: the host's open kernel
  (`fn-lg-recovered-kernel`, `fn-lgt-recover`) is `fn-lgk-recover` with the txid
  floor's next txid, so the recovery half speaks of the kernel the host holds.

## 3. Teeth

`tests/acl2/store-log-durable-tests.lisp`: a two-record log with a torn unit
and zeros, recovered (`fn-owb-recover`: both records acknowledged anonymous
members), the store fenced at `log-recovered`; a third record prepared and
appended. Reachable witnesses at every cut: recovery's `log-truncated` with the
zeroing write landed whole / not at all / first unit / a hole and
`log-recovered`; the append's `log-written` whole / none / first unit / a hole;
`log-fenced`; the failed barrier under three selections; the extension's
`log-extended` whole / none / torn and `log-extent-fenced`. T7 on the ground:
the failed barrier's kernel is `:fault`, the open holds the batch when its
write landed and nothing of it when nothing landed. Hypothesis removal, one
witness each, retained hypotheses asserted: the acknowledgement (the batch
member at `log-written` with nothing landed is not held), R (CORRUPTED STATE:
a kernel claiming a record the bytes lack), the cut (MUTATION: a wiped store
is no crash point), the image's admissibility (a wiped image differs from the
sample images and holds nothing), and the recovery half's membership.

## 4. Not done, and the packets

- The administrative publication's byte program (PKT-216's live half): the
  config directory's publication (`fnn-admin-publish` -> `fnn-immutable-publish-effect`:
  stage O_EXCL + write, fsync + close, link, fsync-dir, then the stage unlinked
  and the staging directory fenced) has no model program and no cut. The
  successor's shape: a program of `fn-bs-checkpoint-publish-program`'s form into
  `:config` with cuts `config:candidate-durable / -linked / -published /
  -stage-unlinked`, an old-or-new theorem over the config directory at every
  cut (the entry absent, or present with the record's durable content), and a
  source-order check of `fnn-immutable-publish-effect`'s arms plus
  `fnn-admin-publish`'s call in `native_cuts.py`, listed by `native_program_check`.
- PKT-086 and PKT-215's remaining items (the frontier publication's pairs, barrier
  errors with an authority entry pending, the marker file's limits, K0 at the
  catch-up cuts) belonged to the per-file layout, deleted with the per-file host
  code (PRF-041's note, PKT-838); under the log the marker is M := D (design
  2026-09-27 section 3.4) and there is no catch-up program. Closed by deletion.
- PKT-682 / PKT-747: the shift lemma, the batch induction and the trailer
  corollary are on dev (PRF-244); the host ties by `native_program_check` are
  this record's listing. PKT-832: on dev (PRF-268), cited. PKT-043: this record.
  PKT-050: PRF-270, cited.
- D4 says what it bounds (the log) and names what it does not (the checkpoint's
  transient, the indexes, the service log, the Message-ID history).

## 5. What ran

- proof_repl on persvati: `books/store-log-durable` (62 forms, all admitted; the
  keystone 800 prover steps; the costliest local lemma 135 k steps),
  `books/byte-store-range-read` (the chain), `tests/acl2/store-log-durable-tests`
  with the keystone loaded from source.
- `python3 tools/native_program_check.py` (4 programs, 6 cuts: PASS);
  `python3 -m unittest tests.test_native_program_check tests.test_native_cut_map`
  (23 tests).
- `python3 tools/resource_contract.py --write` and `--check`.
- Certification: farm run-20260929T031004Z-7de9 on persvati (toolchain fcedce7e, 8 jobs): books/store-log-durable, books/byte-store-range-read, tests/acl2/store-log-durable-tests and owner-batch's re-cite, 4 passed, 0 failed; manifest `planning/evidence/manifests/certify-20260929T031304Z-2122246.json`.

## 6. Measure at convergence

Nothing here is a performance change. The book's admission cost is under a
second of ACL2 time in the REPL; the batch's steps ratchet judges it.
