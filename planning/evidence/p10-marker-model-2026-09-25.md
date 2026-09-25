# P10: the committed-history marker in the byte crash model (2026-09-25)

Lane `p10-marker-model`, branch `lane/p10-marker-model` from dev `db8e3d86`.
It answers F1 of [qual-c3420013](qual-c3420013-2026-09-25.md): the ACL2
differential failed at `finish-consumed` and `finish-durable` (23/25, served
16/18) because the store root holds `committed-history.json` and the byte
model's programs wrote no such file. It also closes finding 1 of
[m5-history-lifetimes](m5-history-lifetimes-2026-09-24.md): the marker's
crash table was rename atomicity transcribed, not a program of the model.

## The program

- `fn-bs-marker-program STAGE OCTETS` (`books/byte-store-marker-program.lisp`)
  is `fnn-mark-committed`'s steps in the host's order: create a `.stage-`
  name in `:staging`, write, fsync the file, rename onto
  `committed-history.json` in `:root`, fsync the root. A `:cut` follows each
  step: `marker-created`, `-written`, `-staged-durable`, `-replaced`,
  `-durable`. The book asserts D1 to D3 on a ground instance, that the cut
  names are `fn-hm-marker-cut-names`, and that the step kinds are
  `*fn-hm-marker-program*`'s.
- The program runs between `fn-bs-record-program` and
  `fn-bs-finish-program`. `fn-bs-finish-program` is unchanged (no syscall);
  the composition is the coordinate order `POST_PROGRAMS` in
  `tests/campaign/native_cuts.py` (frontier, record, marker, finish), and
  `verify_marker_cut_map` checks that `fnn-command-post`, `fnn-command-probe`
  and `fnn-owner-publish-prepared` call `fnn-publish`, `fnn-mark-committed`
  and `fnn-finish` in that source order, and that `fnn-mark-committed`'s
  sites are in the program's order.
- The cut table is 30: `POST_CUTS` gains the five marker cuts (candidate
  `present`: the record is durable at each), so 23 post cuts and 7 recovery
  cuts. The host declares them in `+fnn-post-model-cuts+`.
- `tools/native_program_check.py` maps `fn-bs-marker-program` to
  `fnn-mark-committed` and reads each cut's book: PASS, 0 mismatches over 6
  programs, the marker program 10 of 10 steps matched.
- `native_cuts.marker_fate` derives what the root marker must be at each
  cut from the coordinate: old for the frontier and record cuts and the
  first three marker cuts, either at `marker-replaced`, new at
  `marker-durable` and the finish cuts. The NNTP probe's arm derivation
  gives the marker cuts `uncertain` (a program after the record's end: an
  error there is never a refusal).

## Theorems

`books/byte-store-marker-program.lisp` (the subject is the program the host
performs, tied by `native_program_check`; the verdict's subject
`fn-hm-open-verdict` is what `fnn-check-history-marker` calls):
- `fn-bs-marker-run-shape`: from any byte state with a free stage name and
  no pending root entry operation, the run is the five states B1 to B5 (each
  cut repeats its step's state).
- `fn-bs-marker-program-crash-is-old-or-new`: under `fn-bs-marker-inputp`
  (quiet root; the old marker absent, or an allocated fenced inode) and
  `fn-bs-statep`, every crash image of every pair of the run observes the
  marker as the pre-run observation or `(:present OCTETS)`. Never torn,
  never empty.
- `fn-bs-marker-crash-is-the-history-table`: at pair K the observation is
  exactly `fn-hm-crash-image` of the pair's cut: old before the rename, the
  image's choice at the rename, new after the barrier. The table of
  `books/store-history-marker.lisp` is now derived from the byte model.
- `fn-bs-marker-crash-is-a-history-step`: with the host's frame
  `(fn-hm-after-commit SEQUENCE)`, `(cons (1+ SEQUENCE) obs)` is
  `fn-hm-step (:commit CUT CHOICE)` of `(cons SEQUENCE old)`.
- `fn-bs-marker-crash-open-stays-admitted`: if the open admitted
  `(SEQUENCE . old)`, the crash image at any cut, followed by any history
  of burns, uncertain publications and commits within uint32, is admitted
  (by `fn-hm-step-preserves-admitted` and
  `fn-hm-run-keeps-every-open-admitted`).

`books/byte-store-k0-marker.lisp`, K0 at the marker cuts:
- `fn-bs-k0-marker-cuts-relation`: from `fn-bs-store-relation bs ks` in the
  completion window (`fn-bs-finish-inputp ks sequence txid`), a free string
  stage and a non-empty octet list, the run has 10 pairs; the pairs at
  `marker-created`, `-written`, `-staged-durable` and `-durable` are related;
  at `marker-replaced` the pair with the rename's root entry dropped is
  related, and landing it (`fsync-dir :root`) is the `marker-durable` state.
- The two lemmas that carry it: `fn-bs-k0m-with-content-preserves-relation`
  (the content of an inode outside the authority list does not matter) and
  `fn-bs-k0m-with-root-entry-preserves-relation` (a root entry under a name
  that is neither `config.json` nor the frontier does not matter).

Registry: `planning/proof-events.json` and the `events` of
`planning/proofs.json` gain `fn-bs-k0-marker-cuts-relation` and
`fn-bs-marker-program-crash-is-old-or-new` (PRF-041) and
`fn-bs-marker-crash-is-the-history-table` and
`fn-bs-marker-crash-open-stays-admitted` (PRF-076). `planning/ledger.*` is
not regenerated here.

## Teeth (`tests/acl2/byte-store-k0-marker-tests.lisp`)

- Witness: the K5 fixture's second publication at its completing pair (two
  retained records, kernel `:completing` 1 1), the marker program with the
  host's frame for sequence 1. Every hypothesis holds, the K0 conclusion
  holds, the marker is `(:absent)` through `-staged-durable`, absent or new
  at `-replaced` depending on the choice, new at `-durable`; the open admits
  count 2 and refuses count 1 by name.
- A second run from that durable state replaces a present marker (2 to 3):
  old at every cut before the rename, old or new at it, new after; admitted
  at count 3 under both choices and after a burn and a lost uncertain
  publication.
- `must-fail` per hypothesis of `fn-bs-k0-marker-cuts-relation`: the
  relation (initial image under the completing kernel), the stage type, the
  free stage (occupied name), the octet type (`(256)`).
- `must-fail` for the marker theorems: an unfenced old marker is torn
  before the rename; a busy root (another pending marker entry) lands a
  third value; a marker ahead of the history (sequence 0 over count 2) is
  refused after the commit.
- Two premises have no separating instance, and the book says so as tests
  rather than teeth (finding 2): `(consp octets)` (an empty write keeps
  every cut related; the host never writes one, and faults before any write
  when `fn-hm-after-commit` has no frame) and the completion window (the
  frontier program's replaced pair also satisfies the conclusion).

## Certification

- persvati, `run-20260925T014815Z-1582`, manifest
  [certify-20260925T014831Z-3074187](manifests/certify-20260925T014831Z-3074187.json),
  passed, ACL2 8.7 w25 `acl2-literal`, 2 jobs, 300 s, source `3db98cf6`,
  roots and `--affected-by` of both new books (the three roots; nothing else
  includes them): `books/byte-store-marker-program` 3.0 s,
  `books/byte-store-k0-marker` 5.6 s, `tests/acl2/byte-store-k0-marker-tests`
  4.0 s. The three are Makefile roots.
- hbox, w28 `acl2-literal-4g`, for the image and the differentials' bridge:
  `run-20260925T014933Z-0605`, manifest
  [certify-20260925T014952Z-2358477](manifests/certify-20260925T014952Z-2358477.json),
  the default image roots (126 certified, 176 installed, 302 books), and
  `run-20260925T015252Z-aa65`, manifest
  [certify-20260925T015258Z-2362663](manifests/certify-20260925T015258Z-2362663.json),
  the bridge books with `books/byte-store-marker-program` (5 certified).
  Both passed. `proof_artifacts.py acquire/validate --profile default`
  loaded (artifact set `66fc172b…`).

## Native (hbox, `/tank/fn/scratch/p10-marker/`)

Developer image of `3db98cf6` built in the gate tree
`/tank/fn/scratch/p10-marker/gate-3db98cf6` with
`FN_NATIVE_PROFILE=developer … swarm-build sh tools/build_native_host.sh`:
launcher `460eb6a1…`, core
`3f71ee5722ca6424ee4c4b46c2f850d2ee6d2c1f5eaff120144f83603109e4ad`. The
only host change from c3420013's source is the `+fnn-post-model-cuts+`
list. Runner: `native.sh` (in the scratch directory), 01:54:59Z to 02:00:43Z.

| run | result | log (SHA-256) |
| --- | --- | --- |
| `tests.test_native_crash_model` | **7/7**, all 23 post cut subtests including `finish-consumed`, `finish-durable` and the five marker cuts (82.9 s) | [crash-model.log](p10-marker-model/crash-model.log) `8ed99eda…` |
| `tests.test_native_served_crash_model` | **3/3**, 23 served post cut subtests (18 + 5) and the five recovery barriers (142.8 s) | [served-crash-model.log](p10-marker-model/served-crash-model.log) `bfe9230e…` |
| `tests.test_native_history_marker` | **6/6** | [history-marker.log](p10-marker-model/history-marker.log) `d580c795…` |
| `tests.campaign.native_operator_campaign --no-faults --only` (all 30 cuts) | **60/60** observations pass, both entries at every cut | [campaign.log](p10-marker-model/campaign.log) `9e123a90…`, [judged.txt](p10-marker-model/judged.txt) `2641f03a…`, [campaign.json.gz](p10-marker-model/campaign.json.gz) (json `01d8eadf…`) |

- The differential now derives the marker frame from the committed count
  (`fn-hm-after-commit` of the number of records before the post), checks
  the root marker is the one `marker_fate` names and a staged marker is the
  intended frame, and runs `fn-bs-marker-program` between the record and
  the finish before comparing the byte image.
- Campaign marker rows: the store entry dies at −9 and the served owner at
  −9 (client 3); recovery 0; the candidate present and identical, the prior
  identical; resubmission rc 0 (`duplicate` through the store entry). The
  judge is the scratch `judge.py` (recover 0, prior identical, candidate
  fate by the table, candidate identical when present). The campaign ran
  without `run_faults` (no production image was built).

## Findings

1. At `marker-replaced` K0 is stated on the two resolutions of the pending
   rename. That every crash image of that pair is a crash image of one of
   them (a commutation of the root entry with the rest of the pending list)
   is not proved. The marker in every such image is proved old or new, and
   the byte image's scan does not read the marker name.
2. `(consp octets)` and `fn-bs-finish-inputp` are proof premises without a
   separating instance for the relation conclusion; the test book shows
   both as tests. The general per-step K0 (`fn-bs-program-step-preserves-relation`,
   P10's `next`) would remove the second.
3. `tests.test_native_nntp_post_probe` fails 3 of 11 on dev as on this
   branch (the D25 duplicate wording; qual-c3420013 F2 class), unchanged.
4. The probe (`native_nntp_post_probe`) now covers the five marker cuts
   through its derivation (`uncertain`), but was not run here.

## Finding 1 closed (lane k0-marker-replaced)

`books/byte-store-k0-marker.lisp`:
- `fn-bs-k0m-crash-of-pending-marker-rename`: if every pending root entry
  operation of a byte state is `(:set-entry :root "committed-history.json"
  INO)` and its directory table holds `:root`, then the crash under CHOICES
  is the crash, under `fn-bs-k0m-drop-marker-choices` (the same choices with
  the rename's own removed), of the state with that entry dropped from the
  pending list when the rename's choice is not `:apply`, and of that state
  with the entry durable when it is.
- `fn-bs-k0m-marker-rename-crash-is-a-resolution-crash`: the same over
  `fn-bs-crash-imagep`.
- `fn-bs-k0-marker-replaced-cut-relation`: under the hypotheses of
  `fn-bs-k0-marker-cuts-relation`, at pair 7 of the marker program the
  rename-dropped state and the root barrier's state are both related to the
  pair's kernel, and every crash image of the pair's byte state is a crash
  image of one of them.

Teeth (`tests/acl2/byte-store-k0-marker-tests.lisp`): the second marker run's
replaced pair, two images (every operation lands; every one but the rename's
root entry), each equal to its resolution's crash, observing new and old
marker; `must-fail` for each hypothesis of the commutation (a second
pending marker entry lands a third marker; a table without `:root` orders
the created root after another directory). Finding 2's two premises stay
tests.

Certification: persvati `run-20260925T022624Z-ce2c`, manifest
[certify-20260925T022639Z-3425101](manifests/certify-20260925T022639Z-3425101.json),
passed, ACL2 8.7 w25 `acl2-literal`, 2 jobs, 300 s, source `65b1ae40`,
roots and `--affected-by books/byte-store-k0-marker` (no other root includes
it): `books/byte-store-k0-marker` 7.5 s, `tests/acl2/byte-store-k0-marker-tests`
4.6 s.
