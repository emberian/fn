# Carry the kind: the signed path's re-recognitions (2026-09-25)

Lane `carry-kind`, branch `lane/carry-kind` from dev `595d3a47`. Packets
PKT-112 and PKT-113 of `planning/backlog-2026-09-25.md`; PKT-114 is not done
(section 6). Registry: PRF-092 (HST-001, HST-004).

## 1. What was found

The signed POST is an identity event: host/native/owner.lisp
`fnn-owner-identity-commit` prepares it through `fn-owner-prepare-identity`
and completes it through `fn-owner-finish`, not through the carried article
commit (`fn-ccar-own-finish`). Both host functions issued the owner event
through `fn-owner-step`, that is `fn-ocfg-step` → `fn-own-step` →
`fn-own-store-step` → `fn-snrt-step`, none of them guard-verified. So each
call:

- evaluated `fn-sn-statep` of the whole store (the unverified function's
  guard, checked by its executable counterpart under guard-checking t);
- completed through the reference `fn-sn-finish`, whose
  `fn-sn-completion-record` is `fn-sn-find-record`: a walk of the whole
  history computing `fn-sf-record-pair` (so `fn-store-event-sequence` and
  `-txid`, so `fn-record-p` and `fn-stxa-p` over each record's octets) of
  every record, and it did so from the gate twice (`fn-own-complete` and
  `fn-sn-finish` each evaluate `fn-sn-completion-enabledp`);
- read the composite's kind, sequence and txid through the guard-t
  dispatchers, each of which re-ran the recognizers.

The article commit already carried the history's positions (`fn-ccar-seek`)
but also re-recognized the found record for each field it read
(`fn-rcon-sf-record-pair`, `fn-rcon-store-event-sequence`, `-txid`, the two
projection steps' `fn-rcon-store-event-p`), and evaluated its gate three
times per commit (the word, `fn-own-complete`, `fn-sn-finish`).

## 2. What changed

**`books/store-events-carried.lisp` (new, prefix `fn-evc-`).** Under
`fn-store-event-p` a Store event's kind is fixed by its shape: the head is
`:retention`, `:consumer`, another symbol (a topic event), or a number, and
then the width (6, 8, 10, 11) separates keyring snapshot, statement verdict,
composite and article record. `fn-evc-class-by-shape` and
`fn-evc-field-by-shape` read that: O(1), at most ten conses, no field
contents. KEYSTONES (`:rule-classes nil`, used through `:use`):

- `fn-evc-field-by-shape-is-store-event-sequence` / `-txid` / `-generation`:
  `(implies (fn-store-event-p x) (equal (fn-evc-field-by-shape N x) (fn-store-event-sequence x)))`
  for N = 0, 1, 2 and the three dispatchers.
- `fn-evc-class-by-shape-is-fn-record-p`, `-fn-store-retention-event-p`,
  `-fn-stxe-p`, `-fn-stxk-p`, `-fn-stxa-p`, `-fn-cpe-eventp`,
  `-fn-th-topic-eventp`: `(implies (fn-store-event-p x) (iff (R x) (equal (fn-evc-class-by-shape x) C)))`.

The carried accessors `fn-evc-sequence`, `-txid`, `-generation`,
`-recordp`, `-retentionp`, `-stxep`, `-stxkp`, `-stxap`, `-consumerp`,
`-topicp` are `(mbe :logic <reference> :exec <reading by shape>)` with guard
`(fn-store-event-p x)`: in the logic each is its reference, so every caller's
theorem is unchanged by the substitution; guard verification is where the
keystone is spent. The recognizers stay closed throughout (shape facts are
read from each recognizer's own head and width conjuncts).

**`books/owner-commit-carried.lisp` (`fn-ccar-`).**

- `fn-ccar-seek` (guard now `(and (natp seq) (fn-sf-record-valuesp records))`)
  compares the pair through `fn-evc-sequence`/`-txid`;
  `fn-ccar-seek-finds-a-store-event` and
  `fn-ccar-completion-record-is-a-store-event` carry the fact out of the
  history (`fn-ccar-sn-statep-carries-record-values`).
- New carried twins, each equal to its reference with no hypothesis:
  `fn-ccar-cpe-projection-step`, `fn-ccar-th-prefix-step` (the
  `fn-store-event-p` test becomes `(mbe :logic ... :exec t)` under the
  guard), `fn-ccar-sn-record-bindsp`, `fn-ccar-sn-prepare-identity`.
- The gates and the finish dispatch on the carried kind
  (`fn-ccar-completion-core-enabledp-is-reference`,
  `fn-ccar-completion-enabledp-is-reference`, `fn-ccar-sn-finish-is-sn-finish`,
  all unchanged statements). The finish's enabled branch is its own function
  (`fn-ccar-sn-finish-enabled`, guard includes the gate), and
  `fn-ccar-own-complete` and `fn-ccar-own-finish` evaluate the gate once.
- `fn-ccar-ocfg-complete`, KEYSTONE `fn-ccar-ocfg-complete-is-ocfg-step-complete`:
  `(equal (fn-ccar-ocfg-complete oc) (fn-ocfg-step oc '(:complete)))`, no
  hypothesis, guard-verified under `fn-sn-statep` of the store (carried by
  `fn-ocl-relation`: `fn-ccar-ocl-relation-carries-sn-statep`).
- `fn-ccar-ocfg-prepare-identity`, KEYSTONE
  `fn-ccar-ocfg-prepare-identity-is-ocfg-step`:
  `(equal (fn-ccar-ocfg-prepare-identity oc event) (fn-ocfg-step oc (list :store (list :prepare-identity event))))`,
  no hypothesis, guard-verified under the same premise.

**Host lines (host/owner-host.lisp).**

- `:635` `fn-owner-finish` installs `fn-ccar-ocfg-complete` (was
  `fn-owner-step '(:complete)`). Subject of
  `fn-ccar-ocfg-complete-is-ocfg-step-complete`.
- `:495` `fn-owner-prepare-identity` installs `fn-ccar-ocfg-prepare-identity`
  (was `fn-owner-step (:store (:prepare-identity e))`). Subject of
  `fn-ccar-ocfg-prepare-identity-is-ocfg-step`.
- `:674` `fn-owner-finish-submission` calls `fn-ccar-own-finish` (unchanged
  line; `fn-ccar-own-finish-is-own-finish` unchanged statement, new body).

**`books/owner-intent-carried.lisp` (PKT-113).** The carry `fn-owner-take`
writes (`:737`, `fn-icar-carry-of`) is now `(SUB ID . PATH)`: the
submission's Path (`fn-own-feed-path-of`, which parses the article) is
parsed once at take. KEYSTONES under `fn-icar-carryp` (which now also says
the PATH is the parse of the carry's own submission):
`fn-icar-path-is-path-of` and `fn-icar-submission-targets-is-submission-targets`
(`(equal (fn-icar-submission-targets o carry) (fn-own-submission-targets o))`).
The intent (`:1118`) and the resolution (`:1136`) read the targets through
it; `fn-icar-submission-intent-is-reference` and
`fn-icar-submission-resolution-records-is-reference` keep their statements.
The Path was parsed at both before.

`books/owner-offer-indexed.lisp`: `fn-oix-ccar-own-finish-keeps-view-indexed`
is now proved from `fn-oix-finish-keeps-view-indexed` and the keystone
(statement unchanged), since the carried commit's body changed.

## 3. Teeth

- `tests/acl2/store-events-carried-tests.lisp`: reachable witness
  `*ospt-completing*` (owner-signed-post-tests: the owner at `:completing`
  after a signed POST's composite, reached by `fn-own-run`). Every record of
  its history (more than one) and the composite satisfy all ten readings;
  the composite's class is `:stxa`. One concrete refutation and one
  `must-fail` over a constant per keystone: lists shaped like each kind that
  are not Store events (`*evct-junk-stxa*` ... `*evct-junk-topic*`), and the
  composite with its article record replaced by `(256)` (not a Store event,
  class still `:stxa`, the reference sequence nil, the shape's the
  composite's). The carried commit on the witness equals `fn-own-step
  (:complete)`'s owner (`*ospt-finished*`) and moves the store;
  `fn-ccar-ocfg-complete` equals `fn-ocfg-step (:complete)` there; the
  carried prepare on the same trace one step earlier equals `fn-ocfg-step`
  and stages the composite (`:record-staged`).
- `tests/acl2/owner-commit-carried-tests.lisp`: unchanged witnesses; the
  bad-store lookup now evaluates under `with-guard-checking :none` (the
  lookup's guard is now `fn-sn-statep`); the new functions are
  `:common-lisp-compliant`.
- `tests/acl2/owner-intent-carried-tests.lisp`: the carry holds the Path;
  a carry with the right identity and a Path naming the outbound peer
  (`out.example!not-for-mail`) violates `fn-icar-carryp` and the targets
  drop the peer (the intent differs); `must-fail`s over constants for both
  new keystones.

## 4. Certification (persvati, w25 `acl2-literal`, 2 jobs, 300 s)

| Run | Rev | Result | Manifest |
| --- | --- | --- | --- |
| run-20260925T090637Z-31bf | cf7c41ff | `--affected-by` store-events-carried, owner-commit-carried, owner-offer-indexed: 11 certified, 170 installed, passed | `certify-20260925T090709Z-3027421.json` |
| run-20260925T091135Z-c1e4 | 542c2045 | `--affected-by` owner-intent-carried: 2 certified, passed | `certify-20260925T091156Z-3077911.json` |
| run-20260925T091348Z-9a9f | 3233a9f3 | `--affected-by` store-events-carried, owner-intent-carried (14 roots, the new test root registered in the Makefile): 1 certified, 13 at these bytes, passed | `certify-20260925T091410Z-3100224.json` |
| run-20260925T091757Z-aade | e61c5d90 | `--affected-by` owner-commit-carried, owner-intent-carried: 12 certified, passed; slowest owner-offer-indexed 6.7 s, owner-commit-carried 6.6 s, store-events-carried-tests 5.3 s | `certify-20260925T091819Z-3145574.json` |

store-events-carried itself took 2.4 s (run 1; unchanged since). No book this
lane changed or that depends on one is over 10 s at the last run.
`tools/green_check.py --changed-since 595d3a47`: 7 changed books, 7
dependents, 0 not green at the bytes a merge would carry.

The hbox image builds (`build-dev.sh`, w28 `acl2-literal-4g`, 8 jobs,
incremental over `/tank/fn/certcache`) certified the default image closure of
each tree before building (logs under `/tank/fn/scratch/carry-kind/logs-*`).

## 5. Measurement (hbox, developer images, native, `systemd-run --user --scope -p MemoryMax=24G`)

Script `prof_carry.py` (this directory; base-1 and after-1 ran the same
script before its `--prof` option was added): one owner, plain NNTP, profile
A = 4 MiB, one enrolled principal. Phase "fresh": 7 rounds of an unsigned
204,800-octet-body POST then a signed one (215,388 octets, hybrid v2
carrier), each timed from the article to the 240. Then 200 unsigned 2 KiB
articles are preloaded, and phase "preloaded" runs 7 more rounds. Every
round's store holds the earlier rounds' articles, so both phases grow the
history. Images (`*-image.sha256`): base = dev `595d3a47`; after = `3233a9f3`
(the carried commit and complete); after2 = `e61c5d90` (plus the
guard-verified identity prepare). Box: hbox, shared with other lanes; load
average 4 to 13 during the runs, highest during after2. The spread between
runs of the same image is as large as the effect on the fresh phase.

Pooled over all rounds of all runs of an image (medians; base 3 runs, after
2, after2 2):

| Image | Phase | unsigned | signed | signed / unsigned |
| --- | --- | ---: | ---: | ---: |
| base | fresh | 0.471 s | 1.123 s | 2.38 |
| after | fresh | 0.394 s | 0.827 s | 2.10 |
| after2 | fresh | 0.436 s | 1.090 s | 2.50 |
| base | preloaded | 0.491 s | 2.106 s | **4.29** |
| after | preloaded | 0.416 s | 1.144 s | **2.75** |
| after2 | preloaded | 0.408 s | 1.408 s | **3.45** |

Per run (each 7 rounds): base fresh 3.10, 3.02, 2.04 and preloaded 3.77,
3.90, 5.17; after fresh 2.49, 1.85 and preloaded 3.60, 2.09; after2 fresh
2.75, 2.74 and preloaded 3.75, 3.47.

**Reading.** On the preloaded store the signed POST's median wall fell from
2.11 s to 1.14 to 1.41 s and the ratio from 4.3 to 2.8 to 3.5. On the fresh
store the change is inside the noise. **The 2x target is not met.** after2
is not slower than after by construction (it removes work); its runs were
the most loaded. A quiet-box rerun is owed before any figure here is quoted
as the effect size.

**Where the rest is** (`post-after2-preloaded-flat.txt`/`-graph.txt`, one
signed POST on the preloaded after2 store, 826 samples at 1 ms):

- 46.7 % in the identity prepare (`fn-ccar-ocfg-prepare-identity`), of which
  32.2 % is `fn-sf-history-recoverablep` → `fn-sf-replay-node` →
  `fn-replay-loop`: the replay of the whole appended history, re-recognizing
  every record (`fn-replay-apply-record`, `fn-store-event-txid`,
  `fn-record-p`, `fn-stxa-p`). This is O(N·L) per signed POST and grows with
  the store: section 6.
- 19.6 % in the completion (`fn-ccar-ocfg-complete`), now one gate
  evaluation and a finish; what it still pays is `fn-replay-apply-record` and
  `fn-replay-identity-step` decoding and binding the composite.
- The whole-history `fn-sn-find-record` and the `fn-sn-statep` guard
  evaluations are gone from the profile.

Logs and sha256 (`planning/evidence/carry-kind-2026-09-25/`):

| File | sha256 |
| --- | --- |
| base-1.log / base-2.log / base-3.log | `ed5a81b4…` / `17878e97…` / `fa1d5051…` |
| after-1.log / after-2.log | `6d926cda…` / `92a31889…` |
| after2-1.log / after2-2.log | `6bedbc7c…` / `6b6002f1…` |
| prof-after2.log | `a709c956…` |
| post-after2-preloaded-flat.txt / -graph.txt | `041e10b3…` / `e1fa6108…` |
| base-image.sha256 / after-image.sha256 / after2-image.sha256 | `71d02018…` / `94f25023…` / `d0ab6328…` |
| prof_carry.py / build-dev.sh | `72de2e8a…` / `9cf59012…` |

Images: base developer `4080cb58…`, after `1468f7a5…`, after2 `b20bc4b5…`
(launchers; cores in the `.sha256` files).

## 6. Not done, and why

- **PKT-114** (store-node-invariants, owner-invariants under 10 s): not
  started. The lane's four farm runs and its call budget went to PKT-112/113
  and the identity prepare.
- **The identity prepare still replays the appended history.**
  `fn-ccar-sn-prepare-identity` keeps `fn-sf-prepare-record`, whose
  `fn-sf-history-recoverablep` replays `(append records (list event))`:
  O(N·L) per signed POST. The article prepare omits it under the owner
  relation (`fn-spc-related-candidate-is-recoverable`,
  books/store-prepare-correspondence.lisp); the identity event has no such
  correspondence yet. This is the next packet for the signed path.
- **The replay steps still re-recognize.** `fn-replay-apply-record` and
  `fn-replay-identity-step` (books/replay.lisp) dispatch on the event through
  `fn-stxa-p` and decode the composite's record, on the prepare, on the gate
  and on the finish. Carried twins of those two (guard `fn-store-event-p`)
  are the natural continuation of this book.
- `owner-offer-indexed` certified at 10.88 s in run 1, of which 7.34 s is
  the include of `owner-served-carried` loaded without a fasl (the cache
  stores no fasl; PKT-121) and under 1 s is proof. Not a proof-cost defect
  of this lane; noted.
- TLS was not measured.
