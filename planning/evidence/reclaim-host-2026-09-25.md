# Content reclamation, the host half: what landed and what the byte program needs (2026-09-25)

Lane `reclaim-host`, branch `lane/reclaim-host` from dev `ac70f38d`.
Registry: PRF-088, STO-014, SCN-048. Continues
`planning/evidence/reclaim-d13-2026-09-25.md`.

## 1. The host asks the tombstone-aware D25 verdict (done)

Every host call of `fn-pb-existing-action` is now `fn-rcl-existing-action`
(books/store-reclaim.lisp), which is `fn-pb-existing-action` whenever the
held payload is not a tombstone (`fn-rcl-existing-action-is-pb-without-a-tombstone`):

- host/owner-host.lisp `fn-owner-prepare` (the `existing` binding) and
  `fn-owner-existing-action`;
- host/store-node-host.lisp the prepare's `existing` binding and
  `fn-store-sn-existing-action`.

The brief named four sites; there are six. The native owner's hot path asks
with the payload in the octet buffer (host/owner-host.lisp
`fn-owner-prepare-buffer` and `fn-owner-existing-action-buffer`, called from
host/native/owner.lisp `fnn-owner-attempt`), through
`fn-pbb-existing-action`, which knows no tombstone. Switching only the list
sites would have left the live owner calling a resend of a reclaimed
article a conflict (witness in the test book). New book
`books/store-reclaim-buffer.lisp`:

- `fn-rclb-existing-action` (the buffer twin; the two buffer sites call it);
- KEYSTONE `fn-rclb-existing-action-is-rcl-existing-action`:
  `(implies (fn-octets-p fn-octets) (equal (fn-rclb-existing-action msgid fn-octets groups s) (fn-rcl-existing-action msgid fn-octets groups s)))`.

A live held payload is compared in place as before. A held tombstone is
compared by digest. Since D32 (restated in the continuation, section 7.1):
the whole submission is digested in place by `fn-sha256-of-prefixed-buffer`
(books/sha256-buffer, empty prefix), and when the tombstone kept a D25 source
under the submission's own agent, the submission's source is D32's
description (K A B) (`fn-pbb-source-index`), whose two ranges st[K..A) and
st[B..) are sliced into one list and hashed by `fn-sha256-stobj`
(`fn-rclb-desc-digest`, equal to `fn-sha256` of `fn-pbb-desc-list` by
`fn-rclb-desc-digest-is-sha256-of-desc-list`). That list is built only on the
resend-of-a-reclaimed-article path; a two-range buffer digest reader would
remove it (open, D27).

The three native images (host/native/build.lisp, build-dtn.lisp,
build-store-test.lisp) include `books/store-reclaim-buffer`.

Teeth (`tests/acl2/store-reclaim-buffer-tests.lisp`): the owner fixture of
octets-stobj-tests with its one article reclaimed; on a live local buffer and
on the list side: the same octets resent and the same source re-injected are
`:duplicate`, a changed body and other groups `:conflict`, an unknown ID nil;
the old buffer call answers `:conflict` on the reclaimed store; on the live
store the new call is the old one. `must-fail` for the one hypothesis: the
held octets with an improper tail.

## 2. `store reclaim`: not implemented, and why (a model decision)

The K0 byte model (`books/byte-store-k0-step.lisp` `fn-bs-k0-step-inputp`)
admits, in `:transactions`, only `:link` of a staged file at the NEXT
transaction name, with the kernel unchanged except through `:observe`. No
step replaces a committed transaction file's content, and the kernel's
records (`fn-sf-records`) cannot change under any syscall step. Rewriting a
record's file with its tombstone payload (the reclaim-d13 plan) is therefore
a step the model cannot express; under the assurance rules
("every process-death cut is a model crash point") the program cannot ship
until the model says what that rename means.

Two designs, for the deputy to choose:

- (A) Replace in place: a new `:rename` arm, `:staging` onto an existing
  transaction name, whose landed resolution is related to the RECLAIMED
  kernel (records with that one payload replaced) and whose dropped
  resolution to the old kernel, with a covering lemma like the marker
  rename's (`fn-bs-k0s-marker-rename-covered`). It needs a kernel
  transition outside `:observe` and the reclaimed record's own replay step
  (reclaim-d13 open item 4). New proof surface in the K0 step books, which
  lane k0-rest is changing now (PKT-080/086).
- (B) Reclaim through compaction: the pack capture
  (`books/checkpoint-compaction.lisp` `fn-cc-capture`, verb
  `books/store-compact-verb.lisp`) writes the tombstone in place of each
  reclaimable payload, and the existing pack/select/reclaim/retire program
  (already a K0-era program with its cuts) removes the transaction files.
  The obligation becomes: replay of the reclaiming pack equals
  `fn-rcl-reclaim-state` of replay of the history. No new byte step. Limit:
  a pack is at most 4 MiB of summary (`:exceeds-compaction-unit`), so an
  N=5,000 store of ordinary articles needs the chained packs that are
  already open.

(B) keeps the transaction log append-only and reuses a proved program; it is
this lane's recommendation. `--dry-run` needs no byte program (it writes
nothing), but it needs an operator verb in books/native-operator.lisp, whose
action keystones enumerate the actions; it is left to the lane that lands
the program, so the two land together. The plan it would print is ACL2's
already (`fn-rcl-plan`).

## 3. Status counts (done)

books/native-live-status.lisp owns the words. The `status` report has one
new line after `open=`:

    reclaim rule=R reclaimable=N reclaimable-octets=N held=N reclaimed=N freed-octets=N

`fn-nls-reclaim-words` reads the rule from the configuration
(`fn-rcl-config-rule`), the instant from the clock observation the host now
passes as the fourth element of the open observation (host/native/io.lisp
`fnn-store-observation` appends `fnn-store-prepare-observation`), derived by
`fn-record-stamp-of-observation`, the same derivation that stamps an
article; an unusable clock reclaims nothing under release-after. The counts
are `fn-rcl-store-counts` (books/store-reclaim-holders.lisp): the reclaim-d13
summary plus the number of articles a holder keeps. The live report reaches
the same function (`fn-nls-live-report-is-the-offline-report` is unchanged
in statement).

## 4. OVER, XOVER and NEWNEWS drop a reclaimed article (done)

books/nntp-responses.lisp, books/nntp-range-indexed.lisp; theorems in
books/nntp-reclaimed.lisp, each of the function the dispatcher calls:

- `fn-nntp-over-by-msgid-answers-reclaimed`: OVER <message-id> of a held
  tombstone answers `430 article reclaimed` (subject `fn-nntp-over-response`,
  called by `fn-nntp-archive-command`, books/nntp.lisp). It was
  `503 stored article framing unavailable`.
- `fn-nntp-over-current-answers-reclaimed`: OVER with no argument, current
  article reclaimed: `423 article reclaimed`.
- `fn-nov-lines-indexed-skip-a-reclaimed-article` (subject
  `fn-nov-lines-for-numbers-indexed`, called by `fn-nntp-over-range-indexed`,
  the pinned dispatcher's OVER/XOVER range) and
  `fn-nov-lines-skip-a-reclaimed-article` (the unpinned range): the lines
  over NUMBERS equal the lines without the reclaimed article's number. The
  tombstone is skipped before it reaches the header parser.
- `fn-nntp-newnews-scan-lists-only-live-articles`: every ID
  `fn-nntp-newnews-scan` lists (called by `fn-nntp-newnews-response`) is an
  article that is not a tombstone.

A changed contract, stated: `fn-nntp-newnews-scan-reads-no-payload`
(books/nntp-newnews.lisp) said NEWNEWS reads no payload octet. Whether an
article was reclaimed is a payload fact, so the erasure it quantifies over
(`fn-nntp-newnews-without-payload`) now keeps a tombstone and erases every
other payload. The scan still parses nothing and reads at most the
tombstone's fixed head (89 conses).

Teeth (`tests/acl2/store-reclaim-tests.lisp`, new section): two whole
articles in "g", 1 reclaimed; OVER <w1> 430, before reclamation 224; teeth for
each hypothesis (a live article, a number token, an unknown ID; current 2,
no group, no current, current 7); range 1-2 gives the one line of 2, and
removing the live 2 changes the lines; NEWNEWS lists <w2> only though <w1>
is a candidate and new.

## 5. Holders, charge, feeds (partly)

`books/store-reclaim-holders.lisp` `fn-rcl-store-holders` reads the E2
consumer projection. A consumer acknowledges a Store journal position, not a
group number, and the acceptance state does not keep an article's journal
position, so the reading is conservative: a consumer whose acknowledgement
is below the committed frontier holds every article (a cursor at 0 in every
served group). KEYSTONE `fn-rcl-store-holders-hold-behind-a-lagging-consumer`:
while any registered consumer lags, no article numbered in a served group is
reclaimable, for every rule, clock and verdict list. Teeth
(`tests/acl2/store-reclaim-holders-tests.lisp`): lagging holds, caught up
reclaims; `must-fail` with the consumer caught up, an article with no
membership, and one numbered only in a group the store lacks.

Not done: the precise consumer reading (the article's journal sequence);
feed state and FNBS rows (they are not in this Store's state); the retention
charge released for a reclaimed article (the ledger in `fn-node-retention`
keeps it, so admission headroom does not grow).

**Finding: reader pins have no durable form. Does reclaim need one? No,
under design (A) or (B) as an offline verb:** `store reclaim` holds the
exclusive Store lock after recovery, so no reader connection exists when it
decides, and a pin cannot outlive its connection. A pin matters only if
reclamation becomes an owner-live operation; then the pin must be carried in
the owner's state (it is: `fn-ocfg-pins` for configuration pins), not made
durable. The live `status` count is advisory for the same reason: it reads
no reader pin.

**Finding, settled in the continuation (section 7.3): a tombstone-shaped
submission is refused at every served ingress,** because its first octet is
NUL and no article opens with NUL; the refusal is now a theorem over the
function every served ingress calls.

## 6. Native (not done)

No hbox run: there is no `store reclaim` verb to exercise (section 2). The
N=5,000 run, disk bytes before and after and the cut campaign wait on it.

## 7. Continuation (2026-09-25 evening, after pbb-d32 landed)

Branch `lane/reclaim-host`, dev merged at `36fc0007` (pbb-d32), again at
`af09e509` and `0d0cc0f8` (make check needed dev's PRF-032 citation and
6ebae0a0's comment fix).

### 7.1 The buffer twin over D32 (done)

`books/store-reclaim-buffer.lisp` restated over D32's `fn-pbb-path-agent`
(now `(msgid fn-octets)`) and `fn-pbb-source-index` (now a description
(K A B), not a suffix index); section 1 says how it digests. Events:
`fn-rclb-desc-digest-is-sha256-of-desc-list`
`(implies (and (true-listp fn-octets) (fn-pbb-descp d (len fn-octets))) (equal (fn-rclb-desc-digest d fn-octets) (fn-sha256 (fn-pbb-desc-list d fn-octets))))`;
`fn-rclb-same-as-tombstonep-is-rcl` (under `fn-octets-p`); KEYSTONE
`fn-rclb-existing-action-is-rcl-existing-action`, statement unchanged. Its
proof went from 3.5 s (2.1 M steps) to 0.01 s (792 steps) by using the two
component equalities instead of opening both verdicts. Host lines unchanged:
host/owner-host.lisp `fn-owner-existing-action-buffer` and
`fn-owner-prepare-buffer`, called from host/native/owner.lisp
`fnn-owner-attempt`.

Teeth (tests/acl2/store-reclaim-buffer-tests.lisp): the earlier witnesses,
plus a D32 v3 witness: tin's article injected at clock A, reclaimed, and the
same article injected at clock B resent (different octets, a description
with a real cut, A < B) is the same article on the list and on a live
buffer; one more body octet is not. The improper-tail tooth for
`fn-octets-p` separated the two sides only by accident before D32; SHA-256
reads a list to its last cons, so on the reclaimed store both sides now
agree, and the tooth is taken on the live store, where the list side
compares the improper source by `equal`.

### 7.2 The status-count witness: a definition defect, not a witness defect (done)

Cause, evaluated on persvati (not guessed): the owner fixture's store has a
verdict entry for EVERY accepted article, `(msgid :absent :no-field 0)`
(`fn-sn-finish` records `fn-stx-verdict-of-octets` of each payload,
`fn-sn-finish-records-the-acceptance-verdict`), and `fn-rcl-verdict-heldp`
held any article with an entry. So no article of a live store was ever
reclaimable: the counts were right and the rule was vacuous. The per-article
witness passed only because it passed `nil` for the verdict list.

Fix, in the definition: `fn-rcl-verdict-heldp` holds an article only for an
entry whose token is not `:absent`. Why that is exactly the payload's
obligation: the statement index is re-derived from the stored payloads at
open (`fn-stx-index-of-store` over `fn-stx-delta`), and a payload that
verifies under that open's keyring contributes; an `:unverified` article may
verify under a later keyring, so it stays. New events:

- `fn-rcl-absent-verdict-contributes-nothing`
  (books/store-reclaim-holders.lisp):
  `(implies (equal (fn-stx-verdict-token (fn-stx-verdict-of-octets payload k1 g)) :absent) (equal (fn-stx-delta payload k2) nil))`,
  every keyring pair;
- `fn-rcl-tombstone-contributes-nothing` (books/reclaim-admission.lisp):
  `(implies (fn-rcl-tombstonep payload) (equal (fn-stx-delta payload keyring) nil))`.

Together: reclaiming an `:absent` article leaves every later open's
statement index unchanged. The PRF-088 keystone
`fn-rcl-reclaimable-is-no-obligation-names-it` keeps its statement (it names
`fn-rcl-verdict-heldp`; the prose now says "no authorship verdict other than
:absent").

Teeth (tests/acl2/store-reclaim-holders-tests.lisp): the Store's own verdict
list holds nothing and the article is reclaimable with it; `must-fail` with
an `:unverified` entry for the same Message-ID. The absent theorem: witness
the fixture's article (`:absent` under the empty keyring, no statement under
`*stxt-keyring*`); `must-fail` on stx-transit-tests' `*stxt-r1*`, which is
`:unverified` under the empty keyring and contributes its statement under
`*stxt-keyring*`. The count witnesses now pass unchanged (certified r7).

Finding (for the byte program): a reopened store has NO verdict entry for an
unsigned article (open rebuilds verdicts from the identity replay, which
records only signed composites, books/replay.lisp `fn-replay-identity-step`),
while the live store has an `:absent` one. Before this fix a live `status`
therefore counted nothing reclaimable where the offline verb, on the
reopened store, would have found the same articles reclaimable. After it
the two agree for unsigned articles.

### 7.3 Security: a tombstone-shaped payload at admission (done)

Traced every served ingress (POST through `fn-inj-decide`; IHAVE, TAKETHIS
and peer transit through `fn-peer-decide-transfer`; BP transit through
books/bp-transit-join; bound submissions): each parses the payload as an
article before the Store, and all reach the Store prepare only through
host/native/owner.lisp `fnn-owner-attempt-transit`, whose `form` binding
calls `fn-owner-peer-carrier-form` (host/owner-host.lisp), that is,
`fn-pa-carrier-form`, before any Store call. So it was already refused, not by
name but because it is not an article. It is now a theorem, new book
`books/reclaim-admission.lisp`:

- KEYSTONE LEMMA `fn-rca-nul-first-octet-is-not-an-article`:
  `(implies (equal (car octets) 0) (not (fn-article-result-okp (fn-article-parse octets))))`
  (the first header line would open with NUL, not ftext, books/article
  `fn-article-ftextp`; via `fn-rca-nul-line-first` and
  `fn-rca-nul-line-is-no-field`);
- `fn-rcl-tombstone-does-not-parse`;
- host subject `fn-rcl-tombstone-refused-at-carrier-form`:
  `(implies (fn-rcl-tombstonep received) (equal (fn-pa-carrier-form received) '(:refused :article)))`.

Teeth (tests/acl2/reclaim-admission-tests.lisp): a real tombstone
(`fn-rcl-tombstone-of` of an article) is refused and the article it
replaced is admitted `:absent`; `must-fail` on that article; the article
with its first octet set to NUL does not parse, `must-fail` on the article
itself; the line lemma on "H: x" versus NUL ": x"; the index corollary with
`must-fail` on `*stxt-r1*`.

Not covered, recorded: the developer image's `store post`
(host/native/io.lisp `fnn-command-post` to `fn-store-sn-prepare`) prepares a
raw payload file with no article check, so on a developer image an operator
can store a tombstone-shaped payload. It is not a served ingress and not in
the production image. A Store-level refusal in `fn-owner-prepare-buffer` and
`fn-store-sn-prepare` would cover it too; not done (it moves the prepare
closure, several hundred books).

### 7.4 `store reclaim` through the compaction pack (NOT done)

bounds-p5 (chained packs) has not landed, so the design is at N within one
pack (4 MiB of summary, `*fn-cc-max-octets*`; the N=5,000 store needs the
chain). Nothing was implemented: the program needs a new model obligation
and a proof, and blind code would be a host decision. The design, for the
lane that implements it:

1. Verb: `operator CONFIG store reclaim [--dry-run]` in
   books/native-operator.lisp `fn-nop-parse-store`, a native action
   `:reclaim` / `:reclaim-dry-run` in `fn-native-operator-result-native-action`,
   with the pair of keystones the compact and checkpoint verbs have
   (`fn-native-operator-run-store-reclaim-is-the-reclaim-action`,
   `fn-native-operator-run-reclaim-action-is-only-store-reclaim`). Offline,
   after the ordinary open's recovery, under the exclusive lock.
2. Decision: `fn-rcl-plan` over the reopened store with
   `fn-rcl-store-holders` and the configured rule (books/reclaim-rule).
   `--dry-run` prints the plan and `fn-rcl-store-counts` and writes nothing
   (exit 0; refused 1 with the reason; the three outcomes as elsewhere).
3. Program: the compact verb's program unchanged (pack, select, reclaim,
   retire, books/store-compact-verb `fn-cverb-decide`), with the capture
   taking a RECLAIMING event list: each reclaimable article record
   re-encoded with `fn-rcl-tombstone-of` in place of its payload, every
   other record's octets exact. No new byte step, so K0 needs no new arm.
4. Obligations: (a) the re-encoded record decodes to the record with the
   tombstone payload (codec round trip); (b) replay of the reclaiming pack
   equals `fn-rcl-reclaim-state` of replay of the history, from
   `fn-rcl-prepare-commutes-with-reclaim` lifted to the replay loop; (c)
   `fn-cc-octet-event-listp` of the reclaiming list, so the pack is a
   summary; (d) the statement index of the reopened store unchanged
   (7.2's two theorems, per reclaimed article); (e) the cut campaign of the
   compact verb reused, each cut a model crash point already.
5. Limits and findings: the reclaimed octets leave the disk only when the
   transaction files the pack covers are unlinked, so "disk bytes after" is
   the pack plus the retained suffix; the retention charge is not released
   (section 5); the precise consumer reading is still open.

### 7.5 Native (NOT done)

No image was built on this branch and nothing ran on hbox: without 7.4
there is no reclaim to run, and the behaviour this continuation changed
(the counts `status` prints under a releasing rule, and the tombstone
refusal, which the served path already had) was observed only in ACL2.
The hbox campaign (reclaim under release-after, 423/430, OVER/NEWNEWS skip,
counts, disk bytes, kill and EIO at the program's cuts) waits on 7.4.

## Certification

All persvati, ACL2 8.7 w25 `acl2-literal`, 2 jobs, 300 s, cache
`/home/ember/fn-certcache`. Manifests under planning/evidence/manifests/.

- `run-20260925T183827Z-4dd7`, manifest `certify-20260925T183859Z-4091844`,
  after merging dev, `--affected-by` nntp-responses, nntp-newnews,
  nntp-range-indexed, nntp-reclaimed, native-live-status,
  store-reclaim-holders, store-reclaim-buffer (265 roots). Every book this lane
  changed certified: nntp-reclaimed 1.5 s, nntp-range-indexed-invariants
  2.0 s, nntp-newnews 1.8 s, native-live-status 6.5 s and its tests 5.1 s,
  store-reclaim-tests 3.4 s, store-reclaim-holders 2.0 s. Failed:
  books/poster-bytes-buffer (red on dev for D32; lane pbb-d32 owns it) and
  what includes it: store-reclaim-buffer, its tests, octets-stobj-tests. The
  buffer twin has to be restated over D32's `fn-pbb-path-agent` when that
  lands; its proof (section 1) was admitted before D32 in run
  `run-20260925T100702Z-292c` and in a REPL.
- The D32 join fix to store-reclaim (branch lane/reclaim-d32fix, 0915bac2):
  `run-20260925T183420Z-c5c7`, `certify-20260925T183440Z-4046016`, passed.
- store-reclaim-holders-tests (`certify-20260925T185623Z-65311`): the
  keystone's witness and its three `must-fail` teeth pass; the status-count
  witness fails. It is open (LANEDUMP names the probable cause: the
  fixture's verdict list).

Continuation (section 7), all persvati, the same toolchain and settings:

- r7 `run-20260925T191946Z-777f`, `certify-20260925T192046Z-305043` (at
  5a9a4a74): 54 books passed, among them store-reclaim 8.6 s,
  store-reclaim-holders and its tests (the count witnesses), nntp-effects,
  nntp-invariants and nntp-newnews (PRF-052 now cites it); failed
  store-reclaim-buffer (a lemma dropped in the restatement) and its tests.
- r8 `run-20260925T192639Z-6de7`, `certify-20260925T192713Z-366804`: the
  admission book (an unused lemma that does not prove) and the buffer
  tests' improper-tail tooth (see 7.1) failed; both fixed after REPL checks
  on persvati.
- r9 `run-20260925T192918Z-9e78`, `certify-20260925T192944Z-391564`
  (8994737c): passed; reclaim-admission 0.7 s, its tests 1.2 s,
  store-reclaim-buffer-tests 1.7 s.
- r10 `run-20260925T194303Z-c7b1`, `certify-20260925T194323Z-519198`, at the
  final bytes after the two dev merges (0d0cc0f8), `--affected-by`
  store-reclaim, store-reclaim-buffer, store-reclaim-holders,
  reclaim-admission, nntp-range-indexed-invariants: 15 roots, 43 books
  certified, 0 failures. Over ten seconds: owner-invariants 11.6 s (known,
  baseline, not this lane's). `green_check --changed-since e13ece8e` showed
  every changed book green except nntp-range-indexed-invariants, which r10
  certifies.
- `make check` green in the worktree with the ledger and current view
  regenerated (not committed; the deputy regenerates them on merge).
