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
compared by digest: the submission (or its source, when the tombstone kept a
D25 source under the submission's own agent) is sliced out of the buffer once
and hashed by `fn-sha256-stobj`. That slice is one list the size of the
submission, built only on the resend-of-a-reclaimed-article path. A buffer
SHA-256 that reads the stobj in place would remove it (open, D27).

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

**Finding (unverified, for the deputy): a submitted payload that is itself
tombstone-shaped.** `fn-rcl-tombstonep` is a prefix test (NUL "FN-RCL1"
and at least 89 octets). Nothing in this lane shows that acceptance refuses
such a payload; if a peer can store one, it is served as reclaimed and
counted reclaimed. Locally posted articles get an injected Path line first,
so only the peer/feed paths are in question.

## 6. Native (not done)

No hbox run: there is no `store reclaim` verb to exercise (section 2). The
N=5,000 run, disk bytes before and after and the cut campaign wait on it.
