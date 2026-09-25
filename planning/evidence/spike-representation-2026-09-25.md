# Spike: the octet buffer at the host boundary, the codecs over it, and the long-lived copy (D27 waves B and C on the megaspike, D28), 2026-09-25

Lane `spike/representation`, branched from `spike/mega` at dev `0e2173ab`.
Commits `60ebe290` (the buffer stobj, the frame and record codecs over it,
the host boundary, the spike waiver in the certifier, the measurement
driver), `3715d494` (the host ld order), `e7cd2d2b` (the article scan over
the buffer), and the evidence commit that carries this record. Design:
`planning/design-2026-09-25-representation.md` §5, wave B (boundaries 6 to
9) and wave C (boundary 10, the freeze items). The rule this spike works
under: D28 lets a correspondence be deferred with `skip-proofs` marked
`;; SPIKE`, and this record lists every deferral with its statement, so
the dev lanes have a specification of what runs.

## 1. What runs now (the executable path)

Before this lane every octet argument crossed the host boundary as a
list (`fnn-octet-list`, host/native/io.lisp), every codec copied the list
at each split and append, and the served POST payload made the round trip
core list, byte vector, and three fresh lists per POST. After it:

- **The buffer** (`books/octets-stobj.lisp`, `fn-octets`): an abstract
  stobj whose logical value is the octet list (`fn-cbor-octet-listp`,
  creator nil) and whose executable is a resizable `(unsigned-byte 8)`
  array with a fill count. The host fills it in raw Lisp with one
  `replace` (`fnn-octets-fill`, io.lisp) and reads it out with one
  (`fnn-octets-vector`); nothing else reaches the array. That fill is the
  host boundary of the book, at the same trust as `fnn-octet-list`
  handing a list to the core today.
- **The transaction file, written** (`books/records-stobj.lisp`
  `fn-rcs-store-seal-record`, `books/frame-stobj.lisp`
  `fn-frs-store-seal`): the pending article record is encoded by ACL2
  straight into the buffer (CBOR heads from `fn-cbor-encode-argument`,
  strings by `char` at an index, the payload by one write per octet of
  its list), the store header is written over ten placeholder octets,
  the SHA-256 trailer is computed from the buffer read as a string
  (`fn-sha256-of-string`, the proved string entry of `sha256-stobj`) and
  appended. The host copies the frame out once and writes the file.
  Host lines: `host/owner-host.lisp` `fn-owner-pending-frame`;
  `host/native/owner.lisp` `fnn-owner-publish-prepared` (SEALED, then
  `fnn-publish-data`). A pending record of another kind (retention,
  identity, consumer, topic) answers nil and takes the list path as
  before.
- **The transaction file, read** (`fn-frs-store-decode`,
  `fn-rcs-unframe-record`): at open every file is read into the buffer
  once; the frame is checked in place (length, header, the trailer against
  the SHA-256 of the prefix compared by index) and the record is decoded
  by position, building only the values the record holds (the four strings
  straight from the buffer, the payload once as the octet list the logical
  record holds). Host lines: io.lisp `fnn-unframe-value` (in
  `fnn-durable-records`), `fnn-record-value` (memoised on the record's
  byte vector: the frontier check, the store bridge and the owner's
  recovery share one decode); `host/store-host.lisp`
  `fn-store-frame-value-in-buffer`, `fn-store-event-value-in-buffer`;
  `host/owner-host.lisp` `fn-owner-recover-values` and
  `host/store-node-host.lisp` `fn-store-sn-recover-values` (the recovery
  entries with their `fn-store-decode-records` step removed);
  `host/native/owner.lisp` `fnn-owner-install`. A frame whose record is
  not an article record (a retention, statement, configuration or topic
  event) is handed to the list codec `fn-store-event-decode-exact` as
  before.
- **The served POST payload** (`fnn-owner-list-global`, native
  owner.lisp): the payload the core staged at the take goes back to the
  core as the list object it produced, for `fn-owner-existing-action`,
  `fn-owner-prepare`, the transit comparison and the carrier plan;
  before, each of those calls consed a fresh list from a byte vector that
  was itself copied from the core's list.
- **The article scan over the buffer** (`books/article-stobj.lisp`
  `fn-ars-parse`): the header grammar of `fn-article-parse` by index
  (lines found by scanning for CR LF, the body discipline in place, the
  field helpers of `article` on each consed line). No host line calls it
  on the spike: the served POST arm parses the submission's octet list
  inside the session machine (books/nntp-post.lisp under
  `fn-owner-chunk`), and the reroute is the wave C item below.

Certification: `books/octets-stobj`, `books/frame-stobj`,
`books/records-stobj`, `books/article-stobj` and
`tests/acl2/records-stobj-tests` certify on the laptop (ACL2 8.7, literal
launcher, 8,000 MB) and on hbox in the after tree's default-profile
closure (`after-cert.log`: 320 of 323 books from the cache, 3 certified,
`certify-20260925T085252Z-2964603`) under `FN_SPIKE=1`, which is the
D28 waiver in `tools/certify_books.py`: a `skip-proofs` carrying the
`;; SPIKE` mark within twelve lines is admitted with `:skip-proofs-okp t`;
`defaxiom`, `defttag`, `set-raw-mode` and `include-raw` stay forbidden,
and without `FN_SPIKE` the books are refused as before.

## 2. The theorems, and every deferral

Proved on this image (ordinary `defthm`s in the books):
`fn-oct-bufp-cell-is-octet`, `fn-oct-nth-of-octet-listp-is-octet`,
`fn-oct-nth-is-nth`, `fn-oct-snoc-is-append`, `fn-oct-update-is-update-nth`,
the write-chain shape facts (`fn-oct-len-of-update`, `-octet-listp-of-update`,
`-len-of-snoc`, `-octet-listp-of-snoc`), `fn-frs-byte-is-octet`,
`fn-rcs-pos-facts`, `fn-rcs-read-uint-value-natp`,
`fn-rcs-read-strings-names-true-listp`; every export and every function
the host calls is guard-verified (`records-stobj-tests` checks the
symbol classes).

Deferred with `skip-proofs` and the `;; SPIKE` mark, stated exactly as the
dev lane proves them, in the order the dev lanes should take them (each
later one uses the earlier):

1. **The abstract stobj obligations** (`books/octets-stobj.lisp`): the 22
   events `defabsstobj` requires, each as ACL2 prints it
   (`create-fn-octets{correspondence}`, `{preserved}`, and per export
   `fn-octets-len{correspondence}`, `fn-octets-get{correspondence}`,
   `fn-octets-get{guard-thm}`, `fn-octets-append-octet{correspondence}`,
   `{guard-thm}`, `{preserved}`, `fn-octets-put{correspondence}`,
   `{guard-thm}`, `{preserved}`, `fn-octets-clear{correspondence}`,
   `{preserved}`, `fn-octets-reserve{correspondence}`, `{preserved}`,
   `fn-octets-list{correspondence}`, `{guard-thm}`,
   `fn-octets-from-list{correspondence}`, `{guard-thm}`, `{preserved}`,
   `fn-octets-string{correspondence}`, `{guard-thm}`), under
   `(fn-octets$corr fn-octets$c fn-octets)` = the array's first FILL cells
   read in order are the logical list. Also
   `fn-oct-buf-list-down-is-from`: `(implies (and (natp n) (true-listp acc))
   (equal (fn-oct-buf-list-down n acc fn-octets$c) (append
   (fn-oct-buf-list-from 0 n fn-octets$c) acc)))`. Four facts prove them:
   `nth` of `fn-oct-buf-list-from` is `bufi` in range; the prefix is
   unchanged by an `update-bufi` at or past the fill and by a `resize`
   that keeps it; a write at the fill point extends it by one; the creator's
   array is empty.
2. **The derived readers' vocabulary** (`octets-stobj`):
   `fn-oct-slice-list-is-take-nthcdr`: `(implies (and (natp i) (natp n)
   (<= i n) (<= n (len (fn-octets-list fn-octets)))) (equal (fn-oct-slice-list
   i n fn-octets) (take (- n i) (nthcdr i (fn-octets-list fn-octets)))))`;
   `fn-oct-slice-list-down-is-slice-list`; `fn-oct-append-list-is-append`:
   `(implies (fn-cbor-octet-listp xs) (equal (fn-octets-list (fn-oct-append-list
   xs fn-octets)) (append (fn-octets-list fn-octets) xs)))`;
   `fn-oct-append-string-from-is-append`; `fn-oct-prefix-equalp-is-equal`:
   `(implies (and (natp i) (fn-cbor-octet-listp xs) (<= (+ i (len xs)) (len
   (fn-octets-list fn-octets)))) (equal (fn-oct-prefix-equalp i xs fn-octets)
   (equal (take (len xs) (nthcdr i (fn-octets-list fn-octets))) xs)))`.
3. **The frame** (`books/frame-stobj.lisp`):
   `fn-frs-store-decode-is-store-decode`: `(equal (fn-frs-store-decode
   fn-octets) (fn-frs-range-of (fn-frame-store-decode (fn-octets-list
   fn-octets) (fn-sha256 (fn-frame-protected-prefix (fn-octets-list
   fn-octets))))))`; `fn-frs-store-decode-range-is-payload`: under
   `(fn-frs-okp (fn-frs-store-decode fn-octets))`, the slice of the range
   is `(fn-frame-result-payload (fn-frame-store-decode ...))`;
   `fn-frs-store-seal-is-frame-encode`: with at least ten octets in the
   buffer and the rest within `*fn-frame-max-store-payload*`, the seal
   answers t and `(fn-octets-list (mv-nth 1 (fn-frs-store-seal fn-octets)))`
   is `(fn-frame-encode *fn-frame-magic-store* *fn-frame-version*
   *fn-frame-store-kind* record (fn-sha256 (fn-frame-protected ... record)))`
   for `record` = `(nthcdr 10 (fn-octets-list fn-octets))`. These are
   stated with `fn-sha256` where the list codec's `fn-frame-seal`/`-open`
   have the constrained `fn-frame-digest`, because the host image attaches
   `fn-sha256-stobj` to it (`crypto-attach`), which is `fn-sha256` by
   `fn-sha256-stobj-is-sha256`; the bytes are therefore exactly the bytes
   `fnn-frame`/`fnn-unframe` wrote and accepted before this lane. Proof
   ingredients: `fn-frs-get-u32` is `fn-cbor-u32-from` of the header
   slice; `fn-oct-prefix-equalp-is-equal`;
   `fn-sha256-of-string-is-sha256-of-octets` on `fn-oct-slice-string`
   (whose `fn-shs-string-octets` is the slice list).
4. **The record codec** (`books/records-stobj.lisp`):
   `fn-rcs-encode-into-is-record-encode-impl`: `(implies (fn-record-p
   record) (and (equal (mv-nth 0 (fn-rcs-encode-into record fn-octets))
   (not (null (fn-record-encode-impl record)))) (equal (fn-octets-list
   (mv-nth 1 (fn-rcs-encode-into record fn-octets))) (append
   (fn-octets-list fn-octets) (fn-record-encode-impl record)))))`;
   `fn-rcs-decode-exact-is-record-decode-exact-impl`: `(equal
   (fn-rcs-decode-exact 0 (len (fn-octets-list fn-octets)) fn-octets)
   (fn-record-decode-exact-impl (fn-octets-list fn-octets)))`;
   `fn-rcs-store-seal-record-is-sealed-frame` (from the two above and 3):
   for a record whose encoding exists and fits the store payload bound,
   the sealed buffer is `fn-frame-encode` of `fn-record-encode-impl` under
   `fn-sha256` of the protected prefix. Proof ingredients: the fourteen
   items (`fn-rcs-put-arg` is `fn-cbor-encode-argument` appended,
   `fn-rcs-put-string` the `(:bytes . codes)` item, `fn-rcs-encoded-size`
   is `len` of the encoding, so the whole-record bound is decided where
   the reference decides it); each `fn-rcs-read-*` is its
   `fn-record-read-*` on `(nthcdr i list)` with NEXT the position of the
   rest (the clamps `fn-rcs-pos` are identities on what the readers
   return and go with the proof). The seam: these are stated against
   `fn-record-encode-impl` and `fn-record-decode-exact-impl`; the seam's
   `fn-record-encode` is attached to `fn-rcon-record-encode-impl`
   (`records-attach-concrete`, equal to `fn-record-encode-impl` by
   `fn-rcon-record-encode-impl-is-record-encode-impl`), and
   `fn-store-event-decode-exact` tries `fn-record-decode-exact` first, so
   `fn-store-frame-value-in-buffer` answers what `fn-store-decode-records`
   answered, modulo the attachment, as `records-concrete` already argues.
5. **The article scan** (`books/article-stobj.lisp`): the guards of
   `fn-ars-parse-lines` and `fn-ars-parse` (the reference verifies its
   own in `article-work`), and `fn-ars-parse-is-article-parse`: `(equal
   (fn-ars-parse fn-octets) (fn-article-parse (fn-octets-list fn-octets)))`,
   by `fn-ars-next-line` = `fn-article-next-line` on `(nthcdr i list)` and
   `fn-ars-body-crlfp` = `fn-article-body-crlfp` on the slice, under the
   induction of `fn-article-parse-lines`.

The teeth on the spike are the evaluation witnesses of
`tests/acl2/records-stobj-tests.lisp`: on a schema-1 record and a legacy
record with a 3,000-octet payload and two groups, the buffer path writes
exactly the list model's frame bytes and reads the record back; the
encoder and the decoder alone agree with `fn-record-encode-impl` and
`fn-record-decode-exact-impl` on those records, on three-octet nonsense,
on nil and on a truncated record; a flipped trailer octet is `:integrity`,
a cut frame `:truncated`, a well-formed frame of non-record octets hands
them back for the list codec. A pass is agreement by evaluation, not the
proof.

## 3. Wave C: the long-lived copy

The census (`rep-heap-2026-09-25.md`) settled the memory question: the
payload is held once (records, archive, views and trie share the one
octet list), 16 bytes per octet, and everything else per article is
small. This lane measured the constant again at the sizes the brief asks
(§5) and did not move the representation of the long-lived copy, for a
reason the reader census below makes exact; the spike's finding is the
cost of moving it, which is what dev must plan.

**What reads the payload of a stored article, on the executable path.**
The record's payload (`fn-record-payload`) and the article body
(`fn-article-payload`, the same object) are read by: the commit's
verdict (`fn-stx-verdict-of-octets`, owner-commit-carried:193) and its
completion test (`equal` of the payload with `fn-own-sub-stored-octets`,
:261); the served reader's ARTICLE/HEAD/BODY arm and the overview
(`fn-nov-overview`, nntp-responses:959, `fn-article-parse` of the payload
per OVER line), HDR (:1470), the feed relay (`fn-peer-relayed-octets`);
recovery's replay (`fn-replay-apply-record`, replay.lisp:517,
`fn-record-p` on every record, then `fn-node-prepare` with the payload);
and the recognizers `fn-record-p`, `fn-rcon-record-p`, `fn-articlep`
(`fn-record-payloadp`, `fn-octet-listp` at the leaves). Every one of
these is a function of the logical value in the owner, reached from a
host entry through the served, commit or replay chains.

**Why a value representation cannot do it.** An ACL2 value in the
payload slot that is not an octet list (a string, an arena reference) is
refused by `fn-record-p`, `fn-articlep` and every theorem that concludes
`fn-cbor-octet-listp` of a payload; widening the two leaf recognizers
(`fn-record-payloadp` in records-shape, the article payload's
`fn-octet-listp` in acceptance) is a logic change to the model at the
root of the tree (`certify_books.py --affected-by books/records-shape`:
624 roots) whose breakage is every theorem that reads a payload as a
list. A leaf `mbe` cannot help: its `:exec` must equal the `:logic` on
the same value, and there is no compact executable for a cons list. This
is the design's own conclusion (boundary 10: the owner as an abstract
stobj with the arena as its `:exec` and the host-called entries as
exports, each export a twin over the struct), and the reader census
above is its export list: the exec twins of the commit's finish, the
served read (ARTICLE/HEAD/BODY/OVER/HDR and the relay), the replay open,
and the recognizers, plus the prepare that appends to the arena. The
served read is the large one: the response builders take the payload
list at the arms named above, five to eight functions below
`fn-scar-ocfg-read-tls-prefix`.

**What it buys, measured (§5).** With the constant measured here at 2 KiB
and 32 KiB, the pessimistic sentence is at the end of §5. The buffer
stobj of this lane is the arena's representation (one resizable byte
array, `fn-octets-reserve` and `fn-octets-append-octet` are the arena's
append); what boundary 10 adds is the owner stobj that holds it and the
offset/length pair in each record's payload slot.

**The freeze items** (design §5, wave C). Not done on the spike, and the
reason is the same closure: each is a leaf `mbe` in `records-shape`
(`fn-record-octet-stringp`, `fn-record-metadata-bytes-p`), `acceptance-alloc`
(`fn-octet-listp`), `msgid-index` (`fn-midx-lookup`) or `owner`
(`fn-own-sub-*`), and each recertifies the tree (1:44 at 16 jobs on hbox)
without moving a runtime number here: the recognizer's conversions are
already off the POST path through the `fn-rcon-` twins, the trie lookup
through `fn-mxc-`, the intent digest through `fn-icar-`. The exact edits:
`fn-record-octet-stringp` gets `(mbe :logic <its definition> :exec (stringp
text))` with the guard obligation `fn-rcon-octet-stringp-is-stringp`
moved from `records-concrete` into `records-shape` before it;
`fn-record-metadata-bytes-p` likewise with `(and (stringp text) (<= 1
(length text)) (<= (length text) *fn-record-max-metadata*))`;
`fn-midx-lookup` with `fn-mxc-lookup`'s walk, its keystone moved into
`msgid-index`. They belong in the coordinator's next freeze, one
recertification for all of them.

## 4. Method

Images: hbox, the developer image built by `tools/build_native_host.sh`
under `swarm-build` from each tree with the rep-heap census hook spliced
before the trust tag (inert unless `FN_CENSUS_LOAD` is set) and a
profiling twin with the served-path-cost sprof hook; the default-profile
closure certified in place from `/tank/fn/certcache` (w28
`acl2-literal-4g`) before each build. Base = `spike/mega` at `0e2173ab`
(`base-tree`, `certify-20260925T083523Z-2922069`, image sha256 in
`spike-representation-2026-09-25/images.sha256`); after = this lane at
`3715d494` (`after-tree`; `e7cd2d2b` adds only `article-stobj`, which no
host line calls). Driver: `tools/rep_measure.py` (this lane): one store
under the default profile with `--max-article-octets` at twice the
article, one owner, N POSTs of about L octets on one reader connection
(POST wall per article), VmRSS after the load and the census's live
dynamic space after `(gc :full t)`, then STAT, ARTICLE (the whole reply
read) and OVER (after GROUP) for 16 identifiers spread over the store on
a fresh connection, then the owner stopped and started again on the same
store (the load time at N is the time to its LISTENING line; VmRSS after
it). Scratch `/tank/fn/scratch/spike-representation/`, work directories
on `/dev/shm`, every run under the measurement user's session on the
same box; rounds alternated base, after. Profiles: `prof_post2.py` (the
rep-records-2 `prof_post.py` with the article size), SBCL sprof in CPU
mode at 1 ms over the last K POSTs.

## 5. Numbers

Three alternated rounds (base, after) per cell; medians of the 16 samples
per run, milliseconds; the live heap is the dynamic space after
`(gc :full t)`. Round 3 at 32 KiB ran under another tenant's load on the
box (both images, 43 to 44 ms per POST against 22 to 24 in rounds 1 and 2),
and is kept in the table because the alternation keeps the comparison
fair; the figures quoted in prose are rounds 1 and 2.

**N = 120.**

| Cell | POST median (all / last quarter) | load s | RSS after load MiB | live heap after GC MB | STAT | ARTICLE | OVER | reopen s | RSS after reopen MiB |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| base, 2 KiB, r1/r2/r3 | 1.88/1.89, 1.93/1.95, 1.93/1.92 | 0.25, 0.25, 0.26 | 381 | 259.5 | 0.18, 0.18, 0.09 | 2.25, 2.55, 2.51 | 0.34, 0.50, 0.37 | 1.53, 1.53, 1.66 | 402 |
| after, 2 KiB, r1/r2/r3 | 1.80/1.79, 1.84/1.85, 1.98/1.94 | 0.23, 0.24, 0.26 | 384 | 260.2 | 0.09, 0.09, 0.20 | 2.53, 2.41, 2.57 | 0.43, 0.34, 0.35 | 1.57, 1.57, 1.69 | 385 |
| base, 32 KiB, r1/r2/r3 | 23.9/23.9, 23.7/23.6, 44.5/42.2 | 3.00, 2.97, 5.02 | 461 | 319.0 | 0.10, 0.11, 0.31 | 34.9, 35.8, 88.9 | 1.56, 1.39, 2.94 | 9.19, 9.36, 12.4 | 691 |
| after, 32 KiB, r1/r2/r3 | 22.4/22.5, 24.6/24.8, 43.1/43.3 | 2.79, 3.06, 5.11 | 449 | 319.3 | 0.09, 0.09, 0.28 | 35.5, 36.4, 93.4 | 1.58, 1.44, 3.00 | 9.36, 9.84, 13.6 | 446 |

Read from it:

- **POST wall is unchanged within noise**: 1.8 to 1.9 ms at 2 KiB and 22
  to 25 ms at 32 KiB on both images. The transient copies this lane
  removed (the record encoding, the frame, the three payload lists at the
  host) are not where a 32 KiB POST spends its 23 ms; the profiles below
  say where.
- **The live heap per article is the same on both images** (the payload
  is the logical record's list on both), and the after image's floor is
  0.7 MB higher (the buffer's array and the record-value table). RSS after
  the load is within 12 MiB.
- **The owner's reopen at 32 KiB leaves 245 MiB less RSS on the after
  image** (446 against 691 MiB at N = 120): recovery no longer conses the
  file as a list and slices it three times per record (about four list
  copies of 32 KiB, 16 bytes per octet, per article); the reopen time is
  the same (9.2 to 9.8 s), because it is the replay, not the decode.
- **ARTICLE of a 32 KiB article costs 35 ms** on both images, fifteen
  times a POST's 2.3 ms at 2 KiB and more than the POST of the same
  article; STAT is 0.1 ms and OVER 1.5 ms. That is the served read
  building its reply over the payload list (the response arm at
  nntp-responses:959 and the retrieval arm, then the output list to the
  socket), and it is the largest per-command number this lane measured:
  the first thing the wave C export list should move.

**Where a POST spends (N = 120, SBCL sprof CPU mode at 1 ms over the last
48 POSTs, three rounds each; `post-*-flat.txt`).** At 32 KiB, 1,126 samples
on base and 1,081 on after (23.5 ms and 22.5 ms per POST). The shares are
the same on both images:

| Cost | base 32 KiB (self / cumulative) | after 32 KiB | Where |
| --- | ---: | ---: | --- |
| `fn-record-payloadp` (the list walk of the payload: `fn-cbor-octet-listp`, `fn-cbor-octetp`, `fn-cbor-at-mostp` under it) | 9.9% / 30.6% | 10.1% / 30.9% | the concrete record recognizer `fn-rcon-record-p` kept the reference payload walk (boundary 1), and the commit recognises the same record at its seek, its completion gates and its finish, so the same 32 KiB list is walked several times per POST |
| the session machine's feed, `fn-scar-feed-counted` / `fn-scar-feed-byte` / `fn-wire-feed-byte` (one step per octet of the article, `fn-ag-cdr`, `fn-wire-ag-cdr`) | 41.3% cumulative; `fn-ag-cdr` 5.8%, `fn-wire-ag-cdr` 5.4% self | 44.6%; 6.9%, 4.8% | `fn-owner-chunk` hands the socket's octets to `fn-scar-ocfg-read-tls-prefix` as a list and the POST arm accumulates the article byte by byte |
| SHA-256 on the word stobj (`fn-shs-rounds`, `-extend`) | 3.6% | 3.6% | the intent and subject identities, the frame trailer |
| `sb-kernel:vector-to-list` (the host's `fnn-octet-list`) | 3.6% cumulative | under 1% | the chunk's list on both; the record and frame copies only on base |

At 2 KiB (92 and 84 samples, 2.1 and 1.9 ms per POST) the same two
items lead (`fn-record-payloadp` 27% / 21%, the feed 21% / 38%), with the
store's I/O (`fsync`, `rename`) the rest. So wave B moved what it
promised, the transient copies, and they were 4 to 5% of a POST; the
POST's cost at large articles is two things wave B does not touch: the
payload recognised several times per POST from the same list, and the
served machine fed one octet at a time from a list. The first has a
sound, ACL2-owned fix with no proof obligation, measured below as the
memo image; the second is the wave C item "the submission holds a buffer
slice" (the article scan of `article-stobj` is its parser).

**N = 1,000, one round each, with the census.**

| Cell | POST median | load s | RSS after load MiB | live heap after GC MB | STAT | ARTICLE | OVER | reopen s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| base, 2 KiB | 2.07 | 2.1 | 418 | 291.3 | 0.08 | 2.27 | 0.63 | 454 |
| after, 2 KiB | 1.99 | 2.1 | 419 | 292.1 | 0.09 | 2.26 | 0.59 | 485 |
| base, 32 KiB | 24.4 | 25.4 | 903 | 783.5 | 0.08 | 34.2 | 1.70 | 912 |
| after, 32 KiB | 22.6 | 23.4 | 955 | 783.9 | 0.08 | 33.7 | 1.75 | 933 |

- **The live slope per article, from N = 120 to N = 1,000 (880
  articles):** 2 KiB (2,027 octets): 36.3 KB per article on after, 36.2 on
  base; 32 KiB (32,691 octets): 528 KB per article on both. The payload
  list is 16 octets per octet (32.4 KB and 523 KB); the rest, 4 to 5 KB
  per article, is the record's other fields, the archive entry, the trie
  and the group bucket. Exponent 1.00 in N between the two points at both
  sizes; the constant is 16 L + 4.5 KB.
- **The owner's open is superlinear in N.** 1.5 s at N = 120 and 454 s at
  N = 1,000 for 2 KiB articles (8.3 times the articles, 300 times the
  time); 9.3 s and 912 s at 32 KiB. At N = 10,000 the reopen did not
  produce its LISTENING line within 3,600 s on either image at 2 KiB (the
  first plan's runs), and the second plan's single 2 KiB reopen under a
  10,800 s deadline is reported below if it finished. This is D27's
  "whole-history replay at open" item, and it is the load-time number the
  brief asked for: a quadratic fit through the two points puts the 2 KiB
  open at N = 10,000 near 45,000 s. The replay (`fn-cpr-replay`,
  `fn-cpo-open-observed`, the recognisers on every record) is the same on
  both images; the buffer changed only the decode, which is why the two
  images agree.
**N = 10,000, two rounds each, no census (the census walk does not survive
160 million conses), the reopen separate (below).**

| Cell | POST median (all / first quarter / last quarter) | load s | RSS after load MiB | STAT | ARTICLE | OVER |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| base, 2 KiB, r1/r2 | 4.01 / 2.38 / 5.59, 3.79 / 2.35 / 5.18 | 41.4, 39.7 | 737, 744 | 0.10, 0.08 | 2.31, 2.25 | 3.68, 3.56 |
| after, 2 KiB, r1/r2 | 3.74 / 2.22 / 6.93, 3.75 / 2.22 / 5.29 | 45.1, 38.8 | 960, 960 | 0.09, 0.10 | 2.27, 2.37 | 3.68, 3.60 |
| base, 32 KiB, r1/r2 | 28.0 / 24.7 / 29.1, 27.2 / 24.6 / 28.6 | 297, 291 | 5,446, 5,446 | 0.08, 0.08 | 35.3, 33.2 | 4.92, 4.77 |
| after, 32 KiB, r1/r2 | 26.3 / 22.8 / 27.5, 25.6 / 23.1 / 27.4 | 275, 272 | 5,499, 5,519 | 0.08, 0.10 | 34.8, 33.4 | 4.83, 4.99 |

Profiles of the last 200 POSTs at N = 10,000 (`post-*-n10000-*-flat.txt`;
5,947 and 5,601 samples at 32 KiB, 1,213 and 1,209 at 2 KiB):

- **A POST's cost grows with N.** At 2 KiB the last quarter costs 2.2 to
  2.9 times the first (5.2 to 6.9 ms against 2.2 to 2.4), and the profile
  of the last 200 is not the payload's: `fn-index-build` 29 to 33%
  cumulative (`fn-gidx-build-entries`, `fn-gidx-put`: the group index
  rebuilt from the whole store at each commit), `fn-ag-car` 17 to 18%
  self, `fn-retain-obligation-ids` 8%, `string=`/`equal` 7%: whole-store
  walks per commit, O(N) each, so the load is O(N^2) (38.8 to 45.1 s for
  10,000 against 2.1 s for 1,000: 19 to 21 times the time for 10 times
  the articles). At 32 KiB the same walks are the 4 ms between the first
  and last quarters, under the payload's 23 ms.
- **The payload's two costs are unchanged at N = 10,000** (32 KiB:
  `fn-record-payloadp` 24% cumulative, the feed 35% on both images), and
  wave B's removals show as the 6% fewer samples on after (5,601 against
  5,947) and 5 to 8% less load time.
- **RSS after load agrees with the census's live slope.** At 32 KiB:
  (5,446 − 380) MiB over 10,000 articles is 531 KB per article on base
  (528 KB by the census at N ≤ 1,000); at 2 KiB, 36.5 KB (36.3). The after
  image holds 220 MiB more at 2 KiB and 60 MiB more at 32 KiB after the
  load; the live heap is the same at every censused N, so this is SBCL's
  collection headroom at the moment of the read (64 MiB nursery, but the
  pause pattern differs when a POST conses less), not data.
- **ARTICLE is O(L), not O(N)**: 33 to 35 ms for a 32 KiB article at
  N = 120, 1,000 and 10,000; 2.3 ms at 2 KiB. **OVER grows with N**: 0.3
  to 0.6 ms at N ≤ 1,000, 3.6 to 5.0 ms at 10,000 (the numbering walk).

**The pessimistic memory sentence.** The owner's live heap is 250 MB plus
(16 L + 4.5 KB) per retained article, exponent 1 in N and 1 in L,
measured at L = 2,027 and 32,691 octets and N = 120 and 1,000 by the
census after a full GC, and agreeing within 1% with VmRSS at N = 10,000
(the 4.5 KB is the record's other fields, the archive entry, the trie and
the group bucket; the 16 L is the payload held once as an octet list on
both images, which is what boundary 10 changes to L + 16 plus the same
4.5 KB). At N = 10,000 and L = 32 KiB that is 5.3 GB on this image and
would be 0.36 GB after boundary 10.

**The memo image** (after plus `(memoize 'fn-record-payloadp)` in
`host/native/build.lisp`, commit `6cedc7df`): filled in from `m-memo-*`
and `post-memo-*` below.

## 6. Logs (planning/evidence/spike-representation-2026-09-25/)

`images.sha256` (the three trees' launcher, core and build-log digests;
base = `0e2173ab`, after = `3715d494`, memo = `6cedc7df`), `cert-logs.txt`
(the closure certification tails), `m-<label>-n<N>-o<L>-r<round>.json`
(every measured run: rounds 1 to 3 at N = 120 with the census, round 1 at
N = 1,000 with the census, rounds 1 and 2 at N = 10,000 without it,
rounds 7 to 9 the memo comparison), `post-<label>-n<N>-o<L>-r<round>-flat.txt`
and `-graph.txt` (the sprof profiles), `run-rounds*.out` (the drivers'
console, including the first plan's refusals and the memo builds that did
not build), the scripts (`hbox-setup.sh`, `hbox-build.sh`,
`hbox-measure.sh`, `hbox-prof.sh`, `run-rounds2.sh`, `prof_post2.py`).
