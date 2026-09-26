# Width producers 2: the producer ceiling, frontier format 3, the served article gate (2026-09-26)

Lane `lane/width-producers-2` (Opus 5.5), the continuation of width-boundary
(PRF-123) under the Fable mandate §5.5 and §12 packets 1 and 6, from dev
23eed13e.  Ids: PRF-126, STO-018, SCN-072, PKT-244.

## What a node can now do

- **Any producer width fits R without moving R.**  A record whose charge
  fits u32 encodes within `fn-record-encoded-octets-ceiling` of its own
  payload length and group count -- the 1 083-octet ceiling every saved
  profile's R was checked against -- whatever the width of its sequence,
  transaction ID, generation and stamp.  The ceiling counts five-octet heads
  for the schema octet (1 octet), the group count (1 below 24 groups, else at
  most 3), the Message-ID (2), the three metadata strings (3 each) and every
  group name (3): at least 17 octets it never uses.  Four eight-octet heads
  need 16.  So the frontier-3 and stamp-2106 migrations cost no profile field
  and no saved-profile translation; only the charge must stay within u32.
  This replaces the plan in the bounds-p6 record ("each widening of a
  producer moves R's ceiling by 4 octets per field").
- **The frontier frame reads and writes u64 (frontier format 3).**  Below
  2^32 the frame is byte-for-byte the format-2 frame; from 2^32 to 2^64 - 1
  the payload is the eight-octet CBOR head, canonical only above 2^32 - 1.
  Every frame the format-2 reader accepts, the format-3 reader reads to the
  same transaction ID, so no store's frontier file is rewritten.  An image
  before format 3 refuses a wide frame by its payload bound.
- **The served POST refuses an article past the remaining history, and the
  store reopens** (natively, SCN-072, below).  The same article on the image
  before the article gate is accepted and leaves the store unopenable.
- **The Python BP and owner clients ask ACL2's article verdict** at the
  article's own counts (`fn-store-sn-article-verdict`): tools/run_owner.py
  `Owner.attempt`, tools/run_bp_ingress.py (`Acl2BpIngress.article_verdict`),
  tools/run_bp_receive.py.  No Python computes the figure or the comparison.

What it cannot do yet: allocate a transaction ID past 2^32 - 1 or stamp past
2^32 s.  Following both values past the codec found five u32 readers (PKT-244,
"Not done").  The allocator's successor and the stamp producer are therefore
unchanged; widening them now would let the node write a store its own open
and checkpoint refuse.

## Assurance chain

native entry (`operator run` served POST; developer `store post`; BP ingress)
-> the POST boundary `fn-sbud-post-boundary` (charge u32) -> the article
verdict before reservation (`fn-store-sn-article-verdict`, host/store-node-host;
the owner's `fn-owner-prepare` passes `fn-sbud-article-budget-for` to
`fn-pcar-sbud-prepare`, equal to `fn-sbud-prepare` by
`fn-pcar-sbud-prepare-is-sbud-prepare`) -> the producer `fn-sn-article-record`
-> the prepare `fn-sn-prepare` (host `fn-spc-prepare`, equal by
`fn-spc-prepare-equals-specification-under-relation`) -> the record codec
`fn-record-encode` (attached `fn-rcon-record-encode-impl`, equal to
`fn-record-encode-impl` by `fn-rcon-record-encode-impl-is-record-encode-impl`)
-> the behavioural theorems below -> observed: the served gate.  The
maintained relation is PRF-123's `fn-sf-statep` (u32 frontier, established
at open, preserved by every file transition); PRF-126 needs nothing of it
beyond the charge.

## Theorems (PRF-126)

- KEYSTONE `fn-record-encode-producer-length-bound` (books/records-seam, a
  seam constraint): `(implies (fn-record-uint32p (fn-record-charge record))
  (<= (len (fn-record-encode record)) (fn-record-encoded-octets-ceiling (len
  (fn-record-payload record)) (len (fn-record-groups record)))))`.
  Discharged by `fn-record-impl-encode-producer-length-bound`
  (books/records-canonicality, 0.04 s in the REPL) and by both attachments
  (records-attach, records-attach-concrete).
- `fn-bs-profile-admits-every-producer-record` (books/record-width-producers):
  admitted profile, charge u32, payload within A, groups within G -> the
  encoding within R.  PRF-086's `fn-bs-profile-admits-every-article-record`
  is the narrow case and keeps its statement.
- `fn-sn-prepare-stages-an-article-record-within-its-ceiling`: a record
  `fn-sn-prepare` stages from `fn-sn-article-record` with a u32 charge is
  within the ceiling of its own payload and groups.
  `fn-bpi-staged-record-fits-the-producer-ceiling`: the same for the BP
  ingress producer (`fn-bpi-policy-p`).  `fn-sn-article-record-charge-and-groups`:
  the producer's charge, groups, payload and stamp are its inputs'.
- KEYSTONES `fn-sbud-article-verdict-keeps-history-at-producer-width` and
  `fn-sbud-prepare-under-article-budget-keeps-history-at-producer-width`
  (books/store-budget-article): the packet-1 history keystones with the
  narrowness premise replaced by the charge premise.  Host lines:
  host/store-node-host.lisp `fn-store-sn-article-verdict` (called by
  host/native/io.lisp `fnn-command-post` before the reservation);
  host/owner-host.lisp `fn-owner-prepare` / `fn-owner-prepare-buffer`.
- KEYSTONE `fn-bs-frontier-impl-round-trip` (books/byte-store-frame, now over
  n <= 2^64 - 1) and KEYSTONE `fn-bs-frontier-decode-extends-format-2`:
  `(implies (fn-bs-frontier-v2-decode octets) (equal (fn-bs-frontier-decode-impl
  octets) (fn-bs-frontier-v2-decode octets)))`, where `fn-bs-frontier-v2-decode`
  is the reader of dev 23eed13e verbatim.  Host line: host/store-host.lisp
  `fn-store-metadata-frontier-decode` / `-frame` through the scan seam's
  `fn-bs-frontier-decode` / `-encode`, attached to these (the seam's round
  trip constraint is now stated over u64).  `fn-bs-frontier-encode-impl-octets`;
  `fn-bs-k0-host-frontier-frame-is-concrete-codec` (the K0 allocator entry)
  now over u64.  `fn-bs-frontier-next` is unchanged (successor stops at
  2^32 - 1).
- PRF-123's theorems are unchanged in statement and proof.

## Teeth

- tests/acl2/record-width-producers-tests: the tightest non-degenerate
  record -- sequence, txid, generation, stamp 2^32 (schema 2), charge
  2^32 - 1, 250-octet Message-ID, three 256-octet metadata strings, a
  65 536-octet payload -- encodes 66 618 octets against the ceiling 66 619
  with no group, and 66 877 against 66 880 with one 256-octet group.  The
  charge hypothesis, affirmatively: the same records at charge 2^32 encode
  66 622 > 66 619 and 66 881 > 66 880 (the latter is the bounds-p6 record's
  "one past R" vector), plus a `must-fail` of the bound without it.  The
  staged fixture record (reachable) within its ceiling; the prepare stages a
  charge of 2^64 - 1 in the 2^65-capacity store (the prepare does not bound
  the charge); a `must-fail` without the prepare hypothesis; the wide G = 1
  record under the saved scale profile within R; the BP fixture record.
- tests/acl2/store-budget-article-tests: packet 1's record moved to schema 2
  (four fields at 2^32) is admitted at H - 138 251 and stays within H; the
  charge hypothesis affirmatively: the tight record with every field at 2^32
  including the charge encodes 66 622 > its figure 66 619, the verdict admits
  it at H - 66 619 and the total is H + 3; a `must-fail`.
- tests/acl2/byte-store-frame-tests: round trip at 2^32 - 1, 2^32 and
  2^64 - 1; the separating witness (the 2^32 frame: nine payload octets,
  four longer than the 2^32 - 1 frame; the v2 reader answers NIL, format 3
  reads 2^32); 2^64 has no frame and the round trip without its width
  hypothesis is a `must-fail`; a nine-octet head holding 5 (not canonical)
  is refused by both readers; the extension at the init frame, at 2 and at
  2^32 - 1, and its hypothesis: at the 2^32 frame the readers differ, with a
  `must-fail`; `fn-bs-frontier-next` still NIL at 2^32 - 1.

## Certification

persvati, w25, 2 jobs, 300 s per book.

- run-20260926T010201Z-edf7 at 857c2a79, `--affected-by` records-seam,
  records-canonicality, byte-store-frame, record-width-producers,
  store-budget-article: manifest
  `planning/evidence/manifests/certify-20260926T010233Z-3422722.json`
  (sha256 prefix 256373a6962ad78e), 722 books, 565 certified: 562 passed,
  3 failed -- the lane's three test books (a `defconst` that evaluated the
  frame digest's attachment; two `must-fail` forms that searched past the
  300 s timeout; one scale-profile witness with a payload above A).  Every
  changed book and every book above the record seam passed.  Changed books:
  records-canonicality 7.4 s, byte-store-scan 5.5 s,
  byte-store-record-provenance-node 2.9 s, byte-store-frame 2.2 s,
  record-width-producers 2.1 s, store-budget-article 1.3 s, records-seam
  0.4 s.  The one book over 10 s is books/owner-invariants (12.9 s), a
  baseline book this lane does not change.
- run-20260926T011811Z-b295 at 9104f415 (the three test books as roots):
  manifest `planning/evidence/manifests/certify-20260926T011837Z-3569115.json`
  (sha256 prefix 65f033fb158ae474), passed: byte-store-frame-tests 1.0 s,
  record-width-producers-tests 1.5 s, store-budget-article-tests 1.5 s.
- The seam change moves the include closure of every book above it; the first
  manifest is added to PRF-032's, PRF-086's, PRF-115's and PRF-123's evidence
  so `tools/certified_claims.py` finds their books certified at these bytes.
- Proof development: persvati `proof_repl` sessions over records-canonicality
  (the keystone, 0.04 s), byte-store-frame (the frontier section) and
  records-stamp (the reverted stamp widening), and the three test books
  loaded end to end before run 2.

## Native (hbox, SCN-072)

Scratch /tank/fn/scratch/width-producers-2.  The served budget call
(host/owner-host.lisp `fn-owner-prepare` -> `fn-sbud-article-budget-for`) and
its books are unchanged between a9ed4dc2 and dev 23eed13e (`git diff
a9ed4dc2 23eed13e` of the host touches only the key-statement rows and one
developer selector) and are not changed by this lane, so the gate runs on the
a9ed4dc2 developer image
(/tank/fn/scratch/bounds-p6/tree-a9ed4dc2/build/fn-host-developer, core
sha256 ca2b54cb2dacb378...).  gate-served.sh fe16f9bf... (in-tree copy
planning/evidence/width-producers-2-gate-served.sh), nntp_post.py 9a45c2fd...
(planning/evidence/width-producers-2-nntp-post.py).  Profile T 4, H 250 000,
R 196 608, A 150 000, G 8; the node under `operator run` on 127.0.0.1:11297
(systemd-run --user, MemoryMax 24G).

- a9ed4dc2 (gate-served.log 4de4b106...): the first 148 112-octet POST
  answers 240; the second `441 posting failed; the store has no capacity for
  this article`; one transaction file (148 613 octets); `store recover`
  exit 0, `recovered transactions=1 articles=1`.
- bbf52159 (the image before the gate, core e6640102...;
  gate-served-old.sh c72ca96b..., gate-served-old.log 96863c7b...): both
  POSTs answer 240, 297 226 record octets are committed against H 250 000,
  and the reopen refuses `transaction recovery input exceeds configured
  bound` (exit 4).  The defect of packet 1, in the served path.

No image was built for this lane's bytes: the lane changes no host decision
on the served path (the frontier frame for values below 2^32 is byte-
identical, and the successor is unchanged), and the frontier native case of
the brief (commit 2^32 - 1 and 2^32 and reopen) is not reachable until
PKT-244.

## Not done (PKT-244)

1. **Transaction IDs past 2^32 - 1.**  The frame carries them; the
   allocator's successor does not issue them, because five readers are u32:
   (a) the file machine `fn-sf-statep` / `*fn-sf-max-uint*` and the K0
   recovery books that carry `(fn-record-uint32p f)`; (b) the observed open
   `fn-sn-open-observed` / `fn-sn-observed-historyp` (books/store-observed)
   and store-open-bridge; (c) the checkpoint: `fn-checkpointp`,
   `fn-checkpoint-capture` and `-restore` refuse a frontier past u32, and the
   codec's TREE naturals (`fn-cpc-treep`, `*fn-cbor-max-uint*`) cannot carry a
   txid past it, so a store past 2^32 could be neither checkpointed nor
   reopened from its checkpoint; (d) the consumer candidate bound
   `fn-csi-candidate-sequence-below-max`; (e) compaction
   `fn-cverb-pack-decision-capture-succeeds`.  A first cut of this lane
   widened (a) and was reverted when (b)-(e) were found: widening the
   successor before its readers would let a node write a store its own open
   refuses.  Order: the checkpoint codec's naturals to u64 (a schema bump with
   a translation keystone, as records schema 2), then the model with the
   frontier u64, then `fn-bs-frontier-next`, then the developer-twin native
   case (frontier file set to 2^32 - 2, commit 2^32 - 1 and 2^32, reopen).
2. **The stamp past 2106.**  `fn-record-stamp-of-observation` still answers
   `:clock-unusable` from 2^32 s.  The widened producer (drop the test; the
   u64 bound needs `(<= (floor ms 1000) ms)`, proved with arithmetic-5 scoped
   to one local encapsulate) was written and proved in the REPL and then
   reverted: a checkpoint's TREE naturals carry each article's stamp, so the
   same codec migration comes first.
3. **Kind 4 and peer-carried producers** are checked against R on their
   actual bytes (host/native/owner.lisp `fn-owner-signed-event-boundary`,
   `fn-owner-peer-carried-event`) and not charged `fn-sbud-article-figure`
   before reservation.  Not started.
4. `host/bp-ingress-host.lisp` `fn-bpi-host-article-verdict` composes the
   ingress parse and group map in host Lisp to get the counts it hands to
   the ACL2 verdict; it should be one ACL2 function with a theorem equating
   its counts to the record `fn-bpi-ingress-prepare` stages.  tools/run_bp_receive.py
   keeps two Python size checks (65 538 and `max_payload_bytes`).
5. The Python owner client's article-verdict path is not exercised on the
   laptop (its host file does not load there without certificates:
   `fn-rcon-ocfg-io` undefined); the BP clients' tests pass (29 + 20,
   `python3 -m unittest tests.test_bp_ingress_host tests.test_bp_receive
   tests.test_bp_receive_faults tests.test_media`), with the unaffordable
   answer mocked, not produced by ACL2.

Harvested by assurance-triage (2026-09-26) as the scenario catalog's evidence log: [`gate-served.log`](width-producers-2-2026-09-26/gate-served.log), gate-served.log, copied from hbox /tank/fn/scratch/width-producers-2/, sha256 `4de4b1062565a378a1138fa706e9f2771bc6255d92797bfa2022a4150906fac7`.
