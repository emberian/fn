# Representation: what the executable path spends on octet lists, and the boundaries to move, 2026-09-25

Lane `lane/representation`, from dev `67b028c7`. This is the design; the
first boundary it ranks highest is landed in the same lane
(`planning/evidence/representation-2026-09-25.md`).

The rule this design works under (AGENTS.md, docs/proofs.md step 4): the
logical model stays over octet lists and ACL2 strings, and every theorem
stated over it stays true. A concrete representation enters only through a
named correspondence theorem or an `mbe` guard obligation, and the function
the host calls is the one the theorem is about.

## 1. Where the POST path spends on octet lists today

Source: the latest after-image profile, `advance-projection-2026-09-24/`
`post-after-n120-r1-graph.txt` (hbox, SBCL sprof CPU mode at 1 ms, 48 POSTs
from N = 72 to 120, 198 samples, so 4.1 ms per POST on that box and run;
the shares are the stable figure, the absolute rate swings with load). Every
whole-state recognizer is already carried off this path; what remains is
per-article work, and almost all of it is work on octet lists or on strings
converted to octet lists.

| Cost | Share of POST CPU | Where | Exponent, from the definitions |
| --- | ---: | --- | --- |
| SHA-256 over octet lists, `fn-sha256-of-octets` (books/sha256.lisp) under the attached `fn-frame-digest` | 33% | `fn-own-feed-intent-id` 17% (computed in `fn-own-submission-intent-result`, books/owner.lisp:1710, again in `fn-own-submission-intent-records`, :1732, which also calls the former, and again in `fn-own-submission-resolution-records`, :2021); host-direct `fn-id-subject-of-payload` 7%, `fn-frame-digest` 8% (frame trailers), `fn-id-obligation-of` 2% | O(L) per digest. The list cost is about four conses per message octet (`fn-sha256-pad` copies, `fn-sha256-firstn`/`-nthcdrx` slice each 64-octet block, the schedule is consed and reversed twice); the arithmetic cost is generic integer `ash`/`logior`/`logxor` on undeclared words (`ASH`, `SB-KERNEL:TWO-ARG-IOR` are the top self entries after the record conversions) |
| The record recognizer `fn-record-p` (books/records-shape.lisp) | 20% | `fn-store-event-sequence` 7%, `fn-store-event-txid` 7%, `fn-sn-record-bindsp` 3%, `fn-store-event-p` 2.5%, the prepare 0.5%; all under `fn-ccar-own-finish` (the commit, 20% of POST) and `fn-pcar-sbud-prepare`. Inside it `fn-record-metadata-bytes-p` is 13%, `fn-record-payloadp` 3%, `fn-record-msgidp` 1.5%, `fn-record-groupsp` 1% | O(M + P + G) per recognition with M the four text fields, P the payload, G the group names, and 2M + G conses: every string is converted to its char-code list (`fn-record-string-octets`: a `coerce` and one cons per character) twice, once for the domain test and once for the length. `fn-record-string-octets`/`-aux` are 27% of all samples (some from outside the recognizer: `fn-record-group-namep`, `fn-store-prov-post`) |
| The article body as an octet list in the archive, `fn-articlep` → `fn-octet-listp` | 0% on POST since advance-projection; it was 4% inside `fn-nntp-projectionp` | O(N·L) wherever `fn-article-listp` runs; carried off the served path, still the representation the trie, the reader commands and every recognizer see |
| Frame assembly, `fn-ag-append` in `fn-frame-protected`/`fn-frame-encode` | 2 to 4% | frame journal writes, `fn-owner-io` | O(L) conses per frame, one copy of the payload per frame |
| The host boundary `fnn-octet-list` (host/native/io.lisp:126, `(coerce octets 'list)`) | under 1% self (`SB-KERNEL:VECTOR-TO-LIST` 1%) | every `fnn-core`/`fnn-core-state` call that passes octets: the article payload (`fn-store-sn-prepare`, io.lisp:838), the Message-ID, the metadata strings, every stored record on recovery (:710, :722) | O(L) conses per call, one list per octet argument per command |

RSS after loading N articles on the same baseline (`base-n*.json`): 342 MiB
at N = 16, 408 at 50, 556 at 120 (the article of `msgid_measure.py` is 160
octets). That slope, 2.0 MiB per article, is not the article's octets (160
octets as a list is 2.5 KiB per copy). It is the owner's per-POST retained
state and SBCL's uncollected garbage; `rss_after_load_kib` reads `VmRSS`
without a full GC, so it bounds live data from above. The per-representation
memory figures below are therefore computed from the representations, not
read from RSS, and the RSS line is reported as an observation.

## 2. Candidate concrete representations in ACL2 8.7

**ACL2 strings for the text fields.** Message-ID, group names and the
three metadata fields are already ACL2 strings in the logical record. An
ACL2 character has a code in 0..255, so the octet-domain test the model
states over the converted list is `stringp`; the length bound is `length`
(O(1) on a simple string); an ASCII test is a walk by index with `char`
and `char-code`, no allocation. Memory: 1 byte per character plus a 16-byte
header, against 16 bytes per character for the list (an SBCL cons is two
words). This is the representation of the first boundary; its
correspondence theorems are hypothesis-free because the concrete tests are
total.

**A `stobj` byte array for payloads and frames.** A single-threaded object
with an `(unsigned-byte 8)` resizable array field, `(defstobj fn-octets
(buf :type (array (unsigned-byte 8) (0)) :resizable t))`, gives O(1)
`buf-i`/`update-buf-i` and 1 byte per octet. The list function's twin takes
the stobj and an index range; the correspondence theorem states that the
twin on a stobj whose array holds the list (`(equal (fn-octets-list st) xs)`)
equals the list function. That hypothesis is the representation invariant,
carried like the store relations (open establishes it, every mutator keeps
it). What it costs: every function between the host boundary and the leaf
must thread the stobj (ACL2 syntax: a stobj is an explicit formal and an
explicit return), so a payload stobj reaches `fn-record-payloadp` only
through twins of `fn-record-p` and its callers up to the host, or through an
`mbe` in `fn-record-payloadp` itself, which the leaf book's dependents
(records-shape: 4 direct includers, records-seam: 17, closure near the
whole tree) forbid a lane from doing. An `(unsigned-byte 8)` array as an
ordinary ACL2 value is not an option: ACL2 8.7 has no logical array type
other than the stobj array and `nth`/`update-nth` on lists.

**Abstract stobjs.** An abstract stobj (`defabsstobj`) exports the *list*
as its logical view and the concrete array as its `:exec`, with the
correspondence proved once as the stobj's `{:logic,:exec}` preservation
obligations. This is the form that keeps the logical model literally the
octet list while the host runs the array, and it is the honest form for the
payload when the callers are rewritten to take the stobj. It is a lane of
its own: the exported operations are the primitives (`nth`, `len`, `take`,
`nthcdr`, `append`) the codecs use, and each needs a `:exec` twin and a
correspondence proof.

**`mbe` with `:logic` the list definition and `:exec` the concrete one.**
Admissible wherever the guard implies the two agree, and ACL2 proves that as
part of guard verification. It is the right form *at the leaf*: an `mbe`
in `fn-record-octet-stringp` whose `:exec` is `(stringp text)` changes no
theorem statement (the logic is unchanged) and every dependent recertifies.
It cannot express a correspondence between two *different functions* the
host chooses between (a list function and a stobj twin with a different
signature), and it cannot be added to a function without recertifying its
closure. So: `mbe` for leaves the coordinator can afford to recertify at a
freeze; named correspondence theorems for twins a lane lands.

**`nth`/`update-nth` on lists versus array access.** `fn-sha256-nthx` on
the reversed schedule is at fixed offsets 1, 6, 14, 15 (a shallow walk, by
design); the rounds walk `ws`/`ks` by `cdr`. The list SHA-256 is not
quadratic; its constant is the conses per octet above and the generic
arithmetic. A stobj SHA-256 (`(array (unsigned-byte 32) (64))` schedule,
eight word fields, `(the (unsigned-byte 32) ...)` from guards) removes both.
The correspondence is the compression function's, round by round, block by
block: the largest proof in this list.

**The host boundary.** `fnn-octet-list` allocates one list per octet
argument per call. With a payload stobj the host would write octets into the
stobj array (`fnn-*` in raw Lisp filling `buf` from the socket buffer) and
call the ACL2 entry with the stobj: zero conses per octet at the boundary.
With strings for text fields the host already passes ACL2 strings for the
Message-ID and metadata (io.lisp:739, :763 convert names back and forth
through `fnn-string-octets`/`fnn-octets-string`; those two conversions per
group name are the next host-side item). Nothing on the host changes for
the first boundary: the record's strings are already strings.

## 3. Memory per article, by representation

Sizes per copy of a payload of L octets (SBCL x86-64): list 16 L bytes;
ACL2 string L + 16 bytes; stobj `(unsigned-byte 8)` array L + 16 bytes
(one array for all payloads, indexed by offset, if the store keeps a
single arena). At the measurement article (L = 160): 2.5 KiB versus 176 B.
At the record maximum (`*fn-record-max-payload*` = 32,768): 512 KiB versus
32 KiB per copy. Copies per article on the live owner, read from the
definitions: the store record's payload (`fn-record-payload` of the history
entry), the node's article body (`fn-article` in the acceptance state; the
view archive shares it, `fn-node-acceptance` is the same object), and, while
a POST is in flight, the submission's `fn-own-sub-octets` and the staged
pending record. So two long-lived copies per article: 32 L bytes as lists,
2 L + 32 as strings or arrays. At N = 120 with L = 160: 615 KiB in octet
lists, which is 0.3% of the measured RSS growth, which is why the RSS figure
above is not a representation figure. Extrapolated to N = 1000 with the
maximum payload: 1.0 GiB of octet-list payload copies against 64 MiB as
arrays; at N = 4096 (the scale profile's ceiling), 4.0 GiB against 256 MiB.
The 15 GB at N = 1000 in `m5-capacity-2026-09-24.md` is the 15 MB per
article slope of the old images (1.95 GB at N = 120), most of which the
carries have since removed (0.68 GB, then 0.56 GB at N = 120); what remains
of that slope is not the payload representation and is unexplained until a
heap census (`room`, or `sb-vm::instance-usage`) is taken on a loaded
owner. That census is the first measurement the next memory lane should
make.

## 4. The obligations, and the risk

Every theorem stated over the list model stays true: no definition in
records-shape, store-events, store-files, store-node, sha256 or frame
changes. The only new proof obligations are the correspondences:
`fn-concrete-X` equals `fn-X` on every input the guard admits, and the twin
chain from the host's call down to the leaf is equal to the reference chain
(the pattern of `owner-commit-carried`, `owner-prepare-carried`,
`owner-advance-carried`: each copy equal to its reference, hypothesis-free
where the concrete test is total, under the carried premise otherwise).
The risk is in the executed chain, not the logic: a twin the host does not
call is a sibling API (AGENTS.md assurance rule 1), and a leaf `mbe` that
recertifies the tree is a freeze the coordinator schedules, not a lane's
edit. A second risk is measurement: the shares are stable across runs and
the absolute milliseconds are not; every before/after figure is quoted as a
share of samples and as milliseconds on the same box in the same session.

## 5. The plan: every boundary the host calls, in the order of measured share

Mandate (D27, `planning/decisions.md`; AGENTS.md): octet lists are not an
acceptable runtime representation. This section is the launch list. Each
boundary names its concrete representation, the correspondence theorem's
statement, the files the lane owns, the dependents its bytes touch (direct
includers, from `include-book` lines, with the closure where it matters),
the memory per article after it, and whether it runs in parallel. Shares
are from the hbox after image of the first boundary
(`representation-2026-09-25/post-after-n120-r*-graph.txt`, N = 120) unless
another record is named. No lane widens a data cap (another lane owns the
profile fields and codec widths under D27); every twin keeps its reference's
`at-most` bounds and work counters, and a twin of a bounded parser restates
the work theorem over the twin with a correspondence to the list parser's
work value.

Two facts shape the order. First, on the POST path the octet-list cost is
now the digests (43 to 46%) and the transient path from the socket to the
record (recognise, encode, frame, write); the long-lived copies of an
article (the store record's payload and the node's article body) are
fields of the logical state and are 16 bytes per octet in every image until
the state itself has a concrete representation (boundary 10). Second, an
abstract stobj (`defabsstobj`) is the only ACL2 8.7 form in which a
concrete array is the executable and the octet list stays the logical view
with the correspondence proved once, so the payload boundaries (6 to 9)
share one stobj book that lands first.

### Wave A: now, in parallel (each owns disjoint files)

**Boundary 1, landed: the record recognizer's strings** (`lane/representation`,
`planning/evidence/representation-2026-09-25.md`). 21 to 22% of POST CPU
to 4 to 6% list recognitions + 2.6 to 3.1% concrete. Memory per article
unchanged (the conversions were transient).

**Boundary 2: the intent identity computed once** (`lane/intent-carried`).
- Share: `fn-own-feed-intent-id` 22 to 24% after boundary 1 (131 to 142
  samples per 48 POSTs), four SHA-256 digests of the payload per POST:
  `fn-own-submission-intent-result` directly and again inside
  `fn-own-submission-intent-records`, which digests once more itself
  (both in one host call, `host/owner-host.lisp` `fn-owner-submission-intent`
  lines 1016 to 1017), and `fn-own-submission-resolution-records`
  (`fn-owner-submission-resolution`, line 1029).
- Representation: not a representation move; the value carried. Step (a),
  the lane: `fn-icar-submission-intent`, one function returning the pair
  the host builds from the two calls, digesting once. Step (b), a freeze
  item: the digest as a field of the in-flight submission (`fn-own-sub-*`,
  books/owner.lisp, 9 direct includers, closure the whole owner half) set
  at `fn-owner-take`, so the resolution's digest is a read; then four
  digests become one, which is the identity itself.
- Theorem: `(equal (fn-icar-submission-intent o evidence generation txid)
  (cons (fn-own-submission-intent-result o evidence generation txid)
  (fn-own-submission-intent-records o evidence generation txid)))`, no
  hypothesis. For (b): `(implies (fn-own-relation o) (equal
  (fn-own-sub-intent-id (fn-own-inflight o)) (fn-own-feed-intent-id
  (fn-own-sub-msgid (fn-own-inflight o)) (fn-own-sub-octets (fn-own-inflight o)))))`,
  carried from take by `fn-own-step-preserves-relation`.
- Owns: `books/owner-intent-carried.lisp`, `tests/acl2/owner-intent-carried-tests.lisp`,
  `host/owner-host.lisp` lines 1016 to 1017 (the two calls become one).
  Dependents touched: none beyond the new roots and the host.
- Memory after: unchanged ((b) adds 32 octets per in-flight submission).
- Parallel: yes, with every other lane; its host lines are its own.
- Expected: two of the four digests gone with (a), about −11% of POST CPU;
  three of four with (b), about −17%.

**Boundary 3: SHA-256 on a word stobj** (`lane/sha256-words`).
- Share: all of `fn-frame-digest`, 43 to 46% after boundary 1 (254 to 278
  samples per 48 POSTs, unchanged by boundary 1), of which the intent
  identity is boundary 2's part; the rest is the host-direct subject and
  obligation identities (`fn-id-subject-of-payload`, `fn-id-obligation-of`,
  books/identity.lisp:201, :207) and the frame trailers (`fn-frame-trailer`,
  `host/owner-host.lisp` line 1894, `host/native/io.lisp` line 950). The
  list cost is `fn-sha256-pad`'s copy, `fn-sha256-firstn`/`-nthcdrx`
  slicing per block, the consed and twice-reversed schedule (about four
  conses per octet), and generic arithmetic on undeclared words (`ASH`,
  `SB-KERNEL:TWO-ARG-IOR`/`-XOR` in every flat profile).
- Representation: `(defstobj fn-shw (h :type (array (unsigned-byte 32) (8)))
  (w :type (array (unsigned-byte 32) (64))) (blk :type (array (unsigned-byte 8) (64))))`
  used under `with-local-stobj`: the message stays the octet list and is
  consumed by `cdr` into `blk` (no slicing, no padded copy: the final one or
  two blocks are emitted from the length), the schedule and the working
  variables are `(unsigned-byte 32)` array cells with `(the (unsigned-byte 32) ...)`
  from the guards, so SBCL compiles fixnum arithmetic. `fn-shw-sha256` has
  `fn-sha256`'s signature (octet list to 32-octet list), so it attaches.
- Theorem: `(equal (fn-shw-sha256 m) (fn-sha256 m))` for every `m`, through
  `fn-shw-compress-is-compress` (one block: the array rounds equal
  `fn-sha256-rounds` on the list schedule, by a per-round lemma indexed by
  t), `fn-shw-schedule-is-schedule` (`(nth t w)` equals `(nth t
  (fn-sha256-schedule ws16))`), and `fn-shw-final-blocks-are-pad` (the
  emitted tail equals the tail of `fn-sha256-pad`). Then
  `books/crypto-attach.lisp` re-proves its three `satisfies` theorems from
  the equation and attaches `fn-shw-sha256` to `fn-digest` and
  `fn-frame-digest` (lines 85 to 86); no constraint moves.
- Owns: `books/sha256-words.lisp`, `tests/acl2/sha256-words-tests.lisp`
  (the FIPS 180-4 vectors sha256's tests already use, the correspondence on
  them, a `must-fail` on a one-round-short twin), `books/crypto-attach.lisp`
  (the attachment). Dependents touched: crypto-attach's 4 direct includers
  and the host image; `books/sha256.lisp` (1 includer) unchanged.
- Memory after: unchanged (transient); the four conses per digested octet
  gone.
- Parallel: yes, with 2, 4, 5. Boundaries 6 to 9 need its stobj entry
  `fn-shw-sha256-of-buffer` (digest straight from the payload stobj) added
  after it lands; that entry is a second theorem in the same book.
- Expected: most of the digest's 43 to 46%; the honest figure is measured,
  because the generic-arithmetic share is not separable in the profile.

**Boundary 4: the remaining list recognitions** (`lane/records-concrete-2`).
- Share: 4 to 6% after boundary 1: the store event encoder's kind dispatch
  and the codec's guard check (`fn-store-event-encode`,
  books/store-events.lisp:160; `fn-record-encode-impl`, books/records.lisp:73,
  through the seam), `fn-sf-record-dir-result` (books/store-files.lisp:501),
  `fn-sbud-pending-sequence` (books/store-budget-naming.lisp:34), the host
  bridge wrappers `fn-store-record-sequence`/`-txid` (`host/native/io.lisp`
  lines 710 to 712, `host/store-node-host.lisp`), and recovery
  (`fn-store-sn-recover`, io.lisp:722, which decodes every record from a
  freshly consed list).
- Representation: the twins of boundary 1 extended to these callers; for
  the encoder, a twin of the dispatch whose kind test is `fn-rcon-record-p`
  and whose codec call is the seam's `fn-record-encode` unchanged.
- Theorem: for each, `(equal (fn-rcon-X args) (fn-X args))`, no
  hypothesis, as in boundary 1.
- Owns: `books/records-concrete.lisp` (extend), `tests/acl2/records-concrete-tests.lisp`,
  `host/store-node-host.lisp` (the bridge entries), `host/owner-host.lisp`
  `fn-owner-pending-sequence`. Dependents touched: records-concrete's
  includers (owner-commit-carried, owner-prepare-carried and the 12 roots
  the second farm run selected).
- Memory after: unchanged.
- Parallel: yes; nobody else edits records-concrete. Coordinate the host
  file with boundary 2 (different functions).

**Boundary 5: the Message-ID trie by index** (`lane/msgid-index-concrete`).
- Share: not on the POST profile beyond `fn-midx-refresh` inside
  `fn-own-refresh` (2% of the commit); on every reader and peer lookup
  `fn-midx-lookup` (books/msgid-index.lisp:69) converts the Message-ID to a
  character list (`fn-midx-key-chars`, :48) and `fn-midx-get-chars` walks it:
  one transient list per command. Served medians at N = 120 are 0.09 to
  0.8 ms (`representation-2026-09-25/shm-*.json`), so the share is a
  fraction of a small number.
- Representation: the walk by string index, `fn-mxc-get msgid i trie`;
  insert by index at refresh.
- Theorem: `(implies (stringp msgid) (equal (fn-mxc-lookup msgid trie)
  (fn-midx-lookup msgid trie)))` and `(equal (fn-mxc-extend article trie)
  (fn-midx-extend article trie))`, so `fn-midx-correspondencep` (the trie
  invariant `fn-own-relation` carries) is unchanged.
- Owns: `books/msgid-index-concrete.lisp`, its tests, and the reroute:
  the served retrieval arm reaches the lookup through
  `fn-nntp-msgid-retrieval-indexed` (books/nntp-responses.lisp:2279, in the
  served half's closure), so the executable switch is a twin arm in
  `books/owner-served-carried.lisp` (`fn-scar-*`, the chain the host calls
  at `fn-owner-chunk`) or a leaf `mbe` in `fn-midx-lookup` at a freeze
  (msgid-index: 4 direct includers).
- Memory after: the transient key list per command gone; the trie's nodes
  unchanged.
- Parallel: yes. Lowest share of wave A; launch if a lane is free.

**Boundary M: the heap census** (`lane/heap-census`, measurement only).
The 2.0 MiB per article RSS slope (§1, §3) is not the octet lists.
Take `(room)` and a per-type census on a loaded owner at N = 16, 50, 120
after `(sb-ext:gc :full t)`, on the profiling twin. Owns nothing in
`books/`; writes `planning/evidence/heap-census-2026-09-25.md`. Its result
decides the size of boundary 10. Parallel: yes.

### Wave B: after boundary 3 lands; parallel among themselves once 6 lands

**Boundary 6: the octet buffer, an abstract stobj** (`lane/octets-stobj`).
- Share: on this profile `fn-record-payloadp` 1.5 to 2.7%, the host's
  `fnn-octet-list` under 1%, frame assembly 2 to 4%; at the payload
  maximum every per-octet cost on the transient path scales with it, and
  this is the representation the other wave-B lanes build on.
- Representation: `(defabsstobj fn-octets ...)`: logical view the octet
  list `(fn-octets-list st)`, executable a resizable `(unsigned-byte 8)`
  array with a fill pointer; exports `fn-octets-len`, `fn-octets-get`,
  `fn-octets-put`, `fn-octets-append-octet`, `fn-octets-clear`,
  `fn-octets-to-list` (the escape hatch for a caller not yet rewritten) and
  `fn-octets-from-list` (the escape hatch the other way). The host fills the
  array from the socket buffer in raw Lisp (`fnn-octets-fill`, one
  `replace`), and passes the stobj to the ACL2 entry.
- Theorem: the abstract stobj's `{:logic,:exec}` preservation for each
  export, proved once (`fn-octets-get{:logic}` is `nth`, `-put{:logic}` is
  `update-nth`, `-append{:logic}` is `append`, each `{:exec}` on the array
  corresponds under `fn-octets-corr`); then, for the first consumer,
  `(equal (fn-rcon-payloadp-of-buffer st) (fn-record-payloadp (fn-octets-list st)))`
  with the bound `*fn-record-max-payload*` kept.
- Owns: `books/octets-stobj.lisp`, `tests/acl2/octets-stobj-tests.lisp`,
  `host/native/io.lisp` (`fnn-octet-list` and its callers at lines 838 to
  844: the store prepare entries), `host/owner-host.lisp` `fn-owner-prepare`
  (line 346, the `payload` argument). Dependents touched: none in `books/`
  until a consumer includes it; the host image.
- Memory after: the transient copies on the POST path gone (the socket
  buffer to the stobj is one array); the long-lived copies unchanged (32 L)
  until boundary 10.
- Parallel: no, it is the base of 7, 8, 9; one lane, then the three.

**Boundary 7: the record codec over the buffer** (`lane/records-stobj`).
- Share: the encoder's `append` of CBOR items and the decoder's
  `take`/`nthcdr` slicing at recovery (`fn-record-encode-impl`,
  `fn-record-decode-exact-impl`, books/records.lisp; the CBOR primitives in
  books/cbor.lisp); on this profile inside `fn-owner-pending-octets`
  (0.7%) and the frame write; at recovery every record.
- Representation: encoder writing into the stobj at an offset, decoder
  reading from it by index with the same self-delimiting grammar and the
  same bound checks before traversal (`*fn-record-max-octets*`,
  `*fn-cbor-max-input*`).
- Theorem: `(equal (fn-octets-list (fn-rcs-encode-into record st)) (append
  (fn-octets-list st) (fn-record-encode record)))` and `(equal
  (fn-rcs-decode-exact st) (fn-record-decode-exact (fn-octets-list st)))`,
  stated against the seam's constrained names (books/records-seam.lisp), so
  nothing above the seam moves; the host calls the twins where it now
  calls the seam.
- Owns: `books/records-stobj.lisp`, `tests/acl2/records-stobj-tests.lisp`
  (the schema-0 and schema-1 golden octets of records.lisp re-run through
  the buffer), `host/store-node-host.lisp` and `host/native/io.lisp`
  (record write and recovery decode, lines 710 to 723). Dependents
  touched: records-attach (1 includer) unchanged; the host.
- Memory after: the encoder's output list per record gone (transient).
- Parallel: yes with 8 and 9 after 6.

**Boundary 8: the frame codec over the buffer** (`lane/frame-stobj`).
- Share: `fn-frame-protected`/`fn-frame-encode` (books/frame-fields.lisp:306,
  :317) copy the payload into the frame (`fn-ag-append`, 2 to 4%), and the
  host writes the frame as a list (`fn-frame-trailer`, io.lisp:950;
  `fn-frame-store-protected`, books/frame.lisp:151).
- Representation: the frame as three writes on the host, header, payload
  (already in the buffer) and trailer, with the trailer computed by
  boundary 3's `fn-shw-sha256-of-buffer` over the protected range.
- Theorem: `(equal (fn-octets-list (fn-frs-seal-into magic version kind st))
  (fn-frame-seal magic version kind (fn-octets-list st)))` (stated against
  the constrained `fn-frame-digest`, as `fn-frame-encode-is-seal` is), and
  the decoder `(equal (fn-frs-decode st digest max) (fn-frame-decode
  (fn-octets-list st) digest max))`.
- Owns: `books/frame-stobj.lisp`, `tests/acl2/frame-stobj-tests.lisp`,
  `host/native/io.lisp` line 950 and the frame write path,
  `host/owner-host.lisp` line 1894. Dependents touched: frame (8
  includers) and frame-fields (2) unchanged; the host.
- Memory after: the frame's copy of the payload gone (transient).
- Parallel: yes with 7 and 9 after 6 and 3.

**Boundary 9: the article parser over the buffer** (`lane/article-stobj`).
- Share: `fn-article-parse` (books/article.lisp:324) and the header field
  parsers over the posted octets (inside `fn-owner-chunk`, 4.8%, and
  `fn-owner-io`, 3.3%), O(L) with conses per field.
- Representation: the parser by index over the buffer, with the same work
  counters: the PRF-016 theorems (`fn-article-parse-work-value`,
  `-input-bound`, `-profile-bound`) restated over the twin through a
  correspondence of the work value.
- Theorem: `(equal (fn-ars-parse st) (fn-article-parse (fn-octets-list st)))`
  and `(equal (fn-ars-parse-work st) (fn-article-parse-work
  (fn-octets-list st)))`.
- Owns: `books/article-stobj.lisp`, `tests/acl2/article-stobj-tests.lisp`,
  `host/owner-host.lisp` `fn-owner-chunk` (line 1414) and the injection
  path. Dependents touched: article-fields (9 includers) and article
  unchanged; the host.
- Memory after: the parsed field lists become string fields (the
  recognizers of boundary 1 already read strings).
- Parallel: yes with 7 and 8 after 6.

### Wave C: the state, and the freeze

**Boundary 10: the owner state as an abstract stobj** (`lane/owner-stobj`,
after wave B and the heap census).
- Share: this is the memory boundary. The two long-lived copies of every
  article, the store record's payload and the node's article body, are
  fields of the logical owner and are octet lists in every image until the
  owner has a concrete representation. 32 L bytes per article today: 1 MiB
  at the payload maximum, 4 GiB at N = 4096 (§3).
- Representation: `(defabsstobj fn-owner ...)` whose logical view is the
  owner value the theorems are about (`fn-own-*`) and whose executable is
  a struct holding the history and the archive with payloads as
  `(unsigned-byte 8)` arrays; exports are the host-called entries
  (`fn-owner-prepare`'s `fn-pcar-sbud-prepare`, `fn-ccar-own-finish`,
  `fn-acar-own-outcome`, the served read, the recovery open), each with a
  `:logic` the existing function and an `:exec` twin over the struct.
- Theorem: per export, the abstract stobj's correspondence `(fn-owner-corr
  st o)` preserved and the export's `{:logic}` equal to the current
  host-called function; the carried premises (`fn-ocl-relation`,
  `fn-sn-statep`) become part of `fn-owner-corr`, which is the "carry the
  invariant in state" AGENTS.md asks for.
- Owns: `books/owner-stobj.lisp` and one book per export
  (`owner-stobj-prepare`, `-commit`, `-outcome`, `-read`, `-recover`),
  their tests, and every host entry in `host/owner-host.lisp`. Dependents
  touched: none of the logical books; the whole host.
- Memory after: 2 (L + 16) per article plus the record's strings: 64 KiB
  at the maximum payload, 256 MiB at N = 4096.
- Parallel: the stobj book is one lane; the exports can then be one lane
  each (they own disjoint books and disjoint host entries).

**Freeze items** (the coordinator's batch, not lanes; each is a leaf `mbe`
whose `:logic` is the current definition and whose guard obligation is the
correspondence, and each recertifies its closure): `fn-record-octet-stringp`
and `fn-record-metadata-bytes-p` (records-shape; then boundary 1's twins
become redundant and boundary 4's callers need no reroute),
`fn-record-payloadp` over the buffer (records-shape, with boundary 6),
`fn-octet-listp` (acceptance-alloc, 6 includers, root of the tree),
`fn-midx-lookup` (msgid-index), the `fn-own-sub-*` intent field (owner).
One freeze with all of them is 1:44 at 16 jobs on hbox
(`fn-freeze-recipe`), the same as one.

### Not on this profile: measure first

The BP and TCPCL codecs (`fn-bpn-receive`, books/bp-node.lisp:446, the
`fn-bpa-*`/`fn-tcl-*` codecs), the feed and peer wire
(`fn-peer-relayed-octets`, books/peer-inbound.lisp:243, the `fn-feed-*`
input step) take octets from the host as lists on their own paths. Their
shares are in their own records (`planning/evidence/bp-*`,
`m4-*`, `d23-*`), not in a POST profile. They follow the wave-B pattern
over the same buffer stobj (boundary 6) once a profile of their path names
the share; a lane for each is `lane/bp-stobj` and `lane/feed-stobj`, owning
`books/bp-octets.lisp` and `books/feed-octets.lisp` with their host files
(`host/native/bp*.lisp`, the feed thread), after boundary 6.

### The order, in one line

Now, in parallel: 2 (intent), 3 (SHA-256 words), 4 (remaining
recognitions), 5 (trie, if a lane is free), M (heap census). After 3: 6
(the buffer). After 6, in parallel: 7 (record codec), 8 (frame), 9
(parser). After the census and wave B: 10 (the owner stobj), then its
exports in parallel. The freeze items go in the coordinator's next freeze.
