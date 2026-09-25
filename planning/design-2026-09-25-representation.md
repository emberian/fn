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

**Census and correction (rep-heap lane, `planning/evidence/rep-heap-2026-09-25.md`).**
The census was taken. The 2 MiB per article RSS slope was SBCL's garbage
headroom filling toward its 1,600 MiB collection trigger, not live data; the
live slope is 6.1 KiB per 160-octet article and 260 KiB per 16 KiB article,
and the payload is held once (records, archive, views and trie share the one
list). Correction to the sizes above: an ACL2 string on SBCL is a
`simple-character-string`, 4 octets per character (`(coerce ... 'string)`
never makes a base string), so a payload as a string costs 4 L + 16 bytes,
not L + 16; only a byte array (stobj) is L + 16.

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

## 5. The boundaries, ranked by measured share divided by dependents touched

"Dependents touched" counts the books whose bytes change (the twin book,
the carried books that call it, their tests) plus the roots `--affected-by`
selects. A leaf `mbe` touches the leaf's whole closure and is listed with
that count.

| Rank | Boundary | Share of POST CPU | Books touched | Ratio | Form |
| ---: | --- | ---: | ---: | ---: | --- |
| 1 | **The record recognizer's strings** (this lane): `fn-rcon-record-p` reads the strings in place; twins of the four dispatchers, the pair, the binding test, the two projection steps; `owner-commit-carried` and `owner-prepare-carried` call them | 17 to 20% (the recognizer minus its payload and group walks) | 2 changed carried books + 1 new book + 1 test, 4 dependents (`owner-advance-carried`, `owner-commit-ocl`, `owner-offer-indexed`, the two carried tests) | ~2.5% per book | hypothesis-free correspondence, landed |
| 2 | **The intent identity computed once.** `fn-own-feed-intent-id` is SHA-256 of the payload three times per POST; the value is a function of the submission's octets and Message-ID, both fixed at `fn-owner-take`. Carry it in the submission record (a field set at take) and prove the carried value is the digest | 17% | `owner` (fn-own-sub-* record, ~60 includers) or a carried twin of `fn-own-submission-intent-result`/`-records`/`-resolution-records` in a new book that `owner-host` calls (3 host lines) | ~4% per book as a carried twin | a carry, not a representation change: `fn-*car-intent-records-is-reference` under "the held submission's cached id is its digest", carried from take |
| 3 | **SHA-256 on a word stobj** | 33% of POST CPU (all digests), and every frame trailer, every identity, every receipt on every path | 1 (crypto-attach: `defattach fn-frame-digest`/`fn-digest` to the stobj-backed function; the constraint stays) | high, but the proof is the whole compression function's correspondence, round by round: a lane of its own | `fn-sha256-stobj-is-sha256-of-octets`: the attached function equals the list specification on every octet list. The attachment mechanism (books/crypto-attach.lisp) makes the switch one line once the theorem exists; without the theorem the attachment would silently change what the host computes, which is exactly the claim this project refuses to make |
| 4 | **The payload as a stobj array** (`fn-record-payloadp`, `fn-id-subject-preimage`, `fn-frame-protected`, the host's `fnn-octet-list` at io.lisp:838) | 3% today (small articles); O(L) per recognition and per frame at the maximum payload, plus the 16 L memory | records-shape's closure if by `mbe` (freeze); or an abstract stobj with twins of `fn-record-p`, the codec's byte-string encoder and the frame encoder up to the host (10 to 15 books) | low today, first at large payloads | abstract stobj; the memory figure is the reason, not the CPU |
| 5 | **Group names by index** (`fn-record-group-namep` → `fn-record-group-name-octetsp`: converts, then the one-pass grammar) | 1% | records-shape (freeze) or a twin in `records-concrete` with the grammar restated over an index, proved equal to `fn-record-group-name-grammarp` through the existing keystone | ~1% per book | correspondence with the RFC 5536 grammar keystone kept |
| 6 | **The archive body as a string** (`fn-articlep`'s `fn-octet-listp`, the trie's `fn-midx-key-chars` on the Message-ID) | 0% on POST after the carries; O(N·L) wherever `fn-article-listp` runs (`fn-statep`, the peer arms' `fn-node-statep` that ember left untouched) | acceptance (the root of the tree) | not a lane; a freeze decision | the leaf `mbe` at `fn-octet-listp`'s callers, or a string body in the logical article: the latter changes statements and is not a representation move |
| 7 | **Frame assembly without the copy** (`fn-frame-encode`'s `append` of the protected prefix and the digest; the host's `write-sequence` of a list) | 2 to 4% | frame-fields, frame-trailer, host io.lisp:950 | ~1% per book | with the payload stobj (rank 4), the frame becomes a header write, a payload write and a trailer write on the host: `fn-frame-encode-is-seal` already separates the digest from the bytes |

The first boundary is rank 1 because it is the largest a single lane can
close with hypothesis-free correspondence proofs, in books the host already
calls, without recertifying the tree. Rank 2 is the next lane: it removes
more CPU than rank 1 and is one carried book. Rank 3 is the largest share
and the largest proof; it should be planned as a lane with the compression
function's round structure written for the proof (word stobj, a per-round
lemma, a per-block lemma, the padding lemma) and measured on the frame
journal and the identities separately.
