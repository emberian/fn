# Why the codec-layer books took 10 to 93 s, and the repairs (lane COST-codec, 2026-09-23)

Branch `cost/codec` from `dev` 1554e2cd. The diagnosis was read from existing
certify logs; slow forms were not rerun except where the log could not name
the cost (one profiled run, one persistence run, both below). Each repair
was tried in one `tools/proof_repl.py` session per book on the Mac, and then
every changed book was loaded whole, form by form, in a fresh session.

## The logs

| log (persvati) | what it is |
|---|---|
| `/home/ember/fn-gates/t1-seam/build/acl2/certify-20260923T000250Z-1473169/books--<book>.certify.log` | the 310-book run whose manifest is `manifests/certify-20260923T000250Z-1473169.json` |
| `/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/books--<book>.certify.log` | the stopped treewide run of `dev`'s head (345 books); same events, same step counts, times within 10% |

Book times below are the sum of the log's event `Time:` lines (the
`certify-book` line itself is the total and is excluded). "Steps" is the
log's `Prover steps counted`.

## Four causes, one pattern

Every slow event in these books is one of four shapes. In each one the proof
needed a small fact that already existed, or was one short lemma away, and
the prover instead carried a definition or rule it did not need:

1. **A definition over a constant table left enabled** (frame, frame-journal,
   frame-invariants). `fn-frame-spec-for` is recursive over the table, the
   table is a constant, so ACL2 opens it all the way: a 7-way split on the
   kind, then `fn-frame-values-okp` and `fn-frame-fields-octets` unroll
   over each kind's field list. The frame books are parts 2 to 4 of one
   grammar and the definitions are disabled only at the end of
   `books/frame.lisp`, so every guard in between carried them.
2. **Accessors open inside a builder** (peer-config). `fn-cfg-ag-car` and
   `-cdr` are `(if (consp x) ...)`; opened inside `fn-cfg-peer-rows` they
   put two cases on every field read of every row, and the splitter
   multiplied them.
3. **A backchaining rule into the decoder** (statement-invariants) and **a
   codec opened under an induction** (records-canonicality, statement,
   statement-codec): the book-wide codec enable put the whole CBOR decoder
   or encoder into goals that needed one fact about it.
4. **`(:type-prescription true-listp-append)` over a deep `append` nest**
   (records-invariants, records-canonicality). This one does not show in
   the step count at all: 27 290 steps took 39 s.

## Per book

### books/peer-config (92.8 s over 68 events)

| event | time | steps | split |
|---|---|---|---|
| `fn-cfg-peer-names-of-peer-rows` | 26.2 s | 14 679 190 | 15 448 subgoals, 612 at `Goal`, deepest `Subgoal 612.16.8.4.10.5` |
| `fn-cfg-peer-rows-keyed` | 23.3 s | 14 736 731 | the same 15 448 |
| `fn-cfg-peer-rows-are-few` | 22.1 s | 16 412 962 | the same 15 448 |
| `fn-cfg-peer-rows-are-rows` | 13.3 s | 2 912 624 | 2 986, 138 at `Goal'` |
| `fn-cfg-peer-find-is-a-peer` | 7.3 s | 3 337 339 | 810 at `Goal` |

If-intro for the first four: `binary-append`, `fn-cfg-ag-car`,
`fn-cfg-ag-cdr`, `fn-cfg-peer-outbound-auth`, `fn-cfg-peer-rows`,
`true-listp`. Line 29 enables `fn-cfg-vocabulary` book-wide, which holds
the accessors. The names, key and length of the rows do not read any field
value, only the row labels, so the accessor cases are pure cost.

Repair:
- `names-of-peer-rows`, `rows-keyed`, `rows-are-few`: the hint closes
  `fn-cfg-ag-car`, `fn-cfg-ag-cdr` and `fn-cfg-peer-outbound-auth`.
- `rows-are-rows` does read the fields (each row is typed against the
  half's recognizer). The builder is named by halves: four local
  functions, each the builder's own subterm for transport, inbound,
  outbound and auth, a local lemma `fn-cfg-peer-rows-by-halves` equating
  the builder to their append (proved with only those definitions in the
  theory, 5 280 steps), one typing lemma per half against that half's
  recognizer, and `fn-cfg-row-listp-of-append`. The theorem then closes by
  those.
- `find-is-a-peer` needs only the decoder's last step, "the result is nil or
  it passed `fn-cfg-peerp`". A local function names the record the decoder
  builds (its `let*` body before the check) and a local lemma states the
  decoder as "check the candidate" (86 663 steps, 0.4 s); the forward rule
  then closes in 212 steps.

All new events are local; no definition or exported rule changed.

### books/frame (87.3 s over 22 events)

| event | time | steps |
|---|---|---|
| `(verify-guards fn-frame-workflow-protected)` | 83.7 s | 17 668 811 |
| `(verify-guards fn-frame-inbound-open)` | 2.1 s | 144 966 |
| `(verify-guards fn-frame-receipt-protected)` | 0.9 s | 200 916 |

If-intro: `binary-append`, `fn-frame-enum-index`, `-field-octets`,
`-field-okp`, `-fields-octets`, `-natp`, `-spec-for`, `-textp`,
`-values-okp`, `-workflow-record-okp`. The guard needs: the kind's spec is
a spec list (`fn-frame-spec-for-workflow-is-spec-list`), the values satisfy
it (a conjunct of `fn-frame-workflow-record-okp`), the payload is octets
(`fn-frame-fields-octets-are-octets`), and its length is bounded (the
branch's own `fn-cbor-at-mostp` test).

Repair: both `-protected` guards get a hint closing `fn-frame-spec-for`,
`fn-frame-values-okp` and `fn-frame-fields-octets`.

### books/frame-journal (43.3 s over 61 events)

| event | time | steps |
|---|---|---|
| `(verify-guards fn-frame-workflow-encode)` | 37.2 s | 7 299 674 (101 at `Goal'`) |
| `(verify-guards fn-frame-workflow-decode)` | 2.4 s | 1 165 565 |
| `(verify-guards fn-frame-receipt-decode)` | 2.1 s | 1 007 706 |
| `(verify-guards fn-frame-receipt-encode)` | 1.2 s | 271 905 |

Same cause as frame. `fn-frame-workflow-encode` has no length test before
`fn-frame-encode`, whose guard wants `(<= (len payload) *fn-cbor-max-uint*)`,
so the unrolling was also how the prover bounded the payload: field by
field.

Repair:
- `fn-frame-workflow-record-okp-fields` and `fn-frame-receipt-record-okp-fields`
  (forward-chaining, exported but disabled at the book's end and not in its
  vocabulary): a well-formed record's spec is a spec list and its values
  satisfy it.
- Three local linear lemmas state the length bound as the fact it is: a
  field encodes to at most a blob's four length octets plus its cap, a
  field list to at most that times its length, and no workflow kind has
  more than eleven fields.
- The two encode guards use the record lemma with the table closed; the two
  decode guards close the table.

### books/frame-invariants (13.3 s over 91 events; 27 s in root's worst manifest)

| event | time | steps |
|---|---|---|
| `fn-frame-workflow-decode-of-encode` | 6.3 s | 1 392 202 |
| `fn-frame-workflow-encode-is-protected-plus-digest` | 5.2 s | 2 500 507 |

If-intro: `fn-frame-enum-index`, `-field-okp`, `-natp`, `-outcome-pairp`,
`-spec-for`, `-values-okp`, `-workflow-encode`, `-workflow-record-okp`.
Closing the table left one fact the unrolling had supplied: a kind with a
specification has a nonzero code. A local lemma states it
(`fn-frame-workflow-spec-for-has-code`, 13 486 steps); both hints now also
close `fn-frame-spec-for`, `fn-frame-values-okp` and `fn-frame-enum-index`.

### books/records-invariants (41.2 s over 33 events)

| event | time | steps |
|---|---|---|
| `fn-record-impl-round-trip` | 39.0 s | 27 290 |
| `fn-record-reconstruct` | 1.4 s | 451 627 |

39 s for 27 290 steps is 1.4 ms a step, and the log shows two subgoals and
no splitter beyond `fn-record-encode-impl`. The log cannot say where the
time went, so this form was run once under SBCL's statistical profiler
(`sb-sprof`, 5 731 samples over 28.7 s, in a throwaway session with a
diagnosis trust tag; nothing of it reaches a book):

| function | self | total |
|---|---|---|
| `type-set-rec` / `type-set-with-rules` | | 99.7% |
| `type-set-relieve-hyps` | 7.1% | 102% (recursive) |
| `one-way-unify1` | 21.1% | 43.3% |
| `push-ancestor` | 14.6% | 15.7% |
| `add-to-tag-tree` | 10.1% | |

All of it is type-set relieving the hypotheses of conditional
type-prescription rules. The enabled conditional ones that apply to lists
are ACL2's own; the one that fits is `true-listp-append`,
`(implies (true-listp b) (true-listp (append a b)))`. The encoder is a
thirteen-deep right-nested `append`, and each type-set of it backchains
through every level's hypothesis again. Type-set work is not counted in
prover steps, which is why the step count is small.

Repair: the hint disables `(:type-prescription true-listp-append)`. The
proof then takes 0.11 s with the same 27 290 steps.

### books/records-canonicality (68.4 s over 35 events)

| event | time | steps |
|---|---|---|
| `fn-record-parse-groups-reencode-prefix` | 39.6 s | 974 285 (induction, deepest `Subgoal *1/2.25.2`) |
| `fn-record-parse-groups-value-length` | 20.9 s | 755 086 (induction) |
| `fn-record-component-prefixes-compose` | 3.3 s | 3 979 |

The two inductions open the whole CBOR decoder in each step
(`fn-cbor-decode`, `-decode-bounded`, `-decode-prechecked`,
`-decode-argument`, `-decode-unsigned`, `-decode-bytes-bounded`,
`fn-cbor-canonical-argumentp`, `fn-cbor-at-leastp`), because line 4 opens
`fn-cbor-codec-vocabulary` and `fn-record-read-bytes` is enabled. Each step
needs only the reader's own facts, proved earlier in the same book:
`fn-record-read-bytes-reencode-prefix`, `fn-record-read-bytes-value-are-octets`
and `fn-record-string-octets-of-octets-string`, plus the parser-result
constructor facts from `books/records-shape`
(`fn-record-parse-{okp,value,rest}-of-ok`, `fn-record-parse-error-is-failure`).
Disabling `true-listp-append` alone did not help here (41.5 s, same steps):
this cost is real rewriting.

Repair: both hints close the reader, the codec, the string conversions,
the group-name recognizer and the result accessors and name the
constructor facts; `component-prefixes-compose` (an eight-deep `append` on
both sides, 3 979 steps in 3.3 s, cause 4) disables
`true-listp-append`.

### books/statement-invariants (28.9 s over 65 events)

| event | time | steps |
|---|---|---|
| `fn-stmt-header-encoding-bound` | 11.6 s | 2 222 297 |
| `fn-stmt-header-items-length` | 4.0 s | 1 028 575 |
| `fn-stmt-header-reconstruct` | 3.6 s | 1 247 530 (2 subgoals) |
| the next five | 0.8 to 1.9 s each | |

`header-reconstruct` needs only `car`/`cdr`/`len` of a six-element list.
One persistence run of it (`:frames`):

| rune | frames | tries (useless) |
|---|---|---|
| `(:rewrite fn-stmt-decode-ok-implies-octets)` | 538 544 | 6 820 (all) |
| `(:definition fn-cbor-decode)` | 535 949 | 803 (all) |
| `(:definition fn-cbor-decode-bounded)` | 535 146 | 803 (all) |
| `(:definition fn-cbor-octet-listp)` | 524 883 | 2 535 (all) |
| `(:rewrite fn-digest-octetsp-implies-octet-listp)` | 497 427 | 24 857 (all) |

`fn-stmt-decode-ok-implies-octets` (line 124) concludes
`(fn-cbor-octet-listp octets)` from `(fn-cbor-result-okp (fn-cbor-decode
octets))`. With the decoder open (the book-wide codec enable), every octet
recognizer the prover met tried to decode its argument. No proof in the
book uses the rule.

Repair: a `local` disable right after the lemma. It stays in the exported
vocabulary unchanged.

### books/statement-codec (11.8 s over 51 events)

`fn-stmt-impl-encode-items-of-cons`, 9.3 s, 2 027 480 steps, 16 subgoals:
one unfolding of the list encoder with `fn-cbor-encode` open (if-intro
`floor`, `fn-cbor-encode-argument`, `-encode-bounded`, `-valuep-bounded`).
Repair: the hint closes `fn-cbor-encode`. (The same book has its own local
copy of `fn-stmt-decode-ok-implies-octets`; the book is under 3 s after the
repair, so it is left.)

### books/statement (8.1 s over 101 events; 12 s in root's worst manifest)

| event | time | steps |
|---|---|---|
| `fn-stmt-signing-preimage-is-octet-list` | 3.8 s | 1 749 472 |
| `(defun fn-stmt-items ...)` guard | 1.6 s | 424 688 |
| `(defun fn-stmt-encode ...)` guard | 1.3 s | 331 996 |

The first opens `fn-stmt-content-id` and with it the header encoder and
recognizer; `fn-stmt-content-id-is-digest` is the fact. The two guards open
the header's item builder and recognizer. Repair: the hint closes
`fn-stmt-content-id`; the guard hints close `fn-stmt-header-items` and
`fn-stmt-headerp`, and `fn-stmt-items` and `fn-stmt-p`.

### Not changed

`cbor-invariants` (2.0 s), `frame-fields` (4.7 s), `frame-octets` (1.0 s)
and `checkpoint-codec` (9.2 s, largest event 3.1 s) are under ten seconds.

## Session times (Mac, whole book loaded form by form in a fresh session)

| book | before (seam log, persvati) | after (Mac session) | largest event after |
|---|---|---|---|
| peer-config | 92.8 s | 2.1 s | `include-book "config"` 0.6 s; largest proof `fn-cfg-peer-of-rows-is-its-checked-candidate` 0.4 s |
| frame | 87.3 s | 2.6 s | `verify-guards fn-frame-inbound-open` 1.7 s (not changed) |
| frame-journal | 43.3 s | 0.9 s | `include-book "frame-fields"` 0.5 s; largest proof 0.09 s |
| records-canonicality | 68.4 s | 4.4 s | `fn-record-read-uint-reencode-prefix` 1.3 s |
| records-invariants | 41.2 s | 1.9 s | `fn-record-reconstruct` 0.9 s |
| statement-invariants | 28.9 s | 2.4 s | `fn-stmt-header-encoding-bound` 0.6 s |
| frame-invariants | 13.3 s | 1.5 s | `fn-frame-u32-bytes-of-u32-from` 0.4 s |
| statement-codec | 11.8 s | 2.1 s | `fn-stmt-prechecked-value-is-cbor-value` 0.4 s |
| statement | 8.1 s | 1.4 s | `fn-stmt-header-items-are-items` 0.3 s |

Summed over the nine books: 395.1 s before, 19.3 s after. Per theorem,
before and after in the session: `fn-frame-workflow-protected` guard 83.7 s
to 0.14 s; `fn-frame-workflow-encode` guard 37.2 s to 0.03 s;
`fn-record-parse-groups-reencode-prefix` 39.6 s to 0.01 s (974 285 to 1 790
steps); `fn-record-impl-round-trip` 39.0 s (33.2 s on the Mac) to 0.11 s;
`fn-cfg-peer-names-of-peer-rows` 26.2 s to 0.27 s; `fn-cfg-peer-rows-are-rows`
13.3 s to 0.01 s; `fn-stmt-header-encoding-bound` 11.6 s to 0.55 s;
`fn-stmt-impl-encode-items-of-cons` 9.3 s to 0.10 s.

The Mac is the slower machine for rewriting (the peer lane measured 12.8 s
per million steps on the Mac against 8.3 s on persvati), so the after column
is not flattered by the box.

## A lead for other lanes: time the step count does not explain

Cause 4 is invisible to the usual reading of a log, because type-set work
is not counted in prover steps. A scan of both runs' logs for events over
2 s that cost more than 40 microseconds a step (ordinary rewriting here is
5 to 13) finds, outside this lane's books:

| book (owner) | event | time | steps | per step |
|---|---|---|---|---|
| `policy` (nntp lane) | `fn-pol-current-is-stmt-or-nil` | 56.2 s | 336 946 | 167 us |
| `policy` (nntp lane) | `(defun fn-pol-current ...)` | 21.8 s | 126 262 | 172 us |
| `bp-adu` (bp lane) | `fn-bpa-encoding-bound` | 20.7 s | 45 462 | 456 us |

These have the signature of `fn-record-impl-round-trip` (1 431 us a step).
They were not examined here; a profiled run of each, as above, would say
whether it is the same rule.

## What changed, and what did not

Hints, `local` lemmas and `local` definitions, one `local` disable, and two
exported forward-chaining lemmas in `frame-journal` that are disabled at the
book's end and are not in any vocabulary. No theorem statement, definition
body, guard or exported vocabulary changed; nothing is skipped; no
`:verify-guards nil` was added. The diagnosis trust tag lived only in a
throwaway session.

These books are low in the graph: a change here recertifies everything
above them. Since no definition and no enabled exported rule changed, no
dependent's proof should change; the treewide run is where that is checked.

## Certification: not submitted

The farm refused the lane run before ACL2 started. `farm.py submit persvati`
with plain roots (the nine books and `tests/acl2/{frame,records,records-teeth,
codec-seam,statement,peer-inbound}-tests`, `--jobs 4 --timeout-seconds 1800
--remote-root /home/ember/fn-gates/cost-codec --acl2
/home/ember/fn-gates/toolchains/w25/acl2-literal --cache
/home/ember/fn-certcache`) answered "no origin/toolchain-coherent
certificate set ... Re-run with --closure". 25 books of the closure have no
pair in the cache at `dev` 1554e2cd's digests: `peer-inbound`,
`peer-inbound-invariants`, `principal`, `provenance`, `provenance-codec`,
`records`, `records-attach`, `records-seam`, `records-shape`, `replay`,
`retention`, `retention-invariants`, `statement-attach`, `statement-items`,
`statement-seam`, `store-events`, `stx-accept-records`, `stx-carrier`,
`stx-evidence-records`, `stx-keyring-records`, `stx-lace`, `stx-verify`,
`wildmat`, `wire`, and `tests/acl2/crypto-seam-tests`. Under
`planning/how-we-work.md`, "Certification cost", a lane does not
`--closure`, so the lane stopped there. The run waits on root's treewide
certification of `dev`; after it, the plain-roots submit above is the gate,
and since these books sit under most of the tree, the treewide run over the
merge is the check that no dependent's proof moved.

## Not verified

- The books were loaded form by form in live sessions, not certified. Books
  whose dependencies changed here (for example `frame-invariants` over the
  new `frame-journal`) were loaded with those dependencies included
  uncertified from source.
- The dependents above these books were not loaded.
