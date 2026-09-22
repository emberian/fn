# The acceptance stamp (T2)

Status: design. Every ACL2 form below is a proposed definition or a proposed
theorem *statement*; none has been submitted to ACL2, and nothing here licenses
a claim under the [assurance rules](../AGENTS.md). It is the design note for
step T2 of [the trajectory plan](../planning/plan-2026-09-22-trajectory.md)
(§0 decision 6, §3 row T2, §3.1 "T2", §4.1), written against `dev` `3373f935`
and against the T1 lane's working tree as it stood on 2026-09-22 (its
`books/records-seam.lisp` and `books/records-shape.lisp` are uncommitted; §6.2
names what T2 needs from them). Books and functions that do not exist yet are
named in code spans, never linked.

## 0. The properties, before anything else

- **S1. Every article this node commits from now on carries the instant this
  node accepted it**, taken from the owner's own clock observation, inside the
  bytes that become durable at the commit. There is no second write.
- **S2. No client, peer or bundle can supply or influence the stamp.** It is a
  function of the owner's observation alone; `Injection-Date` stays what it is,
  a claim in the article.
- **S3. A store written before the stamp keeps opening and serving.** Its
  records are read as they were written, with the stamp `:legacy`; no record
  on disk is rewritten, and every schema-0 record re-encodes to its own bytes.
- **S4. The stamp survives every crash and every replay exactly.** The live
  node and the node replayed from the journal carry the same stamp for every
  article, over a journal that mixes schema-0 and schema-1 records.
- **S5. NEWNEWS answers from the stamp and reads no article octet.** It reports
  exactly the committed articles in matching groups whose stamp is at or after
  the requested instant; the 256-parse budget and its 503 leave the served path.
- **S6. A missing clock is a refusal with the clock's reason, before any
  record is written.** It is never an accepted article with an uncertain
  stamp, and never the article verdict "the article was refused" (D10-a).

What S1 to S6 do not say is in §8.

## 1. The schema-1 record

### 1.1 The field

`fn-record-make` gains an eleventh argument, last:

```
(fn-record-make sequence txid generation msgid payload groups
                obligation-id content-subject release-evidence charge
                stamp)
```

with the field recognizer

```
(defun fn-record-stampp (x)
  (declare (xargs :guard t))
  (or (equal x :legacy) (fn-record-uint32p x)))
```

A natural stamp is **whole seconds since 2000-01-01T00:00:00Z** (the DTN epoch
of RFC 9171 §4.2.6, the epoch `books/clock.lisp` and the NNTP date code already
use), in `0 .. 2^32-1`. `:legacy` is the stamp of a record decoded from
schema-0 bytes and of nothing else (§3). The logical article gains the same
field, last: `(fn-make-article msgid payload groups memberships pin stamp)`,
read by `fn-article-stamp`; `fn-make-pending` likewise, so that
`fn-sn-pending-record` rebuilds the record with its stamp and
`fn-sn-record-bindsp` compares it.

### 1.2 Which instant: the owner's observation at prepare

The stamp is `(floor (fn-clock-wall obs) 1000)` of the observation `obs` the
owner holds (`fn-own-clock`) when the record is built for `fn-sn-prepare`. Two
alternatives were weighed.

**Finish instead of prepare.** "The instant this node accepted it" is, strictly,
the durable commit, which is later than prepare. But the record's bytes are
fixed at prepare: `fn-sn-prepare` stages the record candidate, the file kernel
writes and syncs exactly those bytes, and `fn-sn-finish` only consumes the
completion. A finish-time stamp needs either a second durable write (a
completion record carrying the time, which is a new record kind, a new crash
cut and a new replay rule) or a live node that differs from its replay, which
`fn-snt-mixed-trace-ready-node-is-exact-replay` forbids. Prepare is the latest
instant whose reading can be inside the committed bytes. The gap between
prepare and commit is the file program's syncs; in the native owner it is not
observable by a reader, because one owner read and its serial writer drain run
under one service mutex (`host/native/owner.lisp:968`), so no reader event,
and no clock observation, falls between a prepare and its finish.

**The decision-time reading instead of prepare.** The plan's §3.1 text names
"the observation `fn-own-read` supplies with the submission". For a POST that
is the reading `fn-inj-decide` wrote into `Injection-Date`, so the stamp would
equal the injector's stamp for local posts. It is rejected for two reasons. A
submission can wait in the owner's queue while other reads pin later
observations, so a decision-time stamp can precede the pin of a reader that
does not yet see the article, and a client polling "NEWNEWS since my last
DATE" then misses it (§7 question 4); a prepare-time stamp is taken inside the
mutex hold that also commits. And the submission record would have to carry an
observation, which widens `fn-own-sub-make` across the owner closure for a
value the owner already holds at prepare. In the common case (a POST drained
in the event that decided it) the two readings are the same observation, so
local posts keep `Injection-Date` and stamp in the same second.

### 1.3 Why seconds, not milliseconds

The observation is in milliseconds; the stamp keeps whole seconds. Three
reasons, each sufficient:

1. **The CBOR profile is uint32** (`*fn-cbor-max-uint*`, `books/cbor.lisp:24`).
   Milliseconds since 2000 are already past 2^39. Carrying them needs either a
   uint64 head in the CBOR codec (a change to the CBOR seam that alters the
   accepted language of every codec above it, T1's four clusters included) or
   a two-item encoding. Seconds fit one uint32 item into the year 2136.
2. **The checkpoint codec's value universe is naturals below 2^32**
   (`books/checkpoint-codec.lisp`, TREE). The checkpoint stores the exact node,
   so an article stamp in milliseconds would make every node with a stamped
   article unencodable as a checkpoint. In seconds it is inside the universe;
   the only checkpoint change is admitting the symbol `:legacy`.
3. **Nothing reads a finer instant.** NEWNEWS and NEWGROUPS thresholds are
   whole seconds (`fn-nntp-civil-dtn-ms` returns `1000 * secs`), and DATE
   renders seconds. For a threshold `1000k`,
   `1000k <= 1000 * floor(w/1000)` iff `k <= floor(w/1000)` iff `1000k <= w`,
   so comparing the second-stamp gives exactly the answer the millisecond
   reading would. The sequence number already orders articles within a second.

The observation's error bound is not recorded. The stamp is this node's wall
reading, not an interval claim about true time (§8).

### 1.4 The encoding

Schema 1 is schema 0 with version `1` and one item appended:

```
bstr h'666e2d72'                 ; magic "fn-r"
uint 1                           ; schema version
uint sequence, uint txid, uint generation
bstr msgid, bstr payload
uint group-count, bstr group[0] ... bstr group[group-count - 1]
bstr obligation-id, bstr content-subject, bstr release-evidence
uint charge
uint stamp                       ; schema 1 only: seconds since the DTN epoch
```

The encoder dispatches on the stamp: a record whose stamp is `:legacy` encodes
to the schema-0 grammar exactly as today (version `0`, no stamp item); a record
with a natural stamp encodes to schema 1. The decoder reads the magic, then the
version octet: `0` parses the schema-0 body and yields stamp `:legacy`; `1`
parses the same body, then one canonical uint, then requires no trailing octet;
anything else is `:unknown-version`, as today. This dispatch is what makes
canonicality hold at schema 1 with no side condition: every accepted input is
the encoding of what it decodes to, in both grammars, because the decoded
stamp's kind selects the grammar it came from.

**Bound.** The stamp item is at most 5 octets. The largest schema-0 record is
35,907 octets (5 + 1 + 15 + 252 + 32,771 + 1 + 2,080 + 777 + 5, from the
field limits in `books/records.lisp`), so the largest schema-1 record is
35,912, inside the unchanged `*fn-record-max-octets*` = 65,538, inside the
`fn-stxa` child bound and inside every FNST payload ceiling. No limit moves.

### 1.5 Precedents in the tree

Two, and T2 follows both. `books/provenance-codec.lisp`: "a provenance written
before the typed value existed is the `:legacy` kind and keeps its bytes and
its meaning" (`specs/storage.md` STO-006), with the round-trip keystone K-PROV-2
reading a legacy value back as itself. `specs/encoding.md`'s bounded Store-event
profile: format-7 stores derive a new ceiling and "format-6 metadata remains
readable and derives its original 65,538-octet ceiling". ENC-004's note says
"schema evolution is a single schema-0 grammar today"; this is its first
evolution, and the rule it makes concrete is: the old grammar stays accepted
byte for byte, its values are read with an explicit legacy marker, and nothing
new is ever written in it.

### 1.6 Where the stamp is computed: one ACL2 function

Today the article record is assembled twice in host code with `fn-record-make`
(`host/store-node-host.lisp:464`, `host/owner-host.lisp:326`), and in ACL2 by
`fn-hsig-authorized-submission-event` (`books/hybrid-store.lisp:180`) and
`fn-bpi-record-for` (`books/bp-ingress.lisp:423`). T2 gives the stamp one owner:

```
; books/records-stamp (new): the stamp an observation gives.
(defun fn-record-stamp-of-observation (obs)
  (declare (xargs :guard t))
  (if (and (fn-clock-observationp obs)
           (fn-clock-has-wall obs)
           (< (floor (fn-clock-wall obs) 1000) 4294967296))
      (floor (fn-clock-wall obs) 1000)
    :clock-unusable))

; books/store-node: the article record for the next transaction, built once.
(defun fn-sn-article-record (s obs msgid payload groups
                             obligation-id subject evidence charge)
  (declare (xargs :guard t))
  (let ((stamp (fn-record-stamp-of-observation obs))
        (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (if (equal stamp :clock-unusable)
        :clock-unusable
      (fn-record-make (fn-sn-identity-next s) txid txid msgid payload groups
                      obligation-id subject evidence charge stamp))))
```

Both host prepares call `fn-sn-article-record` instead of `fn-record-make`, so
the two host copies of the record assembly disappear. The owner host passes
`(fn-own-clock (fn-owner-core state))`, the owner's own value, unread and
uncomputed by the host. The standalone store host (`fn-store-sn-prepare`,
reached from `fnn-bridge-prepare`, `host/native/io.lisp:750`, and
`tools/run_store.py:641`) gains an `observation` argument, read by the native
adapter with the same `gettimeofday` reading `fnn-owner-advance-clock` takes.
`fn-hsig-authorized-submission-event` gains an `observation` argument, and the
BP ingress context (`fn-bpi-make-context`, `books/bp-ingress.lisp:253`) gains
a fifth field, the observation the BP host took at receipt, which
`fn-bpi-ingress-prepare` hands to the record builder. Riding in the context
keeps every `bp-receiver-*` theorem statement that names `context` as a
variable textually unchanged.

`fn-sn-prepare` refuses a record whose stamp is `:legacy` (one new conjunct in
its gate, and the same conjunct on the composite child in
`fn-sn-prepare-identity`), so the live path can never write a legacy record;
`fn-accept-prepare` and `fn-node-prepare` accept either stamp kind, because
replay must install legacy articles.

## 2. The theorems

Each is stated over the function the host calls, with the host line. Each has
a teeth book entry: a positive witness first, built by the constructor and
asserting the antecedent before the conclusion, then one `must-fail` per
hypothesis. The teeth book is `tests/acl2/acceptance-stamp-tests.lisp` (new)
unless a row says otherwise.

### 2.1 The codec, at schema 1 (seam constraints)

After T1 these are constraints of the `encapsulate` in `books/records-seam.lisp`,
proved of the implementation in `books/records-canonicality.lisp`. The first
four are T1's constraints with their statements unchanged; what changes under
them is `fn-record-p`, whose eleventh field is `fn-record-stampp`.

```
(defthm fn-record-round-trip
  (implies (fn-record-p record)
           (equal (fn-record-decode-exact (fn-record-encode record))
                  (list :ok record))))

(defthm fn-record-accepted-input-is-canonical
  (implies (fn-record-result-okp (fn-record-decode-exact octets))
           (equal (fn-record-encode
                   (fn-record-result-record (fn-record-decode-exact octets)))
                  octets)))

(defthm fn-record-encode-domain
  (implies (not (fn-record-p record))
           (equal (fn-record-encode record) nil)))

(defthm fn-record-accepted-input-bounds
  (implies (fn-record-result-okp (fn-record-decode-exact octets))
           (and (fn-cbor-octet-listp octets)
                (consp octets)
                (<= (len octets) *fn-record-max-octets*)))
  :rule-classes nil)
```

T1's fifth constraint, `fn-record-accepted-input-header`, pins six octets that
include the version `0`. At schema 1 it is replaced by two:

```
(defconst *fn-record-magic-octets* '(68 102 110 45 114))  ; bstr head, "fn-r"

(defthm fn-record-accepted-input-magic
  (implies (fn-record-result-okp (fn-record-decode-exact octets))
           (equal (take 5 octets) *fn-record-magic-octets*))
  :rule-classes nil)

(defthm fn-record-accepted-schema-is-the-stamp-kind
  (implies (fn-record-result-okp (fn-record-decode-exact octets))
           (equal (nth 5 octets)
                  (if (equal (fn-record-stamp
                              (fn-record-result-record
                               (fn-record-decode-exact octets)))
                             :legacy)
                      0
                    1)))
  :rule-classes nil)
```

T1's derived `fn-record-decode-exact-refuses-another-header` becomes
`fn-record-decode-exact-refuses-another-magic` (take 5); it is what other
record kinds' dispatch uses: the retention, verdict, keyring and composite
events all carry the magic `fn-e` (`books/store-events.lisp:12`), which
differs from `fn-r` in the fifth octet.

Teeth:

| Theorem | Positive witness | `must-fail` per hypothesis |
| --- | --- | --- |
| round trip | `(fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 841000000)` asserts `fn-record-p` of it, then the round trip; the same record with stamp `:legacy` likewise | drop `fn-record-p`: stamp `:uncertain`, which encodes to `nil` |
| canonicality | the schema-1 golden vector and the existing schema-0 golden vector (`records.lisp:801`) each decode `:ok` and re-encode to themselves | drop parser success: the schema-1 vector with the stamp item written non-minimally (`h'1a00000005'` for 5) |
| magic | both golden vectors | drop parser success: an `fn-e` event's octets |
| schema is the stamp kind | both golden vectors, version octet 0 with `:legacy`, 1 with a natural | drop parser success: the schema-0 vector truncated after the version octet (octet 5 is 0, the result carries no record) |

The migration fact is stated below the seam, in `books/records-invariants.lisp`,
because only evidence needs it and no book above the codec should:

```
; The pre-T2 encoder, kept verbatim as a specification function: it ignores
; the stamp field and writes the schema-0 grammar.
(defthm fn-record-schema-0-bytes-decode-as-legacy
  (implies (fn-record-p record)
           (equal (fn-record-decode-exact (fn-record-schema0-encode record))
                  (list :ok (fn-record-with-stamp record :legacy)))))
```

Read with canonicality, this says: every byte string the pre-T2 encoder wrote
is accepted, decodes to the same ten fields with stamp `:legacy`, and
re-encodes to itself. Witness: the ten-field golden vector. `must-fail`: drop
`fn-record-p`, a record whose msgid is 251 octets.

### 2.2 The constructor: the stamp is the observation's, and only its

Subject: `fn-sn-article-record`, called at `host/store-node-host.lisp:464` and
`host/owner-host.lisp:326` (the two sites that call `fn-record-make` today).

```
(defthm fn-sn-article-record-stamps-the-observation
  (implies (natp (fn-record-stamp-of-observation obs))
           (equal (fn-record-stamp
                   (fn-sn-article-record s obs msgid payload groups
                                         obligation-id subject evidence charge))
                  (floor (fn-clock-wall obs) 1000))))

(defthm fn-sn-article-record-without-a-usable-clock-is-refused
  (implies (not (natp (fn-record-stamp-of-observation obs)))
           (equal (fn-sn-article-record s obs msgid payload groups
                                        obligation-id subject evidence charge)
                  :clock-unusable)))
```

The first is S2: the right-hand side mentions no argument but `obs`, so no
payload, header or peer can move it. Witness: a payload whose `Injection-Date`
is 2099-01-01 and an observation of 2026-09-22T12:00:00Z; the stamp is the
2026 second. `must-fail`: drop the hypothesis, an observation with `has-wall`
nil. For the second: witness, an observation with `has-wall` nil;
`must-fail`, drop the hypothesis, a usable observation.

### 2.3 Prepare refuses a legacy record

Subject: `fn-sn-prepare`, which the host reaches through `fn-spc-prepare`
(`host/store-node-host.lisp:477`, equal to it under
`fn-spc-prepare-equals-specification-under-relation`) and `fn-opc-prepare`
(`host/owner-host.lisp:338`, under
`fn-opc-prepare-equals-owner-event-under-relation`).

```
(defthm fn-sn-prepare-refuses-a-legacy-record
  (implies (equal (fn-record-stamp record) :legacy)
           (equal (fn-sn-prepare s record) s)))
```

Witness: a reserved state and a record built by `fn-sn-article-record`, whose
prepare stages it (phase `:record-staged`), then the same record with its stamp
replaced by `:legacy`, whose prepare is the identity. `must-fail`: drop the
hypothesis, the stamped record in the same state.

### 2.4 Finish installs the stamp the record carries

Subject: `fn-sn-finish`. Host lines: `fn-store-sn-finish` calls it at
`host/store-node-host.lisp:549`; the owner reaches it through its `(:complete)`
event, `fn-owner-finish` at `host/owner-host.lisp:415`, which is
`fn-own-complete`'s call at `books/owner.lisp:1034`. (Line 443 of the store
host is the prepare of §2.2, not the finish.) One theorem per arm that
installs an article; the retention, verdict and keyring arms install none and
are T4's to state.

```
; The article arm.
(defthm fn-sn-finish-installs-the-stamp-the-record-carries
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                (not (fn-stxe-p (fn-sn-completion-record s)))
                (not (fn-stxk-p (fn-sn-completion-record s)))
                (not (fn-stxa-p (fn-sn-completion-record s))))
           (equal (fn-article-stamp
                   (fn-find-article
                    (fn-record-msgid (fn-sn-completion-record s))
                    (fn-state-articles
                     (fn-node-acceptance (fn-sn-node (fn-sn-finish s))))))
                  (fn-record-stamp (fn-sn-completion-record s)))))

; The accepted-statement composite arm: the article is the fn-r child.
(defthm fn-sn-finish-installs-the-stamp-the-composite-carries
  (implies (and (fn-sn-completion-enabledp s)
                (fn-stxa-p (fn-sn-completion-record s)))
           (equal (fn-article-stamp
                   (fn-find-article
                    (fn-record-msgid
                     (fn-replay-composite-record (fn-sn-completion-record s)))
                    (fn-state-articles
                     (fn-node-acceptance (fn-sn-node (fn-sn-finish s))))))
                  (fn-record-stamp
                   (fn-replay-composite-record (fn-sn-completion-record s))))))
```

`fn-sn-committed-recordp` (`books/store-node-invariants.lisp:399`) gains the
conjunct `(equal (fn-article-stamp article) (fn-record-stamp record))`, so
`fn-sn-finish-installs-exact-article-and-archive-pin` carries the stamp as
well; the stamp theorems above are proved from
`fn-sn-finish-is-actual-durable-completion` and the node's install, not from
that predicate, so that each is a keystone of its own and not an unfolding.

Teeth (article arm): the witness is a state driven from `fn-sn-initial`
through the reservation, `fn-sn-prepare` of an `fn-sn-article-record` built
from a 2026 observation, and the file steps to `:completing`; it asserts
`fn-sn-completion-enabledp` and the four arm facts, then the conclusion.
`must-fail`: drop `fn-sn-completion-enabledp` (the same state one step before
`:completing`: finish is a no-op, the article is absent); drop each arm
exclusion in turn with a completion record of that kind (a retention event,
a verdict event, a keyring snapshot event, a kind-4 composite), each of
which installs no article under the completion record's own msgid accessor.
Teeth (composite arm): the witness is the kind-4 composite from
`tests/acl2/stx-accept-records-tests.lisp` rebuilt with a stamped child;
`must-fail` for each of its two hypotheses likewise.

### 2.5 Replay reproduces it, over a mixed journal

Subject: `fn-replay-apply-record` and `fn-replay`, which `fn-sn-recover`
reaches through `fn-sf-replay-node` at every open (`fn-store-sn-recover`,
`host/store-node-host.lisp:133`).

```
(defthm fn-replay-apply-record-installs-the-stamp
  (let ((article (if (fn-stxa-p record)
                     (fn-replay-composite-record record)
                   record)))
    (implies (and (fn-node-statep node)
                  (fn-store-event-p record)
                  (not (fn-store-retention-event-p record))
                  (not (fn-stxe-p record))
                  (not (fn-stxk-p record))
                  (consp (fn-replay-apply-record node record)))
             (equal (fn-article-stamp
                     (fn-find-article
                      (fn-record-msgid article)
                      (fn-state-articles
                       (fn-node-acceptance
                        (fn-replay-apply-record node record)))))
                    (fn-record-stamp article)))))

; The journal-level statement.  fn-replay-journal-article-stamps is a
; specification: the (msgid . stamp) pair of every article record of RECORDS,
; oldest first, reading a kind-4 composite's fn-r child; it never calls the
; replay step.  fn-articles-msgid-stamps lists (msgid . stamp) of the node's
; articles, oldest first.
(defthm fn-replay-article-stamps-are-the-journal-stamps
  (implies (fn-replay-okp (fn-replay groups capacity records))
           (equal (fn-articles-msgid-stamps
                   (fn-state-articles
                    (fn-node-acceptance
                     (fn-replay-result-node
                      (fn-replay groups capacity records)))))
                  (fn-replay-journal-article-stamps records))))
```

Teeth: the witness journal is mixed on purpose, four records in sequence 0 to
3: a schema-0 article (decoded, stamp `:legacy`), a schema-1 article, a
retention event, and a kind-4 composite whose child is schema 1; the node's
pairs are `((m0 . :legacy) (m1 . s1) (m3 . s3))`, and the witness asserts
`fn-replay-okp` first. `must-fail` for the journal theorem: drop
`fn-replay-okp`, the same journal with record 2's sequence number wrong (the
fault node holds `m0` and `m1`, the journal lists `m3` too). For the one-record
theorem: one per hypothesis, each with a record of the excluded kind or a node
for which the apply is `nil`.

**Why the mixed journal needs no extra hypothesis.** Replay never sees bytes:
the Store event decoder hands it records, and the codec has already mapped a
schema-0 record to stamp `:legacy` (§2.1). The mixed case is therefore the
general case of both theorems, and the witness is what shows it is not vacuous.

### 2.6 NEWNEWS answers from the stamp

Subject: `fn-nntp-newnews-response` (`books/nntp-responses.lisp`), which the
served path reaches as today:
`fn-nntp-step-dispatches-newnews-to-the-newnews-response` is unchanged and
stays the subject clause.

**The definitions.** The fuel argument and `*fn-nntp-newnews-parse-budget*`
are deleted with `fn-nntp-newnews-stamp` and `fn-nntp-newnews-field-value`.
The scan walks the committed list newest first, as today, carrying one value:

```
; An article is new since THRESHOLD (milliseconds, a whole second) when its
; own stamp is at or after it.  A legacy article is dated by HORIZON: the
; stamp of the nearest article accepted after it that has one, else the
; reader's clock second, else :none, in which case it is reported.
(defun fn-nntp-newnews-newp (threshold stamp horizon)
  (let ((instant (if (natp stamp) stamp horizon)))
    (or (not (natp instant))
        (fn-ng-less-equal threshold (* 1000 instant)))))

(defun fn-nntp-newnews-scan (groups threshold articles horizon)
  (if (consp articles)
      (let* ((a (car articles))
             (stamp (fn-article-stamp a))
             (rest (fn-nntp-newnews-scan groups threshold (cdr articles)
                                         (if (natp stamp) stamp horizon))))
        (if (and (fn-nntp-newnews-candidatep groups a)
                 (fn-nntp-newnews-newp threshold stamp horizon))
            (cons (fn-nntp-string-octets (fn-article-msgid a)) rest)
          rest))
    nil))
```

The response passes, as the initial horizon, `fn-nntp-newnews-reader-horizon
env`: the whole second of the reader's pinned observation when it has a wall
reading, else `:none`. The horizon advances over every stamped article,
candidate or not, because it is a fact about acceptance order in the store and
not about the matched groups.

**The keystones.**

```
; fn-nntp-newnews-accepted-since is the specification: for each article it
; searches the articles before it in the list (those accepted after it) for
; the last one with a natural stamp, and filters by fn-nntp-newnews-newp.  It
; carries nothing; it is quadratic and never on a served path.
(defthm fn-nntp-newnews-scan-is-the-acceptance-filter
  (equal (fn-nntp-newnews-scan groups threshold articles horizon)
         (fn-nntp-newnews-accepted-since groups threshold articles nil horizon)))

; The cost, as a theorem: erasing every payload changes nothing.
(defthm fn-nntp-newnews-scan-reads-no-payload
  (equal (fn-nntp-newnews-scan groups threshold
                               (fn-articles-without-payload articles) horizon)
         (fn-nntp-newnews-scan groups threshold articles horizon)))

(defthm fn-nntp-newnews-scan-lines-at-most-candidates
  (<= (len (fn-nntp-newnews-scan groups threshold articles horizon))
      (fn-nntp-newnews-candidate-count groups articles))
  :rule-classes (:rewrite :linear))

(defthm fn-nntp-newnews-lines-are-clean
  (fn-nov-clean-line-listp
   (fn-nntp-newnews-scan groups threshold articles horizon)))
```

The plan's name `fn-nntp-newnews-scan-reports-only-articles-accepted-at-or-after`
is the soundness half of the first keystone; the equation is stated instead
because it carries completeness as well: an article accepted at or after the
instant in a matched group is reported, which the budgeted scan could not
promise. `fn-nntp-newnews-scan-reports-only-witnessed-lines`,
`-answers-exactly-within-the-budget`, `-reports-at-most-the-budget` and
`-refusal-is-the-only-other-outcome` retire with the budget; the effects book's
`fn-nntp-newnews-block-is-block-text` is restated without the fuel.

None of the four has a hypothesis, so their teeth are witnesses, each asserting
the facts it relies on first (the §4 witness rule of the review):

1. a stamped article at `T`: reported at threshold `T`, absent at `T + 1s`;
2. a stamped article whose payload has no `Date` and no `Injection-Date` and
   does not parse: reported (the pre-T2 scan omitted it), and the same list
   with payloads erased gives the same lines;
3. a mixed list, newest first `(stamped s=100, legacy L)`: `L` reported at
   `T <= 100s`, absent at `T > 100s`;
4. a list `(legacy L)` alone: reported below the reader horizon, absent above
   it, and reported at every threshold when the reader has no wall reading;
5. a candidate-free list of 300 articles: the answer is the empty block, not
   503 (the old budget's refusal is gone);
6. the payload-erasure theorem on a 32 KiB unparseable payload.

**NNT-008, restated.** Title: "NEWNEWS answers from this node's acceptance
stamp". Statement: NEWNEWS reports exactly the Message-IDs of the committed
articles available at a number in a group the wildmat matched whose acceptance
stamp, the owner's wall-clock second at prepare, is at or after the requested
instant; an article written before schema 1 carries no stamp and is dated by
the stamp of the nearest later-accepted article that has one, else by the
reader's clock second, else it is always reported. **The cost, with its scope,
in one sentence:** one `NEWNEWS` is one pass over the committed article list
with, per article, the membership test `GROUP` and `LISTGROUP` already pay and
at most one natural-number comparison, reading no article octet
(`fn-nntp-newnews-scan-reads-no-payload`), and answering at most `C` lines for
`C` candidates in the matched groups, where `C` is bounded by the store's
`max_transactions` profile and nothing smaller, since no size refusal remains.
The pessimistic number is `O(A * G')` for `A` committed articles and `G'`
matched groups, the same walk every reader command pays until the per-group
index reaches the dispatcher (T17); the parse term `min(C,256) * P` of today's
bound is gone.

## 3. Migration

**A store written before the stamp keeps serving.** Its records are schema 0;
the decoder accepts every one (`fn-record-schema-0-bytes-decode-as-legacy`)
and replay installs them with stamp `:legacy`
(`fn-replay-article-stamps-are-the-journal-stamps`). No record is rewritten,
no store configuration format changes, and the frame, kind octets and FNST
ceilings are untouched. The 915 stores on persvati and the T0 node's store on
hbox open under the T2 image and serve every article they served. The
control, beside the theorem: T1's golden-vector tool over every schema-0 vector
and over the record files of one carried-over store, each decoding and
re-encoding byte-identically under the T2 codec.

**It is one-way.** The first schema-1 record a node writes makes its store
unreadable to a pre-T2 image: the old decoder answers `:unknown-version`,
replay faults and the store refuses to open. That is fail-closed, not a
misreading, so no configuration-format bump is proposed (§7 question 5).

**NEWNEWS on a mixed store.** RFC 3977 §7.4.2 defines the answer as the
message-ids of articles "posted or received on the server ... since the
specified date and time"; it lets a message-id appear more than once and lets
the list be empty when there is no new news. It does not permit leaving out an
article received after the instant. (The current `specs/nntp.md` text reads
"permits it to be empty, so the omission stays inside the response" as a
licence to omit; that reading is not the RFC's, and T2 removes the omission
it covered.) For a legacy article fn does not know the instant, so it chooses
the answer that can over-report and cannot omit: the article is dated by the
stamp of the nearest article accepted after it that has one. Acceptance order
is list order, so that stamp was read after the legacy article was committed;
if the wall clock did not run backwards across the upgrade restart, it is an
upper bound on the legacy article's acceptance instant, and reporting it
whenever the threshold is at or below that bound omits no legacy article that
arrived since. When no stamped article follows, the reader's clock second
bounds it the same way; with no clock at all it is reported. A client syncing
across the upgrade therefore sees every legacy article it might have missed,
at most once more than it needed to, and a client whose last sync is after
the first stamped acceptance sees none. The "did not run backwards" condition
is about true time and is stated here, not proved (§8).

**Matrix rows (`tools/v0_matrix.py`).**

| Row | Today | After T2 |
| --- | --- | --- |
| `V0-READ-NEWNEWS` | accepted; the note allows an empty block when no article's date decodes | accepted, and the block is exactly the set `LISTGROUP` lists for the group at the 1970 instant: every article is dated, legacy ones included |
| `V0-READ-NEWNEWS-FUTURE` | empty block | empty block, now also on a mixed store (the reader horizon dates legacy articles) |
| `V0-READ-NEWNEWS-SYNTAX` | 501 | unchanged |
| `V0-READ-NEWNEWS-STAMP` (new) | none | POST, then NEWNEWS since the DATE read before it reports it and NEWNEWS since that second plus one reported by a DATE after it does not |
| `V0-READ-NEWNEWS-LEGACY` (new) | none | on a store carried over from a pre-T2 image: NEWNEWS since 1970 reports the legacy articles; after one POST, NEWNEWS since the second after that POST's stamp reports neither |

`tests/test_reader.py`, `tests/interop_nntplib.py`, `tools/inn_lab.py` and
`tests/scenarios/catalog.json` mention NEWNEWS; any expectation of the 503
budget line changes with the row.

## 4. D10-a: no clock at prepare is a refusal, with the clock's reason

Three facts decide it. D10-a: a refused reading costs the owner its clock, and
a decision attempted without one is refused with its own line, because "the
symptom reaches the client as an article verdict" is the defect D10-a
repaired. D13 and the review's rule: uncertain, refused and accepted stay three
words at every boundary, and an uncertain outcome never reads as accepted. And
§1.2: the stamp is part of the committed record.

An "accepted, stamp uncertain" record would put an uncertain value inside an
accepted outcome, permanently: NEWNEWS would have to treat it as it treats a
legacy article for the life of the store, for a fault that lasted one event,
and legacy articles would stop being a fixed set written before the upgrade.
So the answer is **refuse the submission**, before any record is written, with
the clock's reason:

- `fn-sn-article-record` answers `:clock-unusable` (§2.2). The owner host's
  prepare returns that word; `fnn-owner-attempt` (`host/native/owner.lisp:685`)
  consumes the reservation through the proved `fn-owner-refuse-reservation`
  path, as it does for any refused prepare, and returns `:clock-unusable`
  instead of collapsing it into `:refused` (`host/native/owner.lisp:722`).
- `fn-own-outcome-completion` (`books/owner.lisp:1485`) maps `:clock-unusable`
  to a completion of the same name, a refusal: its resolution record is
  `:feed-abort`, as for `:refused`. It must not fall to the `(t :uncertain)`
  arm, which is where an unknown word lands today.
- The reply is the clock's, not the article's: POST answers D10-a's existing
  `441 posting failed; this server has no usable clock reading`
  (`books/nntp-post.lisp:175`); IHAVE answers `436 retry later; no usable clock
  reading`; TAKETHIS answers in the temporary class the peer book already uses
  for an uncertain transfer, never 437 or 439; a control or BP submission
  answers `:refused` with reason `:clock-unusable`. A BP ADU refused for the
  clock stays staged: it is not a bundle rejection (§7 question 10).
- Teeth: an owner witness whose clock was dropped by a contradicted reading
  (D10-a's own witness) with a queued POST; the take and attempt produce the
  clock line and no record, and a `must-fail` shows the same submission with a
  clock is durable.

The window is D10-a's: one event. It is reachable in the native owner only when
a submission queued under an earlier read is drained in the event whose
reading was refused. No new host reading is added before prepare: the owner
takes one at every read (`host/native/owner.lisp:978`, `:1046`), prepare is
inside that read's mutex hold, and a stamp later than the reading that decided
the submission would buy nothing but a second refusal point. The standalone
store supplies one reading per prepare; a malformed one is `:invalid`, a
defect of that host, as `fnn-owner-advance-clock` treats it.

## 5. The crash model

The stamp is a field of the record, so it is in the bytes every existing cut
already stages, syncs, links and recovers; T2 adds no write, no file, no phase
and no cut, and `tools/transcribe_check.py` has nothing new to match. Which
theorems carry "the stamp after any crash is the stamp at commit":

1. `fn-snt-mixed-trace-ready-node-is-exact-replay`
   (`books/store-node-traces.lisp:621`): over any mixed trace of prepares, I/O,
   finishes, crashes and recoveries, a ready or recovered node **is** the
   replay of the durable records. This is the keystone; T2 adds nothing to it.
2. `fn-replay-article-stamps-are-the-journal-stamps` (§2.5): that replay
   installs each durable record's stamp.
3. `fn-record-round-trip` and `fn-record-accepted-input-is-canonical` (§2.1):
   the durable bytes and the record, stamp included, determine each other.
4. At the byte level, PRF-041's K1 to K4 (every crash image of a related store
   reopens with every acknowledged record, byte-exact), with their standing
   caveat that K0 is open (plan §3.1, T5 and T16).

`books/store-node-traces.lisp` is red at its digest today (a T0 red, plan §1);
the carrier is only as good as that book's certification, and T2 is not DONE
until it is green at T2's bytes. The campaign observation: after the
`postpublish` cut and recovery, NEWNEWS since the prepared second reports the
article and NEWNEWS since the next second does not, which T5's campaign run
records per cut.

## 6. The lane brief

### 6.1 Proposed split

T2 as the plan sizes it (4 to 6 lane-days) did not count four callers that the
stamp cannot skip, because `fn-sn-prepare` refuses a legacy record: the signed
submission (`books/hybrid-store.lisp`, `host/hybrid-signature-host.lisp:55`),
the BP ingress record builder and its ten `bp-receiver-*` invariant books
(`books/bp-ingress.lisp`, `host/bp-ingress-host.lisp:72`), the checkpoint codec
(`:legacy` in its symbol table), and the D10-a outcome plumbing through
`owner`, `nntp-post` and `peer-inbound`. The recommendation (§7 question 3)
is two steps, each DONE on its own:

- **T2a, the stamp in the record** (critical path, before T3 to T6): §1, §2.1
  to §2.5, §4, §5. NEWNEWS behaviour is unchanged by T2a; the budgeted scan
  keeps reading `Injection-Date`. DONE: the theorems of §2.1 to §2.5 and §4
  with teeth, the closure green at T2a's bytes, a carried-over store opening on
  the image, the evidence file.
- **T2b, NEWNEWS over the stamp** (off the critical path): §2.6, the rows of
  §3, NNT-008 and PRF-052 restated. It edits only `nntp-responses`,
  `nntp-newnews`, `nntp-invariants`, `nntp-effects` and their tests, so it can
  run in phase 3 beside T4, T5 and T9 on disjoint books. DONE: §2.6 with
  teeth, the rows accepted on the image.

If ember prefers one step, the order below is unchanged and T2b's books follow
T2a's in the same lane.

### 6.2 What T2 needs from T1's seam, by name

From `books/records-shape.lisp` (not a codec; stays concrete): the
`fn-defrecord fn-record` form, into which T2 adds the eleventh field
`(fn-record-stamp fn-record-stampp)`, and `fn-record-stampp` itself.

From `books/records-seam.lisp` (the `encapsulate`):

| Constraint | At schema 1 |
| --- | --- |
| `fn-record-encode-domain` | kept, statement unchanged |
| `fn-record-round-trip` | kept, statement unchanged |
| `fn-record-accepted-input-is-canonical` | kept, statement unchanged |
| `fn-record-accepted-input-bounds` | kept, same `*fn-record-max-octets*` |
| `fn-record-accepted-input-header` (6 octets, version 0) | **replaced** by `fn-record-accepted-input-magic` (5 octets) and `fn-record-accepted-schema-is-the-stamp-kind` |
| derived `fn-record-decode-exact-refuses-another-header` | becomes `-refuses-another-magic`, derived from the magic constraint |

The request to T1, through root, while T1 is still in flight: export the
header constraint as the five magic octets plus "octet 5 is the schema
octet" now, so that no consumer of the six-octet form exists when T2 lands
(§7 question 9). Nothing else in T1's seam needs to change; everything above
the seam sees one new accessor, `fn-record-stamp`, and one new recognizer
conjunct.

### 6.3 Books, in order

The edited set, each certified with its test book before the next layer
relies on it:

1. The record: `records-shape` (field), `records` (schema dispatch; the
   pre-T2 encoder kept as `fn-record-schema0-encode`), `records-invariants`,
   `records-canonicality`, `records-seam`, `records-attach`, new
   `records-stamp` (`fn-record-stamp-of-observation`; includes
   `records-shape` and `clock`), and T1's golden tool with one schema-1
   vector and one cbor2 case in the independent probe.
2. Acceptance and node: `acceptance` (article and pending stamp fields,
   `fn-accept-prepare` stamp argument, last), `acceptance-invariants`, `node`
   (`fn-node-prepare` stamp argument, last), `node-invariants`, `node-traces`,
   `node-retention-transitions`.
3. Replay and the carriers: `replay` (pass `fn-record-stamp`),
   `stx-accept-records` (comment only: the child may be schema 1),
   `hybrid-store` (observation argument), `store-events` (dispatch on the
   magic), `checkpoint` and `checkpoint-codec` (`:legacy` in
   `*fn-cpc-symbols*`).
4. The store: `store-node` (`fn-sn-article-record`, the prepare conjuncts,
   `fn-sn-pending-record` with the stamp), `store-node-invariants`
   (`fn-sn-committed-recordp`, §2.3, §2.4), `store-node-traces`,
   `store-node-resolution`, `store-prepare-correspondence`,
   `owner-prepare-correspondence`, `store-observed*`.
5. Ingress: `bp-ingress` (context observation) and the `bp-receiver-*` books
   whose proofs destructure the context.
6. The D10-a outcome: `owner` (`fn-own-outcome-completion`), `owner-invariants`,
   `nntp-post` (the reply arm), `peer-inbound` (the transit arms).
7. T2b: `nntp-responses`, `nntp-newnews`, `nntp-invariants`, `nntp-effects`.

Host: `host/store-node-host.lisp:442` (`fn-store-sn-prepare` gains
`observation`; line 464 calls `fn-sn-article-record`), `host/owner-host.lisp:304`
(line 326 calls `fn-sn-article-record` with `fn-own-clock`),
`host/native/io.lisp:750` (reads the clock, passes it),
`host/native/owner.lisp:685` (passes the word through), 
`host/hybrid-signature-host.lisp:55`, `host/bp-ingress-host.lisp:72`,
`tools/run_store.py:641`, `tools/run_owner.py:141`. Tests: the new teeth book
`tests/acl2/acceptance-stamp-tests.lisp`; every test book that calls
`fn-record-make` (35 files), `fn-make-article` (6), `fn-accept-prepare` or
`fn-node-prepare` gains the stamp argument. Counts at `3373f935`:
`fn-record-make` 101 call sites in 43 files, `fn-node-prepare` 102 in 26,
`fn-accept-prepare` 56 in 18, `fn-make-article` 22 in 7. The edit is
mechanical and the stamp is always the last argument.

Specs updated with the code: `specs/encoding.md` (ENC-004's first evolution),
`specs/store-experiment.md` (the schema-1 grammar), `specs/nntp.md` §Polling
(T2b), `specs/time.md` (the stamp as a consumer of the owner's clock). Registry
edits, root's: ENC-004's note and keystones; NNT-008 and PRF-052 restated
(§2.6); a new proof target for §2.2 to §2.5 and §4; ENC-001's note says schema
1.

### 6.4 Closure, box, size

`records-shape` is below nearly every book, so T2a's closure is the image
closure and the DTN closure together; this is the "one red umbrella of phase
2" the plan names. Discovery: `python3 tools/farm.py submit hbox --remote-root
<abs lane path> --affected-by books/records-shape.lisp --closure` at the 300 s
per-book budget, one provisional wave, every red named; the final closure run
at 1800 s. Then `python3 tools/green_check.py --changed-since 3373f935
--strict`. Box: hbox (phase 2, hbox lane 1), under `swarm-build`. Evidence:
`planning/evidence/t2a-acceptance-stamp-<rev>-2026-09-2x.md`, with the
carried-over-store control and the image rows.

Size: T2a 5 to 7 lane-days, Fable (the plan's 4 to 6 plus the four callers of
§6.1); T2b 1.5 to 2 lane-days, Opus. The pessimistic figure is the whole-tree
recertification: each discovery wave over the image closure is the wall of a
full wave on hbox, and a proof that stops returning inside it is a finding for
the 300 s rule, not a budget to raise.

## 7. Questions for ember

1. **Seconds or milliseconds in the stamp?** Recommend seconds (§1.3): the CBOR
   profile and the checkpoint universe are uint32, and nothing reads a finer
   instant. Milliseconds would cost a CBOR seam change across T1's clusters and
   a checkpoint codec change, for no answer that differs.
2. **How NEWNEWS dates a legacy article.** Recommend the horizon rule of §3
   (the nearest later stamp, else the reader's clock). Alternatives: always
   report legacy articles (simpler, but every NEWNEWS lists them forever), or
   omit them (loses articles for a client syncing across the upgrade, which the
   RFC does not permit).
3. **Split T2 into T2a and T2b?** Recommend yes (§6.1): T2a is what T3 to T6
   wait for; T2b touches only the reader books and runs in phase 3. Each is a
   complete property, not a partial row.
4. **The no-miss polling property.** "A client that uses a DATE answer as its
   next NEWNEWS threshold sees every article committed after that DATE" holds
   when stamps are taken at prepare, no reader pins between a prepare and its
   finish, and the wall clock does not run backwards. The native host has the
   second fact (one mutex); the owner model does not, since an `:open` event
   can fall between a take and `(:complete)`. Recommend proving it in T6 (it is
   a pinned-reader theorem over `owner-invariants`), either from a model rule
   that defers opens while a transaction is in flight or with the host's mutex
   as a named `A-HOST` fact, and stating it with A-CLOCK (question 7). Not in T2.
5. **Rollback.** After the first schema-1 record a pre-T2 image refuses the
   store (fail-closed). Recommend accepting that, with no store-format bump, and
   saying in the deploy runbook and on the node's page that the T2 deploy is
   one-way.
6. **Any size refusal for NEWNEWS?** Recommend none: the scan is now the same
   walk as `LISTGROUP`, and the answer is bounded by the store's own capacity.
   The alternative is a line cap with RFC 3977 §3.2.1's 503.
7. **A-CLOCK.** The legacy dating rule and question 4 rest on "the wall clock
   does not run backwards across the interval". T2's theorems are stated over
   wall readings and need no assumption. Recommend adding A-CLOCK to
   `books/assumptions.lisp` with question 4's theorem, not in T2.
8. **Nodes with no wall clock.** After T2 an owner whose observations have
   `has-wall` nil accepts nothing (it already injects nothing). The native host
   always supplies a wall reading. Recommend accepting this for v0 and recording
   the wall-less DTN node as open under FLR-004; serving one needs a stamp kind
   NEWNEWS dates like a legacy article, which is a later schema step.
9. **T1's header constraint.** Recommend root asks T1 now to export the magic
   (five octets) and the schema octet instead of the six-octet header (§6.2), so
   T2 changes no constraint another lane has started consuming.
10. **A BP ADU refused for the clock.** Recommend it stays in inbox staging with
    no deletion report, since a clock refusal says nothing about the bundle;
    T12's lane confirms against `specs/bp-node-machine.md` before T2a lands the
    ingress change.

## 8. What this design does not claim

- The stamp is this node's wall reading at prepare, to the second. It is not
  true time, not an interval with an error bound, and not comparable across
  nodes; `specs/time.md`'s honesty of `wall-error-bound` stays an unstated
  assumption.
- It is not the commit instant. The prepare-to-commit gap is invisible to
  readers in the native owner (one mutex); in the owner model it is question 4.
- Stamps are not monotone in sequence order across a restart or a D10-a
  refusal: the first reading after either is admitted whatever it says, which
  is D10-a's recorded cost.
- It exposes nothing new to readers: no `HDR`, `OVER` or header carries the
  stamp; that is T10b's S6 to decide.
- It stamps article records only. Retention, keyring and verdict events carry
  no stamp; no query reads their time.
