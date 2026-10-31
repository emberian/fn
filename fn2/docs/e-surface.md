# fn2 layer E: the surface a consumer speaks (present state; rewritten whole by the layer-E seat)

The contract is `build/coordinator/briefs/FN2-LAYER-E-SURFACE.md` over `FN2-SEAT-COMMON.md`. This file
holds E's decisions as built, or marked *(statement)* before the build. Its first part is the consumer
port (brief item 3; REGROUND §4 item 1 and §5), the design M2 is accepted by: "a consumer appends, reads,
waits and acks on the laptop, and an NNTP reader sees the same article". Peering and BP (items 4-5) are
designed against the same engine next (§13); TLS, auth, CLI, web and packaging (items 1, 2, 6-8) follow
the spine.

Sources: FN2-ORIENTATION, REGROUND-20261030 §4-5, WIDEST-ROLE §2-3 (Port, Meter, Grant),
INBOX-DELIVERY §4-5 (ruled: selection), CLIENTS-AND-DATA-MODELS §1.1-1.2 (Mini, helm, their numbers),
IDENTITY-ACROSS-PEERS (rulings 2, 6, 8), MACHINE-FORM, WORKFLOW-20261031, ROUND2-ASTRA §B.2 and §F
scenarios 7-9, D's layer doc §6, §11, §13, §14-15, C's §4 and §6, fn1's `specs/consumer-progress.md` and
`docs/agents.md` (the meaning kept), Mini's `docs/FN-CONSUMER-E1.md` and `Kernel/FnConsumer*.lean`.
Astra's read: `build/coordinator/fn2/lanes/e-quests/astra-1.md` (§15 says what it changed).

## 0. Built (dev; the commit that lands this file)
| piece | file | state |
|---|---|---|
| the port form: `defport`, `defcarrier`, the generated enums, readers, outcome recognizer, precondition order, the binding/class/coverage checks, loss signatures | `fn2/books/port.lisp` | certifies alone (no core) |
| the consumer port and its three carriers | `fn2/books/consumer-port.lisp` | ten verbs; L, R, N; N's bindings checked against D's NNTP reply rows |
| the reference model (the meaning; the CONSUMER checker's oracle) | `fn2/books/consumer-model.lisp` | the ten verbs, the world's steps, nine faults |
| the keystones K0-K8, statement first, owed with teeth | `fn2/books/owed-consumer.lisp` | 0 proved (ember's ruling); every tooth evaluates |
| Mini's processing transaction, twelve cuts | `fn2/tests/consumer-mini.lisp` | all accepted; K0-K8 hold on each; six faults caught |
| helm's rooms, tiny profile | `fn2/tests/consumer-helm.lisp` | accepted; K0-K8 hold; three faults caught |
| the form's refusals (eight malformed ports and carriers refused; the bridge loss computed) | `fn2/tests/port-unit.lisp` | certifies |
| big-endian layout kinds `:u16be :u32be :u64be (:octets16 n) (:octets32 n)`, codes 12-16, every earlier code unchanged (main's ruling: E builds them, B reads the diff) | `fn2/books/layout.lisp` | the interpreter, the generated codec and the list spec; teeth in `layout-unit` (exact octets, `:wide`, `:length`, `:truncated`), the 10,000-assignment roundtrip campaign with mutations over a big-endian layout |
| the frames: FNCT (header layout, BLAKE3 trailer), `fncu` v1 and v2, kind 4 codes 0-18, replies 5, 6, 9 and 28, page items, results; what each code is (§4.2) | `fn2/books/consumer-codec.lisp` | every form a `deflayout`; the code table checked against the port and both carriers |
| fn1's bytes as fixtures | `fn2/tests/consumer-codec-unit.lisp` | fn1's three `.fncu` vectors read from `tests/fixtures/consumer-position/` and re-encoded exactly; fn1's eleven request payloads decoded and re-encoded; fn1's twenty-one refusal words; BLAKE3 at a known answer; every fixture through the generated codec |
Owed, in order: peering and BP designed (§13); then, when D5 2/n serves a durable POST and D6 an article,
the served kind `fn2-cns` and the XFNC block (§14).

## 1. What the consumer port is
One port, `fn2-consumer`, is the interface every application speaks: Mini, helm's seats, akapug's
fleet, an agent, a script. Its ten verbs (§3) run over the one engine: an appended item is an article in
D5's transaction, filed in a group and in the addressing index; a read is C's range reads over
per-stream indexes merged by commit position; a cursor is C's `fn2-consumer-cursor` fold; a retry
answer is C's `fn2-outcome` (S-OUTCOME). The port adds no store, no queue and no second authority.

| carrier | where | bytes | who |
|---|---|---|---|
| **L**, local control | the owner's 0600 Unix socket, peer UID checked | FNCT frames; fn1's codes 0-10 with fn1's payloads, translated (§4.2); the port's codes 11-18 | `fn consumer`, `fn-agent`, local scripts |
| **R**, remote | the authenticated (TLS) NNTP connection: `XFNC <length>` and one framed FNCT body (§5) | the port's own FNCT payloads | Mini on another box, helm's seats, any remote agent |
| **N**, the NNTP convention | POST, ARTICLE | RFC 3977 | any newsreader; it sees the same articles |

R binds the cursor's principal to the connection's login, rechecks current authority on every read and
wake, and admits the remote whitelist (§3). N is a translation of the port with declared losses (§2.3).

## 2. The port as data (`defport`, `defcarrier`; `fn2/books/port.lisp`)
WIDEST §2: "an interface as data, generated from the command grammar and read by parser, machine,
client, checker and wiring validator alike".

### 2.1 The declaration
`(defport NAME :fields ((F KIND) ...) :reasons (WORD ...) :verbs ((VERB :request (F ...) :result (F ...)
:effect E :retry R :grant (SCOPE F) :meter (DIM ...) :reasons (WORD ...) :spec S) ...))`. Each verb is a
`(:command NAME-VERB)` row through `fn2-declare` with `:grammar NAME :port t` (the existing declaration
kind; Astra agrees a new kind buys nothing; port rows do not satisfy NNTP's keyword or state rules and
are filtered by `:port`). Checked at expansion: fields declared; `:effect` one of `:read :durable :park`;
`:retry` one of `:op :idempotent :position :repeat`, and a durable verb is never `:repeat` (its lost
reply must be settleable); the grant's field is a request field; `:requests` among the meter dimensions;
reasons declared. Generated: the verb, field and reason constants; per-verb readers (effect, retry,
reasons, arity, request, result, grant scope and field, meter, spec); `NAME-outcome-p` (accepted with one
value per result field; `(:refused WORD [DETAIL])` with a word the verb may give, DETAIL carrying for
example the evidence outcome beside a conflict; `(:uncertain PHASE)` only for a durable verb); and
`NAME-admit`, the precondition order of §6. The words `access` and `meter` are added to every verb by
the generator, so no verb can omit its preconditions' refusals.

### 2.2 Carriers
`(defcarrier NAME :port P [:frame :fnct | :grammar G] :binds (...) :refuses (VERB ...) :loses ((VERB
FIELD WORD) ...))`. A frame binding is `(VERB KIND CODE)`, the codes distinct. A grammar binding is
`(VERB COMMAND :terminal (REPLY ...))`: the terminal replies of D's command that carry the verb's
outcomes (POST's 340 is a continuation, never an outcome), and their `:class`es must cover every class
the verb can produce, so accepted, refused and uncertain stay distinct all the way out. Every verb is
bound, refused by name, or declared `(VERB * :not-carried)`, exactly once. Each carrier is a `(:command
NAME)` row; generated: `NAME-binding` and `NAME-loss`. The N carrier binds append to POST's `:received`
/ `:refused-*` / `:uncertain` and fetch to ARTICLE's `:sent` / `:reclaimed-msgid` / `:withdrawn-msgid` /
`:no-msgid`, checked against `fn2-nntp`'s table when the book loads.

### 2.3 Losses are a product
A carrier's loss for a verb is a set of `(FIELD . WORD)`, FIELD one of the verb's fields or `*`; WORD
one of `:retry-by-message-id :reply-code-only :no-position :not-carried`. A bridge through two carriers
loses the union, verb by verb (`fn2-port-loss-union`). N loses append's op (retry by Message-ID only)
and its position, numbers and receipt (the reply code only), and carries no read, wait, ack, position,
status, register, rebase or unregister. The first draft ordered losses in one chain; Astra showed they
are independent (§15).

## 3. The verbs (`fn2/books/consumer-port.lisp`)
Every verb also answers `access` (the grant step) and `meter` (the meter step).

| verb | request | accepted | refused | uncertain | carriers |
|---|---|---|---|---|---|
| `register` | consumer id, streams, start (`:now` or `:history`) | cursor; the same registration again answers the recorded cursor | `query`, `rebase-required` (a changed registration) | after its record may exist | L R |
| `rebase` | cursor, optional streams, start (`:keep`, `:now`, `:history`) | cursor under a new epoch | `scope`, `unknown-consumer`, `query` | as register | L R |
| `unregister` | cursor | | `scope`, `unknown-consumer` | as register | L R |
| `read` (fn1 `poll`) | cursor, limits ≤ policy | items, `more`, next cursor proposal | `scope`, `unknown-consumer`, `rebase-required`, `cursor-version` | never | L R |
| `wait` | cursor, limits, timeout | the read's answer when it answers | as read, `waiters` | never | L R |
| `ack` | cursor proposal | position | `scope`, `unknown-consumer`, `rebase-required`, `behind`, `beyond-frontier`, `cursor-version` | after its record may exist | L R |
| `position` | consumer id | the recorded cursor | `unknown-consumer` | never | L R |
| `status` | consumer id | position, frontier, their difference, counters (§8) | `unknown-consumer` | never | L R |
| `fetch` | reference | the article's octets | `unavailable` (absent, unreadable or reclaimed alike), `withdrawn` | never | L R; N as ARTICLE |
| `append` | stream, article, optional op id | Message-ID, position, group numbers, receipt | `operation-reused`, `operation-expired`, `addressees`, `duplicate`, `conflict` (with the evidence outcome as detail), `unaffordable`, `unknown-group`, `malformed-article` | after its transaction's record may exist | L R; N as POST |

**Consumers are the principal's namespace.** A registration is keyed by (principal, consumer id); another
principal's consumer is simply unknown, never a distinguishing refusal. The remote whitelist (CNS-011)
is therefore every verb, each over the login's own consumers and the streams its grant allows.
`bootstrap` (fn1 code 4) is answered by L as an accepted no-op once `init` and recovery have established
the store's identities (never for an uninitialized or unresolved store), in fn1's accepted reply shape.
The `bound-*` forms (codes 7, 8, 10) are L carrier forms (read, ack, wait as the bound account), refused
on R by the absence of a binding.

### 3.1 The cursor
`fncu` v1 (≤ 346 octets: `fncu`, version 1, five length-prefixed IDs history, incarnation, consumer,
principal, query; four u32 query version, view version, registration epoch, position). A cursor from
another store, incarnation, consumer, principal, query or epoch is refused `scope` before any mutation; a
stale view version answers `rebase-required` everywhere (read, wait, ack); an unknown version
`cursor-version`, never guessed. fn2's position is `(domain, sequence)`, domain 0 in 5.1.1. **v2:** while
every field fits, v1 cursors are issued; past any u32 field (position, epoch, query or view version) the
node issues `fncu` v2 with domain u32 and every counter u64 (≤ 366 octets), and a v1 cursor beyond the
bound is refused `cursor-version`, never truncated. The wire's counters are eight octets; a resident value
is at most 2^60 - 1 (B's value column), and a larger one is refused `:wide` by the codec. A v2 form of a
cursor that fits v1 is refused, so each cursor has one form. The `cursor` field is v2's width (366). Every ownership and retry key is the durable principal identity (account and its
incarnation), never a D7 scheduler slot.

### 3.2 The ack contract (fn1's, bound to the account)
An ack is the consumer's durable declaration that its own transaction finished through the proposal's
prefix. Forward only: a higher position is recorded (C's `:ack c e to`); an equal one is accepted with no
write and no durable reservation; a lower one is refused `behind` without rewind; past the committed
frontier `beyond-frontier`. Delivery is at-least-once until ack; exactly-once is the consumer's (§10.1).
A rebase is a new registration epoch: `:keep` keeps the recorded position and the starts of the streams
that stay, a new stream added from now (INBOX §4.3, so joining a room never rescans); `:now` moves to the
frontier; `:history` to 0. A recorded position is therefore monotone per (principal, consumer, epoch).
Uncertainty has two sources: the node's (a commit whose outcome recovery settles, ROUND2 §E.2) and the
client's (a lost reply). Either way the client's rule is fn1's: no further mutation of that consumer
until `position` settles it; the recorded position is the old or the proposed one, and a repeated ack is
accepted in both cases (K6).

### 3.3 Append, retry identity, and the same article for NNTP
An append is POST: D's upload and D5's transaction, the same path, the same refusal words, the same group
numbers. So an NNTP reader sees the appended article by GROUP and ARTICLE with the exact octets: no second
write path exists to diverge.
- **Operation identity.** With an op id the transaction records `(durable principal, op) → (digest,
  outcome)` in the same batch, the digest over the canonical request (stream, article octets, addressing,
  the op's own semantics) before any injection. A retry with the same op and digest answers the original
  outcome and writes nothing; another digest is refused `operation-reused`. Concurrent requests with one
  (principal, op) serialize on that key, not on the Message-ID (two contradictory requests can name
  different Message-IDs). The table keeps its meaning for a declared retry lifetime (C5's retention row);
  after it a retry answers `operation-expired` and is never executed anew. What is stored is the semantic
  result (Message-ID, position, numbers, receipt, the evidence outcome) or an immutable reference to it.
  An owner who has lost append authority cannot settle an existing operation by retrying it (the grant
  step refuses first); an `outcome(op)` lookup of the principal's own retry table is owed for that case.
- **Message-ID.** An article without one gets `<op-PRINCIPAL-OP@node>`, so a retry is the same article
  on every carrier; with neither, POST's injection rule applies and N's `:retry-by-message-id` is what the
  client has.
- **Conflict.** IDENTITY ruling 6: the article's refusal and the evidence commit are reported separately,
  `(:refused conflict EVIDENCE-OUTCOME)`.
- **Addressing.** `FN-To:` names principals by key identity, `@room` is a group-address flag (one entry
  with a reason, never one per member; INBOX §4.2); bounded by `max-addressees` (`addressees`), charged to
  the poster, written into `addr` in the same transaction, never parsed from bodies.

### 3.4 Large items and `fetch`
An item whose octets exceed the read's `max-remote-report-octets` is delivered as a **reference item**
(`FNRF` 0x01: Message-ID, the exact occurrence's position, octet count, typed content identity with its
subject) instead of fn1's `oversize` refusal. `fetch(reference)` answers the octets under the grant
current at the fetch, or `unavailable` (absent, unreadable or reclaimed answer alike) or `withdrawn`; it
never substitutes a later selection for the referenced occurrence. A failed fetch is never processed
content: Mini does not acknowledge past it, and a reclaimed item later arrives as a `gap` item, whose
acknowledgement is the explicit waiver. A client that has not negotiated references (v1 without FNRF)
gets fn1's `oversize` and no progress. On N, fetch is ARTICLE.

## 4. Pages and frames
### 4.1 A read's answer (INBOX §4.8)
Items in commit-position order, one per event: RECORD (exact octets and Message-ID, the node-supplied
current authorized group projection, never the author's statement), FNWD1 (an article withdrawn before
its delivery, at its own position), the withdrawal report at a cancel's position (CNS-008: delivered to
every reader the target was selected for, after an ack of the target too), FNRF1, and `gap` (an item the
retention policy reclaimed). Each with its position, the streams it was selected through and its reasons
(`room dm mention group-address backfill`; unknown codes ignorable). Several items travel in FNRB1. `more`
when a limit stopped the page; the next cursor proposal is the position through which the walk is
complete; the current query and view versions. Never on the wire: materialization, coverage, lag.

### 4.2 The local frames (`fn2/books/consumer-codec.lisp`)
FNCT: `FNCT`, version 1, kind, a four-octet big-endian payload length (10 octets), the payload, BLAKE3-256
over the protected prefix (32). The header is a layout; the trailer is computed and compared, never a
field. A frame is exactly its extent (no trailing octets); the payload ceiling is the code's.

Kind 4, one code octet and its fields. fn1's codes keep **fn1's payloads and refusal words** (the field
that failed: `consumer group secret timeout cursor`; `size`, `kind`, `bootstrap`), and the port's codes
carry the port's payloads:

| code | word | fields after the code | verb (L translation) |
|---|---|---|---|
| 0 | register | consumer, group | register, query (group), start `:history` |
| 1 | ack | the cursor's octets (v1 or v2) | ack |
| 2 | position | consumer | position |
| 3 | unregister | consumer | unregister of position's cursor |
| 4 | bootstrap | none | accepted no-op once init minted the identities |
| 5 | poll | consumer | read of position's cursor, fn1's one-article limits |
| 6 | status | consumer | status, fn1's kind 9 reply |
| 7, 8, 10 | bound-poll, bound-ack, bound-wait | as 5, 1, 9 with the account's secret (two-octet length, 1-496) | as the configured account; L only |
| 9 | wait | consumer, seconds (≤ 3600) | wait on position's cursor |
| 11 | append | stream, op (≤ 64, empty for none), article (four-octet length) | append |
| 12 | rebase | cursor, streams, start (`:keep :now :history`) | rebase |
| 13 | fetch | Message-ID, domain, position | fetch |
| 14 | register-query | consumer, streams, start (`:now :history`) | register |
| 15 | read | cursor, max items, max octets | read |
| 16 | wait-cursor | cursor, max items, max octets, seconds | wait |
| 17 | unregister-cursor | cursor | unregister |
| 18 | status-wide | consumer | status, eight-octet positions |

A cursor followed by other fields carries a two-octet length; streams are the canonical concatenation of
stream names. Both carriers bind each verb to its port code (register 14, rebase 12, unregister 17, read
15, wait 16, ack 1, position 2, status 18, fetch 13, append 11; ack and position keep fn1's codes
because their payloads already are the port's), and the codec asserts that the table, the port and both
carriers agree. R carries no legacy code; kind 22 (fn1's reasoned request) is the same payload.

Replies: fn1's kind 5 (status octet 0-3, the cursor when accepted), kind 6 (status, four-octet-prefixed
cursor and report) and kind 9 (status; accepted carries ack, frontier and their difference), unchanged;
kind 28 for the port's codes: the class, the reason word (≤ 64), and the verb's result (a cursor's own
octets; ack's `(domain, position)`; status's position, frontier and gap; append's Message-ID, position,
numbers, receipt and evidence outcome; fetch's article; a page's `more`, next cursor, count and items).
An item is its type (record, withdrawn, reference, gap), `(domain, position)`, the reasons bit set (room
1, dm 2, mention 4, group-address 8, backfill 16), the streams it was selected through, its Message-ID
and its body (a reference's body is its octet count and content identity). fn1's kind 18 (the reasoned
reply) and the FNWD and FNRB forms are owed with the served kind, where their first sender is.

## 5. The remote carrier: `XFNC` over the authenticated connection (the recommendation to main)
A maximal `fncu` v2 (366) inside an FNCT frame (+42) is 408 octets before the request's other fields; base64
and `XFNCT `+CRLF exceed 512. **(a), taken:** a short command and an explicitly framed body on the
connection that already has TLS, a login and an accounting principal.
```
C: XFNC 412<CRLF><412 octets: exactly one FNCT frame>
S: 290 455<CRLF><455 octets: one FNCT reply frame>   accepted
S: 490 37<CRLF><frame>                               refused (the frame carries the word)
S: 491 37<CRLF><frame>                               uncertain
```
- **Grammar.** `defgrammar`'s block declaration generalizes into opening mode, delimiter and refusal
  disposition: TAKETHIS stays immediate and dot-terminated; XFNC is immediate and count-delimited. The
  outer length is exactly one complete FNCT frame (its inner length and trailer included, no trailing
  octets). Nothing commits before the frame is validated whole.
- **Refusals and resync.** Before authentication (480) or before TLS under protected-only (483) the
  body cannot be skipped safely, so the reply is followed by close. Authenticated: a length that is not
  digits closes; a length over `max-consumer-request-octets` but within `max-consumer-discard-octets` is
  read and discarded (bounded in work and time), then 490 `frame`; over the discard bound closes; a frame
  invalid inside is 490 `frame` after exactly its outer extent; a short body times out and closes. A
  partially sent reply closes the connection; no status line is ever inserted into a reply's remaining
  bytes. The 512-octet line limit is never raised.
- **Outcomes.** Three line codes, one per class (`290 :accepted`, `490 :refused`, `491 :uncertain`, as
  grammar reply rows), and the client checks that the line's class agrees with the frame's status before
  treating 290 as acceptance. Pages are rendered into TX by handle.
- **Barriers.** STARTTLS and COMPRESS stay parser barriers: earlier replies finish before a hand-off and
  nothing beyond it is parsed under the old transport. Under COMPRESS the length counts application
  octets after decompression, and the decompression bounds apply.
- **Cancellation.** Pending application input (including an already buffered pipelined suffix) ends a
  parked wait exactly once with the read's answer at that moment, and every suffix octet is then framed as
  the next command, so coalesced and fragmented arrival behave alike; the next-command timer applies to a
  lone octet. A closed connection cancels the wait and releases its edges exactly once.
- **(a) over (b).** (b), raw FNCT on a second TLS port, could share authentication and accounting; its
  real value would be independent scheduling and no head-of-line blocking behind a parked wait on the
  same connection. Neither justifies a second listener for the first slice; a client wanting both waits
  and requests opens two connections.

## 6. The preconditions: Grant first, then Meter
WIDEST §2's order, generated by `NAME-admit` for every verb and emitted for the served kind as staged
machine steps (Astra: never a second executor): (1) **principal** (R: the connection's login; L: the
owner or the bound account; R before authentication: 480 and close); (2) **grant**, the verb's scope by
one predicate `(fn2-grant-allows principal scope view)`: refusal `access`; a stream the principal cannot
read answers as an absent one; in 5.1.1 the body is E2's access rules (read wildmats, post wildmats, a
consumer surface right), replaced by the Grant record kind when it lands without changing the port;
visibility is the pullback along the grant, checked per item against the article's own streams (an
`addr` entry never authorizes its originating room) at publication and again after a park; (3)
**meter**, the verb's declared dimensions reserved through D7's ledger: a request that cannot fit at all
(over its limit with nothing held, or a zero limit) is refused `meter`; one that could fit later parks on
the principal's FIFO (D7's request bundle), with its timeout still running; settled on completion from
actual counts, an unconsumed reservation rolled back; (4) **receipts** named by the verb (none for these
ten in 5.1.1); (5) the verb's **domain predicate**; (6) the work. Bounded parsing and the grant
evaluation itself are funded work charged before step 2. A parked wait holds its priced wait row and
edges, never a maximal report allocation; an append under shared exhaustion keeps a bounded input
continuation and rechecks authority when resumed; a disconnect before commit eligibility cancels, after
a possibly durable write cannot roll it back.

## 7. The inbox is a selection (INBOX-DELIVERY §4-5, ruled)
A registration is durable, keyed (principal, consumer, epoch), and names its edges, each `(stream,
start)`: a group, a DM lane (a two-member private group) or the principal's own `addr` stream; an edge
selects events after its start. Mentions-from-any-room is one edge on the seat's `addr`. The query is the
edge set, canonically encoded (sorted, no duplicates; `max-consumer-query-groups`). A read is INBOX
§4.4's bounded merge of the dirty edges with dedup and reasons; a wait parks on its edges with the final
frontier check, so a lost wake costs latency and never an event (scenario 7, K4). A cancel enters the
target's streams: the withdrawal report is a positioned entry in every stream the target was filed in
(without giving the cancel membership there) and raises their frontiers, so a reader that acknowledged
the target is woken and told. Every edge is `select` in 5.1.1; `edge-policy` and `inbox` exist in C's
format and the model's differential (C's K9). **Backfill is owed:** an edge added with history needs a
versioned proposal that carries its progress beside the main position and is acknowledged atomically;
until it exists `rebase :history` is the history path.

## 8. Limits as policy rows
`max-waiters` (fn1's fixed 12 becomes a setting priced by the profile's wait rows and edges; over it a
wait is refused `waiters`), `max-subscription-edges`, `max-consumer-query-groups`,
`max-remote-report-items`, `max-remote-report-octets`, `max-consumer-request-octets`,
`max-consumer-discard-octets`, `max-wait-seconds` (default 3600), `max-addressees`: each a `policy set` row
(E6). Lowering one never evicts what holds it: parked waits stay until they answer, and the new bound
applies to the next admission or page. Protocol widths (FNCT's u32 length, the cursor's fields) are not
policy; an object larger than a frame travels by bounded continuation into the same upload machine.
Counters per edge, stream, consumer and principal (INBOX §4.7) are `status` fields.

## 9. The reference model and the keystones (`consumer-model.lisp`, `owed-consumer.lisp`)
The model is a logic-only interpreter: the log, registrations with per-edge starts, acknowledged
positions, the retry table, grants with authority versions, the meter, parked waits, numbers,
reclamations and evidence; one function per verb returning `(mv outcome state)`; the world's steps
(grant, revoke, limit, withdraw, reclaim, timeout, crash). A crash drops parked waits and keeps the rest:
every accepted durable verb is atomic in the model, so node-side ambiguity is exercised as its two
branches (committed: a lost reply, c2 and c3; not committed: the request lost, c10). The CONSUMER
checker uses the model as its oracle; H's Python model is written from the spec and compared once.
FAULT is nil in every statement; each fault is a wrong node a tooth must catch.

| | statement (owed) | teeth | fault caught |
|---|---|---|---|
| K0 `fn2-cns-outcomes-declared` | every reply is an outcome the port declares for its verb | Mini, helm; two undeclared replies | — |
| K1 `fn2-cns-at-least-once` | at every reachable state, a chain of pages from the acknowledged position, at any page size, delivers exactly the selected events, in order | helm's pages of four | `:skip` |
| K2 `fn2-cns-ack-monotone` | no recorded position decreases, per (principal, consumer, epoch) | Mini c7 | `:rewind` |
| K3 `fn2-cns-append-retry` | a retried append answers its first outcome and adds nothing | Mini c2 | `:reappend` |
| K4 `fn2-cns-wait-is-read` | a woken wait answers the read at that moment, and no parked wait is ever left due | Mini c0, c6 | `:stale-wait`, `:lost-wake` |
| K5 `fn2-cns-nntp-parity` | an accepted append's article is NNTP's ARTICLE, exact octets, at its numbers, in the state it produced | Mini's R and Q | `:rerender` |
| K6 `fn2-cns-uncertain-settles` | after an accepted ack, committed or not, POSITION answers old or proposed and the repeat is accepted | Mini c3 | `:equal-behind` |
| K7 `fn2-cns-authority-current` | every delivered item is readable through its article's own streams under the grants current when answered | helm's denied mention, added r3, revoked r4 | `:pinned-grant` |
| K8 `fn2-cns-refusal-changes-nothing` | a refused verb changes nothing, the meter included, but ruling 6's evidence | helm's denied post | `:meter-first` |
| K9 (C's) `fn2-select-materialize-equivalent` | observations equal the select-only reference at equivalent cuts | C's teeth | — |
| K10 (owed, stated with D5 2/n) | the served carrier refines the model through crashes: every fully validated accepted reply is a recoverable committed effect, recovery never tears article, outcome, addressing and cursor apart, cancellation releases every edge and reservation exactly once and no stale wait writes a reused connection | "accepted before durable"; "article recovered without its retry outcome" | — |

## 10. The fixtures and their numbers (the acceptance)
### 10.1 Mini's processing transaction (`fn2/tests/consumer-mini.lisp`)
Mini is driven as a client: it registers on the report group (start `:history`), waits or reads, fetches
reference items, commits its own transaction (an operation index keyed by its operation, an outbox holding
Q), acknowledges, then posts Q from the outbox with op `m-OP`, re-posting on an uncertain reply. The report
R is a 191,283-octet source in a 198,919-octet article (CLIENTS §1.1), so under a 64 KiB report limit it
arrives as a reference and is fetched. **Twelve cuts:** c0 a parked wait woken by R; c1 death after
Mini's commit; c2 a lost Q reply; c3 a lost ack reply; c4 another source under the same operation; c5 R
cancelled before Mini reads it; c6 a node crash under a parked wait, and again after the ack; c7 a stale
duplicate ack; c8 R withdrawn after Mini acknowledged it; c9 death before Mini's commit; c10 the Q request
lost before the node; c11 R reclaimed between the page and the fetch. **Accepted, all twelve:** one Q
article per operation Mini processed (none for c5 and c11), its Message-ID `<op-mini-m-o1@node>` on every
retry, the outbox drained, R's octets at Mini equal to NNTP's ARTICLE, GROUP showing R and Q at numbers 1;
c4's conflict recorded in Mini with no second Q; c5 and c8 delivering the withdrawal; c11 delivering the
gap that Mini acknowledges past. K0-K8 hold on every cut's trace. This is the model of the exchange; that
Mini's E1 adapter (its 16-event and 17,408-byte bounds) runs it is shown only when it talks to the served
port.

### 10.2 helm's rooms (`fn2/tests/consumer-helm.lisp`)
helm's port maps one to one (CLIENTS §1.2): `append(row) → Evidence` is append with mentions and an op id
(accepted, refused, uncertain = OBSERVED, NOT_OBSERVED, UNKNOWN); `read(room, after)` a one-edge read;
`wait(seat, timeout)` the seat's wait; `ack(seat, row)` ack; helm's `row_id` maps to the cursor proposal
of the page that delivered it, never to a Message-ID alone. **Tiny profile** (the REPL scenario): three
seats, four rooms, two DM lanes, 60 rows, pages of four, waits re-parked after every answer; a mention in
a room the mentioned seat may not read; an `@room` row; a refused post into a room the seat may not post
to; a grant adding r3 (the parked wait answers `rebase-required`, the seat rebases `:keep`); a revocation
of r4 with later r4 rows; row 10 withdrawn after its readers acknowledged it; a crash under parked waits;
a seat that stops waiting and catches up page by page. **Accepted:** each seat's deliveries strictly
increase in position (no acknowledged row redelivered, the crash included); the `@room` row is one item
per reader with `:group-address`; the denied mention never reaches its seat; s1 gets no r3 row before its
rebase and every one after; rooms and lanes reach exactly their readers; s3's r4 rows stop at the
revocation; row 10's withdrawal reaches both its readers; row 1 wakes exactly s1 and s3, row 2 exactly s1
and s2 (several commits may coalesce into one answer; these rows are the first after a re-park). K0-K8
hold on the trace. **Concrete profile** (published beside the profile, never a gate): 30 seats (#19's
fleet), 427 rooms and 27 DM lanes (helm's store on 09-30, observed), a 7,000-row day at about 1 KB a row
with bursts (the upper end of the observed 3-7k a day, a scenario, not an fn2 measurement), about 10
edges a seat (a modelling assumption: about 300 edges against `Esub` = 4,096); reported: wake p50/p95
(akapug's falsifier: p95 over 2 s), resident bytes per waiter and per edge, heap at one day (falsifier:
over 2 GB), bytes per isolated ack (M5), and the waiter bound at 30. "An acked row is never redelivered
after a crash" is a correctness acceptance, gated in the tiny profile above.

## 11. Seams (exact forms, through main; owners' answers taken)
- **D, grammar.lisp (accepted, amended):** the block declaration `(:block (:mode :immediate|:after CODE)
  (:delimiter :dot|(:count ARG :max BOUND)) (:refusal :discard|:close))`, TAKETHIS unchanged; BOUND names a
  profile key or a constant (the framer's feed quantum needs a static bound): XFNC's is
  `(:profile :max-consumer-request-octets)`. The XFNC row (`:authenticated`, a `:digits` length,
  290/490/491, close after 480/483 through `after :closing`): E writes the rows, D owns the framer.
- **D8 (ruled):** the wait machine's edge rows are E's, in E's book, declared in the new machine form when
  its placement steps land; D reviews the diff.
- **D7 (accepted, amended):** every holding dimension is a D0 kind. `:waiter` is `:wait-row` (capacity
  `:w`, limit `max-waiters`); `:subscription-edges` is `:subscription-edge` (capacity `:esub`, a profile
  key with ROUND2's 4096 as default; limit `max-subscription-edges`); `:durable-octets` is a new kind ranked
  after `:principal-reservation`, unit 4096-octet blocks, bound and capacity `:dstore`, reserve `:system`.
- **C (accepted, amended):** `fn2-outcome` (id 9) keyed `((principal (:id principal)) (operation (:octets
  64)))`, value `((request :digest) (outcome :u16) (result (:id object)) (evidence (:enum (:none :committed
  :uncertain :refused))) (event (:id event)))`, `:unique`, written in the append's batch, the result an
  immutable reference. The key is the local principal id on the condition that a principal id is never
  reused within a store; a retry across peers, if §13 admits one, makes it ruling 2's origin digest.
  `operation-expired` is a pure comparison (the row's event plus the retry lifetime at or below the
  published frontier); C5 reclaims only rows that already read expired. Per-edge starts in C4b. The
  withdrawal is a stream schema `fn2-withdrawals` (id 15) keyed `((stream (:id stream)) (position (:id
  position)))`, value `((article (:id article)) (number (:id group-number)))`, one row per stream of the
  cancelled article in the cancel's transaction; no overview tombstone. Equal acks never reach the fold.
- **B (accepted):** register, rebase, ack and unregister are commit-stream record kinds whose envelope (the
  record header) carries revision, occurrence, lineage, domain, incarnation, author key, payer and grant;
  each kind lands with its producer, E, with the served machine.
- **The form seat:** `port.lisp` read as a declaration kind in the registry, one notion with the others.
- **E2 (mine):** `fn2-grant-allows` over the access rules; the principal binding at authentication.

## 12. Dispositions of fn1's consumer rows (RELEASE-PLAN §1 rows 63-70)
| fn1 row | disposition |
|---|---|
| `fncu` v1, nine fields, foreign cursor refused before mutation | carried; v2 past any u32 field (§3.1) |
| k4 codes 0-10 and k22 | carried with fn1's payloads, translated by L (§4.2); bootstrap a no-op; `bound-*` L only; the port's codes 11-18 added |
| k5, k6 (FNWD1, FNRB1), k9, k18, k23 | carried; FNRF1, gap items and reasons added for new codes |
| one group, 16 events, one article per poll | replaced by the selection (§7) with policy limits |
| 12 waiters, every commit wakes every waiter (CNS-007) | replaced by `max-waiters` and per-edge wake; CNS-007's meaning kept as K4 |
| `oversize` (PKT-466) | replaced by reference items and `fetch` for a client that negotiates them; kept for v1 |
| a changed register refuses `rebase-required` | carried |
| the remote consumer (CNS-011, PKT-673), never served | carried as specified here |
| the consumer's exactly-once contract | carried as the client's (§10.1); the clients ship (E6) |

## 13. Peering and BP *(statement, revised after Astra's read `lanes/e-quests/astra-2.md`)*
Brief items 4 and 5 over the same engine. Sources: IDENTITY rulings 2-14 and Astra's ten witnesses
(IDENTITY-ASTRA, "What E4 must prove"); fn1's `specs/peering.md` and `specs/bp-*.md` (the meaning kept);
D's peer rows (§11 `peering`, `peer_catchup`; the reply-word table; D5 3/n owed); C's §4a identity records
and the `obligations` schema. The one idea: **a peer is a principal, an outbound feed is consumer
machinery, and a bundle is a carrier**. No second store and no second decision path, but every
responsibility fn1's separate journals carried (FNFD, FNBS) is kept, as typed records in the common store.

### 13.1 A peer is a principal with a peer grant
- **Identity.** A peer authenticates as a principal (TLS, then AUTHINFO; or a BP neighbor admitted in
  fn1's order: observed channel, configured peer, allowed EID, admitted principal, which is a conditional
  authority resting on the boundary assumption, never cryptographic origin). fn1's source-address peer
  (A-PEER) is retired: it made every loopback client the peer. The role is fixed at authentication by the
  grant, never by `MODE`; STARTTLS resets it.
- **Current authority at every decision.** The role stays fixed for the connection; the grant and the peer
  policy are rechecked at each offer and each transfer (an offer can check only what it carries; groups,
  Distribution, Path and evidence wait for the body; a `238` never exempts a transfer). Revocation stops
  later offers and transfers and never rewrites an earlier admission or confiscates an obligation. This
  replaces D's "pinned until reauthentication" for peer operations (seam to D).
- **The peer row is policy over the principal:** accept-groups, feed-groups, `max-inflight`, streaming,
  carried count and octets, distributions, path identity, transport, the reply profile (§13.2).
- **Charges.** A peer's offers are charged to the peer principal (transfer octets, evidence admission,
  durable octets). Per-principal limits compose with the aggregate capacity and the reserved settlement
  capacity, so many funded peers still cannot exhaust what settling existing work needs.

### 13.2 Inbound transit is the shared acceptance transaction
Transit runs D5's transaction after **carrier-specific preparation**: POST injects; transit keeps the
authored fields byte-exact and updates Path once at acceptance (fn1 §2.3) and Xref; the loop check reads
the received Path and the provenance. BP ingress reaches the same transaction (fn1's K6, built from the
start). Decisions and words:
| point | decision | IHAVE / CHECK / TAKETHIS |
|---|---|---|
| offer, **local acceptance history** for the name (accepted, withdrawn or reclaimed) or a local not-wanted decision | `:have` | 435 / 438 / — |
| offer, evidence-only knowledge, a foreign receipt, a pending authority dependency | not suppressing: `:want` (subject to the rest) | 335 / 238 / — |
| offer, staged, or the window full | `:defer` | 436 / 431 / — |
| transfer, identical subject | `:duplicate`; new evidence still admitted, funded, no article, membership or retention promise | 437 / — / 439 |
| transfer, a different authored subject under a name with local acceptance | ruling 6: evidence commits separately, the article is refused | 437 / — / 439 `conflict` |
| transfer, contention (`:contended`) or account exhaustion (`:exhausted`) | retryable | 436 / — / default 400 and close; profile `fn-compat`: 436 |
| transfer, structurally impossible for this profile (`:incompatible`) | permanent | 437 / — / 439 |
| transfer, uncertain commit | fence | 436 then close / — / 400 and close |
| transfer, accepted | 2xx only after `:durable` | 235 / — / 239 |
TAKETHIS's default follows RFC 4644 (400 and close on a temporary failure); fn1's `436 <id>` (chosen after
INN's retry behavior) is the named `fn-compat` profile; uncertainty closes in both. **Declared losses
(ruling 11):** CHECK and IHAVE suppress by Message-ID before the body, so neither a conflicting body nor new
evidence beside identical bytes is learned that way; the legacy codes cannot report the article result and
the evidence result separately, so settlement of the evidence is through the evidence stream (§13.4).
`239`/`235` are transmission receipts, never retention receipts.
**The window.** `max-inflight` CHECK credits per streaming connection (IHAVE is never pipelined), a D0
holding kind `:peer-credit` charged to the peer; a CHECK credit becomes the transfer's holding by transfer,
not a second charge; unsolicited TAKETHIS, abandoned credits, duplicate offers, timeouts and policy
lowering each have a stated disposition; replies leave in request order (D5 3/n's queue), and a reply
settles only its own (phase, Message-ID).

### 13.3 An outbound feed: a node-owned consumer installing delivery work
- **Discovery** is a consumer owned by the node (a service consumer), accounted to the peer, whose query is
  the peer's feed selection: an article matches by its Newsgroups, and a control article also by its
  target's groups (fn1 NNT-033: a peer subscribed to the room receives its cancel without subscribing to
  `control.cancel`), minus loops (the peer's identity in Path, or the peer as provenance). The peer cannot
  rebase, unregister or acknowledge it: managed consumers are outside the remote whitelist.
- **Its processing transaction installs delivery work and acknowledges** (Astra's position, taken): for
  each selected occurrence a `feed-work` row keyed by the stable **delivery identity** (feed epoch,
  occurrence), with the destination, the immutable object reference and the query version; then the
  cursor's ack, in one batch. A changed feed query is a rebase, a new epoch; the work already installed
  keeps its epoch's responsibility; a removed peer's work drains or is explicitly dropped (fn1's
  busy-feed drain). Selection is a pure function of the occurrence and the epoch's query, so the target set
  is fixed as fn1's acceptance-time intents fixed it, without a feed write in every POST transaction.
- **Delivery** is a scheduled fold over feed-work rows, fair across them: a deferred head never blocks
  ready later work. A row carries its phase (offered by CHECK/IHAVE, sent), attempt identity (connection
  incarnation, request), deferral count, loss count, backoff deadline (restart-safe), and terminal
  disposition: `accepted` (235 239), `not-wanted` (435 438), `rejected` (437 439), `dropped` with its
  reason when losses reach the bound (only losses with an attempt in flight count; 431/436 never do), or
  `withdrawn` (the target was withdrawn before delivery: never offered after). Offer backoff and link-redial
  backoff stay distinct. An operator waiver ends permanently deferred work explicitly.
- **Restart** retires every unresolved attempt and re-offers by CHECK/IHAVE, sending only after a new
  affirmative answer, never a blind TAKETHIS; a terminal disposition is durable before anything depends on
  it (fn1's honest exactly-once, P:1290).

### 13.4 fn2 peers exchange evidence, not only articles
XFNCATCHUP is carried for fn1 peers with its declared loss (skips across a view reshape undetected) and is
not extended (ruling 11). An fn2 peer reads, over R, an **evidence page**: a result type distinct from the
consumer page (§4.1's "no coverage on the wire" is the consumer page's rule), read through C's
position-ordered admission index (never the per-name key cursor; a commit's several facts are paged with
an ordinal or kept whole). The page carries:
- **history identity:** origin domain, incarnation or lineage relation, revision, an advertised cut (a
  commitment identifies the history; it never proves honest disclosure);
- **scope:** namespace, streams, fact interpretation version, disclosure scope, authority and view version;
- **traversal:** start, next, advertised end, and why it stopped (limit, unavailable history, completion);
- **exceptions:** source coverage gaps, withheld or unavailable dependencies;
- **completion, two claims kept apart:** examined through this cut, and durably incorporated every eligible
  fact and required dependency through this cut. `more = false` is never evidence completeness.
Each item is portable evidence (namespace, name, typed content identity, evidence identity, issuer,
dependencies); its identity survives import, so re-export never mints a new observation and evidence does
not amplify around a cycle. The receiver admits through C's `:admit` and `:receipt-import` (which never
selects); a refused or unfunded admission is a durable local gap (C's funded or coarse gap mechanism);
persisting a gap may advance the **scan** cursor, never the **incorporation** claim, and a repair pass
revisits gaps when funding or dependencies arrive. Dependency and proof references are fetched by an
authorized evidence fetch, not the article `fetch`. The first evidence protocol is scoped to connected
peers over R; evidence over BP is a third ADU kind, owed. Catch-up for an fn2 peer is `register :history`
and pages: the same port.
**The peer claim** (K-P1): within a named namespace and fact interpretation, replicas that durably
incorporated the same eligible evidence and dependencies have equal evidence Bindings and equal conflict
predicates; local acceptance receipts stay attributed; served choices agree only when policy and decision
inputs agree; eventual incorporation is a separate claim under its connectivity, availability,
authorization and resource assumptions.

### 13.5 Control across peers
Control articles relay as articles; every receiver decides again under its own authority (ruling 10). A
cancel's decision is a **durable cancel intent** independent of the target: target namespace and name,
cause, issuer, authority basis and the decision-time grant context (seam to C: a record beside
`fn2-withdrawals`, whose rows need the target and are materialized when the target is known). That retained
decision is what makes cancel-before-target, across a crash, order-independent (fn1 P:1948).

### 13.6 BP: one store, carrier lifecycle distinct from custody
- **Ingress** decodes fn1's ADU (request and receipt kinds; the ADU bound is the profile's, with codec width,
  admission profile and bounded continuation stated separately, not a fixed 32,768) and reaches §13.2's
  transaction. Custody is taken only over an admitted channel.
- **One store, typed records.** fn1's FNBS journal is replaced by records in the common store: **bundle**
  (bundle identity), **submission**, **attempt**, **outcome**, **handoff** and **obligation**, the four
  identities never substituted. A held bundle may be a fragment, a transit object, an application receipt or
  an administrative report, with no accepted article at all. Carried over from FNBS as obligations of the
  engine: the five budgets (live objects and octets, staged family reservations, authoritative history,
  publication capacity) separately accounted; the **cleanup debt** (admission reserves the future writes
  that settle attempts, publish receipts, end families and reclaim; exhausted admission credit never blocks
  paying existing debt); recovery and compaction preserving held objects, outcomes, handoffs, family
  reservations, age evidence and non-reused frontiers; fragment families with outcomes for every child;
  the expire, dispatch, deliver and discard classes independently eligible.
- **Custody is an obligation**, distinct from the carrier: carrier expiry or deletion leaves the
  application obligation outstanding and a new carrier may retry it. C's `obligations` needs a typed
  contract (seam to C): stable identity and kind; the exact subject reference; obligor, beneficiary, payer
  and authorization provenance; immutable terms (promised action, receipt authority, release predicate,
  retry, expiry and waiver); state with discharge evidence scoped to that obligation; reserved resources and
  remaining cleanup liability. An imported foreign obligation is evidence, never adoption.
- **Receipts** have an outbox: `(receipt fact, triggering carrier) → owed | handed-off`; losing a receipt's
  carrier does not erase the fact; a status report is never evidence and never stops the requester's
  receipt timer; the final TCPCL ACK follows durable reception (or an exact durable duplicate), and a
  refusal or uncertainty never sends a successful final ACK.
- **Egress** is a feed (§13.3) whose transport is a convergence layer and whose destination is chosen by the
  operator's route table; no route keeps the work held and reported. A contact is a wake source for the
  fair selector, never a scheduler of its own.
- **The bundle machine** is declared in the machine form with fn1's events and effects as vocabulary, after
  the served consumer kind.

### 13.7 Keystones (statement first, owed with teeth)
| id | statement |
|---|---|
| K-P1 | the peer claim (§13.4), checked against an independent fold of the retained evidence and conflict observations; conditional equality separate from eventual exchange |
| K-P2 | transit refines the shared acceptance transaction after carrier-specific preparation: identity, admission, membership, charges and durability effects agree (not stored-byte equality) |
| K-P3a (safety) | every installed delivery responsibility is pending or has exactly one terminal disposition; no cursor advance loses one |
| K-P3b (progress) | settlement only under stated scheduling, availability, resource and peer-response assumptions (an infinite `431` refutes the unconditional claim) |
| K-P4 | at most one durable terminal disposition per delivery identity across restarts, duplicate replies, stale sessions and compaction; a re-feed is a new identity linked to the old outcome |
| K-P5 | a local custody obligation is discharged only by its authorized, exactly bound receipt or an authorized durable waiver; transport ACKs, reports, carrier expiry, cancellation and another obligation's receipt cannot |
| K-P6 | a reoffer matching a local acceptance whose body was reclaimed is `:duplicate`, allocates no publication, discharges no unrelated obligation; evidence-only or foreign-receipt knowledge is not this case |
Each keystone's positive fixture asserts its full antecedent (K-P2 accepts something; K-P5 releases
something) and a fault per keystone is caught.

### 13.8 The witnesses as fixtures, and what they establish
A **witness-to-property matrix** names, per fixture, which keystones it exercises non-vacuously. The
reference model is extended to several nodes with evidence, obligations, feed work and gaps; its fixtures
are executable obligations and checker oracles, **not served acceptance evidence**.
| fixture | exercises |
|---|---|
| W1 opposite first arrivals | K-P1 |
| W2 two candidate sets meet with funded capacity exhausted: partial import, gap, restart, later funding, completion after repair | K-P1 (incorporation vs scan) |
| W3 identical content with new evidence | K-P2, K-P6 |
| W4 a forged arbitrary-key signature (authority logic, not signature security) | K-P1 |
| W5 an object before its authority dependencies | K-P1 |
| W6 cancel before target with a crash between | §13.5 |
| W7 reclamation with identity and evidence surviving; a reoffer | K-P6, K-P5 |
| W8 the evidence commit before persistence, after it, before the reply (semantics only; physical cuts need the served machine) | K-P2 |
| W9 one article through two routing projections, through the real subject extraction and relay transforms | K-P2 |
| W10 a transported domain against old-incarnation decisions (a specified model, not transport implemented) | ruling 12 |
| F1 A→B→C→A propagation, evidence circulating with its identity | K-P1, loops |
| F2 a deferred head, later successes, mixed CHECK/TAKETHIS phases, stale replies, restart with attempts unresolved | K-P3a, K-P4 |
| F3 conflict visibility at an authorized typed read under incomplete coverage and disclosure limits | K-P1 |
| F4 carried count and carried octets exhausted independently; lower, refuse, raise, restart with usage kept | charges |
| F5 cleanup credit exhausted for admissions while existing attempts, handoffs and reclamation settle | BP debt |
| F6 fragment replacement at full capacity, a family across a crash, a receipt lost after a delivery report | K-P5 |
| F7 grant or query changes while an offer, an evidence page or feed work is pending | §13.1 |

### 13.9 Seams this needs
- **D:** the `:peer-credit` holding kind; D5 3/n answering §13.2's table (the exhaustion reasons split
  into `:contended`, `:exhausted`, `:incompatible`; `:unaffordable` today names the last); current
  authority per peer decision; the reply profile row; D's identity text reconciled with rulings 6-7 before
  its peer path is coded (the fifth-content bound, POST conflicts writing nothing, transit deciding by
  Message-ID after receipt, d-machines-nntp.md around line 1414); A's outbound `Connect`.
- **C:** the typed obligations contract (§13.6); the cancel intent record (§13.5); the position-ordered
  admission index with an intra-commit ordinal; the `feed-work` schema keyed by delivery identity; the
  bundle, submission, attempt, outcome and handoff schemas.
- **B:** the ADU as a record subject; evidence identity preserved across import.

## 14. Order of the build
1. Done: the port form, the consumer port and carriers, the model, the keystones, the two fixtures.
2. Done: the big-endian layout kinds; the FNCT and `fncu` codecs (v1 and v2, codes 0-18, replies 5, 6,
   9 and 28) with fn1's bytes as fixtures; the legacy translation as data.
3. Peering and BP: §13 stated and revised after Astra's read; seams to main; then the multi-node model
   with the witness matrix and K-P1..K-P6 owed with teeth.
4. When D5 2/n and D6 land: `fn2-cns` in the new form over C's reads and folds, the XFNC block, the local
   socket, the CONSUMER checker over the model, scenarios 7, 8, 9, K10 stated.

## 15. Astra's read (`lanes/e-quests/astra-1.md`): what it changed
Taken: losses as a product, not a chain (§2.3); grammar bindings name terminal replies (§2.2); fn1's
codes keep fn1's payloads and L translates (§4.2); a changed register answers `rebase-required` and a
stale view answers `rebase-required` everywhere (§3, §3.1); every verb answers `access` and `meter`;
`fetch` as a verb with named failures, and a failed fetch never processed (§3.4); the S-OUTCOME seam
widened, keys on the durable principal, `operation-expired`, the conflict's two outcomes, serialization
by (principal, op) (§3.3, §11); withdrawal entries in the target's streams (§7); backfill owed with a
versioned proposal (§7); XFNC's 480/483 close, the generalized block, exact-frame length, partial-reply
close, COMPRESS counting, cancellation by pending input stated without claiming IDLE (§5); the receipts
step, funded parsing, limit-versus-shared as fit-at-all, the parked wait's holdings (§6); the D7
dimensions seam (§11); K4b no lost wake, K1 at every state, K10 named (§9); Mini's cuts c8-c11 and the
acceptance worded "per processed operation"; helm's denied mention, revocation, withdrawal after ack,
pagination and coalesced wake; the numbers' provenance stated (§10); v2 widths (§3.1); policy lowering
(§8). Two positions recorded: on (b), Astra holds it need not duplicate authentication and would value
independent scheduling; E keeps (a) for the first slice (§5). On K4, Astra notes a waiter polling only at
its timeout satisfies "wait is read"; E answers with K4b rather than weakening K4.

## 16. Astra's second read (`lanes/e-quests/astra-2.md`, §13): what it changed
Taken: the feed acknowledges once its processing transaction installs delivery work, scheduled by a fair
fold (no head-of-line hole), with a stable delivery identity, attempt phases, separate deferral and loss
counts, explicit drops and an operator waiver; the feed consumer is node-owned and outside the remote
whitelist; control matched by its target's groups; CHECK/IHAVE suppress only on local acceptance history or
a local not-wanted decision, never on evidence alone; the exhaustion reasons split three ways; TAKETHIS's
default follows RFC 4644 with fn1's 436 as a named profile; phase-aware reply matching; the evidence page
as its own result with history identity, scope, traversal, exceptions and two completion claims, scan
cursor apart from incorporation, repair of gaps, evidence identity preserved across import; BP as typed
bundle, submission, attempt, outcome, handoff and obligation records carrying FNBS's budgets, cleanup debt,
recovery, fragments and progress classes; custody distinct from the carrier; the typed obligations
contract; the receipt outbox and the final-ACK boundary; the profile's ADU bound; current authority at
every peer decision; aggregate capacity beside per-peer charges; the sharpened K-P1..K-P6 with full
antecedents; the witness-to-property matrix and fixtures F1-F7; model fixtures labeled oracles, not
served evidence; the durable cancel intent; withdrawn feed work as a terminal disposition.
One position recorded: Astra notes acceptance-time installation (feed work in the POST batch) would fix the
target set at acceptance; E installs at the feed consumer's processing transaction instead, because the
epoch's query makes selection a pure function of the occurrence (the same target set) and keeps a feed
write out of every POST transaction as peers multiply.
