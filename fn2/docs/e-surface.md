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
| the port as a declaration: `(:port P)` on the shared registry (`declare.lisp`'s `fn2-ports`), its generated readers as its manifest, beside its verbs' `(:command ...)` rows (the form seat's read) | `fn2/books/port.lisp` | certifies; the consumer books and fixtures recertified over it |
| the peer reference model: each node's history (its entries with their origin), identity evidence by identity, peers' history entries from catch-up, coverage gaps and funding, forward pins, the feed queue with phases, deferrals, losses and dispositions; eight faults | `fn2/books/peer-model.lisp` | the meaning §13 states; an oracle, not served evidence |
| K-P1, K-P3a, K-P4, K-P5, K-P6 owed with teeth (K-P2 and K-P3b are stated over D5 3/n's served path) | `fn2/books/owed-peer.lisp` | 0 proved; every tooth evaluates |
| witnesses W1, W2, W3, W7, the offer rule, F1, F2, each asserting its antecedent; each fault caught | `fn2/tests/peer-witnesses.lisp` | all hold; eight faults caught |
| CONSUMER: a refinement checker over the L carrier's FNCT frames, the world steps, the published frontier and the ledger's rows (the consumer-cursor fold, the `:wait-row` holdings); every model state the observations allow, mutations linearized at any boundary before their reply (orphans after a lost reply or a crash, until the next settle), a wait answering the read at a moment while pending (K4), a due parked wait at a settle failing `:lost-wake` (K4b) | `fn2/sim/check-consumer.lisp` | certifies; the model's items carry the streams they are selected through, and its log is padded with commits nothing selects, so its positions are commit positions |
| scenarios 7, 8, 9, the lost ack and paging, as FNCT clients against the oracle node; five wrong nodes caught | `fn2/tests/sim-layer-e.lisp` | all pass, each shown to exercise its path |
| K10 stated over CONSUMER and the served producer (constrained until the simulator's adapter lands with the kinds) | `fn2/books/owed-consumer.lisp` | owed; the oracle and the controls as teeth |
Owed, in order: the rest of §13.8's matrix as the records they need land (W4, W5, W6, W8-W10, F3-F7);
then, when D5 2/n serves a durable POST and D6 an article, the served kind `fn2-cns` and the XFNC block (§14).

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
  immutable reference. The key is the local principal id on the premise (D7's allocator guarantees it; C states it in the outcome keystone) that a principal id is never
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

## 13. Peering and BP *(statement; each record kind lands with the verb that writes it, D46)*
Brief items 4 and 5 over the one engine. The protocols served: NNTP transit (IHAVE, RFC 3977 §6.3.2;
streaming CHECK and TAKETHIS, RFC 4644; Path, history and control, RFC 5537 §3.3, §3.5, §5); catch-up
between fn2 nodes, the successor of fn1's XFNCATCHUP (`specs/peering.md` NNT-053), carried in XFNC (§5);
and BPv7 (RFC 9171) over TCPCLv4 (RFC 9174) with fn1's ADU (`specs/bp-adu.md`) and its application receipt
(`specs/bp-receipt.md`). Sources: IDENTITY rulings 2-14 and Astra's witnesses (IDENTITY-ASTRA); fn1's
`specs/peering.md` and `specs/bp-*.md`; D's peer rows (§11) and D5 3/n; C's §4a identity records. Astra's
read is `lanes/e-quests/astra-2.md` (§16).

Every record kind below carries one line: **written by** VERB on PROTOCOL, **read by** VERB on PROTOCOL.
A kind without such a line is not in the design. A kind that no served verb writes yet stays here as
design; C lands it with the verb that writes it (main's ruling 2026-10-31, D46).

### 13.1 A peer is a principal with a peer grant
- A peer authenticates as a principal: AUTHINFO (RFC 4643) over TLS (RFC 8143) for NNTP; a BP neighbor in
  fn1's order (observed TCPCL channel, configured peer, allowed EID, admitted principal: an authority resting
  on the boundary assumption, never cryptographic origin). fn1's source-address peer (A-PEER) is retired. The
  role is fixed at authentication by the grant, never by `MODE STREAM`; STARTTLS resets it.
- The grant and the peer policy are rechecked at each offer (IHAVE, CHECK) and each transfer (the IHAVE
  body, TAKETHIS) (D: yes). An offer checks what it carries; groups, Distribution and Path wait for the
  body; a `238` never exempts a transfer. Revocation stops later offers and transfers and never rewrites an
  earlier acceptance or a held pin.
- The peer row is policy over the principal (fn1's `fn peer add`, peering.md §1.1): accept-groups,
  feed-groups, `max-inflight`, streaming, carried count and octets, Path identity, transport, the reply
  profile (§13.2). A peer's offers are charged to the peer principal; per-principal limits compose with the
  aggregate capacity and the system reserve.
- **The window.** `max-inflight` CHECK credits per streaming connection (IHAVE is never pipelined), the D0
  holding `:peer-credit` on the peer principal. A `238` turns a credit into the transfer's holding by one
  ledger net change on `fn2-account-attribute`'s pattern (release the credit, acquire the transfer's holding
  on the same principal, re-acquire the credit if the acquire is refused), so nothing is charged twice (D's
  amendment). Replies leave in request order; a reply settles only its own (phase, Message-ID).

### 13.2 Inbound transit is the acceptance transaction POST uses
IHAVE and TAKETHIS run D5's transaction after carrier preparation: POST injects; transit keeps the authored
fields byte-exact and prepends the node to Path once at acceptance (fn1 §2.3) and writes Xref. BP ingress
reaches the same transaction (fn1's K6). D5 3/n takes this table whole (D: yes):
| point | decision | IHAVE / CHECK / TAKETHIS |
|---|---|---|
| offer; the Message-ID is in this node's **history** (accepted, withdrawn or reclaimed) or locally not wanted | `:have` | 435 / 438 / — |
| offer; only identity evidence or a peer's history entry knows the name, or an authority dependency is pending | `:want` | 335 / 238 / — |
| offer; the name is staged, or the window is full | `:defer` | 436 / 431 / — |
| transfer; the same authored subject | `:duplicate`: new evidence still admitted and funded; no article, number or retention | 437 / — / 439 |
| transfer; a different authored subject under a name in the history | ruling 6: the evidence commits, the article is refused | 437 / — / 439 |
| transfer; `:contended` or `:exhausted` | retryable | 436 / — / 400 and close (RFC 4644); profile `fn-compat`: `436 <id>` |
| transfer; `:incompatible` with this profile | permanent | 437 / — / 439 |
| transfer; the commit's outcome uncertain | fence | 436 then close / — / 400 and close |
| transfer; accepted | 2xx only after the commit is durable | 235 / — / 239 |
Declared losses (ruling 11): CHECK and IHAVE decide by Message-ID before the body, so a conflicting body or
new evidence beside identical bytes is not learned that way; the legacy codes cannot report the article and
the evidence separately, so evidence settles through catch-up (§13.4). `235` and `239` are transmission
receipts, never retention (fn1 RET-003).

**The history entry** (fn1 peering.md §2.5, RFC 5537 §3.3, with its origin). C's `fn2-identity-evidence`
and `fn2-identity-receipts` (id 1, 11; on dev), the identity summary their fold.
- written by POST, IHAVE and TAKETHIS on NNTP and by BP ingress on TCPCL (D5's acceptance transaction);
  for a peer's entries, by the catch-up import on XFNC (§13.4).
- read by the offer decision of IHAVE and CHECK (the `:have` row), by ARTICLE/HEAD/STAT by Message-ID
  (the selected subject), and by the catch-up batch on XFNC.

### 13.3 The outbound feed (fn1's FNFD, peering.md §4)
- **Selection** is a consumer the node owns for the peer (the port's `register`, §3, node-authored),
  whose query is the peer's feed-groups: an article matches by Newsgroups, a control article also by its
  target's groups (fn1 NNT-033), minus loops (the peer's name in Path, or the peer as the arriving
  connection). The peer cannot rebase, unregister or ack it: it is outside the remote whitelist (§5).
- **The feed entry**, keyed by the delivery identity (feed epoch, occurrence): destination, the article's
  position, the query version, the phase (offered by CHECK or IHAVE, then sent by TAKETHIS or the IHAVE
  body), the attempt (connection incarnation, request), deferral and loss counts, the backoff deadline, and
  one terminal disposition: `accepted` (235, 239), `not-wanted` (435, 438), `rejected` (437, 439),
  `dropped` (losses with an attempt in flight reached the bound; 431 and 436 never count; or the peer's
  grant no longer covers it), `withdrawn` (the target was cancelled before delivery).
  - written by the feed consumer's processing transaction (the port's `read` then `ack`, one batch: install
    the entries, then advance the cursor) and by each IHAVE, CHECK and TAKETHIS reply on NNTP (phase,
    counts, disposition); by the operator's drop (`fn peer drop`, fn1's busy-feed drain).
  - read by the feeder's fair selection (fewest deferrals first, oldest among equals: a deferred head
    neither blocks later entries nor starves) that sends CHECK/TAKETHIS (RFC 4644) or IHAVE (RFC 3977) to
    the peer; at restart, every unresolved attempt is retired and re-offered by CHECK or IHAVE, never a
    blind TAKETHIS (fn1 P:1290).
  - design until the feeder serves (D5 3/n's peer path with E's served consumer).
- A changed feed-groups is a rebase: a new epoch; the entries installed keep their epoch. Selection is a
  pure function of the occurrence and the epoch's query, so the target set is the one fn1's acceptance-time
  intents fixed, without a feed write in every POST transaction.

### 13.4 Catch-up between fn2 nodes (the successor of XFNCATCHUP)
fn1 peers keep XFNCATCHUP with its declared loss (a view reshape skips undetected; ruling 11), unextended.
An fn2 peer catches up over XFNC with the port: `register :history` on the peer grant's view, then `read`.
A **catch-up batch** is a read page whose items are the view's entries in commit order, each with its
history entry and its identity evidence (namespace, Message-ID, subject identity, evidence identity, issuer,
dependencies), and whose header carries what XFNCATCHUP's `291` line carried and more: the sender's
history identity (domain, incarnation, revision) and its chain at the batch's end, the scope (view and its
version, the evidence interpretation version), NEXT and END, and why it stopped. `more = false` claims
nothing about completeness. Evidence keeps its identity across import, so a re-export never mints a new
observation and evidence does not circulate as new around a ring (B: yes).
- The receiver admits each item through C's `:admit` (evidence) and `:receipt-import` (a peer's history
  entry, which never selects). An item it cannot fund or whose dependency is absent is a coverage gap in the
  identity summary (C's `coverage` field); the batch cursor may pass a gap, the receiver's coverage claim
  may not, and a later batch or funding repairs it.
- **No new record kind**: the batch is a read result; what it writes are the history entries and evidence
  of §13.2, written by the catch-up import on XFNC, read as there.
- **The peer claim** (K-P1): within one namespace and evidence interpretation, nodes whose coverage includes
  the same evidence have equal Message-ID bindings and equal conflict predicates, whatever their own history
  entries say; served choices agree when policy agrees; eventual coverage is a separate claim under
  connectivity, authority and funding.

### 13.5 Control across peers (RFC 5537 §5)
Control articles relay as articles; every receiver decides again under its own authority (ruling 10).
- **The withdrawal** (C's `fn2-withdrawals`, id 15, answered): written by the cancel's acceptance on NNTP
  (D5's control path, one row per stream of the target, positioned by the event); read by ARTICLE, OVER and
  the consumer `read` (an absent article; a positioned withdrawal entry in each stream).
- **The cancel intent** (target namespace and Message-ID, cause, issuer, authority basis, the grant in force
  at decision): written by a cancel accepted by POST, IHAVE or TAKETHIS whose target is not here; read by
  the target's acceptance on POST, IHAVE or TAKETHIS, which writes its withdrawal rows in the same
  transaction. It makes cancel-before-target order-independent across a crash (fn1 P:1948). Design until
  D5's control path serves.

### 13.6 BP (RFC 9171 over TCPCLv4, RFC 9174)
The bundle is the carrier; the article is the subject (fn1 bp-design.md §1.1). RFC 9171 has no custody
(Appendix A removes RFC 5050's) and fn2 imports none. What fn1 calls custody is the **forward pin**.
- **The bundle** (RFC 9171 §3.1's bundle store; fn1's FNBS journal; a fragment is a bundle with its
  offset, RFC 9171 §5.8):
  - written by TCPCL reception (XFER_SEGMENT to the final XFER_ACK, RFC 9174 §5.2) at BP ingress, and by
    the BP feeder's encoding of a feed entry whose destination is an EID;
  - read by TCPCL transmission (the feeder's attempt), by reassembly (RFC 9171 §5.9), and by delivery to
    the application agent, which is the acceptance transaction of §13.2 for the ADU;
  - the final XFER_ACK follows the durable write (or an exact durable duplicate); a refusal or an uncertain
    commit never sends a successful final XFER_ACK.
- **The forward pin** (fn1 `fn-bprl-undertake`): written by the BP feeder when a feed entry to an EID is
  first attempted; released only by the receipt ADU naming it from its destination, read by BP ingress on
  TCPCL (fn1 bp-receipt.md), or by the operator's waiver (fn1 `carry drop WORK --abandon`, PRF-950). A
  TCPCL XFER_ACK, a "delivered" status report (RFC 9171 §6.1.1; fn1 T5), carrier expiry or deletion, and
  another pin's receipt release nothing; a new bundle may carry the subject again.
- **The receipt the node owes** is a feed entry whose object is a receipt ADU: written by BP ingress's
  acceptance of an ADU that requests one, read by the BP feeder; losing its bundle does not lose it.
- Submission, attempt, outcome and handoff are not kinds: a submission is a feed entry, an attempt and its
  outcome are the feed entry's phase and disposition, and a handoff is the ADU's acceptance transaction.
- FNBS's five budgets and its cleanup debt are Meter dimensions (D0 holding kinds), not records: admission
  reserves the writes that settle what it admits; exhausted admission credit never blocks a settlement.
- Egress is a feed (§13.3) whose transport is a convergence layer and whose next hop is the operator's route
  table; no route keeps the entry pending and reported. A contact is a wake for the feeder, never a
  scheduler of its own.
- All of 13.6 is design until BP ingress serves (after the served consumer kind).

### 13.7 Keystones (statement first, owed with teeth; `fn2/books/owed-peer.lisp`)
| id | statement |
|---|---|
| K-P1 | the peer claim (§13.4), against an independent fold of the evidence and conflict observations |
| K-P2 | IHAVE and TAKETHIS refine POST's acceptance transaction after carrier preparation: identity, admission, membership, charges and durability agree (stated over D5 3/n's served path) |
| K-P3a | every installed feed entry is pending or has exactly one terminal disposition; no cursor advance loses one |
| K-P3b | settlement only under stated scheduling, availability, resource and peer-reply assumptions (an endless `431` refutes the unconditional claim); stated over the served feeder |
| K-P4 | at most one durable terminal disposition per delivery identity across restarts, duplicate and stale replies; a re-feed is a new identity |
| K-P5 | a forward pin is released only by its receipt ADU from its destination or the operator's waiver |
| K-P6 | an IHAVE or TAKETHIS matching a history entry whose body was reclaimed is a duplicate (435/439), allocates no article number and releases no pin; evidence or a peer's history entry alone is not this case |

### 13.8 The reference model and its witnesses (`peer-model.lisp`, `tests/peer-witnesses.lisp`)
The model's fixtures are checker oracles, not served evidence. Built: W1 (opposite first arrivals, K-P1),
W2 (two nodes meet with funding exhausted: partial import, gap, later funding, repair; K-P1), W3 (identical
content with new evidence; K-P6's premise), W7 (reclamation under a forward pin and a reoffer; K-P5, K-P6),
the offer rule (evidence alone never answers 435/438), F1 (a ring A→B→C with the loop excluded by Path),
F2 (a deferred head, later successes, mixed CHECK and TAKETHIS phases, a stale reply, a restart with an
attempt unresolved, losses reaching the bound; K-P3a, K-P4). Each asserts its antecedent and catches its
fault. The other witnesses of Astra's matrix (a forged authority, an object before its authority, cancel
before target across a crash, the commit cuts, two routing projections, an old incarnation, conflict
visibility under disclosure, carried count and octets, cleanup debt, fragments, a grant change under
pending work) land with the served verb each exercises.

### 13.9 Seams, with the owners' answers
- **D (answered):** §13.2's table whole in D5 3/n; authority rechecked at each offer and transfer;
  §14.4.3's identity text rewritten to rulings 6/7/8/11 in D's next push; `:peer-credit` as a ledger net
  change (its D0 row sent through main).
- **C (ruled):** the feed entry, the cancel intent and the forward pin land with their producers; C's
  intra-commit ordinal on the position-ordered admission index lands with the catch-up batch's reader.
- **B (answered):** the BP ADU is a record subject (a payload kind in the commit stream, its envelope by
  the record header); an imported record keeps the origin's occurrence, lineage, domain and incarnation.
- **A:** outbound `Connect` for the feeder, after the form's P4.

## 14. Order of the build
1. Done: the port form, the consumer port and carriers, the model, the keystones, the two fixtures.
2. Done: the big-endian layout kinds; the FNCT and `fncu` codecs (v1 and v2, codes 0-18, replies 5, 6,
   9 and 28) with fn1's bytes as fixtures; the legacy translation as data.
3. Done: peering and BP stated in wire words (§13); the peer model, K-P1, K-P3a, K-P4, K-P5, K-P6 owed
   with teeth, six witnesses.
4. Done: the CONSUMER checker over the model, scenarios 7, 8, 9 over the oracle node, K10 stated.
5. `fn2-ctl` and `fn2-cns` pasted as certifying kinds (E.P1, the form's G2 with the extra-children
   tuple, C's read `:child` faces), driven at the adapter boundary with a fixture peer record until A's
   `:local` listener; register and ack answer `unavailable` until D's txn port carries `:consumer`;
   the simulator adapter that defines K10's producer; then the XFNC block.

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
Taken, in §13's words: the feed consumer installs feed entries and acks in one processing transaction; the
feeder's fair selection; the delivery identity, phases, separate deferral and loss counts, explicit drops;
the feed consumer outside the remote whitelist; control matched by its target's groups; 435/438 only from
the node's history or a not-wanted decision; the exhaustion reasons split three ways; TAKETHIS's RFC 4644
default with fn1's `436 <id>` as `fn-compat`; replies matched by (phase, Message-ID); the catch-up batch's
history identity, scope, stop reason and the coverage claim kept apart from the batch's end; evidence
identity kept across import; the carrier distinct from the forward pin; the final XFER_ACK after the durable
write; the profile's ADU bound; authority rechecked at every peer decision; aggregate capacity beside
per-peer charges; K-P1..K-P6 with full antecedents. Dropped under main's ruling (a kind lands with its
producer): Astra's typed bundle, submission, attempt, outcome, handoff and generic obligation records, which
§13.6 reduces to the bundle and the forward pin. One position kept: Astra would install feed entries in the
POST batch; E installs them in the feed consumer's processing transaction, because selection is a pure
function of the occurrence and a feed write stays out of every POST as peers multiply.
