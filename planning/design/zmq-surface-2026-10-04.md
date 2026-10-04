# The zmq-pattern surface and the application article kind (D50) — 2026-10-04

Lane `zmq`. Inputs: D49 (6.6.0 may carry "a zmq-pattern surface (pub/sub,
req/rep, push/pull, pair) over groups, the consumer cursor and signed
exact-byte articles, generated and not hand-written"), Mini's M6
(`redregg/designs/MINI-FN-660-REQUIREMENTS-20261004.md` §M6, §3.2) and fn's
reply (`redregg/work/FN-660-RESPONSE-20261004.md` §M6, C-0a, C-0b).
Companion: `planning/design/wire-grammar-2026-10-04.md` (lane mini-contract,
the one grammar language and its interpreter).

## 1. What fn has, and the three acknowledgements

The surface is made of things fn already serves. None is new state.

| fn piece | what it gives a pattern |
|---|---|
| a newsgroup | a topic / a queue / a mailbox: a named, permissioned, ordered set |
| `fn hybrid-author` over the 0600 control socket | a signed exact-byte post; idempotent resend by Message-ID (D25) |
| the consumer cursor (`fncu` v1; register, poll, wait, ack, position) | a durable, per-reader position over one group, woken by the owner's commit signal |
| the article kind `opaque` v1 (this decision) | the one envelope every pattern frame is carried in |

fn keeps three acknowledgements apart, and every pattern below names which
one it gives at each step. They never substitute for each other:

1. **Transport ACK**: the control reply frame reached the client. It says
   nothing about durability (AGENTS.md: "durable acceptance comes only from
   persisted state, never from a socket write").
2. **Retention receipt**: `hybrid-author` answered `accepted` or "already
   stored here" (exit 0). The authored source is stored byte for byte. A lost
   or ambiguous answer is `uncertain` (exit 3), never a guessed refusal; the
   sender resends the SAME signed bytes (never re-signs: ML-DSA is
   randomized, a new signature is a new carrier and a refused conflict,
   C-0b).
3. **Application outcome**: the reader's own `ack` of its cursor, after its
   own transaction. Monotone and idempotent; `position` settles an uncertain
   ack.

## 2. The article kind `opaque`, version 1 (Mini's M6)

Not a "profile": in fn a profile is the D27 store profile. This is an
**application article kind**, new fn vocabulary, row D50.

- **Subject.** The *authored source* (the bytes D01 signs). A served article
  is Xref, Path, Injection-Info and the FN-Authorship carrier lines, then the
  authored source; the extraction is `fn-hc-authored-source`.
- **Grammar** (`books/article-kind.lisp`, `*fn-ak-v1-rows*`): eight header
  rows in fixed order — From, Date, Newsgroups, Subject, Message-ID,
  `FN-Kind: opaque 1` (the version word), Content-Type (the application's
  media type; fn never reads it), `Content-Transfer-Encoding: base64` — one
  physical line each, then the blank line, then the payload as RFC 4648
  padded base64 in CRLF lines of 76 (the last 1..76; the empty payload is no
  lines). The payload has no ceiling here (D27); the operator's article
  bound applies at admission.
- **The kind refines the grammar.** A value of the kind is a grammar value
  whose header values open with a VCHAR and pass fn's own injection checks:
  From is a mailbox-list (`fn-mbx-mailbox-listp`), Newsgroups a nonempty
  newsgroup-list, Message-ID a msg-id without WSP. So acceptance is
  unconditional on content; a grammar-legal value outside the kind is
  refused by the injection decision BY NAME (`:from-invalid`,
  `:newsgroups-invalid`, `:message-id-invalid`; tests/acl2/article-kind-tests).
- **One codec.** The wire-grammar interpreter at `*fn-ak-grammar*`
  (computed from the rows) IS the renderer and the recognizer; its generic
  round trips are the kind's (`fn-wg-decode-of-encode`,
  `fn-wg-encode-of-decode`). This lane writes no second encoder or decoder.
  `fn-ak-layout` is the proof-side spelled-out layout; one bridge theorem,
  `fn-ak-grammar-encode-is-the-layout`, joins them when the interpreter
  lands (owed; §6). The base64 is `books/octet-text.lisp`'s, which already
  proves both round trips.
- **Version word.** `FN-Kind: opaque 1`. Another version of `opaque` is
  refused `:kind-version` by name, anything else in that row `:kind`, on
  both sides. A new version is a new row table and a new grammar constant,
  never an edit of v1.
- **Export.** Family `article.opaque-1` in `specs/wire-grammar.json`, with
  vectors from `fn-ak-example-values` × `fn-ak-example-payloads`.

Keystones (PRF-1320, PRF-1321; `books/article-kind-acceptance.lisp`):

- `fn-ak-layout-parses`: for every value of the kind and octet payload within
  the codec ceiling, `fn-article-parse` (what every reader calls) answers
  `:ok` with exactly the eight fields, the header the rows, and the body the
  76-column base64 frame. Its general form `fn-ak-layout-parses-under` holds
  under any header limits of at least 8 fields, 8 lines and the header's
  octets.
- `fn-ak-layout-is-injected`: under a valid, posting-allowed injection
  configuration whose groups admit the article's newsgroups, whose header
  limits are at least those, whose article bound covers the injected octets,
  and a usable in-cycle clock, `fn-inj-decide` answers `:injected` with the
  author's Message-ID, the parsed newsgroups and the octets
  `Path`+`Injection-Info` prefix followed by the source unchanged (no
  Injection-Date: Date and Message-ID are supplied, so the article does not
  depend on the clock). Host callers: the POST and operator-post routes
  (`fn-inj-decide`), and through the hybrid route below.

- `fn-ak-layout-is-a-hybrid-injection` (PRF-1322;
  `books/article-kind-hybrid.lisp`): the route Mini posts by. For carrier
  material whose field encodes, under the same premises with the header
  limits holding the carrier's ninth field and its fold lines,
  `fn-hsig-injected-carrier-plan` answers `:injected` with the octets
  Path + Injection-Info + FN-Authorship carrier + the source unchanged.
  `fn-ak-carrier-parses`: the carrier parses with FN-Authorship first and
  the eight fields after it.

Owed for M6 (named, not claimed): e1/2 (`tools/fn_consumer.py`) re-expressed on the
kind or deleted (the derived-path law on fn's side; the consumers lane holds
that file).

## 3. The patterns: what each maps onto, and its durable guarantee

| pattern | carrier | send | receive | guarantee (scope) |
|---|---|---|---|---|
| **pub/sub** | topic group T | PUB: `opaque` article to T via hybrid-author → retention receipt | SUB: a consumer registered on T; `wait`/`poll` → event → authored source → kind decode → payload; `ack` → application outcome | every retained message in T is delivered at least once to every registered subscriber (registration starts at position 0, so a late subscriber reads T from the start, unlike zmq), in Store history order, until reclaimed; reclaimed content is an explicit `unavailable` gap, never a silent skip; a withdrawn message arrives as a withdrawal event, never as content; a slow subscriber is never dropped (unlike zmq's high-water mark) |
| **pair** | two groups A→B, B→A (or one group and two consumers that skip their own principal) | as PUB | as SUB | pub/sub's, with exclusivity from the accounts' post/read patterns, not from the socket |
| **req/rep** | request group Q; the requester's reply group R | REQ: `opaque` request to Q, Message-ID M | REP: consumes Q, posts a reply to R correlated to M; REQ consumes R | the request is durable from its retention receipt; the reply is delivered at least once; a REP resend is idempotent when the reply's Message-ID is derived from M (D25); fn enforces no timeout and no one-reply rule (the application's) |
| **push/pull** | queue group W, N workers | PUSH: `opaque` to W | PULL i: a consumer on W that processes the messages whose Message-ID digest is i mod N and acks the rest | each retained message is processed by its one partition's worker at least once; static N: a dead worker's partition waits for it (no stealing) |

**Not in 6.6.0, by name:**
- zmq's *prefix* subscription (one SUB over many topics): needs the general
  v1 query (multi-group selection, `specs/consumer-progress.md`), which the
  local profile does not serve. One group per subscription until it does.
- **Competing consumers with leases** (push/pull with work stealing): needs
  owner state (a claim with a lease, re-offered on expiry), i.e. new FNCE
  event kinds, which D46 parks until their producer exists. A decision row
  of its own when wanted.
- **Correlated replies inside the kind**: req/rep needs a `References: <M>`
  row, so it is kind `opaque-reply` v1, a second row table generated by the
  same machinery, with its own acceptance instance. Until it lands, req/rep
  correlation would be in the payload, which fn cannot check; so req/rep is
  not offered on v1.
- Remote (FNCR) senders and readers: the remote consumer lane's; the
  patterns are transport-agnostic over whichever control path admits them.

## 4. One generator per pattern, no hand-written per-pattern code

`books/app-pattern.lisp` (prefix `fn-pat-`), one macro `def-pattern`. A
pattern is a declaration:

```lisp
(def-pattern pubsub
  :kind opaque-1                      ; the grammar constant and acceptance instance
  :roles ((pub :posts topic)
          (sub :reads topic))
  :guarantee (:at-least-once :history-order :reclaim-gap :withdrawal-event))
```

From it the generator emits, and nothing else is written per pattern:

1. **The role plans**, as ACL2 data: each role is a sequence over a closed
   step vocabulary — `(:encode KIND)`, `(:author GROUP)`,
   `(:register GROUP)`, `(:wait S)` / `(:poll)`, `(:project)`,
   `(:decode KIND)`, `(:ack)` — every step an existing control request or an
   offline ACL2 verb. The host has ONE verb, `fn pattern NAME ROLE ...`,
   that interprets a plan (a fixed loop over the step vocabulary); adding a
   pattern adds no host code.
2. **The delivery keystone instance**: for the role pair, what the receiving
   role decodes from the served article's authored source is the value the
   sending role encoded — the composition of the grammar round trip, the
   exact-source retention theorem
   (`fn-hsig-injected-carrier-retains-exact-signed-source`) and
   `fn-hc-authored-source`. Proved once generically; each pattern is an
   instance.
3. **The export rows**: the pattern's exchange (`exchanges` in
   `specs/wire-grammar.json`) and its usage row for the CLI and the docs.

The patterns' meaning lives in their declarations; `def-pattern` is the
only author of plans, instances and rows.

## 5. Order of work

1. M6 kind book and acceptance keystones (done at this decision's commit).
2. The bridge to the interpreter, when `books/wire-grammar.lisp` lands
   (mini-contract), and the kind's decode wrapper with `:kind-version`.
3. `def-pattern` with pub/sub as its first instance; `fn pattern` host verb;
   native scenario: publish three payloads (empty, short, two full lines)
   from one principal, a subscriber waits, decodes, acks; owner restart in
   between; the subscriber receives exactly the three payloads in order.
4. The hybrid-route acceptance keystone (done, PRF-1322).
5. pair, then push/pull (partitioned) as instances; `opaque-reply` and
   req/rep after.

## 6. Owed / what would change this

- `fn-ak-grammar-encode-is-the-layout`: owed on the interpreter's landing.
- If Mini wants the kind's refinements (mailbox-list, newsgroup-list,
  msg-id) in its generated decoder, they need grammar nodes; today they are
  fn's acceptance premises, exported as the family's named premises.
- If ember wants competing consumers in 6.6.0, the lease decision comes
  first (it touches D46).
