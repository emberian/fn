# Peering: transit feeds as a port of F_node

Status: design, wave 4 (`w4/peering-design`, branched at `ca66782`). No book
in this document exists; every ACL2 form is a *statement to be certified*,
written against definitions that exist at `ca66782` with their names used
exactly, or against sibling lanes' designs where marked. The prefixes
`fn-peer-`, `fn-feed-` and `fn-path-` are reserved here and are registered in
[`docs/prefixes.md`](../docs/prefixes.md) by packet K0. Counts live in the
generated ledger and nowhere here. A proposed theorem is not a theorem proved
by ACL2.

What peering is, in one sentence: a *transit* interface (RFC 3977 §6.3.2
IHAVE; RFC 4644 CHECK/TAKETHIS) on the same listener as the reader, whose
inbound half ends in the one acceptance path every article takes
(`fn-node-prepare`/`fn-node-complete`, [node](../books/node.lisp)), whose
outbound half is a durable per-peer queue stepped by the scheduler's
contact/tick model, and whose peer table is a configuration record kind under
[reconfiguration](reconfiguration.md). The DTN relay of [relay](relay.md) and
[bp-design](bp-design.md) is the same profile over a different convergence
layer; §1.4 says exactly which state is shared.

RFC vocabulary, used exactly: fn acting on a received transit article is a
*relaying agent* (RFC 5537 §3.6) toward its outbound peers and a *serving
agent* (§3.7) toward its readers; both sets of duties apply to one
acceptance. Path construction is §3.2.1; history and duplicate suppression is
§3.3. Where the text below says "MUST", it is quoting an RFC; where it says
"fn requires", it is a stronger fn guarantee; "local policy" marks a choice
the RFC leaves open.

## 1. The peering profile

### 1.1 fn-to-fn and fn-to-legacy over TCP NNTP

One listener, two roles per connection. A connection is a *peer* connection
when its source resolves to a configured peer record at `:open` (§1.2); every
other connection is a reader. Peer connections get the transit commands;
reader connections get `501` for them, as today for every unknown keyword.
(RFC 3977 §3.4.1 lets a server be transit-only or reader-only per connection;
fn decides by peer identity, never by `MODE`.)

| Command | RFC | Peer connection | Reader connection |
| --- | --- | --- | --- |
| `CAPABILITIES` | 3977 §5.2, §3.3.2 | adds `IHAVE` and `STREAMING` | unchanged (`VERSION 2`, `IMPLEMENTATION`) |
| `MODE STREAM` | 4644 §2.3 | `203`; stateless, MUST be accepted for legacy clients | `501` |
| `IHAVE msgid` | 3977 §6.3.2 | `335` / `435` / `436`, then article, then `235` / `436` / `437` | `502` (3977 §3.2.1: recognized, not permitted; K1 corrected this from `501`) |
| `CHECK msgid` | 4644 §2.4 | `238` / `431` / `438`, with the offered msgid echoed | `502` |
| `TAKETHIS msgid` + article | 4644 §2.5 | `239` / `439`, msgid echoed; the article always follows | `502` |

Legacy peers (INN's `innfeed`) speak exactly this. fn-to-fn peering uses the
same five commands and no private extension; the fn-specific content travels
*inside* articles as reserved header fields (§6), so that an INN in the middle
carries it unchanged (RFC 5537 §3.6: relaying agents MUST NOT alter anything
but Path and Xref).

Inbound: fn is the server. Outbound: fn is the client, one connection per
configured outbound peer, opened by the host when the peer's contact holds
(§3). Both directions are ports of F_node ([node-functionality](node-functionality.md)
§1.2): inbound reuses `(:open id)`/`(:octets id octets)`/`(:close id)` with the
peer identity resolved at open; outbound adds a client-side connection kind.

```lisp
;; F_node events added by this design (fn-ideal-event-kindp gains them).
;;   (:open id peer)                  ; peer is a peer name or nil (reader); host resolves it
;;   (:feed-open peer id)             ; host opened an outbound connection to peer
;;   (:feed-octets id octets)         ; the peer's responses, any partition
;;   (:feed-close id)                 ; outbound connection lost or closed
;;   (:tick peer obs)                 ; scheduler tick for one peer under a clock observation
;; F_node effects added:
;;   (:command id octets)             ; a command line or a command plus article block, to an outbound connection
;;   (:connect peer endpoint)         ; ask the host to open an outbound connection
```

`:command` is distinct from `:reply` because `fn-nntp-effectp` types replies
as RFC 3977 §3.2 responses; a command line has a different grammar
(`fn-feed-commandp`, §3.2), and the closed effect type of node-functionality
§1.2 must stay closed.

### 1.2 The peer record: a configuration record kind

[Reconfiguration](reconfiguration.md) §1.5 carries `(:set-peers peers)` with
peers as opaque `(eid endpoint contact-plan)` triples read by nothing. This
design refines that slot into a typed record and two deltas, and corrects one
sentence of that design (§1.2.1 below).

```lisp
;; books/config.lisp (reconfiguration packet R1 owns the book; this design adds the shape)
(defun fn-cfg-peer-make (name path-identity transport inbound outbound auth)
  (list name path-identity transport inbound outbound auth))
(defun fn-cfg-peer-name          (p) (car p))         ; local label, fn-record-ascii-stringp
(defun fn-cfg-peer-path-identity (p) (cadr p))        ; RFC 5537 §3.2 <path-identity> the peer prepends; octets
(defun fn-cfg-peer-transport     (p) (caddr p))       ; (:nntp host port) | (:bp eid)
(defun fn-cfg-peer-inbound       (p) (cadddr p))      ; (accept-groups max-octets max-inflight) or nil: no inbound
(defun fn-cfg-peer-outbound      (p) (car (cddddr p))); (feed-groups streaming max-queue backoff-ms) or nil: no feed
(defun fn-cfg-peer-auth          (p) (cadr (cddddr p))); (:source-address addr) | (:principal id) ; see §6

(defun fn-cfg-peer-inbound-groups  (p) (car (fn-cfg-peer-inbound p)))    ; fn-wildmat-listp, RFC 3977 §4
(defun fn-cfg-peer-inbound-max-octets (p) (cadr (fn-cfg-peer-inbound p)))
(defun fn-cfg-peer-inbound-max-inflight (p) (caddr (fn-cfg-peer-inbound p)))
(defun fn-cfg-peer-outbound-groups (p) (car (fn-cfg-peer-outbound p)))
(defun fn-cfg-peer-streamingp      (p) (cadr (fn-cfg-peer-outbound p)))   ; CHECK/TAKETHIS vs IHAVE
(defun fn-cfg-peer-max-queue       (p) (caddr (fn-cfg-peer-outbound p)))
(defun fn-cfg-peer-backoff         (p) (cadddr (fn-cfg-peer-outbound p)))  ; ms, natp

(defun fn-cfg-peerp (p)
  (and (true-listp p) (equal (len p) 6)
       (fn-record-ascii-stringp (fn-cfg-peer-name p))
       (fn-path-identityp (fn-cfg-peer-path-identity p))                ; §2.3
       (fn-cfg-peer-transportp (fn-cfg-peer-transport p))
       (or (null (fn-cfg-peer-inbound p))
           (and (fn-wildmat-listp (fn-cfg-peer-inbound-groups p))
                (posp (fn-cfg-peer-inbound-max-octets p))
                (<= (fn-cfg-peer-inbound-max-octets p) *fn-record-max-payload*)
                (posp (fn-cfg-peer-inbound-max-inflight p))))
       (or (null (fn-cfg-peer-outbound p))
           (and (fn-wildmat-listp (fn-cfg-peer-outbound-groups p))
                (booleanp (fn-cfg-peer-streamingp p))
                (posp (fn-cfg-peer-max-queue p))
                (natp (fn-cfg-peer-backoff p))))
       (fn-cfg-peer-authp (fn-cfg-peer-auth p))))

;; Deltas added to *fn-cfg-delta-kinds*; (:set-peers ...) is retired in favour of these.
;;   (:set-peer record)      upserts by name
;;   (:remove-peer name)     admissible only when no feed queue entry for that peer is
;;                           outstanding (fn-feed-peer-idlep), so a retired peer never
;;                           has an orphaned durable offer
;; The node's own path identity is a policy slot: (:set-policy :path-identity octets).
```

The wildmat lists are RFC 3977 §4 wildmats over the article's Newsgroups
names, matched by the certified matcher (`books/wildmat.lisp`, rightmost
wins). Inbound: an article is *in scope* for a peer when at least one of its
Newsgroups names matches `accept-groups` **and** is live at the current
configuration generation (`fn-cfg-group-livep`). Outbound: an article is
*fed* to a peer when at least one of its accepted local groups matches
`feed-groups`. This is RFC 5537 §3.6's "configured to supply / to receive at
least one of the newsgroup names", stated per direction. Distribution header
matching is not modeled (no requirement carries it; noted as open).

#### 1.2.1 Peer changes are not transport-only

Reconfiguration §2.3 and theorem §3.7 call listener and peer changes "effects,
not state". That is exact for the node's *state* (acceptance, retention,
bindings, stage are untouched, and §3.7 stays true) and inexact for
*decisions*: `accept-groups` and `feed-groups` change what `fn-peer-decide`
answers from the next command on. So `(:set-peer ...)` bumps the generation
like every delta, `fn-cfg-transport-only-deltasp` continues to hold of it
(the theorem is about state), and this design adds the sentence
reconfiguration should carry: *a peer delta changes future transit decisions
and no committed state*. Theorem K7 in §4 states it.

### 1.3 Limits and capacity

Per-peer inbound limits are checked in this order, and the first failing
check names the refusal (§2.2): the connection's `fn-wire-statep` body limit
is set from `inbound-max-octets` at `:open` (so an oversize article is cut by
the wire machine, RFC 3977 §3.1.1 dot-block, never by a second parser);
`max-inflight` bounds the number of `238`/`335` answers outstanding before a
`431`/`436`. Capacity is the retention ledger's: `fn-retain-admissiblep` with
the charge `fn-charge-for-payload` ([identity](identity.md)) of the received
octets, exactly as for a POST.

### 1.4 The DTN relay is the same profile over another convergence layer

| | TCP NNTP peer | BP peer (bp-design §1, relay.md) |
| --- | --- | --- |
| Peer record | `fn-cfg-peerp` with `(:nntp host port)` | `fn-cfg-peerp` with `(:bp eid)`; the same `accept-groups`/`feed-groups`, the same `path-identity` |
| Offer phase | `CHECK`/`IHAVE` before the bytes | none: the bundle arrives whole; offer and transfer collapse into one `(:bundle src octets)` event |
| Decision | `fn-peer-decide` (§2.2) | **the same function**, called by `fn-bpi-ingress-prepare` before `fn-bpi-record-for`; `fn-bpi-policy-group-map` is derived from the peer's `accept-groups` and the live group table |
| Transfer and acceptance | `fn-peer-transfer` → `fn-node-prepare`/`fn-node-complete` through the store | `fn-bpi-ingress-prepare` → the same `fn-node-prepare`/`fn-node-complete` (already so at `books/bp-ingress.lisp:318`) |
| Provenance record | `(:peer-transit peer diag)` §2.4 | the same record with `(:cl session transfer peer)` origin (bp-design §1.3) |
| Duplicate history | `fn-peer-history-hasp` §2.5 | the same predicate (`fn-bpi-adu-durably-acceptedp` is its current BP-side twin and is replaced by it) |
| Outbound queue | `fn-feed-` per-peer queue, feed journal | `fn-bp` works and FNWF journal; `fn-sched-` selects |
| Reply to the peer | NNTP status line | XFER_REFUSE reason / receipt ADU |
| Receipt semantics | `239`/`235` is a *transmission* receipt (RET-003), never a retention receipt; no pin is released by it | `fn-bpr` receipt is application evidence; `fn-bprl-release-decision` may release the `:forward` pin |
| Loop check | Path (§2.3) | Path **and** Previous Node / Hop Count (bp-design §1.2) |

Shared, by construction: the peer record, `fn-peer-decide`, the acceptance
path, the provenance record, the history predicate, the loop check. Different:
the offer phase, the response vocabulary, the outbound driver and journal, and
what a positive reply means for retention. The relay's undertaking rule
(relay.md) applies only to the BP side because only there does a receipt
promise anything.

## 2. The inbound transit machine

### 2.1 Session state and the wire

`fn-nntp-make-session` gains two fields; `fn-nntp-sessionp` gains their
recognizers. This is a shared-struct change: every book that opens the
session shape (`nntp-invariants`, `nntp-effects`, owner, F_node's `fn-ideal-connp`)
rebuilds; packet K1 builds the whole tree, not the changed books.

```lisp
;; books/nntp-session.lisp
(defun fn-nntp-make-session (openp group current projected peer transfer)
  (list openp group current projected peer transfer))
(defun fn-nntp-session-peer     (x) (car (cddddr x)))     ; peer name or nil
(defun fn-nntp-session-transfer (x) (cadr (cddddr x)))    ; nil | (:ihave msgid) | (:takethis msgid)

;; The wire machine already has an :article mode (fn-wire-begin-article,
;; books/wire.lisp:344) that the reader never enters.  A 335 reply, or a
;; TAKETHIS command line, is what enters it; the resulting (:article body)
;; event is routed by fn-nntp-step to fn-peer-transfer.  node-functionality
;; §4.5 marks the current 501-for-:article branch unreachable-in-composition;
;; this design and w4/post are the two lanes that make it reachable, with
;; disjoint session-transfer values (POST uses (:post)).
```

`fn-nntp-open-session archive config peer` sets `peer` from the `:open`
event and `transfer` to `nil`; a peer connection whose record has no
`inbound` half opens with `peer` set and answers `435`/`438` to every offer
(policy: not wanted), so a feed-only peer that misbehaves cannot inject.

### 2.2 Offer → decision → transfer → acceptance

Three functions, one decision.

```lisp
;; books/peer.lisp (K1)

;; The decision is total and typed.  Reasons are a closed enumeration so that
;; *fn-ideal-refusals* (node-functionality §1.2) stays closed.
(defconst *fn-peer-decisions* '(:want :have :defer :refuse))
(defconst *fn-peer-reasons*
  '(:not-a-peer :no-inbound :message-id-syntax :history :staged :busy :fenced
    :inflight-limit :capacity :out-of-scope :loop :no-date :date-future :no-clock
    :proto-article :oversize :unknown-group :date-cutoff))

(defun fn-peer-decision (kind reason) (list kind reason))
(defun fn-peer-decision-kind   (d) (car d))
(defun fn-peer-decision-reason (d) (cadr d))

;; Offer-time decision: only what is knowable from the Message-ID and the
;; connection.  The article's own headers are not yet available.
(defun fn-peer-decide-offer (node cfg peer session msgid clock inflight)
  (declare (xargs :guard t))
  (cond ((not (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
         (fn-peer-decision :refuse :not-a-peer))
        ((null (fn-cfg-peer-inbound (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
         (fn-peer-decision :refuse :no-inbound))
        ((not (fn-af-message-idp msgid))                       ; books/article-fields.lisp:124
         (fn-peer-decision :refuse :message-id-syntax))
        ((fn-peer-history-hasp (fn-record-octets-string msgid) node)   ; §2.5
         (fn-peer-decision :have :history))
        ((fn-peer-stagedp (fn-record-octets-string msgid) node)        ; the same msgid is the pending transaction
         (fn-peer-decision :defer :staged))
        ((equal (fn-state-fenced (fn-node-acceptance node)) t)
         (fn-peer-decision :defer :fenced))
        ((<= (fn-cfg-peer-inbound-max-inflight (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
             inflight)
         (fn-peer-decision :defer :inflight-limit))
        ((not (fn-retain-admissiblep (fn-node-retention node)
                                     (fn-peer-probe-obligation-id msgid)
                                     (fn-peer-probe-subject)
                                     :archive (fn-peer-probe-evidence) *fn-charge-minimum*))
         (fn-peer-decision :defer :capacity))                  ; local policy, see below
        (t (fn-peer-decision :want nil))))
```

The capacity probe at offer time uses the minimum charge (one history unit
plus the smallest payload class of `fn-charge-for-payload`); it can only
under-refuse, never over-refuse, and the exact check happens at transfer.
Local policy: capacity at *offer* time is `:defer` (`431`/`436`, the peer
retries after a reconfiguration raises capacity); capacity at *transfer*
time, when the peer has already sent the bytes, is `:refuse` (`437`/`439`,
RFC 3977 §6.3.2.2 lists "disc space limitations" among rejection reasons).
The reason is in the reply text and the journal, so an operator can re-feed
after raising capacity.

```lisp
;; Transfer-time decision: the whole article is here.  Every check of RFC
;; 5537 §3.6 steps 1 to 4 and §3.7 steps 1 to 3 is one cond arm, in the
;; RFC's order, and every arm names its reason.
(defun fn-peer-decide-transfer (node cfg peer msgid octets clock)
  (declare (xargs :guard t))
  (let* ((parsed (fn-article-parse octets))                            ; bounded, books/article.lisp
         (article (fn-article-result-article parsed))
         (check (and article (fn-af-proto-article-check article))))     ; books/article-fields.lisp:280
    (cond ((> (len octets) (fn-cfg-peer-inbound-max-octets (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
           (fn-peer-decision :refuse :oversize))
          ((not article) (fn-peer-decision :refuse :proto-article))
          ;; §3.6.1: Newsgroups, Message-ID, and Injection-Date or Date.  The
          ;; proto-article check permits a missing Message-ID for POST; transit
          ;; requires it, and requires it to equal the offered one.
          ((not (equal (fn-af-status-kind check) :ok)) (fn-peer-decision :refuse :proto-article))
          ((not (fn-af-message-id-equalp (fn-peer-check-msgid check) msgid))
           (fn-peer-decision :refuse :message-id-syntax))
          ((not (fn-path-date-presentp article)) (fn-peer-decision :refuse :no-date))
          ;; §3.6.2: date more than 24 hours in the future.  With no clock
          ;; observation the check cannot run: defer, never guess.
          ((null clock) (fn-peer-decision :defer :no-clock))
          ((fn-path-date-futurep article clock *fn-peer-future-slack-ms*) (fn-peer-decision :refuse :date-future))
          ;; §3.6.3 / §3.7.3: already accepted.  Re-checked here because the
          ;; offer may be stale (RFC 4644 §2.4.2: CHECK responses are advisory).
          ((fn-peer-history-hasp (fn-record-octets-string msgid) node) (fn-peer-decision :have :history))
          ;; loop: our own path identity already in Path (§2.3)
          ((fn-path-names-p (fn-af-path-field-value article) (fn-cfg-policy (fn-cfg-value cfg) :path-identity))
           (fn-peer-decision :refuse :loop))
          ;; scope: at least one Newsgroups name accepted from this peer and live now
          ((null (fn-peer-scope-groups (fn-af-check-groups check) peer cfg)) (fn-peer-decision :refuse :out-of-scope))
          ((fn-peer-stagedp (fn-record-octets-string msgid) node) (fn-peer-decision :defer :staged))
          ((consp (fn-node-stage node)) (fn-peer-decision :defer :busy))
          ((equal (fn-state-fenced (fn-node-acceptance node)) t) (fn-peer-decision :defer :fenced))
          ((not (fn-retain-admissiblep (fn-node-retention node)
                                       (fn-id-obligation-of (fn-record-octets-string msgid) (fn-id-subject-of-payload octets))
                                       (fn-id-subject-of-payload octets) :archive
                                       (fn-peer-evidence peer cfg) (fn-charge-for-payload (len octets))))
           (fn-peer-decision :refuse :capacity))
          (t (fn-peer-decision :want nil)))))
```

`fn-peer-scope-groups` returns the sublist of the article's Newsgroups names
that match the peer's `accept-groups` and are live: those, and only those,
become the local memberships (`groups` argument to `fn-node-prepare`). The
original Newsgroups header stays in the stored source bytes untouched (D01,
NNT-006 (defined in [nntp.md](nntp.md)): "preserve the original Newsgroups header/provenance"; D05's
"incoming transfers may retain the original group list while indexing only
configured admissible groups"). An unknown group in Newsgroups is therefore
not a refusal by itself; an article *none* of whose groups is in scope is
`:out-of-scope`. RFC 5537 §3.7: "Serving agents MUST NOT create new
newsgroups simply because an unrecognized newsgroup-name occurs" — structural
here, since only `fn-cfg-group-livep` names can be memberships.

Then the transfer itself is the post path, called with arguments ACL2
computed from the octets, and nothing else:

```lisp
;; The injection arguments of a transit article.  One owner: ACL2.
(defun fn-peer-injection-arguments (node cfg peer msgid octets)
  (let* ((check  (fn-af-proto-article-check (fn-article-result-article (fn-article-parse octets))))
         (id     (fn-record-octets-string msgid))
         (subject (fn-id-subject-of-payload octets)))
    (list (fn-cfg-generation (fn-node-config node))          ; cfg-gen (reconfiguration R2)
          (fn-sf-frontier-generation node)                     ; the transaction generation the store hands out
          id octets
          (fn-peer-scope-groups (fn-af-check-groups check) peer cfg)
          (fn-id-obligation-of id subject) subject
          (fn-peer-evidence peer cfg)                          ; (:peer-transit peer path-diag generation)
          (fn-charge-for-payload (len octets)))))

;; fn-peer-transfer returns (mv node2 decision).  On :want it is exactly one
;; fn-node-prepare; the durable completion arrives later as the store's
;; (:finish)/(:io ...) events through fn-snrt-step, as for POST.  It never
;; calls fn-accept-prepare directly and never touches retention itself.
(defun fn-peer-transfer (node cfg peer msgid octets clock)
  (let ((d (fn-peer-decide-transfer node cfg peer msgid octets clock)))
    (if (not (equal (fn-peer-decision-kind d) :want))
        (mv node d)
      (let ((args (fn-peer-injection-arguments node cfg peer msgid octets)))
        (mv (fn-node-prepare node (nth 0 args) (nth 1 args) (nth 2 args) (nth 3 args)
                             (nth 4 args) (nth 5 args) (nth 6 args) (nth 7 args) (nth 8 args))
            d)))))
```

(`fn-node-prepare`'s signature at `ca66782` is
`(s generation msgid payload groups obligation-id subject evidence charge)`;
the leading `cfg-gen` is reconfiguration packet R2's addition and this design
depends on it, §7.) The w4/post lane's injecting-agent step (Injection-Date,
Injection-Info, generated Message-ID, RFC 5537 §3.5) is **not** called here:
a relaying agent MUST NOT add or alter Injection-Date (§3.6: nothing but Path
and Xref), and fn stores the received bytes exactly. What POST and transit
share is everything from `fn-node-prepare` down.

Responses, exactly per RFC, as a function of `(command, decision, outcome)`:

| Command | `:want` | `:have` | `:defer` | `:refuse` |
| --- | --- | --- | --- | --- |
| `IHAVE` (offer) | `335 send it` | `435 duplicate` | `436 retry later` | `435 not wanted` |
| `CHECK` | `238 <msgid>` | `438 <msgid>` | `431 <msgid>` | `438 <msgid>` |

| Command | accepted (durable) | refused (`:refuse` or `:have`) | deferred at transfer | uncertain (indeterminate commit) |
| --- | --- | --- | --- | --- |
| `IHAVE` (after article) | `235` | `437` | `436` | `436` then `fn-wire-close`: no further command is served on a fenced node |
| `TAKETHIS` | `239 <msgid>` | `439 <msgid>` | `436 <msgid>` (local policy, K1: see status) | `436 <msgid>` then close |

Three outcomes stay distinct all the way out (assurance rule D13): `accepted`
is only ever answered after the store's `:durable` completion (never on
`fn-node-prepare` alone: `fn-node-prepare-does-not-publish-or-commit-retention`,
`books/node.lisp:548`); `refused` is a `4x7`/`4x9`/`4x5`/`4x8` with the
typed reason in the text; `uncertain` never produces a `2xx` or a
do-not-retry `4xx`. RFC 4644 gives TAKETHIS no retry-later code; the lack of
a response is what a client MUST treat as retry-later (RFC 3977 §6.3.2.2 says
so for IHAVE and `innfeed` requeues on connection loss), so closing is the
only RFC-honest signal for a deferral after the bytes arrived. An IHAVE peer
waiting on `335` gets `436` on uncertainty because that code exists.

The pipelining rule: `IHAVE` MUST NOT be pipelined (RFC 3977 §6.3.2.1) and
`CHECK`/`TAKETHIS` MAY be. fn serves both through the same `fn-wire-drive`
fold, so pipelined CHECKs are answered in order with no state (each `238`
increments `inflight`, each `TAKETHIS` decrements it); an `IHAVE` while
`transfer` is non-nil is `501`, which is the RFC's "MUST NOT" enforced.

### 2.3 Path: prepending, the loop check, no rewriting of the source

D01 fixes that mutable Path/Xref live in a separate projection from the
signed source bytes. RFC 5537 §3.6.7 requires the relaying agent to update
Path. These compose as: the stored payload is the received octets exactly;
the Path update is *rendered* when the article leaves (§3.2), from the
provenance record and the node's own identity, deterministically. The
inbound side stores the diagnostic it would have prepended:

```lisp
;; books/path.lisp (K1): a bounded parser for RFC 5537 §3.2 / RFC 5536 §3.1.6 Path content.
;; path-identity = 1*( alnum / "-" / "_" / "." ) with no leading/trailing "."; separators "!";
;; diagnostics ".POSTED", ".SEEN.", ".MISMATCH." after a "!"; the tail-entry is the rightmost.
(defun fn-path-identityp (octets) ...)
(defun fn-path-parse (octets fuel) ...)          ; (:ok entries) | (:error why); entries left to right
;; The loop test of §3.6: identity appears as a <path-identity>, excluding the
;; tail-entry and anything to the right of a "POSTED" diag-keyword.
(defun fn-path-names-p (path-octets identity) ...)

;; §3.2.1 step 3, decided from the connection's peer record, never from the article:
(defun fn-path-diagnostic (peer-record path-octets)
  (cond ((null peer-record) (list :seen))                                          ; "!.SEEN.<addr>"
        ((equal (fn-path-leftmost path-octets) (fn-cfg-peer-path-identity peer-record)) (list :match))   ; "!!"
        (t (list :mismatch (fn-cfg-peer-path-identity peer-record)))))             ; "!.MISMATCH.<id>"

;; The outbound rendering (§3.2): the article as offered to a peer.
;; render = source with the Path header's content replaced by
;;   <our identity> "!" <diag> "!" <original content>
;; and any Xref header removed (§3.7.7); every other octet identical.
(defun fn-peer-render-outbound (source provenance identity) ...)
```

Provenance is a record, not a header. As built (w10/provenance) it is
`(fn-prov-make-transit peer kind diagnostic generation)`, and its WIRE form
--- a printable string `fn-prov-of-wire` inverts --- is the `evidence`
argument of `fn-node-prepare`, so it is inside the stored transaction record,
replayed, and `fn-node-stage-evidence` carries it while staged with no change
to the record grammar. An article accepted through POST has
`(fn-prov-make-post principal generation)`; the outbound renderer treats both
the same way, reading them with `fn-prov-of-wire` and `fn-prov-kind`. `Injection-Date`
is never touched by transit; `Xref` is never stored.

### 2.4 The record

No new journal record kind for inbound transit. The article record of
`books/records.lisp` already carries `evidence`; a transit article is an
article record whose evidence is a `:peer-transit` provenance. Replay
reproduces the provenance for free, and `fn-replay-reproduces-acceptance-
binding` (reconfiguration §3.3) covers it unchanged. What is new is one
*value* in the evidence slot, and NO change to `fn-record-p`'s evidence
recognizer was needed: the wire form of a provenance is bounded printable
text, which is exactly what `fn-record-metadata-bytes-p` already admits.

### 2.5 Duplicate suppression: the history is the store plus its tombstones

RFC 5537 §3.3 requires a record of every article seen; §3.6.3/§3.7.3 require
rejecting an already-accepted article. D13's selected interim is "preserve
duplicate history". fn requires, more strongly than the RFC's date-cutoff
optimisation: **no cutoff and no pruning until D13 lands a proved pruning
rule**, so the history is exact and `:date-cutoff` is a reserved reason that
no branch emits yet (marked `unreachable-in-composition` until D13).

```lisp
;; The history of a node: every Message-ID that has ever completed durably.
;; fn-node-bindings is consed on every :durable completion (books/node.lisp:441)
;; and never popped by release (fn-retain-release removes the pin, not the
;; binding: fn-node-complete-preserves-existing-binding, fn-bprl-release-preserves-node-state).
;; The article set is the subset still retained.
(defun fn-peer-history-hasp (msgid node)
  (or (fn-acceptedp msgid (fn-state-articles (fn-node-acceptance node)))          ; books/acceptance.lisp:139
      (consp (fn-node-find-binding msgid (fn-node-bindings node)))))              ; books/node.lisp:260

(defun fn-peer-stagedp (msgid node)
  (and (consp (fn-node-stage node)) (equal (fn-node-stage-msgid (fn-node-stage node)) msgid)))
```

Bindings are the tombstones. This is why the design needs no separate
"history file": an article released from its archive pin keeps its binding,
and a reimport of the same Message-ID is `:have` forever. Cost: both
membership tests are linear in the store. `fn-acceptedp` is a lookup, not a
recognizer, so the served-path rule is not violated; but a CHECK storm at
`O(A)` each is the cost node-functionality §3.2 must quote, and packet K5
carries a history index twin (`fn-nntp-index-` style, `books/nntp-index.lisp`)
with the equality theorem `fn-peer-history-index-agrees-with-history`.

## 3. The outbound feed machine

### 3.1 State

One feed state per configured outbound peer, all inside F_node's state as a
new field `feeds` (an alist by peer name). Each entry is durable through the
feed journal (§3.3) and carries no article bytes: the queue holds Message-IDs
and the article is rendered from the store when offered.

```lisp
;; books/feed.lisp (K2)
(defun fn-feed-entry (msgid state attempts last-tick) (list msgid state attempts last-tick))
;; state: :queued | (:offered attempt) | (:sent attempt) | :done | (:dropped reason)
(defun fn-feed-make (peer queue contact backoff-until conn next-attempt)
  (list peer queue contact backoff-until conn next-attempt))
(defun fn-feed-peer          (f) (car f))
(defun fn-feed-queue         (f) (cadr f))          ; fn-feed-entry list, FIFO, no duplicate msgids
(defun fn-feed-contact       (f) (caddr f))         ; nil or fn-sched-contact (books/scheduler.lisp:54, w3/scheduler)
(defun fn-feed-backoff-until (f) (cadddr f))        ; monotonic ms, natp
(defun fn-feed-conn          (f) (car (cddddr f)))  ; nil or (id wire) : the outbound connection and its response framer
(defun fn-feed-next-attempt  (f) (cadr (cddddr f))) ; natp, monotone; attempt ids are (peer . n)

(defun fn-feedp (f) ...)          ; shapes; queue length <= fn-cfg-peer-max-queue; msgids distinct;
                                  ; at most one entry in (:offered _) or (:sent _) per peer (one in flight per
                                  ; connection for IHAVE; up to inflight-window for streaming)
```

TCP peers are always-on contacts: the host opens `(fn-sched-contact peer 0 *fn-feed-horizon*)`
when the peer record is live and re-opens it after every `:feed-close`;
`fn-sched-contact-holdsp contact obs` is then the question "is a connection
up". A BP peer's contact is its contact plan window, as in the scheduler.
The `:tick` event is the scheduler's tick for that peer; `fn-feed-tick-step`
has the select/drive/take shape of `fn-sched-tick-step`
(`fn-sched-tick-step-is-select-drive-take` is the equation on the BP side;
K2 states the same equation for the feed side against the three host calls).

### 3.2 Transitions

```lisp
;; Enqueue: on every durable completion at this node, for every outbound peer
;; in scope, unless the loop check or provenance forbids it.
(defun fn-feed-offerablep (article provenance peer-record identity)
  (and (fn-cfg-peer-outbound peer-record)
       (fn-wildmat-any-matchp (fn-cfg-peer-outbound-groups peer-record) (fn-article-groups article))
       ;; §3.6: never relay to a peer whose path-identity is already in Path
       (not (fn-path-names-p (fn-af-path-field-value (fn-article-parse (fn-article-payload article)))
                             (fn-cfg-peer-path-identity peer-record)))
       ;; and never back to the peer it came from (provenance, stronger than the RFC)
       (not (equal (fn-peer-provenance-peer provenance) (fn-cfg-peer-name peer-record)))))

(defun fn-feed-enqueue (f msgid tick)            ; refused (f unchanged) when full or already present
  (if (or (fn-feed-find msgid (fn-feed-queue f))
          (>= (len (fn-feed-queue f)) (fn-cfg-peer-max-queue (fn-feed-record f))))
      f
    (fn-feed-with-queue f (append (fn-feed-queue f) (list (fn-feed-entry msgid :queued 0 tick))))))

;; Select: the head :queued entry, when the contact holds, the connection is up,
;; backoff has elapsed and no entry is in flight (IHAVE) or the window has room (streaming).
(defun fn-feed-selection (f obs) ...)             ; msgid or nil

;; Drive: the offer.  Durable first (the journal record), then the effect.
;; The effect is one command line; for a streaming peer with a prior 238 it is
;; TAKETHIS plus the rendered article block.
(defun fn-feed-offer (f msgid attempt streamingp)
  (mv (fn-feed-set-state f msgid (list :offered attempt))
      (list (list :command (fn-feed-conn-id f)
                  (if streamingp (fn-feed-check-line msgid) (fn-feed-ihave-line msgid))))))

;; Observe: one parsed response line from the peer (through the peer-response
;; framer, a small fn-wire twin that yields (:response code msgid-or-nil)).
(defun fn-feed-observe (f response obs)
  (let ((code (fn-feed-response-code response)) (msgid (fn-feed-response-msgid response)))
    (case code
      ((335 238) (fn-feed-send f msgid))                          ; -> (:sent attempt) and the article effect
      ((235 239) (fn-feed-done f msgid :accepted))               ; -> :done
      ((435 438) (fn-feed-done f msgid :peer-has))               ; -> :done; the peer's duplicate suppression
      ((437 439) (fn-feed-done f msgid :peer-refused))           ; -> :done; do not retry (RFC), the reason journaled
      ((431 436) (fn-feed-backoff f msgid obs))                  ; -> :queued again, attempts+1, backoff-until = now + backoff * 2^attempts
      (400       (fn-feed-lost f obs))                           ; connection closing: every in-flight entry -> :queued (retry)
      (otherwise (fn-feed-lost f obs)))))                        ; any other code: treat as loss (RFC 3977 §6.3.2.2)

;; Loss of the connection: every (:offered _) or (:sent _) entry returns to
;; :queued with attempts+1 and backoff; nothing is dropped.
(defun fn-feed-close (f obs) ...)
;; Give up: after retry-bound backoffs an entry becomes (:dropped :retry-bound);
;; the record stays in the journal (an operator can re-feed).
```

`235`/`239` and `435`/`438` both end the entry as `:done` because both mean
the peer has the article; RFC 5537 §3.3 makes the peer's `438` its history
answer, and that is what lets a restart resolve an unknown outcome by asking
again (§3.3). Backoff on `431`/`436` is exponential with the peer record's
base and capped at the retry bound; a `:dropped` entry is never re-offered
automatically and is reported as refused by the CLI.

### 3.3 The feed journal: a record kind

Proposed frame family `FNFD` (schema 1), one file per peer under
`<journal>/feed/<peer>/`, written with the frame grammar of `books/frame`
(magic, version, kind, bounded length, payload, A-CRYPTO trailer) and
replayed by `fn-feed-replay`. Records, with the discipline "durable before
the effect it authorizes" (bp-workflow-host, scheduler.md):

| Record | Fields | Written |
| --- | --- | --- |
| `(:feed-enqueue peer msgid tick)` | text, text, nat | before the entry is `:queued` |
| `(:feed-offer peer msgid attempt tick)` | text, text, nat, nat | before the `:command` effect for CHECK/IHAVE |
| `(:feed-sent peer msgid attempt)` | | before the TAKETHIS/article effect |
| `(:feed-outcome peer msgid attempt code)` | code in `{235 239 435 438 437 439 431 436 400}` | after the response is parsed, before the next selection |
| `(:feed-drop peer msgid reason)` | | when the retry bound is reached or the peer is removed |
| `(:feed-restart peer)` | | on open, before any offer; fences the in-flight entries |

Replay: `fn-feed-replay records` folds them into an `fn-feedp`. An entry with
`(:feed-offer ...)` or `(:feed-sent ...)` and no `(:feed-outcome ...)` for its
attempt is *unresolved*; `fn-feed-restart` marks it `:queued` with the
attempt retired, and the next offer of it is a `CHECK`/`IHAVE` (never a
blind TAKETHIS), whose `438`/`435` is the peer's own history saying "you
already sent it". This is the two-generals-honest form of exactly-once:
the *decision* to transfer is journaled once per attempt, the peer's history
absorbs the one retransmission a lost reply can cause, and no attempt is ever
re-run under its old id. The BP side has exactly this shape
(`fn-bp-restart` fences a pending intent, `fn-bp-recover` resolves it).

## 4. Keystone theorem statements

Each is a proposed statement; teeth are named per hypothesis. Hypotheses
below are the carried invariants `fn-ideal-statep` (node-functionality §1.1
extended with `feeds`) or the subsystem recognizers, never a negated branch
test. No witness may use a node with one group or an empty queue.

### K1. Peering refines acceptance

The node a transit transfer produces is the node the post path produces on
the arguments ACL2 computes from the same octets, and a transfer the
acceptance path refuses is a typed refusal with the node unchanged.

```lisp
(defthm fn-peer-transfer-is-the-post-path
  (implies (and (fn-node-statep node) (fn-cfgp cfg)
                (equal (fn-peer-decision-kind (fn-peer-decide-transfer node cfg peer msgid octets clock)) :want))
           (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock))
                  (let ((a (fn-peer-injection-arguments node cfg peer msgid octets)))
                    (fn-node-prepare node (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                                     (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a) (nth 8 a))))))

(defthm fn-peer-refused-transfer-leaves-the-node
  (implies (and (fn-node-statep node)
                (not (equal (fn-peer-decision-kind (fn-peer-decide-transfer node cfg peer msgid octets clock)) :want)))
           (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock)) node)))

;; The content: nothing the acceptance machine would refuse gets in through
;; peering.  Stated positively over the reachable outcome, not the branch:
(defthm fn-peer-accepted-article-is-acceptance-accepted
  (implies (and (fn-node-statep node) (fn-cfgp cfg)
                (member-equal article
                              (fn-state-articles (fn-node-acceptance
                                (fn-node-complete (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock))
                                                  txid gen :durable))))
                (not (member-equal article (fn-state-articles (fn-node-acceptance node)))))
           (and (equal (fn-article-payload article) octets)                      ; exact bytes, D01
                (fn-selection-validp (fn-article-groups article) (fn-state-groups (fn-node-acceptance node)))
                (not (fn-acceptedp (fn-article-msgid article) (fn-state-articles (fn-node-acceptance node))))
                (fn-retain-admissiblep (fn-node-retention node)
                                       (fn-id-obligation-of (fn-article-msgid article) (fn-id-subject-of-payload octets))
                                       (fn-id-subject-of-payload octets) :archive
                                       (fn-peer-evidence peer cfg) (fn-charge-for-payload (len octets))))))
```

The second is `-by-definition` shaped and is named for what it is; the first
and third are the keystones. Teeth for K1: a transit article whose
Newsgroups has one in-scope and one unknown group is accepted with exactly
the in-scope membership (witness, non-degenerate: two groups, one
membership); drop `fn-node-statep` (a node whose articles list already holds
the msgid without a binding: the transfer must not be `:want` yet the
must-fail shows the theorem needs the recognizer); drop `fn-cfgp` (a config
whose peer has `accept-groups` naming a retired group); a separating witness
for the third with the same octets offered through POST and through transit
whose resulting `fn-state-articles` entries are `equal` except for evidence.

### K2. Loop freedom

An article whose Path already names this node is never accepted through
transit and never offered to a peer whose identity it names.

```lisp
(defthm fn-peer-loop-is-refused
  (implies (and (fn-node-statep node) (fn-cfgp cfg)
                (fn-article-result-okp (fn-article-parse octets))
                (fn-path-names-p (fn-af-path-field-value (fn-article-result-article (fn-article-parse octets)))
                                 (fn-cfg-policy (fn-cfg-value cfg) :path-identity)))
           (and (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock)) node)
                (member-equal (fn-peer-decision-kind (fn-peer-decide-transfer node cfg peer msgid octets clock))
                              '(:refuse :have)))))

(defthm fn-feed-never-offers-a-loop
  (implies (and (fn-ideal-statep s)
                (member-equal (list :command id octets) (mv-nth 1 (fn-ideal-run s events)))
                (fn-feed-command-offersp octets msgid)                               ; CHECK/IHAVE/TAKETHIS <msgid>
                (equal (fn-feed-conn-peer s id) peer))
           (not (fn-path-names-p (fn-af-path-field-value (fn-peer-stored-article s msgid))
                                 (fn-cfg-peer-path-identity (fn-cfg-peer-find peer (fn-cfg-peers (fn-ideal-config-value s))))))))

;; Rendering is the only Path change and it is a prepend: the loop check is
;; monotone, so a node that refuses a Path refuses every Path we could render from it.
(defthm fn-peer-render-prepends-path
  (implies (fn-article-result-okp (fn-article-parse source))
           (equal (fn-af-path-field-value (fn-article-parse (fn-peer-render-outbound source prov identity)))
                  (append identity (list 33) (fn-path-diag-octets prov) (list 33)
                          (fn-af-path-field-value (fn-article-parse source))))))
```

Teeth: witness with our identity as the *second* entry of a three-entry Path
(not the tail, not after `.POSTED`); drop the parse hypothesis (unparseable
octets are refused as `:proto-article`, which is not the loop reason: the
must-fail separates reasons, not just kinds); a Path naming our identity only
in the tail-entry is *accepted* (RFC 5537 §3.6's exclusion, as a witness
that `fn-path-names-p` is not substring search); a `.POSTED` diagnostic
followed by our identity is accepted.

### K3. Merge: two fn nodes peering both ways converge

Over the fact-set model of REP-002 (`fn-exchange-merge`,
`books/exchange.lisp:327`) and the lace merge (`fn-lace-merge`,
`books/lace.lisp:105`). `fn-peer-facts` projects a node's committed articles
to exchange facts `(schema kind message-id content-id origin incarnation sequence provenance)`
with `content-id` the payload digest (`fn-id-subject-of-payload`) and
provenance the evidence; `fn-sys-run` is node-functionality §5.4's composed
system with two nodes and an NNTP channel in place of `fn-dtn`.

```lisp
;; A complete exchange: every article accepted at either node before the run
;; is, during the run, offered to the other and answered 235/239 or 435/438.
(defun fn-peer-complete-exchangep (sys a b events) ...)

(defthm fn-peer-bidirectional-exchange-converges
  (implies (and (fn-sys-invariantp sys)
                (fn-peer-symmetric-scopep sys a b)              ; equal accept/feed wildmats both ways, same live groups
                (fn-peer-same-validation-profilep sys a b)      ; same fn-exchange-policyp: schemas and authorizations
                (fn-peer-capacity-sufficesp sys a b)            ; each side can admit the other's set
                (fn-peer-complete-exchangep sys a b events))
           (let ((final (fn-sys-run sys events)))
             (and (fn-exchange-set-equiv (fn-peer-facts (fn-sys-node a final))
                                         (fn-exchange-merge (fn-peer-facts (fn-sys-node b sys))
                                                            (fn-peer-facts (fn-sys-node a sys))))
                  (fn-exchange-set-equiv (fn-peer-facts (fn-sys-node b final))
                                         (fn-exchange-merge (fn-peer-facts (fn-sys-node a sys))
                                                            (fn-peer-facts (fn-sys-node b sys))))
                  (fn-exchange-set-equiv (fn-peer-facts (fn-sys-node a final))
                                         (fn-peer-facts (fn-sys-node b final)))))))
```

The third conjunct is `fn-exchange-merge-commutative-member`
(`books/exchange.lisp:392`) applied to the first two; the first two are the
content. Local numbers, Xref and rendered Path are outside `fn-peer-facts`,
which is exactly REP-002's "modulo local numbering". The statement-level
twin, for articles carrying `FN-Statement` (§6), replaces `fn-peer-facts`
by `fn-peer-lace` and `fn-exchange-set-equiv` by `fn-lace-same-idsp`, and
its third conjunct is `fn-lace-merge-commutative-ids`; equivocations survive
by `fn-lace-merge-preserves-equivocation`.

Teeth: witness with three articles at A, two at B, one shared, run in an
interleaving where B's offer of the shared article is answered `438` (the
witness must exercise `:have`, not only `:want`); drop symmetric scope (A
feeds `fn.*`, B accepts `fn.letters` only: the sets differ by one fact);
drop completeness (one `431` never retried); drop capacity (B admits two of
three, the third is `:refuse :capacity` and the theorem fails at B). The
must-fail for the profile hypothesis needs a fact of a schema one side does
not know.

### K4. Duplicate suppression is complete, across restart

```lisp
(defthm fn-peer-accepted-once-is-have-thereafter
  (implies (and (fn-ideal-statep s)
                (fn-peer-history-hasp msgid (fn-ideal-node s)))
           (and (fn-peer-history-hasp msgid (fn-ideal-node (mv-nth 0 (fn-ideal-run s events))))   ; history only grows
                (equal (fn-peer-decision-kind
                        (fn-peer-decide-offer (fn-ideal-node (mv-nth 0 (fn-ideal-run s events)))
                                              (fn-ideal-config s) peer session msgid clock n))
                       :have))))

;; Restart: the history is a function of the durable records, so a crash image
;; that keeps an acknowledged completion keeps the tombstone.
(defthm fn-peer-history-survives-reopen
  (implies (and (fn-snt-relation store)
                (fn-peer-history-hasp msgid (fn-sn-node store))
                (fn-sn-acknowledged-msgidp msgid store)                          ; its completion was acknowledged
                (fn-sf-crash-imagep (fn-sn-files store) frontier records)
                (fn-sn-open-okp (fn-sn-open-observed frontier records)))
           (fn-peer-history-hasp msgid (fn-sn-node (fn-sn-open-state (fn-sn-open-observed frontier records))))))
```

`fn-peer-history-hasp` is monotone because `fn-node-bindings` is only consed
(`fn-node-prepare-preserves-bindings`, `fn-node-complete-preserves-existing-binding`,
`fn-node-recover-preserves-existing-binding`, `books/node-invariants.lisp`)
and a release keeps it (`fn-bprl-release-preserves-node-state`). The
restart half is `fn-snt-acknowledged-history-retained-through-mixed-trace`
(`books/store-node-traces.lisp:484`) plus the replay of bindings. Teeth: a
witness whose article was *released* (pin gone, binding kept) and is still
`:have`; drop the acknowledgement hypothesis (a completion in the lost tail
is permitted to vanish, STO-004, and then the offer is `:want`: this is a
must-fail that separates "acknowledged" from "written"); drop
`fn-sf-crash-imagep` (a fabricated image with the binding record removed).

### K5. Feed exactly-once per peer under restart

```lisp
;; At most one accepted transfer decision per (peer, msgid) is ever journaled,
;; and no TAKETHIS is emitted for an entry that is :done.
(defthm fn-feed-at-most-one-accepted-outcome
  (implies (fn-feed-journal-okp records)
           (<= (fn-feed-count-outcomes peer msgid '(235 239) records) 1)))

(defthm fn-feed-done-is-never-reoffered
  (implies (and (fn-ideal-statep s)
                (equal (fn-feed-entry-state (fn-feed-find msgid (fn-feed-queue (fn-ideal-feed s peer)))) :done)
                (member-equal (list :command id octets) (mv-nth 1 (fn-ideal-run s events)))
                (equal (fn-feed-conn-peer s id) peer))
           (not (fn-feed-command-offersp octets msgid))))

;; Crash then replay: the live feed and the replayed journal agree on every
;; entry except the in-flight ones, which replay returns to :queued.
(defthm fn-feed-replay-is-the-live-feed-modulo-inflight
  (implies (and (fn-ideal-statep s)
                (fn-feed-journal-imagep (fn-ideal-feed-journal s peer) records))     ; a crash image of the feed file
           (equal (fn-feed-settle (fn-feed-replay records))
                  (fn-feed-settle (fn-ideal-feed s peer)))))

;; After a restart, the first command for a formerly in-flight entry is an offer, never TAKETHIS.
(defthm fn-feed-restart-resolves-by-offer
  (implies (and (fn-ideal-statep s)
                (fn-feed-inflightp msgid (fn-ideal-feed s peer))
                (member-equal (list :command id octets)
                              (mv-nth 1 (fn-ideal-run (fn-ideal-restart s) events)))
                (fn-feed-first-command-for-p msgid id octets events))
           (or (fn-feed-check-linep octets msgid) (fn-feed-ihave-linep octets msgid))))
```

`fn-feed-settle` maps `(:offered _)`/`(:sent _)` to `:queued` and forgets
attempt ids; it is the relation, not a re-implementation. Teeth: witness of
five queued articles, a crash after the third `(:feed-sent ...)` with no
outcome, replay, and the fourth command emitted is a `CHECK` of the third
msgid (non-degenerate: something was in flight); drop `fn-feed-journal-okp`
(two `(:feed-outcome ... 239)` for one attempt, fabricated); drop the image
hypothesis (a record list with an outcome for an attempt never offered); a
separating witness for `fn-feed-done-is-never-reoffered` that is `:done` by
`438` rather than `239`.

**What is earned, and by which theorem** (lane `w6/peering-feed-4`,
`books/peer-feed-invariants`; the per-root evidence and the exact hypothesis
of each is in the outbound-feed status section at the end of this file).
All FIVE keystones of that book are proved; of the four design statements
above, three are earned with the subject substitution named and one is not:

| Statement above | Earned by | Reading |
| --- | --- | --- |
| `fn-feed-at-most-one-accepted-outcome` | the theorem of that name | **Earned.** Same name, same content. The hypothesis is `fn-feed-drivenp` -- each record admissible in the state the fold had reached -- in place of the design's `fn-feed-journal-okp`, and it is a check over the fold, never the conclusion. |
| `fn-feed-done-is-never-reoffered` | `fn-feed-done-is-never-selected` with `fn-feed-tick-step-offers-the-selection` and `fn-feed-tick-step-is-silent-without-a-selection` | **Earned over `fn-feed-tick-step`**, the function the host calls once per scheduler tick, not over `fn-ideal-run`, which does not carry the feed. `fn-feed-done-is-never-selected` carries `(fn-feed-selection f obs)` as a hypothesis: without it the statement is FALSE at `msgid` = `NIL` (a feed that selects nothing selects `NIL`, and `NIL` is not `:queued`), and the silent-without-a-selection theorem is the other half of the pair. |
| `fn-feed-replay-is-the-live-feed-modulo-inflight` | `fn-feed-replay-is-the-fold`, `fn-feed-replay-preserves-feedp`, `fn-feed-replay-preserves-peer` and the ground crash scenario | **Not earned.** All three replay theorems are proved and the general equation is still open. The live machine that emits its own journal now EXISTS -- `w11/feed-k5` closed the missing `(:feed-enqueue …)` record, and gate `2c27ef6` killed a sender with `kill -9`, replayed eleven records and re-offered by `CHECK` -- but one run of one crash point is a witness, not the equation, and no theorem in this tree relates that journal to that feed. |
| `fn-feed-restart-resolves-by-offer` | `fn-feed-restart-emits-no-transfer` with `fn-feed-restart-then-tick-offers` | **Earned over `fn-feed-send`** -- the only producer of a TAKETHIS or an article block -- **and `fn-feed-tick-step`**, not over `fn-ideal-restart`. Read the first one narrowly: `fn-feed-restart` also forgets the connection and `fn-feed-send` refuses a feed whose `fn-feed-conn` is not a `natp`, so the settled queue is not what it rests on. The statement that would need the settled queue is the one over the REOPENED feed, which is what the host does next; it is recorded open in the lane handoff. |

The fifth keystone of the book has no row above because §4 does not state it:
`fn-feed-drop-needs-a-drop-record`, "nothing leaves the queue without a drop
record naming a reason", which is §3.2's give-up rule. It is proved, with
`fn-feed-not-dropped-survives-a-non-drop-record` under it.

### K6. Every peer input is on the served path

The robustness theorems of node-functionality §3 are restated over the
extended event kinds with no new hypothesis. They are not new theorems; they
are the same five with `e` now ranging over `:feed-octets`, `:tick` and peer
`:open`s. Packet K1 must keep them certifying, and the cost bound gains one
term:

```lisp
(defthm fn-ideal-serve-is-total-and-typed                       ; unchanged statement, larger e
  (and (implies (fn-ideal-statep s) (fn-ideal-statep (mv-nth 0 (fn-ideal-serve s e))))
       (fn-ideal-effect-listp (mv-nth 1 (fn-ideal-serve s e)))))

(defun fn-ideal-cost-bound (config n)
  (* *fn-ideal-cost-k*
     (+ 1 n (fn-ideal-config-line-limit config) (fn-ideal-config-body-limit config)
        (len (fn-ideal-config-groups config)) (fn-ideal-config-capacity config)
        (fn-cfg-max-queue-total config))))                      ; the feed queues, bounded by configuration

(defthm fn-peer-refusal-is-typed
  (implies (member-equal (list :refused r) (mv-nth 1 (fn-ideal-serve s e)))
           (member-equal r (append *fn-ideal-refusals* *fn-peer-reasons*))))
```

The proof burden per event: `:feed-octets` is `fn-wire-drive` on the
response framer then `fn-feed-observe` per parsed line (linear); `:tick` is
one selection over a queue bounded by `max-queue` and one render bounded by
the article's payload length; a peer `:octets` is the existing wire/NNTP
path plus `fn-peer-decide-*`, whose only non-constant term is the history
lookup, `O(A)` today and `O(log A)` after K5's index. Refusals are typed
because `*fn-peer-reasons*` is closed and every `cond` arm returns from it.

### K7. Peer reconfiguration changes decisions, not committed state

```lisp
(defthm fn-cfg-peer-delta-preserves-the-node-and-changes-only-decisions
  (implies (and (fn-node-statep node) (fn-cfg-recordp record)
                (fn-cfg-peer-only-deltasp (fn-cfg-record-change record)))
           (let ((next (fn-node-apply-config node record)))
             (and (equal (fn-node-acceptance next) (fn-node-acceptance node))
                  (equal (fn-node-retention next) (fn-node-retention node))
                  (equal (fn-node-bindings next) (fn-node-bindings node))
                  (equal (fn-peer-history-hasp msgid next) (fn-peer-history-hasp msgid node))))))
```

Tooth: a witness where `(:set-peer ...)` narrows `accept-groups` and the
same offer flips from `:want` to `:refuse :out-of-scope` while
`fn-state-articles` is `equal` before and after; drop
`fn-cfg-peer-only-deltasp` with a `(:create-group ...)` in the list.

## 5. INN interop plan

Location on hbox: `/tank/fn/inn`. Every build and test there runs under
`swarm-build`; INN is small but `make test` is not free, and hbox is
co-tenant.

**Build and pin.** Clone `https://github.com/InterNetNews/inn`, check out
the newest `2.7.x` tag (2.7.2 or later as of this design; the lane records
the tag, its commit sha, and the sha256 of the release tarball if a tarball
is used instead, in `tests/inn/pin.json`, and never writes "2.7" without the
patch level). Configure with `--prefix=/tank/fn/inn/inn-2.7 --with-news-user=$USER --with-news-group=$(id -gn) --with-news-master=$USER --with-openssl=no`;
`make && make install` (no root: the news user is the lane's user). Set
`inn.conf`: `pathhost: inn.hbox.test`, `port: 1119`, `bindaddress: 127.0.0.1`,
`server: 127.0.0.1`; create the groups `fn.letters`, `fn.test`, `fn.dtn` with
`ctlinnd newgroup`; `makehistory -O` and `makedbz -i` for an empty history;
`rc.news` to start `innd`; `inncheck` clean.

**INN as fn's peer, both directions.**

- `incoming.conf` (INN accepts fn as a feeder): `peer fnA { hostname: 127.0.0.1; identity: fnA; patterns: fn.*; streaming: true; max-connections: 2 }`.
  fn's outbound peer record: `(:set-peer ("innA" "inn.hbox.test" (:nntp "127.0.0.1" 1119) nil ("fn.*" t 256 1000) (:source-address "127.0.0.1")))`.
- `newsfeeds` (INN feeds fn): `fnA:fn.*:Tf,Wnm:fnA` and `innfeed.conf`: `peer fnA { ip-name: 127.0.0.1; port: <fn port>; streaming: true; max-connections: 1 }`;
  `innfeed` started by `innd` (`innfeed!:...:Tc,Wnm*:...innfeed` in `newsfeeds`).
  fn's inbound peer record: `(:set-peer ("innA" "inn.hbox.test" (:nntp "127.0.0.1" 1119) ("fn.*" 65536 16) nil (:source-address "127.0.0.1")))`
  (one record carries both halves when both directions are wanted; two are
  shown to keep the two scenarios' configuration minimal).
- fn's own identity: `(:set-policy :path-identity "fnA.hbox.test")`.
- `nnrpd` is INN's reader daemon and is not on the peering path; it is used
  only to read back what INN stored (`ARTICLE <msgid>` on port 1119 from a
  non-peer address, or `sm` on the spool).

**Scenarios.** Each is a transcript test with the exact response lines
expected, an fn journal digest before and after, and INN's `news.notice` and
`history` lines quoted.

| # | Direction | Exercises | Expected |
| --- | --- | --- | --- |
| S1 | fn → INN, `streaming nil` | `IHAVE` → `335` → article → `235` | one `history` line; `fn-feed` entry `:done` by `235` |
| S2 | fn → INN, streaming | `CHECK`/`238`/`TAKETHIS`/`239`, pipelined ×8 | eight `239`s in order; eight `:done` |
| S3 | INN → fn | `innfeed` `CHECK`/`TAKETHIS` | `238` then `239`; the article is served by fn's reader by Message-ID with the *received* bytes; the evidence slot is `(:peer-transit "innA" (:match) g)` |
| S4 | both | duplicate: S2's articles re-offered by a forced backlog replay (`innfeed -y` / re-enqueue in fn) | INN: `438`; fn: `438` at CHECK and, with a client that ignores it, `439` at TAKETHIS (RFC 4644 §2.4.2 advisory rule exercised) |
| S5 | INN → fn | policy refusal: article in `alt.test` only | `438 <msgid>` at CHECK (`:out-of-scope`); forced `TAKETHIS` → `439`; IHAVE variant: `435` |
| S6 | INN → fn | `437`: article with neither `Injection-Date` nor `Date` via `IHAVE` | `335` then `437` (`:no-date`); the node unchanged, journal digest equal |
| S7 | fn → INN | loop, outbound: an article received from INN (Path contains `inn.hbox.test`) | never offered back: no CHECK for it in `innfeed`'s log, and `fn-feed-never-offers-a-loop`'s witness is this transcript |
| S8 | INN → fn | loop, inbound: an article whose Path names `fnA.hbox.test` in the middle, injected at INN with a hand-built Path | `438` (`:loop`); the tail-entry variant is accepted |
| S9 | both | `431`/`436` and backoff: `ctlinnd throttle` during S2 and, reversed, a `reconfigure (:set-capacity r)` at fn's current reservation during S3 | fn backs off with the journaled `431` and resumes after `ctlinnd go`; INN's `innfeed` requeues on fn's `431` and delivers after capacity is raised |
| S10 | fn → INN | restart mid-feed: `SIGKILL` fn after the `(:feed-sent ...)` of article 3 of 5, before its `239` | after restart, the first command for article 3 is `CHECK`, answered `438`; INN's `history` has each of the five exactly once; the feed journal has exactly one `235/239` outcome per msgid |
| S11 | INN → fn | restart mid-transfer: `SIGKILL` fn between the store's record write and the `239` | `innfeed` requeues; on restart fn recovers (`fn-node-recover`) and the re-offer is `438` if the record was durable, `238` then `239` if not; never two copies |

**Evidence record** (`tests/evidence/<date>-inn-peering.md`): the INN tag
and commit sha, configure line, `inncheck` output; hbox kernel and fn
revision; the four INN configuration files and fn's configuration record
history verbatim; per scenario the transcript, the `news.notice` and
`history` lines, the fn journal digests before/after and the feed journal
listing; the exact `kill` timing for S10/S11 as the record index at which the
signal was sent; what was *not* shown (no TLS, no AUTHINFO, no
Distribution, no control messages, single host, loopback only).

## 6. The inter-agent angle

Agents are principals ([identity](identity.md), `fn-prin-`): a 32-octet id
from a public key and a token. An agent's post is a statement
([statement](statement.md)) of kind `:article` whose payload is the exact
authored source bytes (D01), signed under the principal's key, admitted under
the group's policy in force (`fn-pol-admitp`, [policy](policy.md)). Peering
carries such an article unchanged because a relaying agent may touch only
Path and Xref, and fn stores exactly the received bytes: the signature over
the source therefore verifies at every hop, through INN included.

Reserved now, so that later needs no format break:

- **Header field `FN-Statement`** (RFC 5536 §3.1 syntax; RFC 5537 §3.6
  forbids peers altering it): the base64 of `fn-stmt-encode` of the
  statement header and signature *without* the payload, whose `ref` is
  `fn-digest-tagged "fn-payload-v1"` of the authored source bytes. The
  authored source is the article minus every header the injecting agent
  added (Path, Injection-Date, Injection-Info, Xref, FN-Statement itself);
  the injecting agent's projection (w4/post) defines that subtraction
  exactly and this design consumes it. A transit article carrying
  `FN-Statement` is accepted by the same path; verification is not a
  transit precondition (an unverifiable statement is quarantined as
  legacy-provenance content, never rewritten, OBJ-001), and the reader
  projection reports `verified`/`unverified`/`absent` as three values.
- **Header field `FN-Policy`**: the policy term `(policy-stmt-id . evidence)`
  the admitting node computed, so that a receipt at a later hop can name
  the same policy in force. Reserved; not emitted until policy.md's journal
  adoption lands.
- **Record kind `(:peer-transit peer diag generation)`** in the evidence
  slot (§2.4) and the FNFD feed records (§3.3). The BP `(:cl ...)` origin is
  the same slot.
- **Exchange fact schema**: `fn-exchange-kind` gains `:statement` beside
  `:article`, with `content-id` the statement id, so K3's lace twin is the
  same theorem over a different projection.
- **Peer `auth` slot**: `(:principal id)` beside `(:source-address addr)`, so
  a peer can be a principal in the keyring (AUTHINFO SASL, RFC 4643, or a TLS
  client certificate, later) without a new record shape; A-PEER stays the
  stated assumption until then.

Equivocation detection at merge is then `fn-lace-reissue-detected-after-merge`
applied to the laces K3 builds: two agents' nodes that each accepted one
fork of a reissued `(incarnation, sequence)` see, after peering both ways,
both forks in one lace and `fn-lace-equivocatorp` true of the creator.
Neither fork is dropped (`fn-lace-merge-preserves-equivocation`), which is
D10's restore/fork rule delivered by ordinary news transit. A policy change
arriving through peering is admitted only as a verified statement by the
group's authority (`fn-pol-policy-change-needs-authority-signature`): an
INN in the middle, or a hostile peer, cannot change a group's policy by
relaying an article that claims to.

## 7. Packets

Owners are roles of [swarm-cycles](../planning/swarm-cycles.md); acceptance
criteria are checkable without the implementer's summary. Every packet that
touches the session or config shape builds the whole tree.

| Order | Packet | Owner | Deliverable | Acceptance |
| --- | --- | --- | --- | --- |
| K0 | prefixes and registry | assurance-tooling, Sonnet | `fn-peer-`, `fn-feed-`, `fn-path-` rows in `docs/prefixes.md`; requirement rows PEER-001 (transit acceptance is the post path), PEER-002 (loop freedom), PEER-003 (exact history), PEER-004 (feed journal), PEER-005 (typed transit refusals) in `planning/requirements.json`; proof rows per K1–K7 in `proofs.json`, all `open` | `make check` green; no count typed |
| K1 | inbound transit | service integrator, Opus | `books/path.lisp`, `books/peer.lisp`, session fields, `fn-nntp-step` routing of IHAVE/CHECK/TAKETHIS/MODE STREAM and the `:article` event, `*fn-peer-reasons*`, K1, K2 (inbound half), K6 restated; `tests/acl2/peer-tests.lisp` with the RFC transcripts of §2.2's tables as `assert-event`s | whole-tree `make certify` green; every cell of the two response tables has a transcript; one `must-fail` per K1/K2 hypothesis; the `:article`-event `unreachable-in-composition` mark removed |
| K2 | outbound feed | BP lane (scheduler owner), Opus | `books/feed.lisp`, FNFD records in `books/frame`, `fn-feed-replay`, K5, K2 (outbound half), the select/drive/take equation against `host/feed-host.lisp` | K5's five-article crash witness certifies; `tests/test_feed.py` kills the host at every FNFD record boundary and the CHECK-first property holds at each |
| K3 | peer configuration | reconfiguration lane (after R2), Sonnet | `fn-cfg-peerp`, `:set-peer`/`:remove-peer`, `:path-identity` policy slot, K7, the §1.2.1 sentence in reconfiguration.md | `reconfigure` adds a peer without restart and the next CHECK from it is `238`; `:remove-peer` with an outstanding feed entry is refused with a named reason |
| K4 | INN interop | host lane, Opus, on hbox | `tests/inn/` (pin, configs, `run_inn_lab.py`), S1–S11, the evidence record | every scenario's expected lines match; S10 and S11 show one copy each; the record names what was not shown |
| K5 | history index and cost | core lane, Opus | `fn-peer-history-index` twin and `fn-peer-history-index-agrees-with-history`; the K6 cost term quoted with its measured distance | the CHECK cost sentence quotes exponent, constant and measurement in one sentence |
| K6 | BP unification | BP lane, Fable | `fn-bpi-ingress-prepare` calls `fn-peer-decide-transfer`; `fn-bpi-adu-durably-acceptedp` retired for `fn-peer-history-hasp`; the group map derived from the peer record | `bp-dtn7` scenarios unchanged byte-for-byte; the equality theorem between the old and new ingress decision on the reachable set |
| K7 | merge theorem | core lane, Fable design then Opus proofs | K3 over `fn-sys-run` with an NNTP channel; the lace twin | the three-article witness and the four must-fails certify |
| K8 | inter-agent reservation | substrate lane, Sonnet | `FN-Statement`/`FN-Policy` grammar in `books/article-fields.lisp`, `:statement` exchange kind, `(:principal id)` auth | a signed article survives S3 with `FN-Statement` byte-identical and verifies at fn |

Dependencies on current lanes: **w4/post** for the injecting-agent
projection (what the authored source is, the `:article` wire event's POST
branch, `(:injected ...)` evidence) — K1 can land before it with the
`(:post)` transfer value reserved; **w4/served-path** for the F_node books
K6 restates over and for `*fn-ideal-refusals*`; **w3/scheduler** for
`fn-sched-contact`/`fn-sched-contact-holdsp` and the tick model K2 reuses;
**w2/mutable-owner** for the connection/pin model peer connections share and
for the single pending slot that makes `:busy`/`:staged` decidable;
**reconfiguration R2+** (`fn-node-config`, the `cfg-gen` argument, the
delta list) for K3 and for `fn-peer-injection-arguments`. K0 and K1 can
start now against `ca66782` with the `cfg-gen` argument omitted and added
when R2 lands.

## What this design does not decide

Peer authentication (A-PEER stands; `(:principal id)` is a reserved slot,
not a mechanism); Distribution header matching; control messages (RFC 5537
§5; `newgroup`/`rmgroup`/`cancel` are refused as ordinary articles into
`control.*` only if configured, never executed); the D13 pruning rule
(`:date-cutoff` is reserved and unreachable); NEWNEWS-driven pull feeds
(RFC 3977 §7.4, not needed for push peering); TLS and compression
extensions; and any multi-node configuration agreement (a peer record is
local, as reconfiguration says of every generation).

## Status (wave 6, `w6/peering-inbound`, packets K0 to K2 of the inbound half)

Books: `books/path.lisp`, `books/peer-config.lisp`, `books/peer-inbound.lisp`,
`books/peer-inbound-invariants.lisp`, `tests/acl2/peer-inbound-tests.lisp`;
edits to `books/config.lisp` (kinds `:set-peer` 9, `:remove-peer` 10),
`books/config-invariants.lisp` (two local row-list lemmas), `books/nntp.lisp`
(the reader-side `502` branch), `books/served.lisp` (the session is
`fn-peer-sessionp`, dispatch calls `fn-peer-step`, `fn-served-open-peer`,
`fn-served-transit-outcome`, the `:submit` effect carries an injected or a
transit submission). Certification evidence is listed in
`planning/lanes/HANDOFF-w6-peering-inbound.md`; counts are the ledger's.

What differs from the design above, and why:

- **The peer record is rows.** `fn-cfg-peerp` is the six-field opaque record
  of §1.2, but its durable form is a group of configuration rows keyed by the
  peer name in the existing `peers` slot (`fn-cfg-peer-rows` /
  `fn-cfg-peer-of-rows`, `books/peer-config.lisp`), so the record codec of
  `books/config.lisp` carries it with no new item type. `(:set-peers rows)`
  is not retired: it is still a typed kind and the ledger keeps its
  statements. Round trip: `fn-cfg-peer-of-rows-of-peer-rows` over every
  well-formed record: **open** (below); canonicality is by construction
  (one encoder) and witnessed on ground records;
  `fn-cfg-set-peer-delta-is-admissible`, `fn-cfg-peer-rows-after-set-peer`,
  `fn-cfg-peer-find-after-remove-peer`, `fn-cfg-peer-deltas-change-only-peers`
  (the §1.2.1 sentence at the value level); the CBOR round trip of a record
  carrying both deltas is a ground witness in the test book, which is the
  coverage `books/config.lisp` has for its own codec (its general
  decode-of-encode is still open there).
- **`:remove-peer`'s feed condition is owner-side.** `fn-feed-peer-idlep` is
  the feed lane's; config admits `:remove-peer` for any configured peer
  (`:no-such-peer` otherwise), as reader pins never enter a durable record.
- **Signatures.** `fn-peer-decide-transfer` and `fn-peer-transfer` take the
  obligation id and subject strings (and `fn-peer-transfer` the transaction
  generation) as arguments: `fn-frame-digest` is constrained and unattached,
  so ACL2 cannot evaluate `fn-id-obligation-of`; the host computes them as it
  does for POST. `fn-peer-injection-arguments` bundles them; the `cfg-gen`
  leading argument waits for the owner's `fn-cnode-prepare` port.
- **Offer decisions read the live node; the peer record stays pinned.**
  `fn-served-open-peer` pins both under their recognizers at `:open`, and
  `books/owner.lisp fn-own-conn-live-session` re-pins the NODE from the
  owner's own store before every `fn-own-read`, so `fn-peer-decide-offer`
  answers from the node as it is now and `fn-peer-decide-transfer` decides
  again over the same. This corrects the sentence that stood here until
  `w11/transit-correct`, which said the offer answers from the snapshot
  taken at `:open`. RFC 4644 §2.4.2 makes a `CHECK` answer advisory --- a
  server MAY answer `238` and refuse after the bytes --- but it does not ask
  a server to forget what it holds, and a streaming peer that is told `335`
  for an article this connection delivered a moment ago sends the whole
  article for nothing. Measured on the wire at `6fb30ca`:
  `V0-TRANSIT-DUPLICATE-AB/BA` `335` and `V0-TRANSIT-CHECK-DUP-AB/BA` `238`,
  both with the certified refusal (K3) sitting behind them unreachable. The
  peer record is still the one the connection opened with, because the owner
  holds no store configuration to re-read: a `(:set-peer ...)` delta reaches
  an open peer connection's transfer decision (the host passes the live
  configuration, `host/owner-host.lisp fn-owner-transit-decide`) and not its
  offer decision. That asymmetry is open and is on the board.
- **A node with no `path-identity` suppresses no loop.**
  `fn-peer-local-identity` reads the `path-identity` policy slot;
  an unset slot is the empty string and `fn-path-names-p` never matches it,
  so `fn-peer-decide-transfer`'s loop arm cannot fire. This is configuration,
  not a model defect, and it is measurable: at `6fb30ca` `tools/v0_matrix.py`
  --- which wrote both peer records and never set either node's own slot ---
  read `V0-TRANSIT-LOOP` `235` and `V0-TRANSIT-LOOP-ABSENT` `220`, while
  `tools/twonode_gate.py`, which sets the slot, read `437 transfer rejected;
  path loop` and `430` on the same commit. The matrix sets it now and
  `V0-TRANSIT-IDENTITY` is the row the loop rows rest on.
- **Reader connections answer `502`, not `501`.** RFC 3977 §3.2.1 assigns
  `502` to a recognized command the client may not use; `501` is a syntax
  error. Table in §1.1 corrected.
- **"Not now" is 431 or 436, never 400-and-close; refusal after the bytes is
  437 or 439.** Measured against INN 2.7.4 on hbox
  (`planning/evidence/inn-lab-f4e8272-2026-09-20.md`): innfeed retries on
  431, 436, 400, 480, 503 and any unknown code and drops for good on 437 and
  439. `fn-peer-transit-code` and `fn-peer-offer-code`
  (`books/peer-inbound.lisp`) are the explicit mapping, and
  `fn-peer-not-now-is-a-retry-code` states it: `:defer` at transfer and an
  uncertain outcome are 436 for IHAVE and for TAKETHIS (the uncertain one
  also closes: the node is fenced); `:defer` at offer is 431 (CHECK) / 436
  (IHAVE); `:refuse` and `:have` after the bytes are 437 / 439; 2xx only on
  `:durable`. RFC 4644 §2.5 gives TAKETHIS only 239/439 and names 400 for a
  temporary error; 436 on TAKETHIS is fn's local policy so a pipelined
  deferral does not cost the peer a reconnect and its backoff, and it sits
  in the retry class of RFC 3977 §6.3.2.2. The table in §2.2 is corrected
  above. INN's own inbound loop check is its `ME` exclusion sub-field (§5);
  fn's is the RFC 5537 §3.6 scan, and a Path naming INN gets INN's
  `437 Unwanted site <pathhost> in path`, which fn's `437 transfer rejected;
  path loop` mirrors in class.
- **The general rows-to-record round trip is open.**
  `fn-cfg-peer-of-rows-of-peer-rows` over every `fn-cfg-peerp` (sixteen
  shapes through ten slot lookups) did not close in budget; it and the
  injectivity it gives are recorded open, witnessed on two ground records in
  the test book, and `fn-cfg-peer-rows-after-set-peer` (the peers slot holds
  exactly the record's rows after `:set-peer`) is the certified form of the
  find-after-set statement.
- **The evidence slot is a provenance** (w10/provenance, 2026-09-20).
  `fn-retain-admissiblep` takes `fn-provp` (`books/provenance.lisp`), which
  accepts every string as the `:legacy` kind, so the widening changed no
  stored value. `fn-peer-transit-provenance` builds the typed record --- peer
  name, `:ihave`/`:takethis`, the RFC 5537 §3.2.1 Path diagnostic,
  configuration generation --- and `fn-peer-transit-evidence` is its wire
  form: `"fnprov1:"` and the canonical CBOR in lowercase hexadecimal, which
  is printable (the host boundary guard `fn-store-text-octetsp` admits octets
  33 to 126 only) and inside `fn-record-metadata-bytes-p`'s 256, so it rides
  in the record's existing `release-evidence` field with no change to the
  record grammar. `fn-peer-evidence-is-the-legacy-rendering`
  (`books/peer-inbound-invariants`) is the equation between the record and
  the string the transit path writes.
  **Still open, and the only thing between here and a durable transit
  provenance**: the transit command is not in scope at
  `fn-peer-decide-transfer`, so `fn-peer-injection-arguments` still passes
  `fn-peer-evidence`'s rendering. Threading it means a `kind` formal on
  `fn-peer-decide-transfer`, `fn-peer-transfer` and
  `fn-peer-injection-arguments`, which appear inside the K1/K2/K3 statements
  --- the inbound lane owns that. Obligation and the exact call sites:
  `planning/lanes/HANDOFF-w10-provenance.md`.

Keystones, as certified (statements in `books/peer-inbound-invariants.lisp`):

| Keystone | Theorem | Hypotheses | Teeth (`tests/acl2/peer-inbound-tests.lisp`) |
| --- | --- | --- | --- |
| K1 transit node = post-path node | `fn-peer-transfer-is-the-post-path` | the transfer decision is `:want` (the branch), nothing else: `fn-node-statep` and `fn-cfgp` were unnecessary and are dropped | the IHAVE transcript: two Newsgroups, one membership, `equal` to the `fn-node-prepare` call; `fn-state-articles` unchanged until `:durable` |
| K1 memberships are the scope groups | `fn-peer-transfer-stages-only-scope-groups`, `fn-peer-scope-groups-are-live` | as above plus the prepare staged | `alt.test` not staged; the narrowed peer record flips the same article to `:out-of-scope` |
| K1 refused transfer leaves the node | `fn-peer-refused-transfer-leaves-the-node` (`-by-definition`, `:rule-classes nil`) | | loop, duplicate and out-of-scope transfers return the node `equal` |
| K1 "accepted through transit satisfies every acceptance premise" (`fn-peer-accepted-article-is-acceptance-accepted`) | **open** | | not attempted this wave: it is a theorem over `fn-node-complete` after `fn-node-prepare` and needs `fn-node-complete-preserves-state`'s article projection |
| K2 loop refused at transfer | `fn-peer-loop-is-refused` | the Path names the local identity; `fn-node-statep`, `fn-cfgp` and the parse hypothesis were unnecessary and are dropped | identity second of three: refused `:loop`; tail-entry, `.POSTED` and `.POSTED.<src>` variants accepted; `fnA.hbox.test.old` not a match; unparsable octets are `:proto-article`, not `:loop` |
| K2 outbound half (`fn-feed-never-offers-a-loop`, `fn-peer-render-prepends-path`) | **open**, feed lane | | |
| K2 general loop-test lemma over an arbitrary identity | **open** (`fn-path-names-p-ignores-the-tail-entry` was attempted and removed; the split/reverse induction did not close in budget) | | witnessed on concrete Paths |
| K3 (K4 offer/transfer half) duplicate refused at offer and transfer | `fn-peer-history-is-refused-at-offer`, `fn-peer-history-is-have-at-offer`, `fn-peer-history-is-refused-at-transfer`, `fn-peer-history-grows-under-transfer` | history membership; for `-is-have-` also the peer record with an inbound half and a syntactic Message-ID; for `-grows-` `fn-node-statep` | `435`/`438` transcripts after the durable completion; a fresh Message-ID on the same node is `:want`; the binding is a tombstone (`fn-node-find-binding` consp after completion) |
| K3 after replay (`fn-peer-history-survives-reopen`) | **open**, needs the store-node trace books | | |
| Code classes | `fn-peer-not-now-is-a-retry-code` | none | every transit and offer code on ground decisions and completions |
| Served-path keystones | `fn-peer-step-effects-well-formed`, `fn-peer-step-preserves-consistent-session`, `fn-peer-step-submission-is-typed`, `fn-peer-transit-outcome-effects-well-formed`; `fn-served-*` keystones recertified with statements unchanged, `fn-nntp-step-effects-well-formed` and `fn-nntp-step-preserves-consistent-session` recertified with statements unchanged | `fn-peer-session-consistentp` | every cell of both response tables has a transcript in the test book |

Open items (reasons reserved, no arm emits them): `:date-future` and
`:no-clock` (RFC 5537 §3.6 step 2 needs a certified RFC 5322 date-time
reader; `fn-inj-date-decode` reads only the injector's rendering);
`:date-cutoff` (D13); `:unknown-group`. Guard verification of the decision
functions and the step is deferred (`:verify-guards nil`): they are
`:guard (fn-node-statep node)` / `:guard t` as the design writes them, and
the `verify-guards` events are the next packet's first task (the callees
are verified; the obligations are the node-statep-to-retain-statep bridge).


## Status: the outbound feed (packet K2, lane `w6/peering-feed`)

What is built, where it differs from the design above, and what is open. The
inbound half's rows are the sibling lane's and are not repeated here.

| Design text | Built as | Difference |
| --- | --- | --- |
| §3.1 `fn-feed-make (peer queue contact backoff-until conn next-attempt)` | `books/peer-feed.lisp` `fn-feed-make (peer limits queue contact backoff-until conn next-attempt)` | The feed carries a `limits` record (max-queue, backoff base, retry bound, streaming) copied from the peer record's outbound half at open. The book therefore does not include `peer-config`, `fn-feedp` is self-contained, and the owner stays the one place that reads a `fn-cfg-peerp`. |
| §3.1 "Message-IDs" | `fn-frame-textp` octets | Peer names and Message-IDs are bounded non-empty UTF-8 octet lists — the transit vocabulary of `books/peer-inbound.lisp` and exactly the `:text` field type of the FNFD records — so no string conversion happens between the state and the journal. The scheduler's `fn-sched-contact-peer` is a string; binding it to `fn-feed-peer` is the owner's obligation and is not proved. |
| §3.1 "at most one entry in flight … up to inflight-window for streaming" | `(<= (fn-feed-inflight-count (fn-feed-queue f)) 1)` | fn does not take RFC 4644's streaming window yet. One in flight per peer is a conjunct of `fn-feedp`, which is what makes exactly-once an argument about one entry. Widening it is a later packet and would change the keystones' proofs, not their statements. |
| §3.2 `fn-feed-observe` | the same code map | `335`/`238` send, `235`/`239`/`435`/`438`/`437`/`439` done, `431`/`436` exponential backoff with a one-hour ceiling then the retry bound, `400` and any other code loss. |
| §3.3 FNFD, "one file per peer under `<journal>/feed/<peer>/`" | `<journal>/feed/<peer>.fnfd`, a 4-octet big-endian length before each frame | The length prefix is file layout, not a frame field: it is what lets the host hand ACL2 one whole record at a time, and a torn tail ends the record stream. |
| §4 K5 `fn-feed-at-most-one-accepted-outcome` | `books/peer-feed-invariants.lisp`, same name | The hypothesis is `fn-feed-drivenp`, a check over the fold that each record was admissible in the state the fold had reached — never the conclusion. |
| §4 K5 `fn-feed-done-is-never-reoffered` | `fn-feed-done-is-never-selected` + `fn-feed-tick-step-offers-the-selection` + `fn-feed-tick-step-is-silent-without-a-selection` | Stated over `fn-feed-tick-step`, the function the host calls, rather than over `fn-ideal-run`, which does not yet carry the feed. `fn-feed-done-is-never-selected` gained the hypothesis `(fn-feed-selection f obs)` in lane `w6/peering-feed-4`: without it the statement is FALSE at `msgid` = `NIL`, and the third theorem covers the states it excludes. |
| §4 K5 `fn-feed-replay-is-the-live-feed-modulo-inflight` | `fn-feed-replay-is-the-fold`, `fn-feed-replay-preserves-feedp`, `fn-feed-replay-preserves-peer` and the ground witness of `tests/acl2/peer-feed-tests.lisp` | **Open.** The general equation needs a second machine (a live run that emits its own journal) that no lane has built. The three replay theorems are proved (`w6/peering-feed-3` and `w6/peering-feed-4`), so what is missing is the live side, not the fold. |
| §4 K5 `fn-feed-restart-resolves-by-offer` | `fn-feed-restart-emits-no-transfer` + `fn-feed-restart-then-tick-offers` | Stated over `fn-feed-send` (the only producer of a TAKETHIS or an article block) and `fn-feed-tick-step`, not over `fn-ideal-restart`. |

**Certification, lane `w6/peering-feed-4`.** `books/peer-feed-invariants`
certifies with **no open form**: laptop, ACL2 8.7, `tools/certify_books.py`,
31.9 s, evidence
`build/lanes/w6-peering-feed-4/build/acl2/certify-20260920T211815Z-98758/`.
That closed the eleven events behind `fn-feed-apply-record-preserves-feedp`,
which no run of this book had ever reached, and with them all five of its
keystones. One of the eleven, `fn-feed-done-is-never-selected`, was FALSE as
stated and is repaired with a hypothesis true on every state where the host
emits a command; the row above says which, and
`tests/acl2/peer-feed-tests.lisp` carries the violating value.

Open, recorded rather than weakened:

- The scheduler's per-peer interface (a peer dimension on `fn-sched-item` and
  per-peer `fn-sched-retries`) is designed and not built; the exact edit is in
  [the lane handoff](../planning/lanes/HANDOFF-w6-peering-feed.md) and on the
  board. Until it lands, a feed's contact is a `fn-sched-contactp` the owner
  supplies and the scheduler does not know the feed exists.
- `fn-feed-parse-response`: **closed in w10/owner-feed.** The RFC 3977 §3.2
  status framing of a peer's reply is `fn-own-feed-response-code` /
  `fn-own-feed-parse-response` (`books/owner-feed.lisp`); the Python split
  this paragraph recorded as open was deleted with its driver (see the row
  below and `tools/feed_wire.py`).
- The feed is not yet a field of F_node's state, so K6's cost term
  (`fn-cfg-max-queue-total`) and the `:feed-octets`/`:tick` event kinds are
  untouched by this lane.
- No INN and no second fn node had been fed by `tools/run_feed.py`, whose
  only peer was the two-node harness's fake
  (`tests/twonode_gate_fake/tools/run_peer.py`), replies that file's and not
  ACL2's. That driver was retired on 2026-09-21 (`w11/harness-health`): the
  feed is the owner's, and the outbound evidence is
  `tools/twonode_gate.py`'s `scenario_owner_feed` and `scenario_feed_restart`
  against a real fn node.

## Status (wave 9, `w9/peering-e2e`, the CLI, the scheduler and the owner's port)

Delivered here: `fn peer add|remove|list` (bin/fn, tools/run_store.py,
`fn-store-cfg-set-peer` / `-remove-peer` / `-peer-names` / `-peer-slot-text` /
`-peer-slot-nat` in host/store-node-host.lisp); `books/scheduler-peers.lisp`
and `tests/acl2/scheduler-peers-tests.lisp`; the owner's transit port
(`fn-own-open-peer`, `fn-own-transit-subp`, `fn-own-transit-outcome`, the
`(:open-peer peer cfg)` and `(:transit-outcome id kind reason word)` arms,
with `fn-owner-peer-for-address`, `fn-owner-open-peer`,
`fn-owner-transit-decide`, `fn-owner-transit-outcome` in
host/owner-host.lisp and the accept/drain wiring in tools/run_owner.py);
the two evidence harnesses' peer records and the streaming half of the
two-node feed scenario.

- **The per-peer scheduler is a table of schedulers, not a peer field on
  `fn-sched-item`.** §3.1's shape (peer at item index 7, `fn-sched-selection`
  over the peer-filtered queue) **falsifies two keystones of
  `books/scheduler-invariants` as they are stated**:
  `fn-sched-promotion-position-decreases` has
  `(fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)` as a
  hypothesis and `fn-sched-aging-bound` reaches the same test through
  `fn-sched-eligible-runp`; both are peer-blind, so a promoted work for peer
  B while the open contact is peer A is neither selected nor moved closer to
  the head of the promotion queue, and the conclusion fails on a reachable
  state. Making the test peer-aware adds an argument to a function that
  appears in a keystone's statement. `books/scheduler-peers.lisp` keys one
  `fn-sched-statep` per peer name instead: every existing keystone stands
  verbatim and reaches each peer's tick through
  `fn-sched-table-tick-is-the-peer-tick` (the subject rule: what the host
  calls is `fn-sched-tick-step` on that peer's own state), with
  `fn-sched-table-tick-touches-only-its-peer` and `fn-sched-tablep-of-table-tick`
  beside it and the per-peer retry bound transported, not restated. Certified
  on persvati `run-20260920T180716Z-da35` with its teeth.
- **The role of a connection is decided at accept, from the peer table.**
  `fn-owner-peer-for-address` matches the source address against the
  configured records' `auth-source-address` rows and `fn-own-open-peer` opens
  the connection with `fn-served-open-peer`, pinning the node, the live
  configuration and the operator's AUTHINFO policy into the session; the body
  limit is the record's `inbound-max-octets`. `(:principal id)` is a reserved
  slot and matches nothing yet, so A-PEER still stands: the identity is the
  configured address.

  **The match is the ADDRESS and nothing else, and that has a consequence
  worth stating.** On a box where a configured peer answers on loopback —
  which is every two-node harness fn has — *every* client is resolved to that
  peer and opened by this branch. So the peer branch is not a rare path: it
  is the ordinary one under test, and anything it does differently from
  `fn-served-open` is a difference the whole reader surface sees. Until
  2026-09-21 it pinned `(fn-auth-open-config)` in place of the operator's
  policy, and the effect was that no credential, no `required` bit and no
  certificate reached any connection on either node of the v0 matrix
  ([the record](../planning/evidence/auth-live-2026-09-21.md)).
  `fn-served-peer-and-reader-open-under-the-same-policy` (PRF-039) now says
  the two branches pin one value.

  **Implemented 2026-09-21: reader AUTHINFO and transit authorization are
  separate decisions.** `fn-auth-restricted-keywordp` gates local reader
  operations, including POST and article reads, but not `IHAVE`, `CHECK` or
  `TAKETHIS`. `fn-auth-step-transit-command-delegates-to-peer` is the ACL2
  equality on the dispatcher under `fn-served-dispatch`: no AUTHINFO subject
  appears in its hypotheses. `fn-peer-step` then decides those verbs from the
  pinned configured source-role record; its reader branch returns 502 and a
  missing/inbound-disabled record gets the typed peer refusal. The configured
  source address is still local authorization policy, not evidence that an
  AUTHINFO principal or a network peer is cryptographically authenticated.
- **Transit and POST share one durable path, and the theorem says so at the
  owner.** `fn-own-take-installs-the-queued-submission-whatever-it-carries`
  (books/owner-invariants.lisp) states that the writer step installs the head
  of the one queue in the one pending slot with the ledger mark of the
  moment, and tests nothing about what the submission carries;
  `fn-peer-transfer-is-the-post-path` is the node half. The reply side is
  `fn-own-transit-outcome-touches-only-its-connection` and
  `fn-own-transit-outcome-needs-a-transit-submission` (the two reply tables
  cannot be crossed).
- **The transfer decision is re-taken over the live node, in ACL2.**
  `fn-owner-transit-decide` calls `fn-peer-decide-transfer` and
  `fn-peer-injection-arguments` over the owner's node and the live
  configuration; the memberships the durable path stages are
  `fn-peer-scope-groups`', and Python computes no scope, no code and no
  reason text. A decision that is not `:want` ends with no attempt and the
  completion the reply renders with is `nil`, which is what
  `fn-peer-transit-code` expects.

Open at the end of this lane, with the obligation each one needs:

| Item | State | What closes it |
| --- | --- | --- |
| `books/owner`, `books/owner-invariants` with the transit port | **uncertified and unreached**: persvati `run-20260920T180927Z-a8a4` published 29 books and failed six. The two root causes are `books/peer-config`'s `fn-cfg-set-peer-delta-is-admissible` (closed on `w6/peering-inbound-2`, not yet on dev) and `books/nntp-effects` having no certificate on dev; `peer-inbound`, `nntp-post`, `served` and `owner` are cascades of those | merge those two fixes, then resubmit the two roots with `--closure` |
| K6 (`fn-ideal-*` restated over the peer event kinds) | open, not attempted | `books/ideal.lisp` gains `(:open id peer)`, `:feed-octets` and `:tick`; the served-path robustness for peer connections is `fn-peer-step-effects-well-formed` today, which is the per-connection half, not the F_node half |
| K7 (`fn-cfg-peer-delta-preserves-the-node-and-changes-only-decisions`) | open | `fn-cfg-peer-deltas-change-only-peers` is the value-level half and is certified; the node-level statement needs `fn-node-apply-config` |
| K8 / `(:principal id)` | reserved, unimplemented | a keyring lookup at accept beside the address match |
| The feed driven by the owner (milestone 3) | **not delivered** | `books/peer-feed.lisp` is w6/peering-feed's and had not landed on dev at this lane's HEAD; the owner's tick would be `fn-sched-table-tick` per configured peer plus `fn-feed-tick-step`, and the FNFD journal write before the offer |
| K5's crash-replay evidence (milestone 4) | **not delivered** | depends on the feed |
| `tools/twonode_gate.py` feed scenario | the inbound half is real (IHAVE, 435 duplicate, loop, CHECK 438, TAKETHIS 439, reread byte-identical); the offering side is the harness's socket client, not fn's feed | the feed lane's outbound half |
| `tools/inn_lab.py` | the fn node now writes a peer record for INN before it starts, so innfeed's connection resolves to a peer; the lab was not run on hbox in this lane | one lab run on hbox with INN 2.7.4 |

## Status (wave 10, `w10/owner-feed`, the owner drives the feed)

Milestone 3 of the wave-9 handoff, and the parts of milestones 4 and 5 that
depend on it. What is built, what differs from the design above, and what is
open.

| Design text | Built as | Difference |
| --- | --- | --- |
| §3.1 "One feed state per configured outbound peer, all inside F_node's state as a new field `feeds`" | the OWNER's state, not F_node's: `books/owner.lisp`'s record gains a thirteenth field `feeds` holding `books/owner-feed.lisp`'s table | F_node (`books/ideal.lisp`) is still the reader-only skeleton, so the feed lives where the host actually steps it. K6's restatement over `fn-ideal-*` is still open. |
| §3.1 "an alist by peer name" | a list of `(name record feed)`, `fn-own-feed-tablep` | The entry carries the peer's `fn-cfg-peerp` beside its `fn-feedp`, so the scope decision on the durable path needs no configuration argument: `fn-cfg-peers` is read once, at `fn-own-feed-reconfigure`. The recognizer binds the three names of one peer — the key (the string the configuration and the scheduler use), `fn-feed-peer` (the same name as FNFD `:text` octets) and `fn-sched-contact-peer` of the feed's contact — which is the obligation the w6 handoff recorded as the owner's and unproved. |
| §3.2 `fn-feed-offerablep` | `fn-own-feed-offerablep record origin groups path` (`books/owner-feed.lisp`) | Same three refusals in the same order: the peer's outbound wildmat over the article's own Newsgroups names, `fn-path-names-p` against the peer's path-identity, and the origin peer. It takes the article's *octets*' readings rather than a parsed article, because the owner has octets. |
| §3.1 "`:tick` is the scheduler's tick for that peer" | `fn-own-feed-tick-peer`, one `fn-feed-tick-step` per peer under that peer's own `fn-sched-contactp` | **Difference, recorded.** The owner's feed tick does NOT route through `fn-sched-table-tick`. `fn-sched-tick-step` selects an `fn-sched-item` work and drives a BP attempt; its effects are `fn-bp-result-effects` and its queue is not the feed queue, so routing the feed through it would add a table that decides nothing about the feed and would make `fn-sched-table-tick-is-the-peer-tick` a decoration. What the feed does take from the scheduler is the contact model: `fn-feed-selection` gates on `fn-sched-contact-holdsp` of the feed's own contact, whose peer the table binds to the key. |
| §3.3 "(:feed-restart peer) on open, before any offer" | `fn-own-reopen` restarts every feed; `fn-owner-feed-restart` writes one record per peer | The restart is in the owner's crash-recovery transition itself, so it cannot be forgotten by the host. |
| "an ACL2-side `fn-feed-parse-response`" (w6 status, open) | `fn-own-feed-response-code` and `fn-own-feed-parse-response` | **Closed.** RFC 3977 §3.2's three-digit split is ACL2's; `tools/run_feed.py`'s `status()` was deleted for it and the driver itself is gone (`w11/harness-health`, 2026-09-21), so the owner's bridge is the only reader. The Message-ID a CHECK or TAKETHIS reply echoes is not read back at all: at most one entry is in flight per peer (`fn-feedp`), so the owner's own in-flight Message-ID is the unambiguous subject. |
| "the peer enumeration" (host `:program` twin) | `fn-own-feed-peer-names` | **Closed.** `host/store-node-host.lisp`'s `fn-store-cfg-peer-name-list` was a `:program`-mode copy; the fold is in the book now. |

The keystones, each stated over the function the owner calls:

- `fn-own-feed-target-is-offerable` and `fn-own-feed-targets-omit-no-offerable-peer`: the targets of one article are EXACTLY the peers of the table whose own record passes the scope decision, both directions.
- `fn-own-feed-never-offers-a-loop`: K2's outbound half. No target is the origin peer, and no target's path-identity is already in the article's Path.
- `fn-own-feed-target-is-in-scope`: a target's outbound wildmat matches one of the article's own Newsgroups names.
- `fn-own-feed-accept-touches-only-its-targets` and `fn-own-feed-accept-never-enqueues-on-the-origin`: the same, transported to the table the owner holds.
- `fn-own-feed-tick-peer-is-the-feed-tick`: the subject rule. One peer's tick IS `fn-feed-tick-step` on that peer's own feed, with the same effects.
- `fn-own-feed-tick-peer-records-the-command-it-emits`: durable before the effect — a record is built exactly when a command goes out, and it names the Message-ID that command offers. **OPEN, removed rather than weakened.** The residue is `fn-feed-offer`'s own precondition that the selected entry is `:queued`; the lemma for it, `fn-feed-selection-is-queued`, is in `books/peer-feed-invariants` and is a cascade of that book's one open form. The ground case is in the test book.
- `fn-own-feed-retire-keeps-a-busy-feed`: a reconfiguration is a change of decisions; a feed with queued or in-flight work is never dropped.
- `fn-own-feed-tablep` preserved by `fn-own-feed-reconfigure`, `-restart-all`, `-enqueue-all`, `-accept`, `-tick-peer` and `-tick`. `fn-feedp` preservation is CITED from `books/peer-feed-invariants` (`fn-feed-enqueue-preserves-feedp`, `fn-feed-restart-preserves-feedp`, `fn-feed-tick-step-preserves-feedp`) and never restated.

`tests/acl2/owner-feed-tests.lisp` is 98 assertions: the table built from a
real replayed configuration with three peers (streaming outbound, outbound
with a non-matching wildmat, inbound-only), a real parsed article, the four
teeth of `fn-own-feed-offerablep` (no outbound half, wildmat mismatch, Path
names the peer, the peer is the origin), the six teeth of
`fn-own-feed-tablep` (duplicate key, key that is not the record's name, no
outbound half, another peer's feed octets, a non-feed, a non-true-list), the
enqueue and its FNFD record replayed back to the same feed, the tick with
and without a connection, the reply reader and its refusals, the restart
fence and the retire-only-when-idle rule.

Open at the end of this lane, with the obligation each needs:

| Item | State | What closes it |
| --- | --- | --- |
| `books/owner-feed` and its test book | **admitted with no open form, not certified** | `books/peer-feed-invariants` has no certificate: it fails at `fn-feed-apply-record-preserves-feedp`, whose residue is now the attempt bound in the `:feed-sent` arm (`fn-feed-attempts-belowp` of `fn-feed-queue-set-state ... (:sent n)`), not the `find`/`consp` bridge the w6 handoff named. The feed lane owns it. |
| `books/owner`, `books/owner-invariants` with the feed field and the arms | **not admitted at all** | `books/served` has no certificate on dev; `books/peer-inbound`'s `fn-peer-echo-reply-effects-well-formed` is closed on `w10/auth-served` and that file is taken into this lane's worktree, so the chain may certify on the next farm run. Until it does, `include-book "served"` fails and the owner books cannot even be `ld`ed. |
| The owner's feed keystones stated over `fn-own-step` | open | `books/owner-invariants.lisp` needs `fn-own-feed-durable-is-the-target-enqueue` (the subject rule for the `(:outcome id :durable)` arm) and the preservation of `fn-own-relation` by the five new arms. Not written: a theorem that cannot be admitted is not a theorem. |
| `fn-own-feed-group-matchp` vs `fn-peer-wildmat-matchp` | a named twin | One `:rule-classes nil` equality in `books/owner-invariants.lisp`, where both are visible. `books/owner-feed` cannot include `books/peer-inbound` without inheriting the served chain's blocker. |
| fn does not prepend its own path-identity to a transit article's Path (RFC 5537 §3.2.1) | open, inbound lane's | `fn-peer-injection-arguments` stages the peer's octets verbatim. The outbound loop check still refuses a target already in Path and refuses the origin outright, but on the return leg loop suppression rests on the peer's history answer (435/438) rather than on Path. |
| RFC 3977 §3.1.1 dot stuffing of an outgoing article block | executable ACL2, transported by host | `fn-wire-render-feed-command` in `books/wire.lisp` accepts only bounded, exact CRLF source octets; it stuffs every line-leading dot and appends `.` CRLF. `host/owner-host.lisp`'s `fn-owner-feed-render-command` and `fn-owner-feed-install-feed` project those ACL2-produced octets and their explicit status. `tools/run_owner.py::feed_write` preserves its uncertain-feed fence and gives the projected octets to `tools/feed_wire.py::Session.send_block`, whose only operation is `sock.sendall`. It does not split, trim, normalize, dot-stuff, or append a terminator. `tests/acl2/wire-tests.lisp` proves a bounded actual-reader `fn-wire-drive` round trip for literal leading dots, a dot-only line, empty lines, and trailing empty lines; `tests/test_feed.py::SessionTests` witnesses one socket write of that already-rendered byte vector. Bare LF, malformed CR, improper lists, and exhausted source or command bounds are explicit ACL2 refusals. |
| The two-node outbound evidence | **harness written, not run** | `tools/twonode_gate.py` gains `scenario_owner_feed` (A posts, A's own feed offers it to B, then B to A, with the byte-identity check and the 435/438 second offer) and `scenario_feed_restart` (B down, A posts, `kill -9` A, both restart, B ends with exactly one copy: K5). `tests/test_twonode_gate.py` is green (19 tests) against the fake; no run on persvati in this lane. |

## Status (wave 11, `w11/twonode-feed`, the first crossing)

An article has crossed between two fn nodes. Node A accepted a POST, the
feed table of `books/owner-feed.lisp` enqueued it for peer `b`, the owner
offered it over a real NNTP connection, node B accepted it through the same
durable path a POST takes, and a reader on B fetched octets identical to the
ones A serves. Evidence:
[`twonode-feed-w11-2026-09-20`](../planning/evidence/twonode-feed-w11-2026-09-20.md).

### The reason it had never happened, and the correction

§2.2's decision table and §3.2's scope decision both read an article through
`fn-af-proto-article-check`, which is **RFC 5537 §3.4.1: the INJECTING
agent's check on a PROTO-ARTICLE**. Its first refusal is a present
`Injection-Info`, and that refusal is right — adding the field is the
injecting agent's own job (§3.2.3). But a transit article has already been
injected, and every article fn posts carries the field, so:

- `fn-peer-decide-transfer` answered `:refuse :proto-article` to every offer
  of an article any fn node had posted. **No fn node could accept an article
  from another fn node.**
- `fn-own-feed-groups-of` answered `NIL`, so `fn-own-feed-offerablep`'s
  wildmat had nothing to match, `fn-own-feed-targets` was empty, and no peer
  was ever a feed target. **The outbound feed enqueued nothing.**

The correction is a second function, not a weakened one.
**`fn-af-relayed-article-check`** (`books/article-fields.lisp`) is RFC 5537
§3.6 step 1 — §3.4.1's check without the two refusals that belong to the
injecting agent alone (`Injection-Info`, and `Xref`, which RFC 5536 §3.2.13
gives to a serving agent). `fn-af-proto-article-check` is now that check
behind those two tests, in the same order, so **its value on every input is
unchanged and no theorem about it moves**. Both transit sites and
`fn-peer-injection-arguments`' memberships call the relaying check.
`tests/acl2/article-fields-tests.lisp` carries the separation: the two
articles the checks disagree on, and three that say they agree everywhere
else.

This changes what §2.2 decides. The reason `:proto-article` now means "not a
well-formed article", not "an article that has been injected".

### The accept path and the peer record

Two more things had to be true before the first offer could be a transit
offer at all, and neither was an ACL2 decision.

- **`peer add` could never make a record.** `fn-cfg-peer-inboundp` caps the
  inbound bound at `*fn-record-max-payload*` (32768) and the CLI's default
  was 1048576, so every invocation made with the defaults was refused
  `:peer-record`. The default is now 0 and `fn-store-cfg-peer-record`
  supplies the ceiling, so the number has one owner again.
- **The accept path of §1.1 was already correct.** `tools/run_owner.py`
  resolves the source address through `fn-owner-peer-for-address` and opens
  with `fn-own-open-peer`; with a record in place a loopback connection
  draws `335` from `IHAVE`, not `502`. `tests/test_owner.py`'s
  `TransitPortTests` is the unit evidence: the reader control, the peer
  connection, and the tooth that a record for another address does not open
  transit.

### Open, and recorded rather than claimed

| Item | State |
| --- | --- |
| `CAPABILITIES` on a transit connection | **defect, open.** A peer that probes before it offers is told there is no transit surface (RFC 3977 §5.2.2 wants the capability exactly when the command is available). `tests/test_owner.py` asserts the current behaviour so the day it changes is visible. This is the reverse half of NNT-001, which `w10/v0-matrix` also reported. **The cause is not what this row first said**; see the `w11/feed-k5` status section at the end of this file. |
| fn does not prepend its own path-identity to a transit article's Path (§3.2.1) | unchanged from wave 10: `fn-peer-injection-arguments` stages the peer's octets verbatim, so on the return leg loop suppression rests on the peer's history answer rather than on Path. |
| A feed fault ending the service | **contained, and the design question is now answered.** `tools/run_owner.py`'s feed loop no longer lets an unexpected error unwind through `run`; a fault prints `FEED-FAULT <peer>` with its traceback and drops that feed, and three such faults were live on this path and are fixed by name. Whether a host fault should reach the wire as the `403` fourth outcome on a SERVED connection -- the question `w11/twonode-feed` recorded here as undecided -- is decided: it should, and `fn-own-fault` (`books/owner-fault.lisp`, lane `w11/owner-survival`) is the transition. A served read or a drained submission that faults answers RFC 3977 section 3.2.1's `403`, closes that connection, clears the submission it had in flight, and leaves every other connection equal to what it was, all proved; the reply octets are proved distinct from every `fn-nntp-post-outcome` line, so the fault cannot be read as a verdict on an article. An OUTBOUND feed fault still has no wire answer, because there is no connection of ours to answer on: the peer is the server there and dropping the session is the whole of it. |

## Status (wave 11, `w11/feed-k5`, K5 live and the three defects in front of it)

`w11/twonode-feed` left K5's `kill -9` restart-by-offer NOT EXERCISED with
two named blockers. Both are closed, and a third was underneath them.
Evidence:
[`feed-k5-w11-2026-09-21`](../planning/evidence/feed-k5-w11-2026-09-21.md).

### The enqueue record of §3.3 was never written

§3.3's table says `(:feed-enqueue peer msgid tick)` is written *before the
entry is `:queued`*. No deployment wrote it. `fn-own-feed-durable-records`
(`books/owner.lisp`) existed and had **no caller**: `fn-own-outcome` folded
`fn-own-feed-durable` into the new owner, the host installed the served
effects and not the feed records, and nothing flushed them. So the outbound
queue lived in memory and nowhere else until its first offer, and an article
accepted while a peer was unreachable did not survive the process that
accepted it. That is what stopped K5: on gate `15ac399` node A accepted the
article with node B down, was killed, restarted, replayed eight records --
none of them an enqueue -- and never offered it.

`fn-own-outcome-records` and `fn-own-transit-outcome-records` state the
condition under which the records are owed, in ACL2, once; the host reads
them off the owner before the outcome moves it and appends the frames before
the 240 reaches the poster. This is the first deployment in which §3.3's
record family is complete.

### A lost connection applies `fn-feed-lost`, per peer

§3.2's `fn-feed-lost` had no live caller either: `feed_drop` reported only
`(:feed-conn peer nil)`, which stops selection and resolves nothing, so an
entry that was in flight when a socket died stayed `:sent` until the
process restarted. `fn-own-feed-lost` / `fn-own-feed-lost-one` apply it to
ONE peer -- `fn-own-feed-lost-one-touches-no-other-peer` is the theorem --
and the record it authorizes is the `(:feed-outcome peer msgid attempt 400)`
that a 400 on the wire already writes, so `fn-feed-apply-record` replays it
to the state the live machine reached. A `(:feed-restart peer)` record would
not: `fn-feed-restart` retires the attempt where `fn-feed-lost` counts it.

### `CAPABILITIES` on a transit connection


`fn-auth-step` consumes CAPABILITIES so it can append the current STARTTLS
and AUTHINFO USER labels. Its composed list is
`fn-auth-capability-lines-for-peer`: it gets the peer record from the peer
session pinned at accept and delegates the base list to
`fn-peer-capability-lines`. A configured inbound peer is therefore promised
`IHAVE` and `STREAMING`; a reader, unknown peer or peer without an inbound
half is not. `tests/acl2/nntp-auth-tests.lisp` drives the called auth
dispatcher through configured-peer, reader and unauthenticated-reader cases,
and `tests/test_owner.py` observes the advertised labels and a 335 on a live
listener. The older `fn-peer-command` CAPABILITIES arm remains a direct-peer
unit interface; it is not the served-path capability decision.

## Status (wave 12, FNFD physical prefix recovery)

The per-peer file remains `u32-be(frame length) || FNFD frame`, preserving
previously written bytes. `books/feed-journal.lisp` owns the outer prefix,
its read bound, integrity verification, the repair offset and the durability
phase machine. `Journal` in `tools/feed_wire.py` performs only file I/O and
uses the same platform barriers as the store (`run_store.fsync_file` and
`fsync_dir`). This is fn's local persistence policy, not an NNTP requirement.

At open, ACL2 accepts a complete frame only if its envelope length is between
the frame header-plus-trailer size and that size plus the FNFD payload cap,
its FNFD codec accepts its integrity/schema, and its peer equals the journal's
peer. A zero-length prefix is clean EOF. One to three prefix octets at EOF,
or a valid complete prefix followed by too few frame octets at EOF, is a torn
suffix. An out-of-range complete prefix or a complete rejected frame is
invalid evidence: startup fails, the file remains unchanged, and no later
frame is skipped to. Short host reads are accumulated before reporting EOF.

The scanner returns the last accepted offset. A torn suffix is truncated
exactly there, followed by a content barrier, a feed-directory barrier and a
store-directory barrier. Clean EOF and newly created files require those same
barriers. Only then is the journal appendable; the restart record is appended
and made durable before the feed can offer. Reads retain at most a bounded
prefix and one bounded FNFD frame, rather than reading the whole file into
memory. The total journal length and replay work are not bounded by this
repair, and the logical replay queue has its existing limits and costs.

Any ambiguous append or recovery I/O result requires a new owner process.
An append failure closes the journal's I/O handle, places its logical phase
in `:uncertain` when the bridge can still answer, and fences the entire owner
with exit code 3. A later feed drop closes its socket without applying
`fn-own-feed-lost` or writing another record. Poll, dial, receive, command
write and flush stop at that fence. It is unsafe to recover only the socket:
the logical feed may have advanced before the failed append.

The book proves bounded strict offset progress for an accepted scanner step
and that an arbitrary later observation trace cannot clear an uncertain
journal phase. The crash/phase theorem is a control and fence property, not
a physical byte-image survival theorem; physical K0 composition remains open. Its test book has a real enqueue frame, malformed and torn
controls, hypothesis teeth and crash traces. `tests/test_feed_journal_live.py`
drives the actual scanner and existing feed replay fold through byte cuts,
repair/append/reopen, invalid complete evidence, short reads, failed barriers
and process death at the named host phases. The test bridge omits the full
owner/NNTP composition; those tests do not establish K5's general live/replay
equation or acceptance-to-feed atomicity.

The physical guarantee assumes the accepted prefix was not damaged by the
later append/truncate (`A-WRITE-ISOLATION`) and that successful barriers retain
bytes and namespace (`A-DURABILITY`). A torn final suffix is not evidence that
all crashes produce prefixes: damage to a complete frame fails closed, while
loss of an entire previously durable suffix cannot be detected without an
independent durable anchor. The scanner retains existing
`fn-feed-apply-record` semantics for valid records; it does not retroactively
enforce `fn-feed-drivenp` against configuration changes or historical no-ops.

