# Substrate transport: statements, laces, policy and epochs across peers

Status: design, wave 7 (`w7/substrate-transport-design`, branched at `72279c8`).
No book in this document exists. Every ACL2 form is a *statement to be
certified*, written against definitions that exist at `72279c8` with their
names used exactly, or against a sibling lane's design where marked. The
prefix `fn-stx-` is reserved here and is registered in
[`docs/prefixes.md`](../docs/prefixes.md) by packet S0. Counts live in the
generated ledger and nowhere here. A proposed theorem is not a theorem proved
by ACL2.

This design is the wire half of the substrate books
([statements](statement.md), [identity](identity.md), [laces](lace.md),
[policy](policy.md), and the membership epochs of
`books/membership-epochs.lisp`). [Peering](peering.md) §6 reserved the four
slots it needs — the `FN-Statement` and `FN-Policy` header fields, the
`:statement` exchange kind, the `(:peer-transit ...)` provenance record and
the `(:principal id)` peer auth value — and this document spends them.

**The spine, in one sentence: the statement layer never refuses bytes; it
refuses authority.** An article whose statement is missing, malformed,
unverifiable or equivocating is still accepted, stored byte-exact and relayed
unchanged, with a stated verdict (OBJ-001, D01). What such an article loses is
every *authority-bearing* effect: it does not change a group's policy, it does
not admit a post, it does not advance a key, it does not move a roster. That
separation is what makes the substrate safe to carry over a transport fn does
not control, including an INN in the middle.

RFC vocabulary is used exactly, as in [peering](peering.md): "MUST" quotes an
RFC, "fn requires" is a stronger fn guarantee, "local policy" marks a choice
the RFC leaves open.

## 1. Statements on the wire

### 1.1 The carrier: a header-carried attachment, not an article in a reserved group

**Chosen: a statement travels as a header field, `FN-Statement`, of the
article it is about.** The alternative — every statement as its own article in
a reserved group, with the subject article referenced by Message-ID — is
rejected for four reasons, in decreasing order of force.

1. **Legacy peers must relay it unchanged, and only a header field is
   protected.** RFC 5537 §3.6 requires a relaying agent to alter nothing but
   Path and Xref; an unknown header field is therefore carried byte-identical
   through an INN. A *separate article* is not protected at all: it is relayed
   only if the intermediate is configured for its group, so the signature would
   travel exactly where the operator of a machine that is not ours happened to
   subscribe. A signature that a third party's newsfeed configuration can drop
   is not a signature you can build authority on.
2. **Two objects can be separated; one object cannot.** A detached statement in
   another group is an independently droppable, independently expirable,
   independently cancellable object. The bound between an article and its
   signature would then be a *join over two feeds* whose failure mode is an
   article that looks unsigned. Attached, the failure mode is an article that
   does not arrive.
3. **The payload already is the article.** For kind `:article` the signed
   payload is the D01 authored source bytes — the article itself. A reserved
   group would carry a second copy of those bytes, and two copies can diverge;
   the divergence would be undetectable at the reader, who cannot tell which
   copy the signature covers.
4. **Ordering.** A statement in another group arrives in its own time. The
   reader would have to serve an article whose verdict is "not yet", which is a
   fourth outcome nothing in the node is prepared to report.

Against this, a reserved group is *better* at one thing: a statement that is
about no article — a `:policy`, a `:succession`, a `:receipt`. §1.4 handles
those, and it does not need a second carrier: it gives them an article to be
attached to.

### 1.2 The field

```text
FN-Statement: <base64 of fn-stx-detached-encode, folded per RFC 5536 §2.2>
```

The field value is the base64 (RFC 4648 §4, with padding, no line breaks of its
own) of the *detached* encoding of the statement: the header items of
`fn-stmt-header-items` followed by the signature byte string, with the payload
item omitted. The canonical octets of the statement are exactly the
`fn-stmt-*` encoding of [statement](statement.md): the wire adds base64 and
folding above `fn-stmt-encode` and changes nothing below it.

```lisp
;; books/statement-field.lisp (packet S1)

;; The detached projection: fn-stmt-items minus the payload item.
;; (fn-stmt-items s) is  creator incarnation sequence preds kind ref payload signature;
;; the detached list is the same list with the payload item removed.
(defun fn-stx-detached-items (s) ...)                ; fn-stmt-item-listp
(defun fn-stx-detached-encode (s)                    ; octets
  (fn-stmt-encode-items (fn-stx-detached-items s)))
(defun fn-stx-detached-decode-exact (octets) ...)    ; (:ok header signature) | (:error why)

;; Reattachment: the payload comes from the article (section 1.3), never from the field.
(defun fn-stx-reattach (header signature payload) ...)   ; a fn-stmt-p or nil

;; Base64 over the bounded profile.  Canonical: the RFC 4648 alphabet, correct
;; padding, no embedded whitespace after unfolding, no non-alphabet octet.
(defun fn-stx-b64-encode (octets) ...)
(defun fn-stx-b64-decode-exact (chars) ...)          ; (:ok octets) | (:error why)

;; The whole field, from the article parser's proved unfolded value.
;; fn-article-field-unfolded-value (books/article.lisp:118) already removes the
;; RFC 5536 §2.2 folding; this design adds no second unfolder.
(defun fn-stx-field-decode (unfolded-value) ...)     ; (:ok header signature) | (:error why)
```

Bounds, checked before any item is parsed, in this order: the field's unfolded
length (at most 8192 octets, local policy — enough for a hybrid ed25519 +
ML-DSA-65 signature, 3373 octets, plus a 1024-octet header, base64-expanded to
about 5864), then base64 acceptance, then `fn-cbor-at-mostp`, then the item
budget of at most 25 items (`*fn-stmt-max-items*` less the absent payload
item), then each item by `fn-stmt-decode-items`. This is
the bound order of [statement](statement.md) with two outer layers, and it is
the same discipline: **no allocation is sized by a number the input supplied.**

`FN-Policy` carries the policy term the admitting node computed, as two base64
byte strings `<policy-stmt-id> " " <evidence>`, both 32 octets. It is
*informational at the receiver*: a receiving node recomputes its own term from
its own lace and keyring ([policy](policy.md) "The policy term") and never
adopts the sender's. It exists so a receipt at a later hop can say which
policy the *earlier* hop believed was in force, which is provenance, not
authority. Reserved and not emitted until policy.md's journal adoption lands.

### 1.3 Where the payload is, by kind

One field, one rule, two payload locators; the statement's own `kind` selects.

| Kind | Payload | Recomputation of `ref` |
| --- | --- | --- |
| `:article` | the D01 authored source bytes: the received octets minus every header field the injecting agent added (Path, Injection-Date, Injection-Info, Xref, `FN-Statement`, `FN-Policy`) | `fn-digest-tagged "fn-payload-v1"` over that projection, compared with `fn-stmt-header-ref` |
| `:policy`, `:succession`, `:receipt` | the article body, base64 (RFC 4648 §4, CRLF every 76 characters, the final line short or absent), decoded exactly | the same, over the decoded body |

The subtraction for `:article` is *the injecting agent's projection*, owned by
w4/post; this design consumes it and does not restate it. fn requires that the
projection be a function of the received octets alone, so that a reader at hop
three computes the same bytes as the injector at hop zero without knowing the
route.

A non-`:article` statement is delivered as an ordinary article — a real
Message-ID, a real Newsgroups, a real body, ordinary transit, ordinary
retention, ordinary duplicate suppression. It is *not* a control message: no
branch of the node interprets it as a command (§7).

### 1.4 Where a statement about no article goes

**Policy statements travel in the group they govern.** The `Newsgroups` of a
`:policy` statement's article is the group named in its payload. It therefore
follows exactly the feed scope of the group it is about (`accept-groups` /
`feed-groups`, [peering](peering.md) §1.2), which is the correct answer to
"which peers need this policy": the ones who carry the group.

**fn has no newgroup.** A policy statement cannot create a group. If the group
is not live at the receiving node the offer is `:refuse :unknown-group` as for
any article, and the operator's `(:create-group ...)` configuration delta
([reconfiguration](reconfiguration.md)) is the only thing that creates one.
This is deliberate and it is the point of §7.

**Succession statements travel in `fn.principals`**, the one group name this
design reserves — an ordinary group, configured, fed and retained like any
other, with no special handling anywhere in the node. A node that does not
carry `fn.principals` learns key successions out of band; the keyring is
node-local state either way ([identity](identity.md), "Keyrings"), so this is a
convenience for distribution, never a source of authority. **Receipt
statements travel in the group of their subject article.**

### 1.5 The acceptance path

Inbound transit is unchanged: `fn-peer-decide-offer` → `fn-peer-decide-transfer`
→ `fn-peer-transfer` → `fn-node-prepare` / `fn-node-complete`
([peering](peering.md) §2.2). The statement layer is a *projection taken at
prepare time and recorded in the evidence slot*, not a second acceptance path.

```lisp
;; books/statement-transit.lisp (packet S2)

;; Total, three-valued, and computed here — never read from the peer.
(defconst *fn-stx-verdicts* '(:verified :unverified :absent))

(defun fn-stx-verdict (article keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (let ((f (fn-stx-field article)))                      ; the FN-Statement field or nil
    (if (null f)
        (list :absent :no-field)
      (let ((d (fn-stx-field-decode (fn-article-field-unfolded-value f))))
        (if (not (equal (car d) :ok))
            (list :unverified (cadr d))                  ; :malformed reason, bytes still accepted
          (let ((s (fn-stx-reattach (fn-stx-field-header d)
                                    (fn-stx-field-signature d)
                                    (fn-stx-payload-for article (fn-stx-field-header d)))))
            (cond ((null s) (list :unverified :ref-mismatch))
                  ((fn-prin-verifiedp s keyring) (list :verified (fn-stmt-creator s)))
                  (t (list :unverified :signature)))))))))
```

Four properties of that definition are load-bearing and each is a theorem in
§6: the verdict's subject is the statement's *own* canonical octets
(`fn-stmt-verifiedp` runs `fn-sig-verify` over `fn-stmt-signing-preimage`,
which is the tagged content id, which is the tagged digest of
`fn-stmt-header-encode` — the crypto seam of [identity](identity.md) and
nothing else); the peer is not an argument, so no peer verdict can enter; the
`ref` check binds the signed header to the payload the *receiver* projected out
of the *received* bytes, so a rewritten body is `:unverified :ref-mismatch` and
not a forged `:verified`; and every branch returns a member of
`*fn-stx-verdicts*`, so the three outcomes stay distinct all the way out.

The verdict is stored in the evidence slot beside the provenance:
`(:peer-transit peer diag generation)` gains a sibling value
`(:statement id creator verdict keyring-gen)`. The keyring generation is part
of the record because **a verdict without the keyring it was computed under is
not reproducible**, and a replay that cannot reproduce a verdict is a replay
that has invented one. Packet S2 adds both values to `fn-record-p`'s evidence
recognizer, as [peering](peering.md) §2.4 does for `(:peer-transit ...)`.

### 1.6 Principals as posters

A peer's `auth` slot may be `(:principal id)` ([peering](peering.md) §1.2), and
a poster's identity is the statement's `fn-stmt-creator`. These are different
questions and the design keeps them apart: the peer auth says *who handed us
these bytes*; the statement says *who wrote them*. The `From` header is
presentation content and authenticates nothing ([architecture](../docs/architecture.md)).
A transit article's provenance therefore has three independent parts, all
recorded: the peer (`:peer-transit`), the author (`:statement`), and the Path
diagnostic ([peering](peering.md) §2.3).

## 2. Laces across peers

### 2.1 The lace is a projection, not a second store

fn does not keep a lace next to the article store. The lace *is* the store,
projected:

```lisp
;; books/statement-transit.lisp (packet S3)
(defun fn-stx-lace (node) ...)   ; the fn-stmt-p of every accepted article whose verdict is :verified,
                                 ; in acceptance order; fn-lace-p by construction
```

There is exactly one durable copy of every statement — the article that carries
it — so there is no second source of truth to reconcile, no lace journal, and
no way for the lace and the store to disagree after a crash. `fn-stx-lace` is a
*proof-level* projection: it is linear in the store and must never run on a
served path (the no-whole-state-revalidation rule, D3). The executable node
carries an incrementally maintained index, `fn-stx-index`, in the pattern of
`fn-nntp-index-` and [peering](peering.md) K5's history index, with the
agreement theorem `fn-stx-index-agrees-with-lace` as its licence (§6, S3).

### 2.2 The bridge lemma: merge happens at inbound transit

Accepting a transit article is a lace merge of a singleton delta. That single
equation is what lets every lace keystone restate over the transit path without
reproving anything about laces.

```lisp
(defthm fn-stx-lace-of-accept-is-merge
  (implies (and (fn-node-statep node)
                (fn-stx-acceptedp node article keyring))        ; the transaction completed :durable
           (equal (fn-stx-lace (fn-stx-accept node article keyring))
                  (fn-lace-merge (fn-stx-lace node)
                                 (fn-stx-delta article keyring)))))
```

`fn-stx-delta` is `(list s)` when the verdict is `:verified` and `nil`
otherwise — so an unverified article contributes bytes to the store and nothing
to the lace, which is the spine sentence made mechanical. A *batch* from one
contact is the fold, and `fn-lace-merge`'s associativity and commutativity on
ids ([lace](lace.md)) make the batch's lace independent of the order the peer
offered it in, which is REP-002 at the statement level.

### 2.3 Equivocation is detected at merge, recorded, and never dropped

Both forks are kept. `fn-lace-merge-preserves-equivocation` is why: merge
appends what it does not already hold, so evidence of a fork cannot be erased
by later merges. The detection is `fn-lace-distinct-same-slot-is-equivocation`
at the moment of the merge, i.e. at inbound transit.

What "surfaced" means, precisely, because it is easy to get wrong:

- **The article is accepted.** Refusing it would let a hostile peer delete
  content by replaying a fork, and would destroy the very evidence that proves
  the equivocation. `fn-lace-merge-drops-at-collision` shows the *only* way a
  fork is lost — a content-id collision — and that is an A-CRYPTO edge, tested
  under the length realiser in `lace-tests`.
- **A durable record is written** on the accepting transaction:
  `(:equivocation creator incarnation sequence id-held id-new)` in the evidence
  slot. It is a *discovery aid with a proved agreement* to the derived
  predicate (`fn-stx-equivocation-record-agrees-with-lace`, §6), never an
  independent authority: if the record and the lace disagreed, the lace wins,
  because the lace is the articles.
- **The refusal is of authority, not of bytes.** Two new typed reasons join
  `*fn-peer-reasons*`: `:equivocation` (the creator has forked this
  `(incarnation, sequence)`; the statement carries no authority) and
  `:authority-equivocation` (the *group authority* has forked, so
  `fn-pol-current` is `nil` and the group admits nothing until a later unforked
  policy — which is already `fn-pol-current`'s behaviour, unchanged here).
- **The peer is told.** On the transit response an equivocating *authority*
  statement is answered `239`/`235` — it was accepted — and the refusal appears
  where the authority would have been used. fn requires that the two never be
  confused in a log line or an exit code: "accepted, authority refused" is a
  distinct outcome from "refused" and from "uncertain" (D13).

### 2.4 What this buys two nodes

[Peering](peering.md) K3 proves that two fn nodes peering both ways converge on
the exchange-fact projection. Its statement-level twin replaces `fn-peer-facts`
by `fn-stx-lace` and `fn-exchange-set-equiv` by `fn-lace-same-idsp`, and its
third conjunct is `fn-lace-merge-commutative-ids`. Restated over the transit
path in §6 as S3's keystones: ids are the union, a fork is visible after the
merge, and the fork survives every later merge.

## 3. Group policy on inbound transit

The gate on a peer-transit article is `fn-pol-admitp`, evaluated against **this
node's** lace and **this node's** keyring:

```lisp
(defun fn-stx-transit-authority-ok (node article keyring group authority)
  (let ((v (fn-stx-verdict article keyring)))
    (and (equal (car v) :verified)
         (fn-pol-admitp (fn-stx-lace node) keyring group authority
                        (fn-stx-statement-of article keyring)))))
```

Three consequences, each a §6 theorem.

**A peer cannot widen a group's policy.** `fn-pol-current-unchanged-by-foreign-delta`
restated with the delta being the peer's whole contact batch: if nothing in the
batch is a statement by the group's authority verified under the local keyring,
the policy in force is *equal* before and after, so no admission and no
authorization decision changes
(`fn-pol-admitp-unchanged-by-foreign-delta`,
`fn-pol-authorizedp-unchanged-by-foreign-delta`). The constructive
contrapositive, `fn-pol-policy-change-needs-authority-signature`, *names* the
statement that did it — so "which article changed our policy" always has an
answer, and it is always a signed one.

**A peer's verdict is not an input.** `fn-pol-admitp` takes a lace, a keyring, a
group, an authority and a statement. The peer is not among them. That is a
definition, not a proof event, and it is named honestly
(`fn-stx-admission-is-peer-independent-by-definition`); the proof event is the
*equating* theorem that the function the host calls on the transit path is this
one (`fn-stx-transit-admit-is-fn-pol-admitp`, §6), which is what the
theorem-subject rule requires.

**Policy statements propagate as statements.** A policy change reaches a peer
as an ordinary article in the governed group carrying a `:policy`
`FN-Statement`; at the peer it is an ordinary member of the lace, and
`fn-pol-current` recomputes. Nothing is pushed, nothing is applied, nothing is
executed. A node that has not yet received the new policy is not wrong — it is
behind, and `fn-pol-current-is-not-superseded` says exactly what it will do
when it catches up. Policy convergence is therefore a *consequence* of article
convergence and needs no second protocol.

One asymmetry is deliberate and must be stated: **the authority principal of a
group is local configuration, not wire content.** Which principal governs
`fn.letters` at this node is a group configuration field
([reconfiguration](reconfiguration.md)); a peer cannot name it. If two nodes
configure different authorities for the same group name they will admit
different sets, and that is a *local alias* disagreement, D11's open question,
not something the wire can fix. The design refuses to let an article settle it.

## 4. Membership epochs across a partition

A membership commit `(id base actor op subject)` (`fn-me-commit`) travels as
the payload of a `:policy`-kind statement in the group whose roster it changes,
or in `fn.principals` for a site-wide roster. What a peer learns after
reconnection is therefore: **commits, and fork evidence. Never a roster.**

That distinction is the whole of this section. `fn-me-site-merge` merges the
*commits* set and leaves the *chain* untouched:

```lisp
(defun fn-me-site-merge (site delta)
  (fn-me-site (fn-me-site-id site) (fn-me-founding site)
              (fn-me-chain site)                              ; unchanged
              (fn-me-merge (fn-me-commits site) delta)        ; append what is new
              (fn-me-window site) (fn-me-hold-limit site) (fn-me-held site)))
```

Only `fn-me-adopt` extends the chain, and adoption is a *local* act — an
operator or an owner decision at this site, never an inbound event. So:

- **Reconnection cannot rewrite history.**
  `fn-me-site-merge-never-revises-admissibility`: for any well-formed site,
  commits delta and message, `fn-me-decide` after the merge *equals*
  `fn-me-decide` before it. A message that was admitted stays admitted; one
  that was refused stays refused; one that was held stays held. A partition
  that ends does not retroactively un-say what the site said.
- **The partition is exposed, not resolved.**
  `fn-me-merge-exposes-the-partition`: two commits off the same base with
  different ids are both in the merge and `fn-me-forkedp` is true of it. Two
  sites that removed different members while partitioned both see both
  removals, and `fn-me-fork-evidence` names them. fn does not pick a winner by
  wall clock; there is no last-writer-wins anywhere on this path.
- **Revocation does not travel backwards.**
  `fn-me-revoked-refusal-is-monotone`: if a sender is revoked at or before a
  message's epoch at site `a`, then every site `b` whose knowledge extends
  `a`'s refuses that message. Learning *more* can never turn a refusal into an
  admission. This is the property a partition makes valuable: the side that
  revoked can reconnect to the side that did not, and the revocation holds.

The honest limits: the commits set grows monotonically and this design proposes
no pruning (D13); a site that stays partitioned for a long time returns with a
large delta, and `fn-me-hold-limit` bounds only the *held message* buffer, not
the commits. Held messages ahead of the local epoch resolve on reaching it
(`fn-me-hold-resolves-on-reaching-epoch`) or hit `:capacity`, which is a
distinct third outcome and is reported as one.

## 5. The agent angle

An agent is a principal: a 32-octet id from a public key and a token
(`fn-prin-id`, [identity](identity.md)), with a key chain it advances by
signed `:succession`, and a lace — the statements it has made and the ones it
has learned. Nothing about an agent is a special case in fn; it is the same
principal a human with a signing key is.

The round trip, end to end, with the function that does each step:

1. **Agent A composes.** The authored source bytes are exactly what it wrote
   (D01). It signs the statement `(creator=A, incarnation, sequence, preds,
   :article, ref=digest of those bytes)` with `fn-stmt-sign`, producing a
   signature over `fn-stmt-signing-preimage` — the tagged content id of the
   canonical header. `preds` may name up to 16 statements A is replying to,
   which is a causal reference, not a References header.
2. **A posts.** Its client emits the article with `FN-Statement` attached
   (§1.2) through POST (w4/post) or hands it to its own node.
3. **Node 1 admits.** `fn-stx-verdict` recomputes the payload projection and
   verifies against its keyring; `fn-pol-admitp` checks the group's policy in
   force. Admitted, the article is stored byte-exact with both evidence values.
4. **Transit.** Node 1 feeds node 2 (or an INN feeds node 2). Path is prepended
   on the way out and Xref removed; every other octet, `FN-Statement` included,
   is identical (RFC 5537 §3.6).
5. **Node 2 accepts and verifies locally.** The same `fn-stx-verdict` runs
   against *node 2's* keyring. If node 2 does not know A, the verdict is
   `:unverified :signature` — `fn-prin-verifiedp` returns false for an unknown
   creator by construction ([identity](identity.md), "Keyrings") — and the
   article is still stored and served, marked unverified. This is the correct
   answer, and it is why the verdict carries the keyring generation.
6. **Agent B reads** from node 2 and asks two questions: *who signed this*, and
   *may I check it myself*.

### What the reader profile must expose

Both questions must be answerable, and the second one must be answerable
without trusting fn. So the profile exposes the bytes first and the verdict
second.

- **The bytes (primary, no new mechanism).** `ARTICLE` and `HEAD` return
  `FN-Statement` as a header field like any other. A client with its own
  keyring verifies locally: base64-decode, reattach the payload it projects
  from the same article, check the signature. Nothing in the reader path is
  trusted to do this correctly, which is the only arrangement under which an
  agent's verification means anything. fn requires that the field survive the
  reader path byte-identical.
- **The verdict (secondary, a metadata item).** A new HDR metadata item,
  `:fn-verified` (RFC 3977 §8.5 reserves the leading colon for exactly this),
  answers for a range or a Message-ID:

  ```text
  HDR :fn-verified 1-10
  225 Headers follow
  1 verified 9f2c...ab keyring 7 policy 41e0...03
  2 unverified signature keyring 7
  3 absent no-field
  ```

  Three tokens, one per outcome of `*fn-stx-verdicts*`, never a boolean; the
  principal id in hex (`fn-id-hex-octets`) answers "verified by whom"; the keyring
  generation answers "under what, and can I reproduce it"; the policy term
  answers "admitted under which policy in force". A client that wants none of
  this never sees it.
- **OVER, with its cost named.** `:fn-verified` may also be appended as an
  extra OVER field, listed as `FN-Verified:full` in `LIST OVERVIEW.FMT` after
  the seven fixed lines (RFC 3977 §8.4 permits appended fields). This is not
  free: the w3/reader-profile lane emits exactly eight OVER fields and exactly
  seven OVERVIEW.FMT lines and has theorems about that shape, so the extension
  is a *shared-struct change* that rebuilds `nntp-overview`, `nntp-invariants`
  and `nntp-effects` and re-proves their cleanliness theorems. Packet S6 owns
  that or declines it; HDR alone is sufficient for the agent round trip and is
  the smaller change.
- **No new command.** `FN-VERIFY` was considered and rejected: a new command
  needs a capability label, is invisible to every existing client, and would
  make the verdict look like an oracle. A metadata item is a projection of data
  the client already has.

What the profile must *not* do: report a verdict without its keyring
generation; collapse `:unverified` and `:absent`; or let a `verified` line
imply anything about the *content* of the article. `verified` means one thing —
this principal signed these bytes, under the key this node holds for it. It
does not mean the claim is true, the principal is who they say, or the node
approves.

## 6. Keystones

Statements to be certified. Each names its hypothesis stack and its teeth: a
reachable non-degenerate witness, and one `must-fail` per hypothesis showing
the conclusion fails without it (the teeth rule). Where a row restates a
substrate keystone over the transit path, the keystone is cited by name and the
restatement is a corollary of it and the bridge lemma; a corollary is labelled
as one and is not offered as the proof event.

### S1-1. The field codec is canonical

```lisp
(defthm fn-stx-field-round-trip
  (implies (fn-stmt-p s)
           (equal (fn-stx-parse-header (fn-stx-header-value s))
                  (fn-stx-ok (list (fn-stmt-header s) (fn-stmt-signature s))))))

(defthm fn-stx-field-accepted-input-is-canonical
  (implies (fn-stx-okp (fn-stx-parse-header v))
           (equal (fn-stx-header-value-parts (fn-stx-val (fn-stx-parse-header v))
                                             (fn-stx-val2 (fn-stx-parse-header v)))
                  (fn-stx-strip-wsp v))))
```

Corrected by packet S1 against the book that proves it
(`books/stx-invariants.lisp`), in two places where the first drafting was
wrong. **The canonical form is payload free.** The earlier spelling re-encoded
through `fn-stx-reattach` with a free `payload` variable, and `fn-stx-reattach`
is `nil` unless the header's `ref` binds exactly that payload, so the theorem
was false as written. What the field carries is the header and the signature,
and `fn-stx-header-value-parts` is the canonical rendering of that pair.
**The canonical form is the whitespace-stripped value.** RFC 5536 §2.2 folding
is legal, a 6 kB field will be folded, and `fn-article-field-unfolded-value`
retains the continuation WSP; refusing embedded WSP outright would make
folding unusable. `fn-stx-parse-header` strips WSP before decoding and the
theorem concludes about `(fn-stx-strip-wsp v)`, so a middle box can vary only
the folding the RFC already permits and still cannot offer a second value that
decodes to the same statement.

Hypotheses: a well-formed statement; the 8192-octet field bound. Scope: the two
layers this design adds above `fn-stmt-encode`. The second is the one that
matters — every accepted field value has exactly one canonical form, so a
middle box cannot produce a second field value that decodes to the same
statement and thereby split a reader population. Teeth: a golden field value
for a golden statement, byte-for-byte, computed independently of any digest;
`must-fail` on a value with embedded whitespace surviving unfolding, wrong
padding, a non-alphabet octet, a truncated base64 quantum, 8193 octets, 26
items, and a payload item present in the detached encoding.

### S2-1. The verdict is computed from the statement's own octets

```lisp
(defthm fn-stx-verified-implies-signature-over-own-octets
  (implies (equal (car (fn-stx-verdict article keyring)) :verified)
           (let ((s (fn-stx-statement-of article keyring)))
             (and (fn-stmt-p s)
                  (equal (fn-stmt-header-ref (fn-stmt-header s))
                         (fn-digest-tagged *fn-stmt-payload-tag*
                                           (fn-stx-payload-for article (fn-stmt-header s))))
                  (fn-sig-verify (fn-prin-key-for (fn-stmt-creator s) keyring)
                                 (fn-stmt-signing-preimage (fn-stmt-header s))
                                 (fn-stmt-signature s))
                  (member-equal (cons (fn-stmt-creator s)
                                      (fn-prin-key-for (fn-stmt-creator s) keyring))
                                keyring))))
  :rule-classes nil)
```

Hypotheses: the verdict is `:verified`; nothing else. This is the grounding
theorem in the style of `fn-pol-admission-is-grounded` — a `:verified` line at
the reader is *backed by* a named key in the node's own keyring, a signature
check over the statement's own signing preimage, and a `ref` recomputed from
the receiver's own projection of the received bytes. Teeth: a witness at each
of `:verified`, `:unverified` (each of `:malformed`, `:ref-mismatch`,
`:signature`) and `:absent`; `must-fail` that a tampered body yields
`:verified`; `must-fail` that an unknown creator yields `:verified`;
`must-fail` that a statement verified under peer assertion alone is
`:verified` (the peer is not an argument — the must-fail is that no function of
the peer appears in the definition's support).

Companion, and the reason the row above is about the right function:

```lisp
(defthm fn-stx-transit-verdict-is-fn-stx-verdict
  (implies (and (fn-node-statep node) (fn-cfg-peerp peer))
           (equal (fn-stx-evidence-verdict
                   (fn-peer-transfer node cfg peer session msgid octets clock))
                  (fn-stx-verdict (fn-stx-parse octets) (fn-node-keyring node)))))
```

The host line: `fn-peer-transfer` is what the host calls on a `TAKETHIS` body
or a `335`-then-article ([peering](peering.md) §2.2); this equation is what
lets every verdict theorem count for it.

### S3-1. Transit merge: ids are the union

Restatement of `fn-lace-merge-ids-are-union` over the transit path, via
`fn-stx-lace-of-accept-is-merge` (§2.2). Corollary; the keystone is the lace
theorem and the bridge lemma is the new work.

```lisp
(defthm fn-stx-transit-ids-are-union
  (implies (and (fn-node-statep node)
                (fn-stx-acceptedp node article keyring))
           (iff (member-equal h (fn-lace-ids (fn-stx-lace (fn-stx-accept node article keyring))))
                (or (member-equal h (fn-lace-ids (fn-stx-lace node)))
                    (member-equal h (fn-lace-ids (fn-stx-delta article keyring)))))))
```

Teeth: a three-article witness in which one article is already held (the
`:have` path must be exercised, not only `:want`); `must-fail` without the
durable-completion hypothesis, using a `:refused` transaction whose article
contributes no id.

### S3-2. Equivocation is detected at the merge and recorded

```lisp
(defthm fn-stx-transit-equivocation-is-detected
  (implies (and (fn-node-statep node)
                (fn-stx-acceptedp node article keyring)
                (member-equal s1 (fn-stx-lace node))
                (equal (list s2) (fn-stx-delta article keyring))
                (not (equal s1 s2))
                (fn-lace-same-slotp s1 s2))
           (and (fn-lace-equivocatorp (fn-stx-lace (fn-stx-accept node article keyring))
                                      (fn-stmt-creator s1) (fn-stmt-incarnation s1))
                (member-equal s1 (fn-stx-lace (fn-stx-accept node article keyring)))
                (member-equal s2 (fn-stx-lace (fn-stx-accept node article keyring))))))
```

Hypotheses: node well formed; the transaction completed durably; the two
statements are distinct and share a `(creator, incarnation, sequence)` slot.
Proof: `fn-lace-distinct-same-slot-is-equivocation` on the merged lace, with
`fn-stx-lace-of-accept-is-merge` and `fn-lace-merge-ids-are-union` placing both
members. Note the two membership conjuncts: **neither fork is dropped**, which
is the substantive half and is not implied by the equivocator predicate alone.

The wire form of `fn-lace-reissue-detected-after-merge`, i.e. two agents on two
nodes each holding one fork of a reissued slot, peering both ways:

```lisp
(defthm fn-stx-reissue-detected-after-peering
  (implies (and (not (equal p1 p2))
                (not (equal (fn-stmt-id (fn-stmt-sign sk c i n nil :article p1))
                            (fn-stmt-id (fn-stmt-sign sk c i n nil :article p2))))
                (fn-stx-node-holds-only node-a (fn-stmt-sign sk c i n nil :article p1))
                (fn-stx-node-holds-only node-b (fn-stmt-sign sk c i n nil :article p2))
                (fn-stx-complete-exchangep sys a b events))
           (let ((final (fn-sys-run sys events)))
             (and (fn-lace-equivocatorp (fn-stx-lace (fn-sys-node a final)) c i)
                  (fn-lace-equivocatorp (fn-stx-lace (fn-sys-node b final)) c i)))))
```

The A-CRYPTO edge is explicit as a hypothesis, exactly as in the lace book: if
the two forks collide in content id, one is dropped at merge
(`fn-lace-merge-drops-at-collision`) and the fork is invisible. `lace-tests`
already exhibits that under the length realiser, and this design does not
pretend otherwise. Teeth: the two-node witness; `must-fail` on the distinct-id
hypothesis under the length digest; `must-fail` on completeness (one `431`
never retried leaves one node blind).

```lisp
(defthm fn-stx-transit-equivocation-survives-later-merges       ; corollary of
  (implies (fn-lace-equivocatorp (fn-stx-lace node) p i)        ; fn-lace-merge-preserves-equivocation
           (fn-lace-equivocatorp (fn-stx-lace (fn-stx-accept node article keyring)) p i)))

(defthm fn-stx-equivocation-record-agrees-with-lace
  (implies (and (fn-node-statep node) (fn-stx-index-invariantp node))
           (iff (fn-stx-recorded-equivocationp node p i)
                (fn-lace-equivocatorp (fn-stx-lace node) p i))))
```

The second is the licence for the durable record: it is a *twin*, and the
theorem is what stops it becoming a second authority. Teeth: a witness where
the record is present and the lace agrees; `must-fail` after hand-editing the
record without the article (the invariant hypothesis is load-bearing).

### S3-3. The index twin

```lisp
(defthm fn-stx-index-agrees-with-lace
  (implies (and (fn-node-statep node) (fn-stx-index-invariantp node))
           (and (equal (fn-stx-index-lookup (fn-stx-index node) id)
                       (fn-lace-lookup (fn-stx-lace node) id))
                (iff (fn-stx-index-equivocatorp (fn-stx-index node) p i)
                     (fn-lace-equivocatorp (fn-stx-lace node) p i))))
  :rule-classes nil)

(defthm fn-stx-index-invariant-preserved-by-accept
  (implies (and (fn-node-statep node) (fn-stx-index-invariantp node))
           (fn-stx-index-invariantp (fn-stx-accept node article keyring))))
```

The pair is the no-whole-state-revalidation discipline (D3): the invariant is
carried in state and proved preserved, and the linear projection appears only
in proofs. Teeth: a served-path witness showing `fn-stx-lace` is not called per
command (a cost shadow in the `fn-aw-`/`fn-wm-` style, not a comment).

### S4-1. Transit admission is the policy function, and a peer cannot widen

```lisp
(defthm fn-stx-transit-admit-is-fn-pol-admitp                    ; the theorem-subject equation
  (implies (and (fn-node-statep node) (fn-cfg-peerp peer)
                (equal (car (fn-stx-verdict article (fn-node-keyring node))) :verified))
           (equal (fn-stx-transit-authority-ok node article (fn-node-keyring node) group authority)
                  (fn-pol-admitp (fn-stx-lace node) (fn-node-keyring node) group authority
                                 (fn-stx-statement-of article (fn-node-keyring node))))))

(defthm fn-stx-peer-batch-cannot-change-policy                   ; corollary of
  (implies (and (fn-node-statep node)                            ; fn-pol-current-unchanged-by-foreign-delta
                (fn-pol-delta-without-authority-p (fn-stx-batch-delta node peer batch keyring)
                                                  keyring authority))
           (equal (fn-pol-current (fn-stx-lace (fn-stx-accept-batch node peer batch keyring))
                                  keyring group authority)
                  (fn-pol-current (fn-stx-lace node) keyring group authority))))
```

Hypotheses: node and peer well formed; for the second, the batch contains no
statement by the authority verified under the local keyring — which is
`fn-pol-delta-without-authority-p` unchanged, applied to the batch's lace
delta. Teeth: a witness where a peer offers a policy statement for a group it
does not govern and the policy in force is `equal` before and after; a witness
where the *genuine* authority's later policy does change it (so the hypothesis
is load-bearing and the theorem is not vacuous, the same tooth
`policy-tests` uses); `must-fail` when the batch contains the authority's
signed statement; `must-fail` on a batch whose statement carries the
authority's id but another key (the forged-policy tooth, restated on the wire).

`fn-pol-policy-change-needs-authority-signature` restated over a batch names
the offending statement, so the operator question "which transit article
changed our policy" has a constructive answer.

### S5-1. Reconnection never revises admissibility

```lisp
(defthm fn-stx-reconnect-never-revises-admissibility             ; corollary of
  (implies (and (fn-me-sitep site)                               ; fn-me-site-merge-never-revises-admissibility
                (fn-me-commitsp (fn-stx-commits-of-batch batch keyring))
                (fn-me-messagep msg))
           (equal (fn-me-decide (fn-me-site-merge site (fn-stx-commits-of-batch batch keyring)) msg)
                  (fn-me-decide site msg))))

(defthm fn-stx-reconnect-exposes-the-partition                   ; corollary of
  (implies (and (fn-me-sitep site-a) (fn-me-sitep site-b)        ; fn-me-merge-exposes-the-partition
                (member-equal ca (fn-me-commits site-a))
                (member-equal cb (fn-me-commits site-b))
                (equal (fn-me-commit-base ca) (fn-me-commit-base cb))
                (not (equal (fn-me-commit-id ca) (fn-me-commit-id cb)))
                (not (member-equal (fn-me-commit-id cb) (fn-me-commit-ids (fn-me-commits site-a)))))
           (fn-me-forkedp (fn-me-commits (fn-me-site-merge site-a (fn-me-commits site-b))))))
```

The new content in S5 is not these — they are the substrate keystones with a
wire-shaped delta — but the *carrier* obligation, which must be proved
separately and is where a mistake would hide:

```lisp
(defthm fn-stx-commits-of-batch-are-verified-and-well-formed
  (implies (fn-prin-keyringp keyring)
           (and (fn-me-commitsp (fn-stx-commits-of-batch batch keyring))
                (fn-stx-every-commit-has-a-verified-statement
                 (fn-stx-commits-of-batch batch keyring) batch keyring))))
```

Hypotheses: a well-formed keyring. Without it an unverified article could
inject a commit, and the two corollaries above would be true of a poisoned
delta — true, and worthless. Teeth: a witness batch with one verified and one
unverified commit-bearing article, whose delta is the singleton; `must-fail`
that an unverified article contributes a commit; `must-fail` that a merge
extends the chain (adoption is local: `fn-me-chain` is `equal` before and
after, which `fn-me-site-merge-preserves-chain` already gives and the wire
tooth restates).

### S6-1. The reader's verdict is the node's verdict, three-valued

```lisp
(defthm fn-stx-reader-verdict-is-the-recorded-verdict
  (implies (and (fn-node-statep node) (fn-acceptedp msgid ...))
           (equal (fn-stx-hdr-fn-verified node msgid)
                  (fn-stx-render-verdict (fn-stx-evidence-verdict-of node msgid)))))

(defthm fn-stx-reader-verdict-is-typed
  (member-equal (car (fn-stx-evidence-verdict-of node msgid)) *fn-stx-verdicts*))
```

The reader reports what acceptance recorded and does not recompute per query
(no whole-state revalidation, and no chance of the two disagreeing). Teeth: one
transcript per verdict value against the RFC 3977 §8.5 grammar; a transcript
showing `FN-Statement` byte-identical through `HEAD` after transit; a
`must-fail` that any rendering collapses `:unverified` and `:absent` into one
token.

## 7. Control messages: RFC 5537 §5, pgpverify, and why fn implements neither

RFC 5537 §5 defines control messages — a `Control` header field whose content
is a verb, executed by the receiving agent: `cancel` (§5.3) withdraws an
article; `newgroup` (§5.2.1) and `rmgroup` (§5.2.2) create and delete groups;
`checkgroups` (§5.2.3) reconciles a whole hierarchy's group list. The legacy
authentication is **pgpverify**: an `X-PGP-Sig` field over a canonicalised
subset of the article's headers plus its body, checked against a hierarchy
keyring the operator installs out of band, which is how the Big-8 have
administered `newgroup` and `checkgroups` for three decades.

fn implements none of them, and the reasons are architectural rather than
squeamish.

- **An article is not an instruction.**
  [Architecture](../docs/architecture.md) is explicit: an untrusted article
  cannot change configuration, authorize a peer, erase another article, or
  create an obligation by naming it. A control message is precisely the
  opposite arrangement — authority conveyed by content, with the *verb* in the
  data. [Peering](peering.md) already states the transit rule: `newgroup`,
  `rmgroup` and `cancel` are accepted as *ordinary articles* into `control.*`
  if the operator configured that group, and executed never.
- **Unsigned control is a remote root shell.** Anything that reaches the feed
  can forge a `From` and a `Control` field. This is not hypothetical; it is why
  pgpverify exists at all. fn's answer is not "sign the control message"; it is
  "there is no control message".
- **Signed control is still last-writer-wins.** pgpverify's checked signature
  says a hierarchy key signed *this* `newgroup`. It does not order two
  `newgroup`s, does not survive key rotation without a flag day, has no
  revocation, and resolves conflicts by arrival — the three things fn refuses
  (D10 incarnations and explicit origin, D09 key succession, "preserve
  conflicting evidence, no last-writer-wins by wall clock"). It also signs a
  *canonicalised subset* of the article, so two byte-different articles can
  carry one valid signature — the exact ambiguity D01 exists to remove by
  signing the authored source bytes.
- **What replaces each verb.**

  | RFC 5537 §5 | fn |
  | --- | --- |
  | `newgroup`, `rmgroup` | a `(:create-group ...)` / group-retirement configuration delta at *each* node ([reconfiguration](reconfiguration.md)). Local, operator-owned, generation-stamped, never a wire act. A group name is a local alias over a group authority (D11). |
  | `checkgroups` | nothing on the wire. The group table is configuration; two nodes with different tables are differently configured, which is a fact about two operators, not a message. |
  | `cancel` | nothing. D03: keep until explicit authorized release. A withdrawal is a *statement* — evidence that the author retracted, which readers may act on — and never an erasure of the article or of its binding. |
  | moderation / approval | the group's policy in force: a `:policy` statement by the group's authority naming the authorized posters, with `fn-pol-admitp` as the gate and `fn-pol-current-unchanged-by-foreign-delta` as the confinement. |
  | pgpverify's hierarchy keyring | the node's keyring of principals with proved key succession (`fn-prin-trail-is-valid-chain`), and a verdict that carries the keyring generation it was computed under. |

  Every row moves a decision from "a message that arrives" to "a record this
  node holds", which is the same move the whole project makes.
- **The one thing legacy control got right** is worth keeping: an operator can
  see the whole set of administrative acts, in order, as articles. fn keeps
  that: `:policy` and `:succession` statements *are* articles, in real groups,
  readable by any client, and they are evidence rather than instructions.

## 8. Packets

Owners are roles of [swarm-cycles](../planning/swarm-cycles.md); acceptance
criteria are checkable without the implementer's summary. Dependencies name
[peering](peering.md)'s packets K0–K8 as that design numbers them. Any packet
that touches the session, evidence or overview shape builds the whole tree, not
the changed books (the red-umbrella rule).

| Order | Packet | Owner | Deliverable | Acceptance | Depends on |
| --- | --- | --- | --- | --- | --- |
| S0 | prefixes and registry | assurance-tooling, Sonnet | `fn-stx-` row in `docs/prefixes.md`; requirement rows SUB-001 to SUB-006 in `planning/requirements.json`, each defined once in §9 of this document and referenced everywhere else; proof rows for every §6 keystone in `proofs.json`, all `planned` (the registry's word for stated and unproved); the `FN-Statement` reservation in [nntp](nntp.md#reserved-header-fields); the two-node statement exchange as a scenario specification | `make check` green; no count typed into prose | K0 |
| S1 | the field codec | substrate lane, Opus | `books/statement-field.lisp`: detached items, `fn-stx-detached-encode`/`-decode-exact`, base64 with canonicality, `fn-stx-field-decode` over `fn-article-field-unfolded-value`, the `FN-Statement` and `FN-Policy` grammar in `books/article-fields.lisp`; S1-1; `tests/acl2/statement-field-tests.lisp` | whole-tree `make certify` green; the golden field vector is byte-exact and independent of any digest; one `must-fail` per S1-1 hypothesis; a signed article survives the INN scenario of [peering](peering.md) §5 with `FN-Statement` byte-identical and verifying at fn | K8 (which this subsumes), w4/post for the authored-source projection |
| S2 | verdict and evidence | substrate lane, Opus | `books/statement-transit.lisp` part 1: `fn-stx-payload-for`, `fn-stx-verdict`, `*fn-stx-verdicts*`, the `(:statement ...)` and `(:equivocation ...)` evidence values in `fn-record-p`; S2-1 and the `fn-peer-transfer` equation | whole-tree certify green; a witness at each of the five verdict outcomes; `must-fail` that a tampered body verifies, that an unknown creator verifies, and that the peer appears in the verdict's support; replay reproduces every verdict from the journal alone | S1, K1 |
| S3 | lace projection, bridge, index | core lane, Fable design then Opus proofs | `books/statement-transit.lisp` part 2: `fn-stx-lace`, `fn-stx-delta`, `fn-stx-lace-of-accept-is-merge`, `fn-stx-index` and its invariant; S3-1, S3-2, S3-3; the `:equivocation`/`:authority-equivocation` reasons added to `*fn-peer-reasons*` | whole-tree certify green; the two-node reissue witness certifies and both forks are present at both nodes; the index cost shadow shows `fn-stx-lace` is not on the served path; `must-fail` per hypothesis of S3-1 and S3-2 | S2, K1, K3 |
| S4 | policy on transit | core lane, Opus | `fn-stx-transit-authority-ok`, S4-1 and the batch restatement of `fn-pol-policy-change-needs-authority-signature`; the "authority is local configuration" sentence added to [reconfiguration](reconfiguration.md) and the group config field | whole-tree certify green; a transit witness where a hostile peer's policy statement changes nothing and the genuine authority's does; the named-offender theorem returns the right statement in the witness | S3, K1 |
| S5 | epochs across a partition | substrate lane, Opus | `fn-stx-commits-of-batch` and its verified-and-well-formed theorem; S5-1's three rows; the `fn.principals` group name reserved in `books/store-config.lisp` | whole-tree certify green; a partition scenario in `tests/scenarios/` where two sites remove different members, reconnect, and both see the fork with no decision revised; `must-fail` that an unverified article contributes a commit and that a merge extends the chain | S3 |
| S6 | reader exposure | reader lane, Opus | `:fn-verified` HDR metadata item with the three-token rendering, `fn-stx-render-verdict`, S6-1; the `fn` CLI surfacing all three outcomes with distinct exit codes; the OVER/`LIST OVERVIEW.FMT` extension **or** a written decision declining it with its cost | whole-tree certify green; one transcript per verdict against the RFC 3977 §8.5 grammar; `HEAD` returns `FN-Statement` byte-identical after transit; a second agent on the second node verifies the article with its own keyring and no fn code; `must-fail` on any rendering that collapses two outcomes | S2, w3/reader-profile |

S1 and S2 can start against `72279c8` immediately; S3 needs K1's transit path;
S4 needs S3; S5 and S6 are independent of each other.

## 9. Registered requirements

The six requirements this design adds are defined here and nowhere else: every
other mention of a `SUB-` id, in this document or another, is a reference to
its line below. They are registered in
[`requirements.json`](../planning/requirements.json) with the keystones of §6
as their proof targets, and the two-node exchange that exercises them is
`SCN-019` in [the scenario catalog](../tests/scenarios/catalog.json). Each line
keeps the vocabulary of the preamble: "MUST" quotes an RFC, "fn requires" is a
stronger fn guarantee, "local policy" marks a choice the RFC leaves open.

SUB-001: a statement about an article travels as that article's `FN-Statement`
header field, whose value is the base64 of the detached `fn-stmt-` encoding —
the statement's own canonical octets, with the payload item omitted (§1.2).
RFC 5537 §3.6 is what carries it: a relaying agent MUST alter nothing but Path
and Xref, so an unknown header field crosses a peer that does not understand it
byte-identical. RFC 4648 §4 fixes the alphabet and padding and RFC 5536 §2.2
the folding. fn requires more than those RFCs do: every accepted field value
has exactly one canonical form, so no middle box can offer a second value that
decodes to the same statement and split a reader population. Local policy: the
8192-octet unfolded field bound, the 25-item budget, and the order in which
both are checked before any item is parsed.

SUB-002: the verdict on a statement is computed by the receiving node from the
received bytes and its own keyring alone, and is exactly one of `:verified`,
`:unverified` or `:absent` (§1.5). No RFC speaks to it. fn requires that the
peer is not an argument, that the `ref` be recomputed from the receiver's own
projection of the received octets, and that the verdict be stored with the
keyring generation under which it was computed, so a replay reproduces it
rather than inventing one. Local policy: which reasons accompany
`:unverified` (`:malformed`, `:ref-mismatch`, `:signature`), and that an
article whose statement is missing, malformed or unverifiable is still
accepted, stored byte-exact and relayed unchanged — it loses authority, not
bytes.

SUB-003: no peer can change the policy in force for a group at this node
(§3). The gate on a transit article is the policy function evaluated against
this node's lace and this node's keyring; a contact batch containing no
statement by the group's authority verified under the local keyring leaves the
policy in force equal before and after, and a change always names the signed
statement that caused it. RFC 5537 §5 would have an article carry an
executable control verb; fn implements none of them (§7), which is a stronger
guarantee than the RFC asks for. Local policy: the authority principal of a
group is local configuration and is never named on the wire (D11).

SUB-004: equivocation is detected when the statement merges at inbound
transit, recorded durably, and never dropped (§2.3). fn requires that both
forks of a reissued `(creator, incarnation, sequence)` slot stay in the lace —
evidence of a fork cannot be erased by a later merge — that the durable
`(:equivocation ...)` record be a proved twin of the lace rather than a second
authority, and that the equivocating article be accepted while its authority
is refused, with "accepted, authority refused" reported distinctly from
"refused" and from "uncertain". The single exception is explicit and is an
A-CRYPTO edge: two forks that collide in content id merge into one. Local
policy: the two typed refusal reasons, `:equivocation` and
`:authority-equivocation`.

SUB-005: merging the commits a reconnected peer carries never revises an
earlier admissibility decision (§4). What crosses a partition is commits and
fork evidence, never a roster: the merge extends the commits set, adoption of
a chain stays a local act, and every message admitted, refused or held before
the merge decides the same way after it. Learning more never turns a refusal
into an admission. No RFC is involved. fn requires that a commit enter the
merge only from a verified statement, which is the carrier obligation of S5-1;
local policy: the commits set is not pruned by this design (D13), and a held
message that exceeds the hold limit is a distinct `:capacity` outcome.

SUB-006: a reader exposes the statement bytes first and the node's verdict
second (§5). `ARTICLE` and `HEAD` return `FN-Statement` as an ordinary header
field, byte-identical after transit, so a client with its own keyring verifies
without trusting fn; the `:fn-verified` HDR metadata item reports what
acceptance recorded — one token per member of the verdict set, with the
principal id in hex and the keyring generation — and is never recomputed per
query. RFC 3977 §8.5 reserves the leading colon for exactly such a metadata
item, and §8.4 permits appended OVER fields; fn requires that no rendering
collapse two outcomes into one token. Local policy: whether the item is also
appended to OVER, which packet S6 decides with its cost quoted.

## What this design does not decide

The concrete digest and signature suites (D09) and the deployed realiser of the
crypto seam; how a keyring is persisted, distributed or revoked under partition
(the [decision packet](../planning/decision-packet-d09-d11.md)); who controls
group identity, and whether a group authority may be named on the wire at all
(D11 — this design deliberately keeps it local configuration); whether OVER
grows a field (S6 decides, with the cost quoted); the `preds` policy for
articles (how many predecessors an agent should name, and whether a node
refuses a statement whose predecessors it lacks — today it does not, and a
dependency-incomplete lace is bounded pending state per REP-002, not a refusal);
pruning of the commits set or the lace (D13); a wire form for withdrawal
statements; and any claim that a `verified` verdict means more than "this
principal signed these bytes under the key this node holds for it".

## 10. Status (packets S2 to S5, lane `w9/substrate`)

Certification state per root, with its evidence directory, is in
[`planning/lanes/HANDOFF-w9-substrate.md`](../planning/lanes/HANDOFF-w9-substrate.md)
and `tests/evidence/2026-09-20-substrate-transit.md`. Counts are generated;
this table carries obligations, not numbers. Everything below is recorded
open rather than weakened: no §6 statement was edited to make it provable.

| Keystone | State | The exact obligation, if open |
| --- | --- | --- |
| S2-1 grounding theorem | closed by S1 (`books/stx-invariants`) | — |
| S2-1 companion `fn-stx-transit-verdict-is-fn-stx-verdict` | **open** | `fn-peer-transfer` on this tree is `(node cfg peer msgid octets clock generation id subject)` and records provenance as the *string* `fn-peer-evidence` produces, not as a structured `(:peer-transit ...)` value. The equation needs a structured evidence value — either a slot in the article record (a shared-struct change, red umbrella) or an evidence value carried beside the node as the index is. Owner: this lane with the peering cluster. |
| S3-1 `fn-stx-transit-ids-are-union` | closed, as a labelled corollary of `fn-lace-merge-ids-are-union` and the bridge | — |
| S3-2 `fn-stx-transit-equivocation-is-detected` | closed, with both membership conjuncts | — |
| S3-2 `fn-stx-reissue-detected-after-peering` | **open, not attempted** | The statement names `fn-sys-run`, `fn-sys-node` and `fn-stx-complete-exchangep`; no two-node system model exists on this tree. Either the peering cluster lands one or the row is withdrawn in favour of the single-node fork witness in `tests/acl2/stx-transit-tests.lisp`, which exhibits both forks at one node but says nothing about two. |
| S3-2 `fn-stx-equivocation-record-agrees-with-lace` | closed as `fn-stx-recorded-equivocation-agrees-with-lace` | renamed only; the statement is the one in §6. |
| S3-3 `fn-stx-index-agrees-with-lace` | **open**: `books/stx-index` stops at `fn-stx-index-equivocators-agree`. The lookup and slot agreements (`fn-stx-index-bindings-agree`, `fn-stx-index-slots-agree`) and `fn-stx-equivocatorp-of-one-more` are admitted before it; what is left is the step that turns "the slot already held a different statement" into the lace's equivocator predicate, in both directions, over `fn-stx-index-of-store`. | The cost shadow is `fn-stx-index-lookup-cost-is-index-bounded` and `fn-stx-index-grows-by-at-most-one-binding`; `fn-stx-index-query-is-store-free-by-definition` is named for what it is. |
| S4-1 `fn-stx-transit-admit-is-fn-pol-admitp` | **renamed** `fn-stx-transit-admit-is-fn-pol-admitp-by-definition` | It is the unfolding of the gate's definition, and the assurance rule "cite keystones, never corollaries" forbids offering it as the proof event. The theorem-subject obligation it stands in for is the same host-line equation the S2-1 companion needs, and is open with it. |
| S4-1 `fn-stx-peer-batch-cannot-change-policy` | closed (`books/stx-policy` certified), over `fn-stx-accept-batch` and `fn-stx-batch-delta`, with the named-offender theorem. `fn-stx-authority-outcome` moved to `books/stx-authority`, which is open by cascade from the index. | — |
| S5-1 carrier obligation | **open**: `books/stx-epochs` stops at `fn-stx-commit-decode-is-a-commit`, the codec's own well-formedness lemma; `fn-stx-commits-of-batch-are-verified-and-well-formed` is stated and unreached. The five-item decoder and its guards are admitted. | — |
| S5-1 the two corollaries | stated, **not reached** (same book) | — |
| S6-1 `fn-stx-reader-verdict-is-the-recorded-verdict` | **open, and the wiring is not half-done** | There is no slot in which acceptance records a verdict: `fn-node-statep` is `(acceptance retention stage bindings)` and the article record is `(msgid payload groups memberships pin)`, so `fn-nntp-hdr-content (field article)` at `books/nntp-responses.lisp:1375` cannot reach one. Closing it means (a) a verdict log carried beside the node in the `fn-stx-index` pattern, (b) threading it through `fn-nntp-hdr-content` and its four callers, and (c) `(fn-nntp-keywordp token ":FN-VERIFIED")` at `books/nntp-responses.lisp:1322`. That is a red-umbrella change to a chain that is independently red at `books/nntp-effects.lisp:971`. Recomputing the verdict per HDR query was rejected: it needs a keyring on the reader path and contradicts "the reader reports what acceptance recorded". |

Three departures from the design text above, each recorded rather than
silently taken.

1. **The two typed reasons do not join `*fn-peer-reasons*`** (§2.3). Every
   member of that enumeration is a reason a transit *decision* refuses bytes,
   and an equivocating article must be accepted. `*fn-stx-authority-outcomes*`
   in `books/stx-policy.lisp` carries `:admitted`, `:refused`,
   `:equivocation` and `:authority-equivocation` on the authority axis, where
   a transit decision cannot spell them.
2. **The bridge lemma carries a freshness hypothesis.** Two articles with
   different Message-IDs can carry the same statement, and then the store
   grows while the lace's ids do not, so `fn-stx-lace` of the grown store is
   `(append lace delta)` and `fn-lace-merge` drops the duplicate. The
   hypothesis is exercised in both directions by the `:have` witness in the
   test book.
3. **`fn-inj-prefix` is not edited.** A node holds no principal's signing
   key, so a node that attached `FN-Statement` on a poster's behalf would be
   forging. The poster's client attaches it (`fn statement sign` then
   `fn statement attach`), and the ACL2 fact that licenses attaching it
   anywhere is S1's `fn-stx-payload-ignores-the-carrier-field`.
