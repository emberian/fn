# Served authority: principals and grants (ruling of record, 2026-11-05)

Adopted by the fn2 deputy on 2026-11-05 from Astra's consultation (GRANT-ASTRA.last.md, below verbatim), with these fixings:
1. Schema ids 16-19 (`fn2-principals`, `fn2-grants`, `fn2-grant-current`, `fn2-authority-head`) and FNCT request kind 29 / reply kind 30 are the allocations, no longer proposals.
2. `"reader"` in Mini's world is the persisted anonymous principal.
3. Withdrawal authority is the authenticated original submitter or the node administrator.
4. The consumer model's ordering is corrected: retry (outcome) lookup precedes append admission, with a witness.
5. The keystone `fn2-authority-served-enforced` is CRITICAL (authorization, identity-binding) and ships with Ruling 22's whole evidence package.
Lane `authority` (branch `lane/authority`) implements it; the text below is the design, not a claim about the tree.
Where the tree and this text differ, the lane's commits and `docs/e-surface.md` say which, as present state.

**Ruling proposed:** serve durable, named principals and owner-issued grants now. Keep the owner-only Unix socket, but add an explicit connection binding to a named principal. This gives Mini and origin distinct authority, accounting, cursor and retry namespaces on one laptop. It does **not** isolate mutually hostile processes running as the owner’s UID; E2 credentials can later replace the binding mechanism without replacing principals or grants.

All new forms below are proposals for `39d8deda748dd708da13f40d4aa96548b5a04d2d`, not claims about implemented code.

**1. Principal binding**

The kernel UID is authentication evidence for the **node administrator**, not the durable principal identifier.

- `host/ffi.lisp` continues reporting `getpeereid`/`SO_PEERCRED` observations.
- `books/cns.lisp` checks family and UID in ACL2, as today.
- Successful admission binds the connection to a persisted owner principal. Keep that distinct from anonymous slot 0.
- An owner connection can issue `principal-bind NAME` once, before consumer work. It then acts exclusively as that principal: no grant administration, posture changes or further binding on that connection.
- Binding is connection state, not a durable mutation. Reconnection repeats it.
- Store both the authenticated basis (`:local-owner`) and effective durable principal. Never accept a principal field in ordinary consumer requests.
- A same-UID process can open another administrator connection. Describe this as **owner-delegated local execution**, not independent credential authentication.

Use D7’s existing identity:

```lisp
(fn2-account-principal-id slot fn2-accounts)
; slot * 2^32 + incarnation
```

Carry `principal-id` separately from `principal-slot`. The latter schedules and charges; the former keys grants, consumers, outcomes and attribution. Persist allocation/incarnation state and restore it before admitting connections. Rebinding a slot cannot resurrect an old principal.

Proposed bootstrap: persisted `"anonymous"` and `"owner"` principals, created once during store genesis. Profile configuration supplies the owner UID and account capacities; changing the profile must not silently rename durable identities. `principal-create` creates `"mini"` and `"origin"` through the served administrator path.

An unauthenticated NNTP connection uses the anonymous principal. For M2, Mini’s model name `"reader"` maps to that principal; grant it read access to the two demonstration groups. It receives no append or consumer-management right. An authenticated NNTP connection later binds to the same principal IDs through E2 credential verification. `From:`, `Message-ID`, source signatures and payer identity do not authenticate that connection.

**2. Durable records and C’s schemas**

Use a new `books/authority-schema.lisp`, layer C. These are ordered authorization decisions, **not** entries in `books/identity.lisp`’s Message-ID/content Binding relation. `books/accounts*.lisp` remains the ledger and resident account machinery.

Proposed schema allocations 16–19 follow the current 1–15 catalog:

```lisp
(defrunschema fn2-principals :id 16
 :key ((name (:octets 64)))
 :value ((principal (:id principal)))
 :merge :unique)

(defrunschema fn2-grants :id 17
 :key ((grant (:id grant)))
 :value ((grantor (:id principal))
         (grantee (:id principal))
         (right (:enum fn2-authority-right (:consume :read :append)))
         (scope (:enum fn2-authority-scope (:own-consumers :stream)))
         (target (:id stream))
         (enabled :bool)
         (previous (:id grant)))
 :merge :unique)

(defrunschema fn2-grant-current :id 18
 :key ((grantee (:id principal))
       (right (:enum fn2-authority-right (:consume :read :append)))
       (scope (:enum fn2-authority-scope (:own-consumers :stream)))
       (target (:id stream)))
 :value ((grant (:id grant)))
 :merge :latest)

(defrunschema fn2-authority-head :id 19
 :key ((principal (:id principal)))
 :value ((grant (:id grant)))
 :merge :latest)
```

Semantic constraints:

- One right per grant row. `:consume` requires `:own-consumers`, target 0; `:read`/`:append` require `:stream` and a resolved stream ID. Target 0 is not a wildcard.
- `:consume` covers register/rebase/unregister/ack/position/status in the caller’s namespace. Preserve the existing port; do not invent a fourth `:ack` right.
- M2 permits only the owner principal as grantor. Recipients cannot delegate.
- Grant ID is the grant mutation’s commit event, hence also its revision. `previous` is the grantee’s preceding authority-head, or 0.
- A grant mutation atomically appends the immutable row, replaces the affected current pointer, advances authority-head, and records its operation outcome.
- Disabled rows are revocations; retain them and their dependencies.
- `:latest` means local committed order, never wall-clock last-writer-wins. Validate the expected authority-head in the private successor before staging.
- Declare the current/head interpretations as folds over the immutable grant events. Their invariant is that they equal that interpretation.
- Exact reads use the current pointer and immutable row. Historical interpretation follows the predecessor chain; normal requests never walk that chain.

This makes authority-head an immutable reference to the principal’s complete grant-state revision, although each event changes one right. B’s envelope `grant` can name that revision, including when an append requires several stream grants. Retain the referenced history or an equivalent authenticated summary across compaction.

`books/format-base.lisp`, `books/format-events.lisp` and `books/commit-format.lisp` own the corresponding record-kind/layout integration; `books/runs-served.lisp` registers the schemas. Extend the declarations and generated catalog, not scattered numeric tests. Each kind lands with its served producer.

For unsigned local operations, envelope `author = 0`; a principal is not an author key. `payer` is the effective durable principal, and `grant` is the authority revision used. Administrator bootstrap authority is explicitly the persisted owner configuration, not a fabricated signed grant.

**3. Producer verbs and replies**

New E books:

- `books/authority-port.lisp`: operation declarations and carrier bindings.
- `books/authority-codec.lisp`: generated `deflayout` codecs.
- `books/authority-kind.lisp`: request-kind declaration.
- `books/authority.lisp`: machine arms, bounded authorization operations and transaction orchestration.

Reserve FNCT request kind **29**, reply kind **30** for this family; retain the existing FNCT v1 header and BLAKE3 trailer. These numbers are proposed allocations.

Decoded request payloads:

```text
0 principal-create  name
1 principal-bind    name
2 grant-set         grantee right scope target enabled expected-head op
3 grant-get         grantee right scope target
4 stream-resolve    stream-name
```

Types: stream-name = nonempty length-prefixed group-name octets, maximum 250; name/op = nonempty length-prefixed octets, maximum 64; principal/target/head = their typed `(:id ...)` codecs; right/scope = the enums above; enabled = boolean. The opcode is one octet. No Lisp reader.

Reply payload: opcode, existing status enum, length-prefixed reason word ≤64 octets, then exactly the declared result:

```text
principal-create accepted: (principal)
principal-bind   accepted: (principal authority-head)
grant-set        accepted: (grant authority-head receipt)
grant-get        accepted: (found authority-head [grant grantor enabled previous])
stream-resolve   accepted: (target)
```

The bracketed fields occur iff `found = 1`. `found = 0` is a successful absent lookup, not a grant.

```text
refused:   access | frame | unknown-principal | unknown-stream |
           scope | stale-revision | operation-reused | operation-expired | meter
uncertain: persistence
```

Declare reasons per verb; `principal-bind`, `grant-get`, and `stream-resolve` cannot answer uncertain. A failed frame must not default to another verb.

Semantics:

- `principal-create NAME`: owner only; repeated name returns its recorded identity. No deletion/reuse in this slice.
- `principal-bind NAME`: owner connection only; read existing identity, acquire its required D7 holdings, atomically transfer connection ownership, then answer. Failed transfer leaves the prior binding intact. Existing charges remain with their original payer.
- `grant-set`: owner only; grantor comes from the connection, never the payload. Mandatory `op` uses the shared durable outcome mechanism, with verb and complete request included in its digest.
- Retry lookup precedes expected-head checking. Same operation/request returns its recorded result; contradictory reuse refuses. A new operation with a stale expected-head refuses.
- `grant-get`: administrator or the named grantee only. Read current/head at one committed cut and return the immutable row they identify.

`grant-set` is a real durable transaction through the existing C successor/B persistence path. Accepted means recoverable publication; an ambiguous write fences into recovery and answers uncertain when possible. It is not `fn2-*-put` followed by an in-memory publish.

Mini’s `:grant` world step becomes a **client invocation of `grant-set` on an administrator connection**. It must consume and judge the wire reply.

**4. Where authority is checked**

The logical E operation is:

```lisp
(fn2-grant-allows principal scope view)
; scope examples:
; (:consume :own-consumers 0)
; (:read :stream stream-id)
; (:append :stream stream-id)
```

`view` names a committed authority revision and its concrete read context. Guard-verified served operations refine this predicate using C’s exact reads in `books/machines-c-read.lisp`. A request carries a continuation when the read needs I/O.

In `books/cns.lisp`:

| Operation | Required decision |
|---|---|
| register/rebase | Current consume grant; caller-owned namespace; canonical query; record current authority-head in cursor/view |
| read/wait | Current consume grant for the consumer surface; current cursor/view; per-item read grant through an article’s own stream |
| ack | Current consume grant; own consumer/epoch; current authority-head; existing monotonicity/frontier rules |
| position/status/unregister | Current consume grant and own consumer |
| fetch | Current consumer-surface admission and read grant through the referenced article’s own streams |

Registration selects streams; it grants no access. Preserve the model’s ability to register a query whose currently unauthorized streams contribute no items. Do not reveal whether a hidden stream/article exists. An `addr` hit never substitutes for read authority.

Any authority revision change invalidates the grantee’s old read/wait/ack view: `rebase-required` while consume remains allowed; `access` if consume was revoked. Rebase `:keep` adopts current authority without rewinding the recorded position.

Grant publication wakes affected parked requests through a per-principal dependency list, drained in bounded steps. Recheck authority after every park and before handing an answer to the carrier. Define answer linearization at that final check/freeze; bytes already issued cannot be retroactively recalled. Test revoke between selection and handoff.

For append, `books/upload-kind.lisp`, `books/upload.lisp`, `books/txn-kind.lisp`, `books/txn.lisp` and their existing assembly callback books own the `:consumer` mode:

```text
bound principal
→ lookup outcome(principal, op), compare complete request identity
→ if no outcome: current append grants for EVERY destination group
→ meter/reservation
→ upload → fn2-txn → durable publication → consumer result
```

Consumer and NNTP POST share that transaction decision. Recheck after reservation waits and serialize the final authority dependency against grant changes at commit eligibility. A grant revocation ordered before the append prevents acceptance; one ordered after it does not undo the accepted article.

Bind the transaction’s principal and reply destination from its owning connection/request generation. Never let `fn2-cns` stage a second article path. Preserve the complete append result: Message-ID, position, numbers and receipt.

**5. Exactly what Mini requires**

`tests/consumer-mini.lisp` supplies these seven initial facts:

```lisp
(:grant "mini"   :consume :any)
(:grant "mini"   :read   "dregg.fn.e1")
(:grant "mini"   :read   "dregg.fn.e1.reply")
(:grant "mini"   :append "dregg.fn.e1.reply")
(:grant "origin" :append "dregg.fn.e1")
(:grant "reader" :read   "dregg.fn.e1")
(:grant "reader" :read   "dregg.fn.e1.reply")
```

Translate `:any` to Mini’s `(:consume :own-consumers 0)`, not universal access. Resolve group names through the read-only `stream-resolve` authority verb (FNCT kind 29, opcode 4), which queries `fn2-groups` in bounded lookup steps. Its request is a length-prefixed stream name (the existing 250-octet group-name limit); its accepted result is the stream ID, and an absent name refuses `unknown-stream`. It does not bind a principal or mutate grants. The CLI must propagate refusal or transport failure without consulting `.groups` sidecars or inventing a default ID; map `"reader"` to anonymous. Resolve returned principal IDs rather than hard-coding slots.

`tests/m2-cuts.lisp` needs administrator, Mini and origin control connections, plus the NNTP reader. Configure funded account/connection rows accordingly. Create/bind principals, issue all seven grants, verify their replies/readbacks, then run the existing scripts.

| Cuts | Authority requirement beyond initialization |
|---|---|
| c0, c1, c3, c4, c7, c9, c10 | Stable initial grants; correct principal/cursor/outcome isolation |
| c2 | Stable grants in the actual script; retry must return Q’s original outcome |
| c5, c8 | Served origin withdrawal with authenticated attribution |
| c6 | Recover principal identities, grants, cursor and outcome atomically; reconnect/rebind; discard old waits |
| c11 | An authorized maintenance reclamation, then fetch/gap behavior |

The model’s withdrawal rule is **not absent**: `fn2-cns-withdraw` requires the caller to equal the target article’s recorded author. What it leaves open is how that caller was authenticated and how the rule becomes a served cancellation authority. Adopt authenticated original local submitter, or node administrator, for this slice; do not infer cancel authority merely from append permission or a forged `From:`.

c11’s `(:reclaim nil 1)` has no authorization semantics. It is an administrator/storage-maintenance action, not a consumer right.

No cut changes a grant after setup. In particular, despite `docs/e-surface.md` §3.3 citing c2, c2 does **not** test retry after revocation. Moreover, `books/consumer-model.lisp` currently tests append admission before using the prior outcome. Correct that model ordering to match the ruled spec and add the missing witness.

Authority plus D’s append mode and E’s items will not alone make all twelve pass: withdrawal, reclamation, crash/recovery and actual NNTP readback remain necessary. The current driver also needs real requests/results, group-edge selection instead of the poster’s `addr` alone, and removal of its unconditional unsupported-step reasons.

**6. Fixtures and owed statements**

Add `tests/authority-served.lisp`, driven through `fn2-turn`, FNCT and the adapter, with these named witnesses:

```text
fn2-authority-local-binding-positive
  Same kernel UID; distinct Mini/origin durable IDs, ledger attribution,
  consumer namespaces and op namespaces; cross-principal cursor rejected.

fn2-authority-grant-roundtrip-positive
  Served create/set/get; seven Mini grants; restart recovers exact identities
  and revisions; same grant op adds no event or charge.

fn2-authority-current-positive
  Authorized item delivered; denied-room mention hidden; parked wait sees
  grant change; old view refused; rebase adopts it; revocation stops delivery.

fn2-authority-append-retry-after-revoke-positive
  Q commits, reply lost, append right revoked, identical retry returns the
  original result; a fresh op refuses; changed request refuses operation-reused.

fn2-authority-commit-race-positive
  Revoke ordered before commit eligibility prevents fresh append;
  revoke ordered after accepted append preserves its recorded outcome.

fn2-authority-crash-positive
  Process-death cuts around grant persistence/publication/reply:
  recover old or complete new state, never a grant without its head/outcome.
```

Controls must exercise served branches: forged principal, inherited owner privilege after binding, `:pinned-grant`, `:addr-authorizes`, stale authority after reservation wait, grant-before-retry, acceptance-before-durable, slot-incarnation aliasing. Each control must fail the corresponding positive trace’s predicate.

Keep K7 `fn2-cns-authority-current` in `books/owed-consumer.lisp`; its present statement is over the model. Add a served authority obligation in proposed `books/owed-authority.lisp` whose subject is the actual `fn2-turn` trace:

```text
For every reachable served trace from a valid persisted authority state:
each delivered item is readable through its own streams by the bound principal
at answer linearization;
each new committed append has authority for every destination at commit eligibility;
each consumer mutation belongs to that principal;
and each effective grant mutation was issued by the authenticated administrator.
```

Name it `fn2-authority-served-enforced`, with named concrete-to-model refinement obligations for principal binding, grant lookup and grant publication. Link K7 and K10 to those operations; an unconstrained observation function is not the served proof.

Treat this as **CRITICAL authorization and identity-binding**. Supply the whole evidence package: positive witnesses asserting the whole antecedent and conclusion; explicit hypothesis-removal witnesses showing unauthorized delivery/commit when binding, current-grant validation or publication coherence is removed; reachable composed paths; exact producer/refinement subject. Mutation tests supplement those witnesses; they do not substitute for them.

Export the obligations into `docs/OWED.md`; update `docs/e-surface.md`, `docs/c-ordered-runs.md`, `docs/d-machines-nntp.md` and `docs/b-durability.md` at their owned seams. Preserve K8’s distinction between refused semantic mutation/reservations and already-incurred parsing/I/O work.

**Verification limits:** I inspected the named model, cuts, served control/consumer code, ledger identity machinery, schemas, codecs, envelope and identity rulings at the stated commit. I ran no tests or certification and wrote no files. The older `docs/README.md`, `docs/architecture.md`, `planning/decisions.md` and `tools/keystone_critical_map.json` are absent here. New schema/wire allocations and declaration forms above require integration checks against concurrent lanes; they are not certified expansions.