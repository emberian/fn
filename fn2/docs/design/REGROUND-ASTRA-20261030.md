At dev `27978259c20a`, fn2 has a bounded-machine framework and a partial native NNTP server. It does **not yet have a durable served transaction**: admission returns `:not-served` ([txn.lisp:215](/Users/ember/dev/fn/fn2/books/txn.lisp:215)). Today’s review is already partly superseded—native sockets, recovery and the sealer now exist—but its larger concern survives: implementation progress has become easier to recognize than progress toward the intended system.

Ember’s dream was “the persistent event log between systems,” foundational “orthogonal persistence,” and a “high performance database node”—“generalized redis/postgres for the datamodels we’re reaching for.” The method was a “metaprogramming approch that lets us express the whole thing very succinctly,” built “semantics-first” until there is an implementation worth assuring. These are [ember’s words](/Users/ember/dev/fn/build/coordinator/EMBER.md:427), not retrospective justification for the current architecture.

The distinguishing promise is their combination: persistent worlds that humans and agents can consume, revise, fork and transport; obligations, identity and authority surviving those movements; useful operation across disconnected peers. “BP is product.” Mechanical sympathy means reasoning about I/O counts, locality and burstiness. Early service means exercising composition while designing it. Consumers and peering must therefore shape the kernel, rather than arrive as protocol accessories.

Against the [twenty sentences](/Users/ember/dev/fn/build/coordinator/fn2/EMBER-ARCHITECTURE-WORDS.md:450), “kept” below means the implementation direction survives, not that assurance is complete:

| # / commitment | Built |
|---|---|
| 1. Persistent log between systems | **Bent:** no durable served append yet; transaction admission is a stub cited above. |
| 2. Best hybrid persistent representation | **Bent:** the sealer retains **every sealed page** in cache; its durable device half remains outstanding ([sealer.lisp:1](/Users/ember/dev/fn/fn2/books/sealer.lisp:1)). |
| 3. Bounded, metered, backpressure-safe service | **Kept, incompletely:** explicit machine budgets, holdings and continuations exist ([conn.lisp:39](/Users/ember/dev/fn/fn2/books/conn.lisp:39)). |
| 4. All resources accounted upfront | **Bent:** accounts cover two holding dimensions and five charges, not storage, custody, crypto and maintenance liability ([accounts.lisp:22](/Users/ember/dev/fn/fn2/books/accounts.lisp:22)). |
| 5. BP is product | **Never started as served machinery:** E5 remains downstream of CLI/config ([release graph:310](/Users/ember/dev/fn/build/coordinator/fn2/RELEASE-PLAN.md:310)). |
| 6. Arbitrary clients cannot crash us; correct semantics | **Bent:** checked connection machinery coexists with an entirely `:unchecked` commit machine ([machines-b.lisp:169](/Users/ember/dev/fn/fn2/books/machines-b.lisp:169)). |
| 7. Configuration and assured reconfiguration | **Never started as live reconfiguration:** a configuration-change record exists, not its operational lifecycle ([format-events.lisp:53](/Users/ember/dev/fn/fn2/books/format-events.lisp:53)). |
| 8. No runtime octet lists | **Kept in the core:** concrete pool ranges; list views are logical ([A:78](/Users/ember/dev/fn/fn2/docs/a-pool-host-sim.md:78)). |
| 9. No arbitrary stored-data ceilings | **Bent:** six cross-post groups are hardwired to fit successor slots ([txn.lisp:28](/Users/ember/dev/fn/fn2/books/txn.lisp:28)). |
| 10. Escape wasteful serialization | **Bent:** shared range layouts help, but a working orthogonally persistent representation has not emerged; the device boundary remains absent. |
| 11. Realistic laggy storage | **Kept in modeling; unexercised natively:** storage operations have no native backend ([adapter.lisp:175](/Users/ember/dev/fn/fn2/host/adapter.lisp:175)). |
| 12. Sophisticated crashes | **Kept in direction:** recovery now exists; checkpoints, persisted writer epochs and read-misdirection retry remain missing ([B:1107](/Users/ember/dev/fn/fn2/docs/b-durability.md:1107)). |
| 13. Remove legacy formats/migrations | **Kept:** clean replacement remains the release strategy. |
| 14. Performance through counts/locality/burstiness | **Bent:** native polling allocates arrays and scans capacity-sized tables ([adapter.lisp:249](/Users/ember/dev/fn/fn2/host/adapter.lisp:249)). |
| 15. No Python inside fn | **Kept:** the native process is Lisp—currently still the ACL2 runtime ([adapter.lisp:380](/Users/ember/dev/fn/fn2/host/adapter.lisp:380)). |
| 16. Self-contained web reader | **Never started as a served surface:** E7 remains downstream. |
| 17. Ship working postquantum support | **Never started as served TLS:** TLS-start explicitly fails ([adapter.lisp:172](/Users/ember/dev/fn/fn2/host/adapter.lisp:172)). |
| 18. Repetition becomes macros | **Bent:** useful generators coexist with hand-declared multidimensional arrays and their duplicate facts ([accounts.lisp:51](/Users/ember/dev/fn/fn2/books/accounts.lisp:51)). |
| 19. Semantics first; top-level nonvacuity | **Kept as proof policy; bent as attention:** statements can remain owed, but local evidence production dominates visible milestones. |
| 20. Fix forward without full-proof gates | **Kept:** recent repairs improve the implementation instead of requiring completed assurance ([C:768](/Users/ember/dev/fn/fn2/docs/c-ordered-runs.md:768)). |

The lanes optimized local closure: admissible books, bounded arms, populated obligation rows, generated evidence and NNTP compatibility. These are useful, but they became substitutes for composing a useful operation. The clearest example is Q1: the independent upload contract explicitly maps an acceptable article to interim **“441 posting failed”** ([q1-contracts.lisp:335](/Users/ember/dev/fn/fn2/tests/q1-contracts.lisp:335), [372](/Users/ember/dev/fn/fn2/tests/q1-contracts.lisp:372)). That honestly tests an intermediate behavior; it cannot establish the intended service.

There are two different omissions. BP, peering, Mini/helm cursor–ack service and the web face **have quests**, but the graph postpones their architectural pressure. The projection/live/fast planes and the wider fork/transport/revision/port/meter/grant kernel lack corresponding executable quests. The wider design explicitly asks for envelope fields **now** ([WIDEST-ROLE:36](/Users/ember/dev/fn/build/coordinator/fn2/WIDEST-ROLE.md:36)); the actual event header carries kind, schema version and event number ([format-events.lisp:12](/Users/ember/dev/fn/fn2/books/format-events.lisp:12)).

Extraction similarly has no quest; the gate document recommends retiring the inherited gate without supplying a runtime replacement ([release-gates:357](/Users/ember/dev/fn/fn2/docs/release-gates.md:357)). The DSL is being tested for what it can generate, insufficiently for how succinctly an author can express a complete subsystem.

The ten missing pieces of substance are:

1. **Durable service — B/C/D/host:** compose POST, recovery, cold reads and reclamation; existing forms largely suffice, but the composition is missing.
2. **World domains and forks — B/C:** lineage, occurrence, revision, payer and grant must survive storage; missing domain/envelope forms.
3. **Revision and transport — C/D/E:** carry state, cursors and outstanding obligations through fenced movement; missing revision/transfer forms.
4. **General projections — C:** coverage, historical reads, bootstrap and declared loss must be operational; extend today’s arithmetic fold form.
5. **Live and fast planes — A/C/D:** express ordering, durability and scheduling choices beyond the durable log; missing plane contracts.
6. **Mini/helm consumption — C/D/E:** serve authenticated registration, wait/poll/ack, backfill and revocation; existing forms need richer cursor/query composition.
7. **Peering — B/C/E:** exchange validated history and resolve locality of acceptance decisions; transport forms and reconciliation contracts are missing.
8. **BP/DTN — A/B/E:** contacts, custody, retries and discharge evidence must consume reserved resources; existing machines/obligations need contact and custody forms.
9. **Authority and liability — A/C/D:** implement grant derivation and principal-tree accounting across every resource; missing Grant/Meter forms.
10. **Usable native product — A/D/E:** supply the chosen runtime, TLS, configuration and embedded web surface; existing grammars help, but runtime lowering and shared port generation remain missing.

Stop treating ledger growth, mirrored documents and isolated component readiness as architectural completion. Keep the concrete pool, explicit uncertainty, generated machines/layouts, independent behavioral contracts and fix-forward discipline. Complete durable service first, **while** bringing consumer, peer and BP contract producers alongside it; then compose one agent workflow across two nodes, including disconnection, recovery and acknowledgement. Bring the web face into that workflow. Measure allocations, copies, I/O and maintenance amplification before freezing representations.

The spine-first rule should bend wherever a downstream use can invalidate an upstream interface. It should not require building every dream feature immediately. It should require an executable counterpressure example before declaring the spine stable.

Three designs need revisiting before further elaboration:

- **World and identity semantics:** decide which choices are domain-local and what peers converge on; today’s identity theorem assumes the same accepted/evidence states, explicitly excluding opposite first arrivals ([identity.lisp:776](/Users/ember/dev/fn/fn2/books/identity.lisp:776)).
- **Physical execution and DSL:** representations must accommodate semantics; omitting read retry because all 24 fields are occupied reverses that relationship ([B:1112](/Users/ember/dev/fn/fn2/docs/b-durability.md:1112)).
- **Consumer/projection contracts:** reconcile exact versus threshold reads, multidomain cuts and retained history; also fix the selection design that scans every edge while claiming work independent of clean subscriptions ([INBOX:229](/Users/ember/dev/fn/build/coordinator/fn2/INBOX-DELIVERY.md:229)).

Finally, remove the release plan’s stale BP and Linux-only fallbacks: ember already ruled for BP completion and OpenBSD as a prime deployment target ([EMBER:473](/Users/ember/dev/fn/build/coordinator/EMBER.md:473)).