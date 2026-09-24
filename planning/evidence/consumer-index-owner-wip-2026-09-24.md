# Indexed owner poll source checkpoint

`books/consumer-owner-local.lisp` now includes `consumer-poll-index` and changes the actual `fn-col-poll` call to materialize at most sixteen committed events by the Store's derived sequence index, then passes that window to the unchanged `fn-col-poll-scan`. The output cursor, report, refusal, and no-ack semantics are unchanged by construction. The lower indexed-window correspondence and budget theorem are ACL2 certified; this actual owner caller has **not** been certified on the topic/slot13 union. Its include closure currently stops at the independently red topic `store-node-resolution`/`store-observed` relation work. No native indexed-poll claim follows from this checkpoint.

The accompanying owner test source is copied unchanged from the currently served owner poll test. It exercises published bootstrap, registration, and article through the actual owner call; it remains to be certified against the combined topic/index source. The required next proof is a reachable Store relation carrying `fn-ceis-relatedp` through the mixed Store dispatcher and observed open, followed by the owner caller equivalence and a source-matched native fixture. The derived index is not durable authority; recovery builds it from exact Store events.

Store slot13 proof checkpoint: `books/store-node-invariants.lisp` now has local
v6 constructor and projection-preservation facts, plus scoped hints that keep
the new Store copies closed. On hbox run `run-20260924T013056Z-a2b1`
(`certify-20260924T013100Z-698972.json`), ACL2 admitted preparation, I/O,
finish, verdict, crash, and recovery state-preservation theorems, then failed
at `FN-SN-FINISH-IS-ACTUAL-DURABLE-COMPLETION` with a large raw v6/slot13
constructor goal. This packet is **unqualified**: neither that invariant book
nor its reverse closure passed. The topic lane's separate proof-only
`a9f22ade` has certified corrected topic deferred relation, but is not yet in
this source snapshot. No full owner or native index claim follows.
