# Indexed owner poll source checkpoint

`books/consumer-owner-local.lisp` now includes `consumer-poll-index` and changes the actual `fn-col-poll` call to materialize at most sixteen committed events by the Store's derived sequence index, then passes that window to the unchanged `fn-col-poll-scan`. The output cursor, report, refusal, and no-ack semantics are unchanged by construction. The lower indexed-window correspondence and budget theorem are ACL2 certified; this actual owner caller has **not** been certified on the topic/slot13 union. Its include closure currently stops at the independently red topic `store-node-resolution`/`store-observed` relation work. No native indexed-poll claim follows from this checkpoint.

The accompanying owner test source is copied unchanged from the currently served owner poll test. It exercises published bootstrap, registration, and article through the actual owner call; it remains to be certified against the combined topic/index source. The required next proof is a reachable Store relation carrying `fn-ceis-relatedp` through the mixed Store dispatcher and observed open, followed by the owner caller equivalence and a source-matched native fixture. The derived index is not durable authority; recovery builds it from exact Store events.

Store slot13 proof checkpoint: `books/store-node-invariants.lisp` now has local
v6 constructor and projection-preservation facts, plus scoped hints that keep
the new Store copies closed. Hbox run `run-20260924T015835Z-d5f8`
(`certify-20260924T015838Z-719858.json`) admitted preparation, I/O, finish,
verdict, crash, recovery, the exact durable completion pair, all indexed
prepare/I/O facts, and all finish-arm field lemmas. It reached
`FN-SN-FINISH-TOPIC-COMPLETION` and hit the configured 120-second limit;
the current bounded retry closes the raw v6 constructor in that theorem.
This packet is **unqualified**: neither the invariant book nor its reverse
closure passed. The combined source now includes the topic lane's corrected
deferred relation and observed/config recovery patch, but no full owner or
native index claim follows.
