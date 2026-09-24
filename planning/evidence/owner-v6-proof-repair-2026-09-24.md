# Owner invariants after the Store v6 join

Source `d292536e` preserves every public theorem statement in
`books/owner-invariants.lisp`. The idle/replay lemma now opens only the
relation and idle selector. Local configuration projection lemmas use the
existing v6 field facts and cover the new topic/event-index updaters and
topic preparation. No executable Store or owner definition changes.

The frozen `8c61c098` combined run was deliberately bounded at the idle
lemma after 398.14 seconds without a completed proof. On the same hbox w28
toolchain, the unchanged statement admitted in a proof REPL in 0.00 seconds
and 127 prover steps. The REPL installed a complete compatible set of 120
dependencies from composed cache origins; this did not require a single-origin
cache or relaxed certificate checking. Sessions were stopped after use.

The first scoped certification exposed a separate omitted v6 constructor
projection in a local configuration helper. Its original failed manifest
`certify-20260924T034847Z-819574.json` is retained. After that repair, the
whole owner book, owner-fault dependency and owner test passed in hbox run
`run-20260924T035603Z-d5a6`, manifest
`certify-20260924T035614Z-836608.json`, at
`/tank/fn/gates/owner-v6-final-20260924`. The command requested
`books/owner-invariants tests/acl2/owner-tests`, two jobs, a 120-second
per-invocation bound, w28 ACL2 and `/tank/fn/certcache`; 123 compatible
dependencies were reused and three books certified.

The run took 39.757 seconds, including an owner book wall of 31.709 seconds,
owner-fault 3.497 seconds and owner tests 4.497 seconds. This remains above
the per-book ten-second target: the largest completed owner events were
reopen preservation (6.64 seconds) and durable-reply correspondence
(5.98 seconds). The repair removes the unbounded expansion finding; it does
not establish that all owner proofs or the whole project meet the cost target.

The full combined dependent closure and source-matched native image remain
root's convergence gates. This scoped certification does not qualify the
new topic, consumer or BP runtime composition by itself.
