# Store-v6 selector/export interface, 2026-09-24

`books/store-node.lisp` carries a fourteen-field positional state with
versioned constructors and a configuration updater built from `update-nth`.
It does not fit `fn-defrecord`'s single-constructor form, so the representation
stays hand-written. The export now withdraws the `:definition` runes of
`fn-sn-make-v6`, `fn-sn-with-configuration`, `fn-sn-with-consumer`,
`fn-sn-with-topic`, `fn-sn-with-event-index`, and `fn-sn-update-replayed`.
Executable counterparts and guards are unchanged. `fn-sn-update` remains
enabled as the book's documented glue/induction vocabulary.

The existing `fn-sn-fields-of-fn-sn-make-v6` constructor theorem now includes
the previously missing event-index field. Selector laws over the three
projection updaters and replay updater expose their shape, core state fields,
index, configuration history, and the changed or carried consumer/topic/event
index. The configuration updater already has a general unselected-slot law
and selected field laws; these remain exported. Existing downstream laws in
`store-node-invariants` remain in place. No runtime definition or existing
proof hypothesis was weakened.

The first selected dependency run on the pre-guard source
`run-20260924T043102Z-a695` stopped at `fn-sn-io-preserves-state`: the closed
event-index updater left the shape of a nested v6 constructor hidden. In a
bounded hbox REPL on the source containing the retention-guard and Store
proof-cost commits, added shape/core selector laws admitted the unchanged
state theorem. The next REPL stop, `fn-sn-io-preserves-indexedp`, was the
index projection of `fn-sn-with-event-index`; sending that exact field law
and resending the unchanged theorem proved it in 0.16 seconds. The final
174-form `store-node-invariants` REPL loaded without refusal before the
selected certification.

On hbox, ACL2 8.7/SBCL 2.6.8 with pinned w28 toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
the exact-source Store book passed one-job
`run-20260924T044316Z-43d8`
([manifest](manifests/certify-20260924T044319Z-907134.json)), 24.786 seconds
book wall time. Five dependent roots passed two-job
`run-20260924T044521Z-b90d`
([manifest](manifests/certify-20260924T044525Z-910229.json)): Store
invariants 64.186 seconds, Store traces 49.062 seconds, consumer event-index
Store invariants 76.730 seconds, and the Store-node and consumer event-index
test books. The dependent run kept 70 content/toolchain-matched certificates
from the shared cache and certified five roots. In the earlier same-toolchain
Store cost packet ([manifest](manifests/certify-20260924T042336Z-883128.json)),
Store invariants and traces took 86.919 and 52.013 seconds respectively;
those source closures differ, so these figures show that the new export did
not recreate their earlier proof explosion, rather than an isolated timing
benchmark. `make check` passed.

`green_check --changed-since f765ee34 --strict` reports four changed books
including the already integrated retention-guard and Store cost packets,
with 169 dependents and 167 not green at this lane's bytes. This selected
run covers the defining book, its invariants and traces, and one direct
consumer; the next frozen combined gate must test the wider dependent
closure. The material risk is that an older downstream proof relied on one
of the six newly closed definitions instead of a selector law. Such a proof
must use an exported law or open that updater in its own hint; its theorem
statement and runtime behavior are unchanged.
