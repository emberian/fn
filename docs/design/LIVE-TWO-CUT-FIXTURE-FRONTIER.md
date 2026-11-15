# Actual two-cut fixture frontier

`tests/checkpoint-live-two-cut-support.lisp` composes the real same-SIM
REGISTER/APPEND helper, actual persisted publication and ordinary executor
turns. It observes completion only from the combined active catalog/current
summary authority/C-base promise, consumed pending authority, IDLE snapshot
and writer, thawed allocator and completed master cleanup. No helper sets
APPLIED, authority, bank, phase or persistence outcomes.

The standalone456/a749 source still routes summary-authority-copy directly to
rebase/release; it cannot produce this completed-catalog predicate. The actual
typed route is506e346ed6518b1767af1cc19d5e61980ee8b43d, together with the coherent
compactor, bank, authorizer and callback providers. None is a runtime-positive
claim here. Activation remains NIL. The existing explicitly authorized
maintenance-entry fixture starts the real catalog continuation; automatic
scheduler admission is still unqualified and no flag is enabled.

Current served FNCT consumer codes0..18 and authority kind29 contain no DELETE
producer. The durable withdrawal layout alone is not a producer. A group-count
withdraw fold neither deletes ARTICLE/ADDR data nor proves that a new C base
omits payload children: ARTICLE latest values retain location/hash fields and
ADDR is unique. The reviewer owns the whole FETCH/META coverage-removal
fixture; it must obtain two actual completed catalogs and a real deletion or
replacement producer with matching semantic retention before claiming its
whole positive or hypothesis-removal witness.
