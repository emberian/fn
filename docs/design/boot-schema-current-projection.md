# Shared BOOT configuration

This projection replaces the inline `fn2-boot-config` declaration in current
`boot-kind` with its sole `boot-config-state` provider. The named transformation
removes only that declaration and `*fn2-boot-group-entry-bytes*`, then inserts
the provider include. All remaining BOOT forms are byte-preserved. The seven
original config fields are unchanged; the shared declaration also contains the
geometry and bootstrap receipt fields used by the lower producer.

The seven lower source files and real component fixture match the certified
40-book source at `17f802d449574e56ed28e2476cde42b119535e46`.
The [record receipt](receipts/boot-bootstrap-lower-forty-record.json) contains
all current raw hashes, closure keys and actual 8aeb certificate, compiled
payload, port and metadata hashes. Its six component assertions cover full
canonical comparison, corrupt bytes, nonzero padding, backing alias, owner
refusal and short input. Both lower verifier guard proofs are included.

The changed `boot-kind` has a 90-book dependency closure and still needs its own
current-key author and record gate. This projection preserves its existing
machine states, arms, budget and runtime bodies. It does not route BOOT through
the lower verifier or mint authority from expected bytes. The physical-family
owner must connect actual persisted read completion and prior genesis
verification to the shared verifier and receipt predicate, then continue the
bounded anchor and descriptor readers. That composed path remains unfinished.

`tools/boot_config_root_rewrite.py` is the extraction of record.
`tests/test_boot_config_projection_source.py` checks exact transformation,
idempotence, original fields, all 40 recorded inputs, and active component
assertion registration. These source controls do not certify `boot-kind`.
