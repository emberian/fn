# Native peering qualification — `915d5c72`

The production image built on `persvati` from source
`915d5c729877eddee7dd3f72eadad21cca463d1a` ran two native owner processes
over private loopback listeners and ephemeral stores. Python was only the
external driver. No installed service or public listener was changed.

The immutable image copy is
`/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host`:

- launcher SHA-256: `3e989879fc615fab5c929e05c3215768cc6c4b707b7ac123b20aed13f930045f`
- core SHA-256: `eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2`
- certificate artifact set: `3759213a0737c0153ef703f16b6187ccd67ad44e8f51bde4c0a2258a177e1bea`
- qualified ACL2 wrapper: `/home/ember/fn-gates/toolchains/w25/acl2-literal`

`tests.test_native_peering` passed three cases: public operator configuration
and A-to-B byte-identical transfer with duplicate suppression; durable FNFD
requeue after killing and restarting the source; and a direct transit whose
client reset the connection before reading the reply. In the last case the
target still served the accepted article and continued accepting commands.
The full command and five-test output, including two source-structure checks,
are in `native-peering-915d5c72-2026-09-21/runtime.log`.

The earlier broken pipe was secondary. `fnn-owner-drain-one` treated the
ordinary `:taken-transit` tag as a global fault before a Store attempt, stopped
the owner and closed its sockets; the reply then met the closed connection.
The corrected path asks ACL2 for the transfer decision, memberships and
evidence, then uses the shared intent, Store, resolution and transit-outcome
path. Only an actual Store `:uncertain` result requests the global uncertainty
stop. The reset regression covers a connection-local reply failure after a
durable acceptance; it does not weaken or simulate the persistence fence.

Scope remains one-way cleartext loopback on one machine. This run does not
exercise TLS, two hosts, partitions, latency, clock disagreement, general K5
correspondence, or the merge property in `specs/peering.md` section 4.
