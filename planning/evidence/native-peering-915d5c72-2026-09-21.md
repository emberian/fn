# Native peering qualification — `915d5c72`

The production image built on `persvati` from source
`915d5c729877eddee7dd3f72eadad21cca463d1a` ran two native owner processes
over private loopback listeners and ephemeral stores. Python was only the
external driver. No installed service or public listener was changed.

The immutable image copy is
`/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host`:

- launcher SHA-256: `2d8259c22388119793ad3dde525497f9095bdb2489ac01e597b439f3d0ff5c09`
- core SHA-256: `eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2`
- SBCL runtime SHA-256: `b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`
- build-source manifest SHA-256: `eb0051343d388901b48e7f1de281ba3d1f6079cab062f25060b186cf01e3aaa4`
- certificate artifact set: `3759213a0737c0153ef703f16b6187ccd67ad44e8f51bde4c0a2258a177e1bea`
- qualified ACL2 wrapper: `/home/ember/fn-gates/toolchains/w25/acl2-literal`

The source manifest contains SHA-256 identities for all 287 tracked files
under `books/` and `host/`, plus `Makefile` and the native build script. It
was checked against the remote origin and is stored beside the image as
`build-source.sha256`. The launcher names the revision-specific core path.
Root independently compared every manifest entry against Git revision
`915d5c72`; all match and the manifest covers every tracked `books/` and
`host/` source in that revision.

`tests.test_native_peering` passed three cases: public operator configuration
and byte-identical A-to-B and B-to-A transfers with duplicate suppression;
durable FNFD
requeue after killing and restarting the source; and a direct transit whose
client reset the connection before reading the reply. In the last case the
target still served the accepted article and continued accepting commands.
The full command and five-test output, including two source-structure checks,
are in `native-peering-915d5c72-2026-09-21/runtime.log`.
The measured harness is the lane version at `ac96d67d`. Main additionally
retains a distinct test that starts both nodes before configuring peers;
that live-reconfiguration case is not covered by this run and belongs to
the current combined-image gate.

The earlier broken pipe was secondary. `fnn-owner-drain-one` treated the
ordinary `:taken-transit` tag as a global fault before a Store attempt, stopped
the owner and closed its sockets; the reply then met the closed connection.
The corrected path asks ACL2 for the transfer decision, memberships and
evidence, then uses the shared intent, Store, resolution and transit-outcome
path. Only an actual Store `:uncertain` result requests the global uncertainty
stop. The reset regression covers a client reset while a transit completes:
the article is durable and the owner remains live. It does not observe whether
the reply write succeeded before the kernel noticed the reset, and therefore
does not claim a witnessed reply-write failure. It does not weaken or simulate
the persistence fence.

Scope remains bidirectional cleartext loopback on one machine. This run does not
exercise TLS, two hosts, partitions, latency, clock disagreement, general K5
correspondence, or the merge property in `specs/peering.md` section 4.
