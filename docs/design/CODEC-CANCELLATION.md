# Codec cancellation and deferred input

Closing a carrier and completing its application operations are separate events. The carrier can lose its file descriptor before Cancel arrives, while an operation still owns its loan and accepted application prefix.

## Ownership and completion

`defcodec-operation` stores the capability incarnation, operation generation, extent, application progress, pending request, and last accepted observation. Public operations have parent serial zero. A private child instead binds its extent and epoch to one outstanding upper-codec request.

`MARK-CARRIER-CLOSED` requires an already bound public operation and a matching retired carrier: no pending primitive, no live handle, no cleanup credit. It cannot create a loan from a carrier identity. The actual host wrapper first validates the submitted, unposted core descriptor with `fn2-host-codec-op`, then binds that exact operation. This remains valid for held work after core stop.

The closure marker leaves the operation unresolved. `CANCEL` then chooses its terminal result without a live file descriptor:

| Operation state | Target completion | Cancel result |
| --- | --- | --- |
| Receive with accepted input | `:ok`, accepted prefix | Too late |
| Receive without input | `:cancelled`, zero | Won |
| Send | `:cancelled`, accepted application prefix | Won |
| Primitive still pending | No completion or early free | Wait for its observation |
| Already terminal | No second completion | Too late |

A Send count records accepted application bytes. It does not assert that buffered ciphertext reached the peer, and cancelled output carries no delivered-byte payload. A productive Receive must use `:ok`: the common terminal normalizer intentionally erases cancelled input counts.

## Stacked codecs

`CLOSED-CHILD` checks the upper pending request, the child's exact parent epoch, and actual lower cleanup. It returns the child's private prefix without changing either ledger. The upper controller preflights its application operation, advances the private transport span, then settles the application request with zero application progress. Only encode/decode observations change upper application progress.

`ADVANCE-SPANS` settles this logical child result without manufacturing a raw syscall status. Physical `OBSERVE-SPANS` retains raw diagnostics and uses the same span accounting. A pending lower primitive must settle before reclamation; stale identity or a live lower handle cannot authorize child settlement.

## Input evidence before Close

Successful operation `OBSERVE` retains `observed-serial`, `observed-action`, `observed-used`, and `observed-made` before clearing its pending request fields. Rejected observations preserve that receipt. Rearming blocks receipt emission until the new observation, and a new bound child epoch clears old receipt fields.

The shared `INPUT-PREFIX` projector checks the accepted serial, exact sink prefix and extent, and public parent epoch. TLS policy selects action 12; compression selects action 10. Private TLS plaintext and upper child-settlement actions are not application input evidence.

The native public-input path records:

```
(:input-prefix slot generation relative-offset count octets)
```

It emits this packet immediately after the accepted observation, using the actual selected pool bytes. Replay validates the live, acknowledged, unposted Receive incarnation and contiguous bounded prefix, applies the exact byte effect once, and retains it in the taken record. Close acknowledgement ends admission of new input evidence. A later productive completion after Close is allowed only when it matches the previously recorded prefix; publication does not write those bytes a second time.

The logical producer/replay fixture uses an explicit pool-write primitive witness. The native capture fixture calls the actual record dispatcher and replays its actual trace packet, with an explicit record-primitive byte-effect witness. Neither fixture establishes OpenSSL authentication or substitutes for the real handshake/socket gate. External library and OS behavior require their named primitive contracts and the separate native effect connection.

## Qualified logical scope

The 26-book union rooted at the following tests passed record-toolchain certification at source `02328946eb9e707400187cb3ac3bac99f203a075`. All 26 source files matched integration `8d3ae7` when checked. The run reused nine books and certified seventeen in 84.774 seconds; source digests and the runner remained unchanged.

| Root | Qualified closure key |
| --- | --- |
| `tests/tls-record-unit` | `50e41e405e0de28814cd15b37e0cadb64c6c9e74528e02dbee17d434a03b2ad2` |
| `tests/tls-stack-unit` | `5b6693f783f5d99f2fc3488303e48096adfda2fbbfefc1a04f6ca5424e2a19c8` |
| `tests/codec-child-close-unit` | `579f4c2cbac7e84c182669e7a97f9bbe3b2738e3b7753853e3841b481efabbf9` |
| `tests/codec-cancel-unit` | `8a59d07e0c301709c431a8e82eb3beefc054bf7e396c3a435733d545a10f139d` |

Evidence is `forge:/build/lanes/finish-names-export/build/acl2/certify-20261115T013358Z-681968/manifest.json`, using toolchain identity `8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`. Triage reported no failures; the designated `fn` account can read the qualified cache entries.

This scope includes actual TLS record and private bridge guards, accepted-receipt and refusal contracts, and the unchanged productive-Receive regression that originally exposed erased request metadata. Cancellation controls pass through the actual scalar terminal normalizer. The live-core closure wrappers, logical producer/replay composition, actual native capture fixture, and real socket scenario remain separate pending gates. The largest fixture certifications took 25.372 seconds and 14.221 seconds, so their whole-book proof cost still needs improvement.


The later unused-reservation repair at `3c6d773fa` changes these dependency keys. `RETIRE` now discharges the cleanup reservation without a physical free only when no action is pending and both alive and handle are zero; a pending allocation must return first. The actual-name 11-book cancellation closure passed in 16.229 seconds (eight reused, three certified), with all source digests matching integration `a6723f41c` before and after. Its qualified root key is `bdd21f376029f53da90c070def7df3b53937266253bf0fbcde650a8c4f681696`; evidence is `forge:/build/lanes/finish-names-export/build/acl2/certify-20261115T015505Z-701805/manifest.json`. All eleven cache entries passed integrity lookup and were owned and readable by `fn`.

The cancellation fixture still took 15.282 seconds. Source checkpoint `1834945cd` replaces its dummy schemas and the child-close fixture's dummy schemas with actual TLS/COMPRESS carrier and TLS record types. It retains all eight assertions and exercises actual TLS start, handshake observation, handoff and free routing. The earlier 26-book record remains evidence for its historical closure only; the following narrower current gate qualifies the reused fixtures and their actual dependent TLS guards.


The reused-fixture 24-book union passed at `755dbbff1` in `certify-20261115T020143Z-708421` (50.719 seconds, eleven reused/thirteen certified), with before/after source and runner unchanged. All 24 source digests match integration `5bd5a38cf4f57dfd1b4d9a3eec8238ce1f63eac9`. Qualified cache integrity and designated-`fn` ownership/read checks pass. The live record wrapper captured memory.max 2147483648 and memory.swap.max 0. Cancellation certification now takes 1.170 seconds and child-close 4.731 seconds; actual TLS record certification takes 8.795 seconds.

| Current subject | Qualified closure key |
| --- | --- |
| `tests/codec-cancel-unit` | `f61f86119d3d64476d803d56e55dcab8b21bd6e11377d05ce6d0344b7d17a03e` |
| `tests/codec-child-close-unit` | `4741dcdb4d80d6d89c4d38ab62aa90093b057fcf54039f81e1d9ed2b6bd3febd` |
| `books/tls-record` | `27649a65254e7b1f05804b107835e9ecceaf8e57c9ed90cdb1580eba5ce06ce9` |

This gate exercises all eight cancellation/child controls and actual TLS start, handshake observation, handoff, free and record guards. The upper COMPRESS carrier is the actual generated type with explicitly initialized component state; full COMPRESS activation/record policy and live-core/native/replay composition remain separate gates. The historical standalone TLS record/stack test roots were not recertified by this two-root run.
