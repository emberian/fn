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
