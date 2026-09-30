# Typed configuration commit for account adoption

This is the local fn representation of the sole account/configuration adoption
commit. It is an additive source component; the joint publisher, recovery fold,
profile admission and checkpoint relation must be installed before serving it.
Decoding the record establishes no account authority or durable acceptance.

The in-memory physical C record retains the existing five fields:

```
(sequence txid generation change stamp)
```

Its `change` is the fixed eight-field marker:

```
(:account-authority-adopt candidate base-config-generation
 base-authority-revision begin-e-count current-e-count content-count digest)
```

The candidate is the existing nonempty account candidate identifier of at most
64 octets. The digest is exactly 32 octets. Scalars have unsigned 64-bit wire
representations. Actual allocation, sequence, generation and authority admission
must still enforce their selected supported profile and existing domains;
representability in this codec does not grant a wider allocator or counter.

The byte stream uses canonical CBOR items, with the existing `fn-cfg` magic byte
string, explicit schema 1, item count 15, followed by these items:

1. Variant 1.
2. C sequence, transaction id and resulting configuration generation.
3. Stamp monotonic time, wall time, error bound and has-wall flag (0 or 1).
4. Candidate identifier as a byte string.
5. Base configuration generation, base authority revision, begin E count,
   current E count and content count.
6. Digest as a byte string.

There are eleven unsigned 64-bit scalar items, two one-byte flags, a candidate
byte string of at most 66 encoded octets and a 34-octet encoded digest. Including
the nine-octet header, the derived maximum is 210 octets. This bounds this fixed
commit descriptor; it does not cap the number of adopted accounts or bindings.
The decoder checks that bound before traversing external input, requires exactly
the declared types and item count, and refuses trailing bytes and other variants.

Ordinary configuration delta records retain their existing encoder/decoder and
recognizer. `fn-cacm-recordp` is deliberately distinct from `fn-cfg-recordp`.
The physical C reader must dispatch the typed variant to the context-aware joint
interpreter, which must refuse if its exact prepared candidate is unavailable.
It must never pass this marker to ordinary `fn-cfg-apply-record`.

Bounded E stages prepare account authority and the corresponding signing-binding
configuration privately. The successful typed C commit advances C sequence and
configuration generation once, advances authority revision once, leaves the E
frontier unchanged, and records the current E count as the publication cut.
Live completion and recovery must perform the same joint transition. Existing
connections keep their pinned binding configuration; new connections observe
the newly committed pair. These are integration obligations, not codec claims.

The source representation boundary is `fn-cacm-decode-encode` in
`consumer-account-config-marker-invariants`: every valid typed record survives
encoding and exact decoding unchanged. `fn-cacm-encode-octets` and
`fn-cacm-encode-bound` establish the unconditional encoded shape and maximum.
The literal tests assert the full round-trip premise and conclusion and a
counterexample when its sole record-validity premise is removed. Normal
certification status is recorded in the accompanying evidence, separately from
source-session admission.

The joined source transaction uses `fn-acj-stage` for E stages and
`fn-acj-commit` for the typed C decision. Stage returns the complete seven-field
decision `(:ok CP7 nil nil metadata5 nil configuration-preparation)`; commit
returns `(:ok CP7 committed-root current-e-count metadata5 root-carry
prepared-configuration account-row-metadata)`. The owner must consume the
saved complete result once. An ordinary E row never publishes authority.
Each account row or tombstone requires its corresponding FNCE3 binding stage
before another row or seal. Both that binding stage and every configuration
preparation transition participate in the pending digest; account content count
remains the account-row count. The final marker names both count and digest.

`fn-catd-next` selects these stages from the registered fixed12 adoption job.
Its slot10 holds `(:account-preparation preparation16)`. After durable row
completion the candidate head is retained; `fn-catd-published` consumes it only
after the corresponding durable binding stage. The separate preparation is
nonauthorizing. It reverses new bindings, inspects one captured old account row
and reverses retained rows one cell per transition. Static missing signing is
an explicit unbind, first static credentials keep their signing provenance,
and an absent static file does not delete redeemed configuration bindings.

These source functions and their actual-transition literals are guard/source
admitted at a named private coordinate, not a completed runtime claim. The
complete maintained account/configuration/digest grammar relation, exact
captured old-row annotations, operation funding and retirement, typed physical
C and FNCE3 Store dispatch, same-pass configured recovery and atomic owner
installation still have to join. Startup/reload caller source now names the
pooled admission gate and refuses before preparation while its genuine
allowance/turn producer is unavailable. No prior direct credential installation
may substitute for that missing authority.
