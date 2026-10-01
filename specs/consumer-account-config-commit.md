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
configuration generation once. The persisted C sequence is the **prior**
configuration generation, following `fn-ocfg-reconfig-record`; its resulting
generation is prior plus one (genesis is sequence 0/generation 1). A record
that equates the next generation with its sequence is refused. The commit
advances authority revision once, leaves the E
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
## Preservation of nonbinding policy during signing preparation

`consumer-account-config-posting-relation` observes the original preparation
functions through a proof-only projection that removes exactly account rows
whose mark is 2. It preserves every other row literally and in order, including
access, moderation, invitation and redeemed credential rows. No projection scan
is added to the served path.

Successful `fn-bcp-stage` preserves that projection of the new-binding stack.
`fn-bcp-seal`, from collect with an empty nonbinding stack projection,
establishes a relation to the captured base accounts. Every actual
`fn-bcp-tick` preserves this relation; its eventual nonbinding-row projection
is preserved unconditionally. A related ready `fn-bcp-prepared` consequently
returns the exact nonbinding projection of the captured configuration.
PRF-1204 and SCN-1080 record the boundaries and literal transition witnesses.

The same book connects this projection to the actual `fn-cfg-access-table`,
`fn-cfg-moderation-row` and `fn-cfg-moderator-logins` observations. All three
ignore exactly the removed signing rows: first-match moderation selection and
moderator order are preserved, with no additional hypotheses.

This is one premise for reusing posting policy during typed C preparation.
It does not establish group liveness across a configuration-generation change,
the relation between a retained posting/view cache and its captured source, or
the lifetime and funding of the actual host continuation. Those joins must be
established before a retained cache is published with the new configuration.


The selected pooled account caller consumes the same owner-control BODY ticket
and retains all five returned effects before classifying each core result. The
native missing-binding refusal precedes entropy I/O and constructors. New claims
refuse while CURRENT holds a configuration acquiring/source lease. Actual E
completion records the original holder frontier and persisted outcome before
clearing the holder; scalar holder/token/intent counts must agree.

A yielding C preparation parks the same original claim and roots, then rebinds
only its retained slot to a fresh ATS nonce after source prepay. It performs no
new account reserve, PRS issue, selection replay or E alias clear. Journal state
excludes parking after publication begins. Seven actual-source recording cases
pass with synthetic unfunded callbacks; PRF-1198 remains planned. High PROGRAM
admission, genuine family demand, journal/alias-return and runtime activation
remain open. These recording cases grant no allocation or durable acceptance.

## Conditional strict-past control history

`control-visible-prefix-bound` gives a proof-only bridge from the actual ready
Store replay relation to the existing later-configuration withdrawal law
(PRF-1208 / SCN-1081). Its source events are admitted; normal certification and
literal witnesses remain open. The modern typed C successor must establish or
carry the needed strict-past invariant. Actual C acquisition uses the existing node next transaction ID and consumes
no E allocator reservation. Its unchanged physical FILES/frontier still needs
the acquisition scalar correspondence and configured-history relation; the
E-only Store replay relation cannot simply be assumed after configuration. No runtime scan or blanket view-reuse claim follows.
