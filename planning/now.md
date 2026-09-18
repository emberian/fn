# Current work: executable components and integration

The [decision workbook](decisions.md) is a backlog, not a questionnaire that must
be completed before coding. The user authorized broad Terra implementation waves
with Luna/Sol/Astra work and convergence in batches. Routine reversible choices
are owned by the implementation team; public byte formats, cryptographic suites,
and deployment remain explicitly separate decisions.

## Completed integrated checkpoint

- Acceptance has certified initial-state, transition-preservation, immutable
  binding, and local-number uniqueness results. The theorem hypotheses retain
  the abstract durable-completion/recovery boundary.
- Wire framing, CBOR primitives, retention accounting, journal crash experiments,
  disconnected fact exchange, and an experimental NNTP reader have executable
  books and assertion tests. Their full subsystem contracts are still open.
- The acceptance simulator executes the actual definitions in ACL2.
- The node now connects retention and acceptance in one transaction, with
  general transition preservation and article-to-pin binding proofs.
- The reader runs over a real loopback socket via a persistent ACL2 process;
  independent `nntplib` client traffic and the socket regression suite passed.
- Review repairs strengthened wire-state bounds, distinguished journal sequence
  from transaction identity, and hardened NNTP numeric/projection handling.

`make test` passed the complete 19-book certification set, simulator, and nine
Python tests. The [evidence record](../tests/evidence/2026-09-18-integrated.md)
states exact source hashes, outcomes, proof scope, and remaining limitations.

See [implementation status](../docs/implementation.md), the
[proof registry](proofs.json), and [milestones](milestones.md) for scope. A
certified component does not close a complete milestone or prove the host/disk.

## Working rhythm

One writer owns each area. Agents certify their own roots while independent
areas advance. Root integrates a frozen batch, runs the combined suite, records
evidence, and updates the registries. Review each coherent batch once; repair
correctness findings, track remaining proof scope, then advance.

The user requested frequent local checkpoint commits on 2026-09-18. Commits are
for synchronization and may include unfinished work; a commit is not evidence
of passing tests. Keep generated logs/certificates under ignored build paths,
and retain concise evidence summaries and exact source hashes in the repository.

## Current engineering choices

- ACL2 8.7 on SBCL 2.6.8 for the development model, with Python tooling.
- Interpreted ACL2 bridge for the first host experiment; raw Common Lisp calls
  to unguarded logical functions are not the integration argument.
- One owner and one shared-state transaction pending at a time.
- Exact octet payloads and exact Message-ID strings; no native signing preimage.
- Local cross-post names must all be configured; failure is atomic.
- No automatic expiry or history pruning. Resource charges include retained
  history, and inadequate capacity rejects new obligations.
- Experimental CBOR uint32/byte-string primitives; no persistent/native schema
  frozen by their existence.

## Next substantial work

Next: compose real bounded article injection and provenance with the reader;
develop versioned storage bytes and a qualified disk adapter from the crash model;
lift invariants through journal integration, finite traces, and guards. The
current node and journal are separate models: connecting them is a real next
implementation task, not something implied by having certified both books.
The next user-facing design discussion should use concrete native-versus-legacy
article/signature byte examples (D01), then principal/key custody (D09).

Private-group cryptography remains a separate requirements/research track.
Shared community groups come first; MLS is a candidate, not a commitment.
