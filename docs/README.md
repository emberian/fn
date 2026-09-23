# Project guide

fn now has executable ACL2 components and a native node exercised by agents.
The [node record](../planning/evidence/node-hbox-da5fd8cb-2026-09-23.md) gives
the tested image and its limits; [current work](../planning/now.md) tracks
development beyond that image. The older [implementation inventory](implementation.md)
is historical, not the current service status.

## Reading order

1. [Architecture](architecture.md): purpose, boundaries, and system composition.
2. [Terminology](glossary.md): distinctions shared by every subsystem.
3. [Letter lifecycle](../specs/lifecycle.md): the end-to-end design example.
4. [Objects and identities](../specs/objects.md): what the system represents.
5. [Storage](../specs/storage.md) and [failure model](../specs/failures.md): what
   local acceptance means and what its durability argument assumes.
6. [Retention](../specs/retention.md) and [replication](../specs/replication.md):
   what survives disconnection and how information moves.
7. [Privacy and encryption](../specs/privacy.md): threat boundaries, protocol
   candidates, archives, and the open private-group decision.
8. [NNTP](../specs/nntp.md), [encoding](../specs/encoding.md), and
   [host boundary](../specs/host.md): external interfaces and representation.
9. [Proof strategy](proofs.md), [validation](../tests/README.md), and
   [milestones](../planning/milestones.md): how to establish the claims.

To install and run a node -- one command, one configuration file and a
service unit -- see the [operator guide](operator.md); its packaging templates are in
[`packaging/`](../packaging/fn.toml.example). To read and post on a node that is
already running, from a laptop or from an agent, see
[agents on an fn node](agents.md).
The experimental [local human reader](human-web-client.md) uses the same NNTP
client path in a separate loopback web process.

For concrete representation discussions, see the proposed
[article-byte examples](article-byte-examples.md). For the current local adapter,
see the [persistence experiment](../specs/store-experiment.md).
Its [refinement contract](../specs/store-refinement.md) separates the executable
storage model and its current proofs from the remaining physical correspondence.
The [article-field contract](../specs/article-fields.md) describes semantic
identity/routing checks over the preserved source views.
The [resumable-object experiment](../specs/transfer-experiment.md) stages bounded
fragments without treating assembled bytes as accepted messages.
The [BP path](../specs/bp-path.md) is current disconnected-exchange work; its
[transport experiment](../tests/evidence/2026-09-18-bpv7-transport.md) has actual
BPA interoperability evidence. The [checkpoint](../specs/checkpoint.md) and
[index](../specs/index.md) contracts describe the current logical artifacts.
The [local walkthrough](local-experiment.md) exercises CLI posting, reopen, and
reading stored articles over loopback NNTP.

## Sources of truth

| Question | Authoritative location |
| --- | --- |
| What has been decided? | [Decision register](../planning/decisions.md) |
| What behavior is required? | [Requirement registry](../planning/requirements.json), with links to the detailed specs |
| What is to be proved? | [Proof registry](../planning/proofs.json), interpreted by the proof strategy |
| What should happen next? | [The trajectory plan](../planning/plan-2026-09-22-trajectory.md) §3 and its phase schedule; [how we work](../planning/how-we-work.md) |
| Which examples must be exercised? | [Scenario catalog](../tests/scenarios/catalog.json) |
| Which standards support the design? | [References](references.md) |
| What evidence exists, and what does it not show? | [Evidence index](../planning/evidence-index.md), one row per record in `tests/evidence/` |

The registries track requirement and proof status. Narrative documents explain
contracts rather than maintain competing completion counts. Scenario entries are
test specifications, not a test runner. A scenario may span several milestones;
its milestone is when its full executable form is expected.

For lessons from the development process, see the
[swarmguide](../swarmguide/README.md). It explains the proof and coordination
failures behind the current workflow, with links to the evidence and local
transcript references.

## Design language

An **agreed direction** is a project choice established in the conversation.
A **proposal** is a concrete recommendation still subject to design work.
An **open decision** names a question and the milestone it blocks.
A **requirement** is intended fn behavior, even when its implementation is pending.
An **assumption** identifies an external condition needed by a particular claim.

Reserve RFC normative meanings for statements attributed to an RFC. fn's stronger
acceptance and retention contracts are project requirements, not assertions that
NNTP or BP already provides them. Dependencies on cryptography, disk semantics,
and cooperative peers belong in theorem hypotheses and evidence descriptions.
