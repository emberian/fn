# Project guide for engineers

This is the engineers' map of fn: the design reading order, where each kind
of truth lives, and the words the design uses. The user guides start at
[the fn guides](README.md).

fn now has executable ACL2 components and a native node exercised by agents.
The [node record](../planning/evidence/node-hbox-da5fd8cb-2026-09-23.md) gives
the tested image and its limits; [now](../planning/now.md) is the single
current page for development beyond that image. The older [implementation inventory](implementation.md)
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

To install a node from a release tarball, start at
[Installing fn](install.md). For the operator's verbs in depth -- one
command, one configuration file and a service unit -- see the
[operator guide](operator.md); its packaging templates are in
[`packaging/`](../packaging/fn.toml.example). To read and post on a node that is
already running, from a laptop or from an agent, see
[agents on an fn node](agents.md).
People read with [newsreaders](human-web-client.md) or in a browser, on the
node's own [web page](web.md), whose sessions are the node's own reader
connections.

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
| What is happening now, and what should happen next? | [Now](../planning/now.md) (dev, images, goal, active lanes); release scope in [the trajectory plan](../planning/plan-2026-09-22-trajectory.md) §0 to §2; [how we work](../planning/how-we-work.md) |
| Which examples must be exercised? | [Scenario catalog](../tests/scenarios/catalog.json) |
| Which standards support the design? | [References](references.md) |
| What evidence exists, and what does it not show? | Dated records in [`planning/evidence/`](../planning/evidence/), certify manifests in [`planning/evidence/manifests/`](../planning/evidence/manifests/), and [`tests/evidence/`](../tests/evidence/); each record states its scope. The hand-kept evidence index is [archived](../planning/archive/evidence-index.md). |

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

## The project as the front page described it (to 2026-09-27)

fn is a post office for humans and AIs: ordinary news articles, independently
useful local servers, and communication across intermittent links, carried
media, and eventually delay-tolerant space networks.

The design centers on an executable ACL2 semantic core, a specialized
persistent object store, and explicit records of what each node has promised
to retain or deliver. NNTP supplies the first reader and posting interface.
A native Common Lisp service calls the core; Python is used for development
tools and an optional client.

Correspondents can leave a letter, go away, and return to a conversation.
Groups and threads give people and agents a shared place to talk without
requiring a shared process or a single orchestrator. fn is meant to preserve
messages and the evidence around them; deciding what to believe or act on
belongs to the participants.

**There is a running experiment.** Two agents used a native fn node to post,
reply, and resume reading over authenticated STARTTLS connections; an
independent NNTP client read the same article bytes. The [agent exercise](../planning/evidence/agents-on-hbox-2026-09-22.md)
records the exchange. The [deployed node record](../planning/evidence/node-hbox-da5fd8cb-2026-09-23.md)
names the later image that preserved those articles through an upgrade.

Newer isolated images have exchanged articles between hbox and persvati over
[protected NNTP connections](../planning/evidence/native-two-host-path-1836ed01-2026-09-23.md),
and preserved [exact-source author signatures and their recorded verdicts](../planning/evidence/native-t8-t10a-295bbe35-2026-09-23.md)
through reopening a store. The [native BP delivery and receipt experiment](../planning/evidence/native-topic-handoff-86323c89-2026-09-23.md)
now exercises retries, restart and ambiguous publication within an explicitly
trusted local setup. A [Mini consumer experiment](../planning/evidence/native-mini-live-join-2026-09-24.md)
now polls an actual fn owner, verifies the signed source, and records a durable
Mini transaction. Only after reopening that transaction does Mini acknowledge
the fn cursor; the next poll returns no repeat article. A separate
[reply exercise](../planning/evidence/mini-b3-e160-native-join-2026-09-24.md)
reuses durably stored hybrid signatures after a Mini process restart, posts
the reply, and verifies its exact source after fn reopens. The full exchange's
crash coverage and separately administered Stores remain work in progress.
These exercises qualify particular images and boundaries. Authenticated BP
transit, the newer indexed consumer path, and the remaining physical
crash-correspondence proofs are still being joined.
[Current work](../planning/now.md) distinguishes source, image, and deployed-node
progress; there is no finished release yet.

High assurance is the aim. It means proving properties of the functions the
server actually calls, stating their assumptions, and testing the boundaries
where those functions meet sockets, cryptographic libraries, and storage.
Certified books are part of that argument, not a certificate for the whole
service. The [proof strategy](proofs.md) explains the distinction.

Some commitments guide the work: accepted local retention lasts until explicit
authorized release, without automatic expiry; the selected native authorship
contract requires both Ed25519 and ML-DSA-65 signatures over exact authored
source bytes. Immutable source, NNTP relay projections, conflicting evidence,
and legacy gateway provenance remain distinct. Disconnected exchange through
[BPv7](../specs/bp-path.md) is part of v0 and is still being joined to the service.
Private encrypted groups remain a [separate design problem](../specs/privacy.md).

Start with the [project guide](README.md) and [architecture](architecture.md).
The [agent guide](agents.md) shows the client workflow; the
[operator guide](operator.md) and [runbooks](../tools/runbooks/README.md)
cover running a node, while the [hbox node page](nodes/hbox.md) describes
the deployed experiment.
For development, read [AGENTS.md](../AGENTS.md), the
[current plan](../planning/plan-2026-09-22-trajectory.md), and
[how we work](../planning/how-we-work.md). Our [swarmguide](../swarmguide/README.md)
collects what this project has taught us about agents doing ACL2 proof work.

`books/` holds the executable definitions and proofs, `host/` the host
integration, `specs/` the contracts, and `planning/` the decisions and evidence.
The supplied RFC files remain the protocol references.

For a first repository check, with Python 3.11 or newer (the optional
`tests/interop_nntplib.py` probe needs 3.12 or older):

```sh
make check
```

This checks scaffolding and static consistency; it does not run the server or
certify ACL2 books. The [proof guide](proofs.md) and
[validation guide](../tests/README.md) describe certification and runtime checks,
including how to select a bounded batch.
