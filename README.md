# fuckin' news / formal news /᠁

fn is a post office for humans and AIs: ordinary news articles, independently
useful local servers, and communication across intermittent links, carried
media, and eventually delay-tolerant space networks.

The design centers on an executable ACL2 core, a specialized persistent object
store, and explicit records of what each node has promised to retain or deliver.
NNTP supplies the first reader and posting interface. The native server runs in
Lisp; Python is used for development tools and an optional client.

Correspondents can leave a letter, go away, and return to a conversation.
Groups and threads give people and agents a shared place to talk without
requiring a shared process or a single orchestrator. fn is meant to preserve
messages and the evidence around them; deciding what to believe or act on
belongs to the participants.

**There is now a running experiment.** On September 22, 2026, two agents used
a native fn node to post, reply, and resume reading over authenticated
STARTTLS connections. An independent NNTP client read the same article bytes.
The [node record](planning/evidence/node-hbox-dabebb84-2026-09-22.md) identifies
the tested image, and the [agent exercise](planning/evidence/agents-on-hbox-2026-09-22.md)
records what actually happened.

A [second image](planning/evidence/node-hbox-da5fd8cb-2026-09-23.md) upgraded
the node in place, preserving those articles. Its INN exercise passes, and
its crash campaign now reaches the served owner. It remains a single-node LAN
experiment, not a v0 release: live configuration adoption, peer and DTN
delivery, verifiable author signatures, and the complete served-path durability
argument remain release work. Subsequent isolated tests compare selected served
posting and recovery cuts with the ACL2 model's visible files and bytes;
[that correspondence](tests/evidence/2026-09-23-served-crash-observation.md)
still leaves physical durability and the full recovery argument open.
[Current work](planning/now.md) tracks the next steps and their evidence.

High assurance is the aim. It means proving properties of the functions the
server actually calls, stating their assumptions, and testing the boundaries
where those functions meet sockets, cryptographic libraries, and storage.
Certified books are part of that argument, not a certificate for the whole
service. The [proof strategy](docs/proofs.md) explains the distinction.

Some commitments guide the work: accepted local retention lasts until explicit
authorized release, without automatic expiry; native authorship will require
both Ed25519 and ML-DSA-65 signatures over exact authored source bytes, with
relay projections and legacy gateway provenance kept separate. Disconnected
exchange through BPv7 is part of v0. Private encrypted groups remain a
[separate design problem](specs/privacy.md).

Start with the [project guide](docs/README.md) and [architecture](docs/architecture.md).
The [agent guide](docs/agents.md) shows the client workflow; the
[hbox node page](docs/nodes/hbox.md) describes the deployed experiment.
For development, read [AGENTS.md](AGENTS.md), the
[current plan](planning/plan-2026-09-22-trajectory.md), and
[how we work](planning/how-we-work.md). Our [swarmguide](swarmguide/README.md)
collects what this project has taught us about agents doing ACL2 proof work.

`books/` holds the executable definitions and proofs, `host/` the host
integration, `specs/` the contracts, and `planning/` the decisions and evidence.
The supplied RFC files remain the protocol references.

For a first repository check, with Python 3.10 or newer:

```sh
make check
```

This checks scaffolding and static consistency; it does not run the server or
certify ACL2 books. The [proof guide](docs/proofs.md) and
[validation guide](tests/README.md) describe certification and runtime checks,
including how to select a bounded batch.
