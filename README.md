# fuckin' news / formal news /᠁

fn is a post office for humans and AIs: ordinary news articles, independently
useful local servers, and communication across intermittent links, carried
media, and eventually delay-tolerant space networks.

The design centers on an executable ACL2 core, a specialized persistent object
store, and explicit records of what each node has promised to retain or deliver.
NNTP supplies the first reader and posting interface.

**Status: executable ACL2 development.** The first acceptance, framing, encoding,
and retention components have certified books and executable scenarios. A
deterministic simulator runs the same acceptance functions. This is not yet a
durable news service. See [implementation status](docs/implementation.md) for
the exact scope and remaining proof/integration boundaries.

The local CLI now persists articles and archive obligations, and a loopback
reader serves the recovered store through the actual ACL2 core. Follow the
[local walkthrough](docs/local-experiment.md) to post, reopen, and read it.
Network POST and native signatures remain unfinished. The
[storage integration evidence](tests/evidence/2026-09-18-storage.md) records
certification, filesystem/socket tests, and independent NNTP client traffic.

Start with the [project guide](docs/README.md), then the
[architecture](docs/architecture.md) and [development plan](planning/milestones.md).
The [decision register](planning/decisions.md) distinguishes agreed direction
from provisional choices. [Repository guidance](AGENTS.md) applies to development.

Selected so far: native author signatures with explicit legacy gateway provenance,
and local retention until authorized release without automatic expiry. Shared
community groups come first; the [privacy note](specs/privacy.md) keeps the later
cryptosystem open. The [current work page](planning/now.md) tracks the first
implementation batches and their review.

```text
docs/                 architecture, terminology, references, proof strategy
specs/                behavioral contracts and representation requirements
planning/             milestones, decisions, requirement and proof registries
books/                executable ACL2 definitions and proofs
host/                 simulator and host integration
tests/acl2/           executable assertions certified by ACL2
tests/scenarios/      specified scenarios; not executable system tests yet
tools/                checks, certification runner, and simulator launcher
rfc*.txt              original reference documents
```

Run the dependency-free scaffold checks with Python 3.10 or newer:

```sh
make check
# or: python3 tools/check_scaffold.py
```

This checks document links and planning/scenario consistency. To certify books
and execute model traces with ACL2 8.7 / SBCL 2.6.8 installed:

```sh
make certify
python3 tools/run_simulator.py
# or run certification, the simulator, and all Python tests together:
make test
```

See [implementation status](docs/implementation.md) for toolchain configuration
and evidence locations. Model certification is not an RFC conformance audit or
a physical durability test.
