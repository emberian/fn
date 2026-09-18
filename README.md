# fuckin' news / formal news /᠁

fn is a post office for humans and AIs: ordinary news articles, independently
useful local servers, and communication across intermittent links, carried
media, and eventually delay-tolerant space networks.

The design centers on an executable ACL2 core, a specialized persistent object
store, and explicit records of what each node has promised to retain or deliver.
NNTP supplies the first reader and posting interface.

**Status: design scaffold.** There is no server, storage implementation, certified
ACL2 book, or deployment yet. The specifications contain requirements and open
design questions, not claims of implemented or proved behavior.

Start with the [project guide](docs/README.md), then the
[architecture](docs/architecture.md) and [development plan](planning/milestones.md).
The [decision register](planning/decisions.md) distinguishes agreed direction
from provisional choices. [Repository guidance](AGENTS.md) applies to development.

Selected so far: native author signatures with explicit legacy gateway provenance,
and local retention until authorized release without automatic expiry. Shared
community groups come first; the [privacy note](specs/privacy.md) keeps the later
cryptosystem open. The [current work page](planning/now.md) tracks the first
executable acceptance cycle and its independent review.

```text
docs/                 architecture, terminology, references, proof strategy
specs/                behavioral contracts and representation requirements
planning/             milestones, decisions, requirement and proof registries
books/                reserved for executable ACL2 definitions and proofs
host/                 reserved for the Common Lisp I/O adapter
tests/scenarios/      specified scenarios; not executable system tests yet
tools/                development checks
rfc*.txt              original reference documents
```

Run the dependency-free scaffold checks with Python 3.10 or newer:

```sh
make check
# or: python3 tools/check_scaffold.py
```

This checks document links and planning/scenario consistency. It does not run
ACL2, test a server, or establish RFC conformance. ACL2 and the host Lisp will be
pinned during [M1](planning/milestones.md#m1-executable-model).
