# Contributing to fn

fn is an executable ACL2 news core and persistent store, served over NNTP and
carried over BP for disconnected operation. Contributions are licensed under
[AGPL-3.0](LICENSE). Questions and proposed changes can go in repository issues.

## Find the contract and the current work

Start with the [engineering map](docs/engineering.md),
[architecture](docs/architecture.md) and [decision register](planning/decisions.md).
Read the affected specification before changing behavior. The
[contributors' guide](CONTRIBUTORS.md) explains the code boundaries and evidence;
[AGENTS.md](AGENTS.md) contains the repository working instructions.

Use [now](planning/now.md) for the current development state,
[NSLICESQUEUE](NSLICESQUEUE.md) for connected capability work, and the
[repair ledger](planning/repair/STATUS.md) for individual findings. The
[requirements](planning/requirements.json), [proof targets](planning/proofs.json)
and [scenarios](tests/scenarios/catalog.json) retain their stable IDs. Update the
relevant contract, registry and scenario together when behavior changes. Dated
plans and old evidence describe their recorded revision, not today's completion.

## Work in an isolated tree

Start from current `origin/dev`, and keep the shared checkout intact:

```sh
git fetch origin
git worktree add -b codex/my-change build/lanes/my-change origin/dev
cd build/lanes/my-change
```

Use a distinct branch and directory name. Coordinate shared interfaces and file
changes with their current owner. Do not stash or reset someone else's checkout,
or delete another contributor's files or caches. The repository tools use Python
3.11 or newer; ACL2 and native dependencies have separate setup instructions in
[the proof guide](docs/proofs.md) and [installation guide](docs/install.md).

## Iterate on the actual caller

Run the smallest check that can refute your change. For a Python tool, select its
unit-test module or method with `python3 -m unittest`. For native Lisp syntax,
`python3 tools/host_check.py --read FILE` is a static check; it does not execute
that file or establish its behavior.

Use a warm proof session for ACL2 work. This example loads `peer-pull` up to its
schedule function, then sends the remaining source forms and its test file:

```sh
python3 tools/proof_repl.py forms books/peer-pull
python3 tools/proof_repl.py start my-change books/peer-pull --host hbox --cached-only --upto fn-pull-schedule
python3 tools/proof_repl.py send-range my-change books/peer-pull --from fn-pull-schedule
python3 tools/proof_repl.py send-file my-change tests/acl2/peer-pull-tests.lisp
python3 tools/proof_repl.py status my-change
python3 tools/proof_repl.py stop my-change
```

Adapt the book, event and tests to your change. A partial session is useful for
individual forms; loading the complete target is necessary before sending tests
that depend on later definitions. `--cached-only` refuses missing or mismatched
dependency certificates. Choose an explicit source-dependency or certification
route when needed; inspect `start --help` first. Keep unchanged dependencies
loaded and retry the failing event, instead of starting a whole closure again.
An admitted event is not a certificate. Leaked LOCAL rules (`--ld-leak`) are for
discovery; final admission must reproduce without them.

Prefer the cached build host for substantial proof work. On hbox, builds run
under `swarm-build`; farm submissions apply that wrapper. Coordinate available
memory and builds, and inspect RSS and ARC rather than relying on `free` alone.
On the laptop, launch ACL2 only through `tools/acl2` or `tools/proof_repl.py`, which
use the resource pool. Do not bypass it with a bare ACL2 process. See the
[proof guide](docs/proofs.md) and [runbooks](tools/runbooks/README.md) for host setup.

## Exercise a running source process

Saved-image production is not a prerequisite for development feedback.
[`native_source_runner.py`](tools/native_source_runner.py) prepares and runs a
fresh native source process; [`native_source_cache.py`](tools/native_source_cache.py)
can reuse an initialized world before a Store or owner exists. Both expose their
subcommands through `--help`. Preserve attachment order, exact source/runtime
identities and fresh state on restart; an old stobj layout cannot stand in for a
changed one. Source execution, logical admission and packaging qualification are
separate results.

For an operator prompt, use `python3 tools/fn_dev.py shell --executable
/path/to/fn --config fn.toml`. A developer owner started with
`FN_NATIVE_DEV_REPL=/absolute/private/directory/fn-dev.sock` also supports:

```sh
python3 tools/fn_dev.py repl --socket /absolute/private/directory/fn-dev.sock
```

This attaches to the live owner's actual world. It can change code and state;
long forms hold the owner, and disconnecting does not cancel them. Use isolated
test Stores, not the live node. The [developer attachment reference](docs/operator.md#interactive-development-and-live-inspection)
describes admission, inspection, tracing and the production refusal boundary.

## Integrate source and record scoped results

Send coherent source promptly to the integrator for public `dev`; proof checks,
selected runtime checks and evidence filing can follow asynchronously. Include
the commit, affected contracts and actual consumer, results already obtained,
and outstanding work. Composition conflicts may need resolution before push;
source integration does not require a whole certification or image run.

For certification, select changed books and relevant test roots, for example
`python3 tools/farm.py submit hbox books/peer-pull tests/acl2/peer-pull-tests`.
Choose affected consumers when the interface changes, reuse matching artifacts,
and coordinate expensive runs. `make check` is a broader consistency suite;
it is not proof of runtime behavior and need not run for every local edit.
See [validation](tests/README.md) and [proofs](docs/proofs.md) for check selection.

Archive evidence with `python3 tools/evidence_store.py put PATH` and commit the
resulting `planning/evidence-index.tsv` entry; evidence bytes belong in the
archive, not Git. Name the source revision, admitted/certified scope and executed
consumer. Missing, failed and unrun checks remain explicit. Build/load a new
executable only when a concrete consumer question needs it; full qualification
answers a separate release or operational claim.

Known gaps and scope limits live in [now](planning/now.md), the
[current capability view](planning/current.md), [resource contract](docs/resource-contract.md)
and [remaining capability queue](NSLICESQUEUE.md). A passing test or landed
implementation does not close its remaining resource, proof or integration work.
