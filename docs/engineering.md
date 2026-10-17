# Project guide for engineers

The map of fn for someone changing it. Commands and rules are in
`CONTRIBUTING.md`; the user guides start at `docs/README.md`.

## What fn is, in four files

- `README.md` — ten lines.
- `docs/architecture.md` — purpose, boundaries, how the parts compose.
- `docs/glossary.md` — the words every subsystem shares.
- `planning/design-store-representation-2026-10-01.md` — the store
  representation being built now (decisions D41 to D45).

## Reading order for a change

1. `specs/lifecycle.md` — one letter, end to end.
2. `specs/objects.md` — what the system represents.
3. `specs/storage.md` and `specs/failures.md` — what "accepted" means and
   what the durability argument assumes.
4. `specs/retention.md`, `specs/replication.md`, `specs/peering.md` — what
   survives disconnection and how articles move.
5. `specs/nntp.md`, `specs/encoding.md`, `specs/host.md` — the outside
   interfaces. `specs/bp-path.md` — disconnected exchange over BPv7.
6. `specs/privacy.md` — threat boundaries; private groups are still open.
7. `docs/proofs.md` and `docs/testing.md` — how a claim is established.

## The tree

| path | holds |
| --- | --- |
| `books/` | ACL2: every decision the server makes, and the theorems about it |
| `host/` | native Common Lisp: sockets, disks, TLS; calls into `books/` |
| `specs/` | the contracts |
| `tests/` | ACL2 test books, harnesses, native modules, scenarios (`docs/testing.md`) |
| `tools/` | development tools; each has `--help` |
| `packaging/` | the release tarball, `install.sh`, unit templates |
| `planning/` | decisions, registries, the repair ledger, plans |
| `docs/articles/` | the user guides, as Usenet articles; `site/build_site.py` renders them |

## Where truth lives

| question | file |
| --- | --- |
| what is decided | `planning/decisions.md` |
| what fn must do | `planning/requirements.json`, linked to `specs/` |
| what is to be proved | `planning/proofs.json` |
| what is true now | `planning/now.md`; `planning/current.md` (generated) |
| what is broken | `planning/repair/STATUS.md` (generated) |
| which examples must work | `tests/scenarios/catalog.json` |
| what ran, on what | `planning/evidence-index.tsv`; bytes via `python3 tools/evidence_store.py cat PATH` |
| what is deployed | `docs/nodes/fsn1.md`, `docs/nodes/hbox.md` |
| what the RFCs say | `docs/references.md` |

A dated plan or evidence record speaks for its own date. Narrative pages
explain contracts; they do not keep their own completion counts.

## Words the design uses

An agreed direction is a choice made in the conversation; a proposal is
still subject to design; an open decision names what it blocks. A
requirement is intended behaviour, built or not. An assumption is an
outside condition a particular claim needs, and belongs in that theorem's
hypotheses.

RFC terms (MUST, SHOULD) mean what an RFC says only when an RFC says it.
fn's stronger acceptance and retention promises are its own requirements.

## First check

Python 3.11 or newer (the optional `tests/interop_nntplib.py` probe needs
3.12 or older):

```sh
make check
```

It checks static consistency (tens of minutes); it does not run the
server or certify ACL2 books. For one kind of test at a time, use
`docs/testing.md`.
