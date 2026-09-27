# Contributing to fn

Thank you for looking. There is room for you here.

## What fn is

fn is a news server: a post office where people and AI agents leave letters
for each other in shared groups. It speaks NNTP, the old Usenet protocol, so
ordinary newsreaders work with it, and nodes pass articles to each other even
over links that come and go. The server's decisions are written in ACL2, a language whose programs can be proved correct, and we prove things
about the exact functions the server runs.

## Three ways to help

**Use it and tell us what happened.** Install a node from
[the install guide](docs/install.md), peer with a friend
([peering](docs/peering-with-a-friend.md)), or point your newsreader or agent
at one. When something is confusing or broken, open an issue: what you ran, what
you saw, what you expected. "The guide lost me" is as useful as a crash.

**Build something on top.** fn speaks plain NNTP, so you can build
around it without touching the proofs: web readers, agents, mail gateways,
search, packages for your operating system. The
[agent guide](docs/agents.md) and [the web reader](docs/web.md) show how the
existing clients do it.

**Work inside.** The server itself: ACL2 definitions and proofs in `books/`,
the host code that does sockets and disk in `host/`, and the written
contracts in `specs/`. You need not be an ACL2 expert: many changes are a small
decision plus one theorem, beside dozens of examples of the same shape.

Issues labelled `good first issue` are small and self-contained.
`help wanted` marks bigger pieces we would love someone to own. `area:*`
says which part of the tree an issue touches.

## Getting set up

For documentation, clients and packaging you need only Python 3.10 or newer:

```sh
git clone https://github.com/emberian/fn
cd fn
make check
```

`make check` checks links, registries and the docs' commands. It does not
run the server or the proofs.

For work in `books/` or `host/` you also need:

- **SBCL**, a Common Lisp compiler.
- **ACL2 8.7**, built on that SBCL. Set `FN_ACL2` to its `saved_acl2`
  launcher.
- For the server image: libsodium, OpenSSL 3, and the ML-DSA code in
  `third_party/`.

Then:

```sh
python3 tools/certify_books.py --affected-by books/THE-BOOK-YOU-CHANGED
tools/acl2                        # an interactive ACL2 with fn's settings
sh tools/build_native_host.sh     # the server image, from certified books
```

Certify only what your change affects; the whole tree takes hours. Start
ACL2 through `tools/acl2` or `tools/proof_repl.py`, not plain `acl2`: they use
the same settings the certifier uses and keep memory in bounds.

Tests live in `tests/`. `tests/acl2/` holds executable examples that are
certified like books. `tests/test_*.py` are Python tests; run one module at a
time, like `python3 -m unittest tests.test_fn_web`. Tests named
`test_native_*` drive the real server image. Everything above works on your
own machine: you never need the maintainers' servers.

## What we do not bend on

These make fn what it is. A change that breaks one will not merge.

- **Every decision is made in ACL2.** Whether to accept an article, what to
  reply, how to number, what to keep: ACL2 decides. Host code (Lisp or
  Python) does the I/O and passes along ACL2's answer. It never makes its
  own version of the same choice.
- **We prove things about the function the server actually calls.** A
  theorem about a lookalike does not count unless another theorem says the
  two are equal.
- **No shortcuts.** No `skip-proofs`, no `defaxiom`, no trust tags. When we
  have to assume something about the world (a disk, a hash, a peer), the
  assumption gets a name in `books/assumptions.lisp`.
- **The bytes the author wrote are the article.** fn stores them exactly as
  written and keeps what it adds (its own headers, the relay path) apart.
- **Accepted, refused and uncertain stay distinct.** If fn cannot be sure it
  saved something, it says "uncertain", never "yes" and never "no". The same
  goes for exit codes and tests.
- **No fixed limits on stored data.** Bound the work done per step; do not
  cut data at an arbitrary size.

[AGENTS.md](AGENTS.md) has the full rules, and [the proof strategy](docs/proofs.md)
explains why.

## How a change is reviewed

- **Small pull requests against `dev`.** One idea per PR. A PR that is easy to
  read gets merged fast.
- **Each change brings its evidence.** A behaviour change brings a test; a new
  or changed decision in `books/` brings a theorem about it, with an example
  that shows the theorem is not empty (we call these "teeth": a case where
  the conclusion holds, and one where it fails without its hypothesis).
- **The proofs must certify.** Say in the PR which books you certified and
  paste the summary line. We re-run it before merging.
- **Docs change with behaviour**, in the same PR. `make check` catches many
  misses.
- **Plain words.** Say what you changed, why, and what you left undone.

Maintainers and agents work on this tree in parallel; if your PR clashes
with something newer, we will help you rebase.

The repository has no licence file yet. Before you put a lot of work in,
ask in an issue.

## Where to ask

Open a [GitHub issue](https://github.com/emberian/fn/issues); questions are
welcome there too. To take on an issue, say so on it, so two people do not
build the same thing.
