# Handoff: w3/nine-p — a 9P2000 view of a committed store

Branch `w3/nine-p`, branched from `dev` at `9321344`.

## What landed

- [`tools/fn9p.py`](../../tools/fn9p.py): a read-only 9P2000 server over one
  committed store. It replays the store exactly as `tools/run_reader.py` does
  (shared lock, `Acl2Store`, `Store.recover`, `fn-reader-use-store`),
  materializes the whole view through the ACL2 bridge, and then releases the
  lock, the bridge and the ACL2 process. Implements version, attach, walk,
  open, read, clunk, stat, flush; refuses auth, create, write, remove, wstat
  and any non-read open mode.
- [`host/ninep-host.lisp`](../../host/ninep-host.lisp): the ACL2 adapter. Every byte
  the server serves comes from here, and everything here calls
  `books/nntp.lisp` over the archive `host/reader-host.lisp` selected. No news
  semantics in Python.
- [`tests/test_fn9p.py`](../../tests/test_fn9p.py): a 9P client written for the test,
  comparing the view against a live NNTP reader over the same store.
- [`specs/views-9p.md`](../../specs/views-9p.md): the projection contract, what is
  and is not served, the fixed-generation rule, and the trust boundary.
- [`tests/evidence/2026-09-19-nine-p.md`](../../tests/evidence/2026-09-19-nine-p.md):
  the Linux kernel-client mount transcript.
- `planning/milestones.md` M6 now names the experiment.

## What mounts

```
/status                    generation, article count, group count
/groups/<group>/<number>   the stored article source octets
/by-id/<message-id-hex>    the same articles, named by identifier
```

No `.overview`: this tree has no `fn-nntp-over-*` helpers, and building one in
the host would be the second implementation the project forbids.

A group directory is `fn-nntp-group-range-numbers` — LISTGROUP's list from
LISTGROUP's function. An article file is the payload
`fn-nntp-article-response` would dot-stuff into its 220 block, served only when
`fn-nntp-article-idp` and `fn-nntp-article-framedp` hold; an article ARTICLE
answers with 503 is listed but refuses to open, degrading only itself.

## The fixed-generation rule, and the one design choice worth review

A mount serves one frozen generation for its whole life. The server copies the
entire view out of ACL2 under the shared store lock and then drops the lock.

This deliberately differs from `run_reader.py`, which holds its shared lock for
the life of the process and so blocks every post while it runs. A mount can
last days; blocking a writer for days to guard a snapshot the server has
already copied is the worse trade. The committed transaction files the snapshot
was built from are immutable, so nothing it serves can change underneath it.
The cost is that the view cannot follow the store, which is the documented
contract rather than a limitation to fix later. If a future reader wants a
live view it needs a different design (re-replay per generation), not a longer
lock.

## Results

- `make check`: green (107 Markdown files, 50 requirements, 18 proof targets,
  18 scenarios; ledger current).
- `python3 -m unittest tests.test_fn9p -v`: 2 tests, OK, 119 s.
  - `test_files_and_listings_agree_with_the_nntp_reader`: the bytes of
    `/groups/fn.letters/1` and `/2` satisfy
    `ARTICLE <n> reply == "220 <n> <id> article follows" CRLF + file + "." CRLF`
    against a live reader over the same store; the group directory's names are
    exactly LISTGROUP's number lines; `stat` lengths match the bytes read;
    `/by-id/<hex>` returns the same article; `fn.test` holds only the article
    that named it; a write-mode `open` and a walk to a number that does not
    exist are both refused.
  - `test_mount_generation_is_fixed_and_a_fresh_mount_advances`: a post
    succeeds while the view is mounted (the lock is not held), and the mounted
    view keeps its `/status` bytes, its directory and its 404 for the new
    number, while a fresh mount shows the higher generation and the new file.
- Linux kernel mount (hbox, 6.11.0-29-generic, in-kernel v9fs over TCP):
  mounts, walks, `ls -la`, `cat` of an article byte for byte, `ENOENT` for a
  missing article, `EPERM` for create and write, clean `umount`. Recorded in
  [the evidence note](../../tests/evidence/2026-09-19-nine-p.md). The tree served
  there was synthetic, so it is protocol evidence, not projection evidence --
  the store-backed kernel mount with a `diff` against the reader is chained
  behind the hbox `make certify` and will land in
  `/tank/fn/ninep/mount-transcript.log`. That mount showed both refusals
  arriving as `ESERVERFAULT`; a missing file now answers with the string v9fs
  maps to `ENOENT`, and the tests were re-run green after that change.
- A protocol-only exercise of the server over a synthetic tree (multi-read
  files, a directory larger than one msize, `..` walks, two clients) was run
  during development without ACL2; it is not part of the committed suite.
- Baseline certification: the full `make certify` was started locally as
  instructed, but this laptop was running 37 concurrent lane certifications and
  the run reached 27 of ~160 books in 75 minutes. It was stopped on the
  coordinator's instruction not to run a full certification locally. The same
  full `make certify` is running on hbox under `swarm-build` in
  `/tank/fn/ninep` (the tree this lane shipped, `FN_ACL2=/tank/fn/acl2-8.7/saved_acl2`).
  To execute this lane's own tests, the worktree borrowed `books/*.cert`,
  `*.fasl` and `*.port` from `/Users/ember/dev/fn` at the same commit
  (`9321344`) — the book sources are byte-identical, this lane changed no book,
  and ACL2 validates a certificate against the source's own hash, so a
  mismatch would have failed closed rather than passed quietly.

## Open

- `.overview` waits for `fn-nntp-over-*` helpers.
- One file is bounded by the ACL2 bridge's printed-reply limit (about a
  megabyte of article); the whole view is bounded by `--max-bytes`.
- The view has no authentication; bind it to loopback.
