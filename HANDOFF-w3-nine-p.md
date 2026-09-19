# Handoff: w3/nine-p — a 9P2000 view of a committed store

Branch `w3/nine-p`, branched from `dev` at `9321344`.

## What landed

- [`tools/fn9p.py`](tools/fn9p.py): a read-only 9P2000 server over one
  committed store. It replays the store exactly as `tools/run_reader.py` does
  (shared lock, `Acl2Store`, `Store.recover`, `fn-reader-use-store`),
  materializes the whole view through the ACL2 bridge, and then releases the
  lock, the bridge and the ACL2 process. Implements version, attach, walk,
  open, read, clunk, stat, flush; refuses auth, create, write, remove, wstat
  and any non-read open mode.
- [`host/ninep-host.lisp`](host/ninep-host.lisp): the ACL2 adapter. Every byte
  the server serves comes from here, and everything here calls
  `books/nntp.lisp` over the archive `host/reader-host.lisp` selected. No news
  semantics in Python.
- [`tests/test_fn9p.py`](tests/test_fn9p.py): a 9P client written for the test,
  comparing the view against a live NNTP reader over the same store.
- [`specs/views-9p.md`](specs/views-9p.md): the projection contract, what is
  and is not served, the fixed-generation rule, and the trust boundary.
- [`tests/evidence/2026-09-19-nine-p.md`](tests/evidence/2026-09-19-nine-p.md):
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

(filled in below)

## Open

- `.overview` waits for `fn-nntp-over-*` helpers.
- One file is bounded by the ACL2 bridge's printed-reply limit (about a
  megabyte of article); the whole view is bounded by `--max-bytes`.
- The view has no authentication; bind it to loopback.
