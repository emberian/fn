# Handoff: w5/deploy-gate

A deploy gate: one script that puts a named commit on a farm box, runs fn there
as a real server, drives it with real clients, kills it, recovers it, and writes
the evidence with its own gaps.

## What landed

- [`tools/deploy_gate.py`](../../tools/deploy_gate.py) --
  `python3 tools/deploy_gate.py <commit-ish> --host persvati`.
- [`tests/test_deploy_gate.py`](../../tests/test_deploy_gate.py) and the fake
  entry points in `tests/deploy_gate_fake/` -- eleven tests, the whole sequence
  against a local fake host with no ssh and no ACL2.
- [`planning/evidence/deploy-cce4b11-2026-09-20.md`](../evidence/deploy-cce4b11-2026-09-20.md)
  -- the real run against `cce4b11` on persvati.

## The shape of a run

`git archive <commit>` lands at `~/fn-deploy/<rev>` on the host. Certificates
come from the host's own gate of the tree: `~/fn-gates/<tree>-<rev>` when it is
there, otherwise its newest `~/fn-gates/<tree>-*`, and in either case
`certpick.py` copies a pair only when the `.lisp` beside it in the gate hashes
to the `.lisp` in the deploy tree. A pair is valid by content
(`ACL2_BOOK_HASH_ALISTP=NIL`, docs/proofs.md), so a neighbouring revision's gate
is either exactly right per book or exactly wrong per book, and the gate decides
which rather than assuming. Only when no gate of the tree exists does it run
`make certify FN_CERTIFY_JOBS=16` on the host.

Then: a two-group store; the three outcomes through the real CLI; the nntplib
probe if any interpreter on the host still has a stdlib `nntplib`; the server
(`bin/fn run` when it takes a `--store`, else `tools/run_owner.py`, else
`tools/run_reader.py --post`) on a free port with its own log; a raw-socket
transcript; a second reader held live across another connection's whole POST;
`kill -9` of the server from inside an open POST; `run_store recover`; a restart
and a reread of everything that was actually posted; a scripted slrn or tin
session if one is installed. Every command is recorded with its exit code, its
first output line and its wall time.

Each step carries the exit code it expects. A refusal exiting 1 is evidence, not
noise; a server entry point that does not start is a probe the gate fell back
from, recorded with the fallback's consequence, and never a pass. A phase that
cannot run is written into "What was NOT exercised" with its reason, so the
report cannot quietly shrink.

`FN_ACL2` is exported into every remote script from `tools/farm.py`'s host
table, which is the one place the farm boxes' ACL2 images are named; nothing on
persvati's `PATH` is called `acl2`.

## What the first real run found (cce4b11, persvati, 58 s wall)

1. **`books/owner` does not include on dev.** `tools/run_owner.py` dies at
   startup: `books/owner.lisp:461` calls `fn-served-open` with three arguments
   and `books/served.lisp:668` takes five. Already on the board from
   w3/reader-profile and w5-fn-cli; the gate is a third, independent
   observation of it, this time as "the service does not start".
2. **The reader answers POST but does not advertise it.** Started with
   `--post`, it replies `340 send article to be posted`, yet its CAPABILITIES
   block is `VERSION 2 / READER / OVER MSGID / LIST ... / IMPLEMENTATION`
   with no `POST`. RFC 3977 section 5.2.2 requires the capability exactly when
   posting is permitted, so a client that reads capabilities first will not
   offer posting.
3. **No concurrency on the reader path.** `tools/run_reader.py` accepts one
   connection and serves it to completion before accepting the next
   (`listen(1)`, then `while True: accept(); serve_client(...)`), so a second
   reader live across a post cannot be exercised there at all. The concurrent
   server is the owner, which is finding 1.
4. **The kill cut and recovery are clean.** SIGKILL from inside an open POST
   gives the client `ECONNRESET`; the interrupted article is absent after
   recovery; the article acknowledged before the kill rereads byte-for-byte
   through a fresh server.
5. **An injected uncertain publication leaves a staging orphan that recovery
   reports and does not remove** (`staging-orphans=1 [.stage-...]`), stable
   across two recoveries. Reported, not silently collected: worth a decision.

## Open for the next lane

- Re-run the gate once the owner includes; that turns findings 2 and 3 into
  real served-concurrency evidence rather than gaps.
- `slrn` and `tin` are absent on persvati and the gate does not install
  packages. Either install them there once (sudo is passwordless) and re-run,
  or accept that no third-party newsreader has ever spoken to fn.
- persvati has only Python 3.13, which dropped `nntplib` (PEP 594), so the
  independent `tests/interop_store_nntplib.py` probe cannot run there. A 3.12
  on the box, or a vendored client, would close the one place the gate has no
  independent decoder.
- The gate exercises one kill point. `tests/campaign/cuts.py` owns the
  enumerated table; the gate should not grow a second one.
