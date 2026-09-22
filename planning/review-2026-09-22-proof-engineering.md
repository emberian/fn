# Why the image took all night: a review of the proof engineering — 2026-09-22

The overnight goal was a native node agents can use. It needed one thing
first, a certified image closure, and that closure went from 111 to 140 of
164 books across three lanes and about nine hours without producing an image.
The lanes did the right things one at a time. The loop they were in is the
problem. Numbers below are the tools' (`tools/green_check.py`, the manifests
under `evidence/manifests/certify-20260922T*.json`, `grep` over `books/`).

## The latency model

A closure run stops at the first book that fails and every book above it
reads "no certificate on file". So one run reveals one layer of independent
reds. The chain from `hybrid-store` up through `replay`, `config-records`,
`node-config`, `store-node`, `store-node-invariants`, `store-node-traces`,
`owner`, `served` and the `native-*` books is about ten deep. A round costs
the slowest book in it, and four books timed out at the 1800 s per-book limit
(`feed-connection-invariants` four times, `replay`, `config-records`,
`store-files` once each; the manifests record 2400 s walls). Thirty-nine
certification runs happened today. Ten layers times thirty to forty minutes
is the night.

## Findings

**F1. Discovery is serial because a failed book hides everything above it.**
Mechanism: `include-book` refuses an uncertified dependency, so dependents
of a red book cannot show their own independent failures until the red is
fixed. Evidence: the second freeze lane's note lists eight repairs made in
sequence, each surfaced by the previous one's certification; the third lane
started on two reds and 22 books "about which nothing is known".
Change: a triage mode for the farm. On a failure, substitute the failed
book's last-green source (the manifests name its digest, git history holds
the bytes) into the remote tree only, rerun the books above, and repeat, so
one triage reports every independent red in the closure with the
assumption each rests on. Triage certificates never enter the cache. Tool:
`tools/triage.py` (lane w32/triage).

**F2. Timeouts are the round time.** Mechanism: a proof that "stops returning"
rather than failing burns the whole per-book budget, and the budget is 1800 s
for discovery and for the final run alike. Evidence: the timeouts above; the
first freeze lane measured `fn-replay-apply-record-non-nil-is-node-state` at
600 s without leaving `Goal''` and 0.32 s once repaired. Change: discovery
runs use a 300 s budget and report a book that needs more as a finding in
its own right; only the final closure run uses 1800 s.

**F3. Books open whole codec vocabularies book-wide.** Mechanism: `(local
(in-theory (enable ...-vocabulary)))` at the top of a book puts the record and
statement codecs into every proof in it, so a goal that only dispatches on a
record kind carries the codec; when the bounded CBOR profile made the codecs
larger on 2026-09-21, proofs across the tree stopped returning. Evidence: 103
books carry such a top-level opening (117 lines); every repair in the two
freeze records is "close the recognizer where the proof only dispatches on a
kind". Change: a lint, `tools/theory_check.py`, that flags a top-level
opening of a codec theory in a book whose proofs reach it, reported in
`make check` first and made strict once the count is down; the rule in
AGENTS.md: open a codec in a hint, never at the top of a book.

**F4. Behaviour landed under invariant books nobody recertified.** Mechanism:
five commits on 2026-09-21 (6e992351, 6ab2c783, 64a80197, 4bb7bb3d, 40bb3f74)
widened `fn-sn-state`, gave `fn-sn-finish` two arms, bound the AUTHINFO peer
role and gave `fn-sn-recover` a fault arm; `store-node-invariants` last
certified at 01:20 that day and `nntp-auth` at 01:21; several exported
statements were false in the shape the machine has, and `git log` read as
green. Evidence: the second freeze record, and the five theorems that now
carry hypotheses with the commit named at each site. Change: a merge gate.
`green_check --changed-since REV --strict` lists the books a branch changed,
their dependents, and each one's verdict at its current digest, and exits 1
on a red or a never; root runs it in a lane's worktree before merging any
branch that touched `books/`. Behaviour and the invariants over it land
together or the merge waits.

**F5. Each freeze lane re-derived the loop.** Mechanism: the recipe lived in
memory and prose; each lane spent its first hour rediscovering the wrapper,
the root, the closure command and the timeout. Evidence: 558k, 664k and
(pending) tokens for the three lanes, four to five hours each. Change: the
recipe is now `tools/runbooks/hbox-image-build.sh` and the brief in
`fn-freeze-recipe`; with F1 and F2 a lane's job becomes reading one triage
report and fixing every red in it in parallel.

## What is not the problem

Not the farm's throughput (8 jobs on hbox, 6 on persvati; a full closure
certifies in about twenty minutes when nothing hangs). Not the assurance
rules; every repair tonight was a real fact stated at its site. Not the
lanes' judgement; the second lane found the cause the first missed and
named it.

## Order of work

F4's gate and F3's lint are root's, today. F1's triage is a lane. F2 is a
flag on the runner once F1 exists. The open items the freeze surfaced
(`fn-sn-finish-preserves-indexedp` on the accepted-statement arm, PRF-023;
`fn-store-article-match` under OBJ-002) stay open until the closure is green.
