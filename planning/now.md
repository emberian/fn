# Now — 2026-10-03

The active plan is [the development workstreams](overnight-2026-10-03.md), revised
after deeper source/design reading and ember's correction: Sol for implementation,
Astra for composition, continuing subsystem ownership through integration and use.
Read it with [the repair ledger](repair/STATUS.md) and [the contributor guide](../CONTRIBUTORS.md).
The first groundwork wave is active: five GPT-6.1-Sol subsystem deputies, a
GPT-6.1-Sol groundwork deputy coordinating their interfaces and integration, and
the strategic coordinator. Composition and representation are covered by the
groundwork deputy while the wider roster remains a target. New lanes wait for a
useful independent need and coordinator agreement. The initial orientation
snapshot is recorded in the plan; `8d17b09dd` integrated that planning/ledger
reconciliation onto dev. Runtime qualification and deployment remain separate
from source integration. Integrate directly onto dev during
stabilization; qualify immutable candidates alongside continuing development.

The earlier page below is retained as historical scope, not a current roster,
release instruction, source coordinate or deployment observation.

---

# Historical plan — 2026-09-28

The one page a new agent reads first: where dev is, what is being worked on,
and where the rest is. Written by lane records-steward from dev `940bc3104`
at about 21:30 UTC. The page it replaces (2026-09-27, format 9) is in git
history; the log before that is [archive/now-2026-09-26.md](archive/now-2026-09-26.md).

## Coordinates

AGENTS.md keeps four coordinates apart; none implies another.

- **Source.** dev as above. [The current view](current.md) (generated) gives
  each capability's host line, keystone and certificate at this revision.
- **Proof.** Each capability's certificate is named in the current view;
  merged lanes' manifests are under
  [`evidence/manifests/`](evidence/manifests/), cited in each batch's
  "cite round" commit.
- **Qualified image.** None of the current store format. The newest
  qualification record is [qual-69046a76](evidence/qual-69046a76-2026-09-26.md)
  (2026-09-26, format 8). Qualification now runs once, in the prerelease
  convergence checklist ([release-v6.6.0](release-v6.6.0.md) section 2b),
  not per change (ember, 2026-09-28).
- **Deployment.** Two live nodes, both on fn 6.6.0 built from dev
  `a3553e6b4a23` (release `fn-6.6.0-linux-x86_64.tar.gz`, sha256
  `401c6324...6bf0`), both with format-10 stores, peered (the fsn1 node
  accepts node #2's inbound feed; node #2's push to fsn1 is PKT-882). Neither
  image is qualified; each is a release build of that source.
  - `fn.fg-goose.online`, the public node on the fsn1 anchor (88.99.126.35;
    119 STARTTLS, 563 TLS, Let's Encrypt), logins by invitation.
  - node #2, hbox `/tank/fn/node` (LAN only, self-signed).
  Both were migrated to format 10 on 2026-09-28 by `store export`/`store
  import` ([node-migrate](evidence/node-migrate-2026-09-28.md)). That was the
  last migration: at the cut every node is redeployed fresh (below).

## The plan: complete, then cut

ember, 2026-09-28 20:21Z: "i don't want to defer any of the major work
we've identified .... complete the work! get it all on dev. get everything
gucci. *and then* we can cut 6.6.0. it isn't a race :)"

The list is `build/coordinator/COMPLETE-BEFORE-6.6.0.md` (coordinator-owned,
not tracked; rows A to P, each with its lane). In short:

- **A. Store representation**: records read from the committed page image;
  exact prefix binding; adversarial swaps; async page faults; readers by
  access pattern; root lifetime; the tree-codec split; `reclaim --dry-run`.
- **B. Memory (F8)**: the admission gap; the per-record heap term from the
  profile; the 100k reopen; credit admission (GPT-6's recommendation, the
  only option that reaches 256 MiB accountable); chunked bodies.
- **C. Proof speed**: chain-first scheduling with fewer jobs; targeted
  fan-in cuts; one image umbrella; the depth debt; the registry merge and
  the aggregate certification budget.
- **D-H.** One config edit and the legacy deletions; the writable extracted
  build and Chicken speed; the adopted F4 time bars; the native reds and
  the Python host's retirement; paused-peer health and the node redeploy.
- **I-P** (from the archaeology of 2026-09-28): NNTP, auth/TLS and
  durability correctness bugs; F2's join discharge and the F1/F3 rulings;
  the generators (definterface, one profile source, defevent); the Python
  diet; real peers; online compaction and the operator surface; the records
  (this page, [decisions](decisions.md), the backlog); ember's time-bound
  items.

Then, once: the prerelease convergence checklist
([release-v6.6.0](release-v6.6.0.md) section 2b), a quiet candidate
qualified, the format word renamed `fn-store-1`, the tag `v6.6.0`
([D37](decisions.md): the release sequence), and every node redeployed fresh.

## Decided on 2026-09-28 (the register has the words)

- **No migrations** (D38 withdrawn): one store format, no legacy readers or
  migration code; `store export`/`import` is backup and restore of this
  format.
- **Qualify once**: lanes implement and prove, certify their affected roots
  and run the natives their change exercises; full native sets, the OpenBSD
  guest, F1-F8, scale and 1M runs happen once at convergence.
- **Scale by curve**: 1k to 100k, fitted and extrapolated; no 1M runs unless
  the fit is ambiguous.
- **F8 split and F4 bars adopted**; **no ACL2 patch** (stock w28 on both
  boxes); **the source-tree reorganisation not adopted** (chain-first
  scheduling, fan-in cuts and one image umbrella instead:
  [architecture-recommendation](architecture-recommendation-2026-09-28.md)).
- Each is recorded with ember's words and the still-open questions in
  [decisions](decisions.md), "2026-09-28: decision packets recorded".

## What changed since the last page

- **Format 10**: BLAKE3 as fn's digest everywhere fn chooses (SHA-256 only
  where an RFC forces it: Cancel-Lock), LZ4 extents, the page-backed arena
  store (arena-store 1-6), served columns.
- **Release machinery**: the cut script, `tools/fundamentals.py`, the
  version sequence (6.6.0 first), the fail-closed extraction gate and a
  read-only extracted build.
- **Nodes**: the public node deployed 2026-09-27, node #2 on hbox, both
  migrated to format 10 and peered; the site as newsgroup FAQ articles in
  `fn.docs`.
- **Proof tooling**: one ACL2 toolchain (w28) on both boxes with shared
  certificates; the laptop is a REPL target (`tools/proof_repl.py --host
  auto`); defprotocol; the defkeystone pilot.

## Open, as of this page

- The rows of COMPLETE-BEFORE-6.6.0.md; the fundamentals F1-F8 stay OPEN in
  [release-v6.6.0](release-v6.6.0.md) until the convergence run shows them.
- The backlog [backlog-2026-09-25](backlog-2026-09-25.md): every open line
  carries a triage mark of 2026-09-28 (done, duplicate, a COMPLETE-BEFORE
  row, won't with ember's decision, or a question for ember).

## Lanes

Lanes run on Claude Opus 5.5 in `build/lanes/<name>` on `lane/<name>`,
under `build/coordinator/queue/LANE-PREAMBLE.txt` and closeout-common.txt;
the batch runner merges to dev. The coordinator's log is
`build/coordinator/WAVE-STATE.md` (newest on top, not tracked). How lanes
work: [how we work](how-we-work.md).

## Where to read next

[The current view](current.md), [decisions](decisions.md),
[requirements](requirements.json), [proofs](proofs.json),
[the release checklist](release-v6.6.0.md), and the docs index
[docs/README.md](../docs/README.md).
