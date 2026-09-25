# Trajectory to a node agents use, and what comes after — 2026-09-22

This plan's §0 to §2 and §6 are the release scope; §3's step table and
dependencies still name the work. Where dev is and who is working on what is
[now.md](now.md); lane width and the compute budget are
[how we work](how-we-work.md).

Status: a plan, revised the same day with ember's decisions (§0). It changes
no registry, book, host file, tool or test; where a registry row or a
document is wrong, §7 says what root writes. Every number is a tool's, taken
at `dev` `d69e9952`; every statement about the past names the record it comes
from. The two lanes then in `build/lanes/w31-freeze-3` and
`build/lanes/w32-native-guards` were untouched (both worktrees have since
been removed).

Why this exists: [the proof-engineering review](review-2026-09-22-proof-engineering.md)
explains why a night produced no image, and ember asked that the old plans not
be resumed as they are: bigger steps, properties stated up front, no partial or
placeholder rows. The v0 checklist in [milestones](milestones.md) is a table of
`partial`, `open`, `blocked` and `done (with a caution)` cells, several walked
back in place; [now.md](now.md) is 384 lines of dated narrative that supersede
one another; the [wide capability cycle](archive/wide-capability-cycle-2026-09-21.md)
ran twelve capability lanes at once and produced the five commits of
2026-09-21 that landed behaviour under invariant books nobody recertified
(review F4). None of those is the plan.

## 0. Decisions taken 2026-09-22

ember answered the eight questions the first draft asked. Their words, and
what each decides.

1. **DTN is v0.** "Yes, DTN is supposed to be part of v0, it's a crucial part
   of the multi-agent architecture that will be built on top of it." The BP
   node, TCPCL and the contact-plan run are steps T12a to T12d on the critical
   path; the production image keeps its BP, TCPCL and anchor roots; there is
   no `node` image profile.
2. **Native author signatures are v0**, on the critical path (T10). "I do
   kinda would prefer native author signatures." The node still deploys first
   on password-authenticated principals over STARTTLS, and its page says posts
   are unverifiable until T10 lands.
3. **The six-wave shape is retired.** "Yes this seems fine." The v0 checklist
   and the six fiber records stop defining v0; milestones carries §3.
4. **Worktrees go, branches stay, and every checkpointed branch has a
   disposition.** "Let's make sure also that all the work is actually
   integrated into our practice, codex isn't going to be resuming it as-is,
   we've taken over for it." Root is removing the clean non-live worktrees;
   §5.2 gives each of the seven branches its step or its reason. Nothing is
   left "preserved". Astra, Terra, Sol and Luna are retired as names.
5. **LTP after DTN.** "Let's put off LTP for now I suppose, makes sense to
   put after DTN." LTP is the first step after T12 (§2.2).
6. **The acceptance stamp is a v0 step** (T2). "The umbrella is red, that
   doesn't make for an excuse for making bad calls / punting."
7. **Five lanes; converge every two to three batches.** "I would prefer to
   have 5 (two per persvati/hbox, one locally). We do not need to run the
   damn merge gate on every single freaking batch. We can converge every
   2-3." The phase schedule that implemented this (§3.3) was removed on
   2026-09-24 after ember's 2026-09-23 width correction ([decisions](decisions.md));
   [how we work](how-we-work.md) has the loop.
8. **Peering is measured on one box first.** "You do not actually need two
   separate machines to test the peering." The matrix's two nodes on one host
   are T9's gate; the hbox-to-persvati run is a later row of T13.

## 1. What is true today

The numbers, from the tools at `d69e9952`:

- `git rev-list --count 915d5c72..HEAD` is 324; the frozen 915 image serves
  readers, posting, two-node transit and SIGTERM recovery on persvati
  ([record](evidence/native-peering-915d5c72-2026-09-21.md)), and the v0
  matrix reached 128 of its rows on it
  ([record](evidence/native-matrix-915-2026-09-22.md)); `tools/v0_matrix.py
  --list` now prints 200 rows over 16 features.
- `green_check --summary`: 409 books in the closure of 402 roots; 354 green at
  their current digest, 54 red, 1 never. The reds behind the image are the
  eight [now.md](now.md) names from the triage waves (`store-node-traces`,
  `store-node-resolution`, `store-observed`, and guard conjectures in
  `native-admin`, `native-control`, `native-hybrid-control`,
  `native-operator`, plus one `native-operator-tests` assertion); the
  [triage record](evidence/triage-2026-09-22.md) names the failing form in
  each of the first three and a fourth, `store-prepare-correspondence`.
  `checkpoint` is also red at its digest in the 12:16Z persvati run.
- `theory_check --summary`: 74 of 243 books open a codec theory at the top
  for every proof in them, 17 distinct theories; 55 of them are in the image
  closure.
- `ledger.py`: 404 books, 6658 theorems, 5226 functions, 198 `must-fail`s,
  19 `encapsulate`s; guards 1731 verified, 279 declared off, 611 unguarded;
  61 suspect-shaped theorems (none cited); 150 include-hygiene and 646
  host-name warnings.
- Registries: 59 requirements, 36 `specified`, 23 `implemented`; 52 proof
  targets, 8 `certified`, 35 `in-progress`, 9 `planned`. Eleven `in-progress`
  targets carry zero events (§4.5).
- Three `certified` targets sit on books that are red at their current
  digest: PRF-036 (`store-node-traces`, `store-observed`), PRF-037
  (`checkpoint-codec`), PRF-041 (`byte-store-keystones`) (§4.5).
- The production image (`host/native/build.lisp`) includes 47 books and
  `ld`s the host files for the store, owner, auth, admin, feed, BP, TCPCL and
  anchor; `tools/proof_artifacts.py roots --profile default` names 62 roots,
  164 books with the closure ([second freeze record](evidence/native-freeze-01fbdad4-2026-09-22.md)).
  The DTN image (`build-dtn.lisp`) has 26 roots.
- `dev` has STARTTLS, AUTHINFO with principals, path identity, live
  administration, the operator verbs, NEWNEWS, `tools/fn_client.py` run
  against a real node, `tools/node_probe.py`, and the hbox runbooks
  (`tools/runbooks/`). When the image closure is green the image builds and
  the node deploys on hbox in about ninety minutes.

## 2. A. Trajectory

### 2.1 The purpose, as properties

[Architecture](../docs/architecture.md): a nexus for humans and AIs that
stays useful when peers are asleep, disconnected or far away; a site accepts
local work without a remote quorum; the central questions are what the node
has, why it keeps it, what it has undertaken, and what evidence releases that.
[Agents](../docs/agents.md): yue and tulip do not run at the same time and
cannot rely on each other being reachable; what they need is a Message-ID, a
group and a local number to resume from, and the three outcomes kept apart.
[The BP path](../specs/bp-path.md) and decision 1: the multi-agent
architecture is built on nodes that carry each other's articles across
outages, so the disconnected exchange is part of what "a node" means.

A node agents can use is one on which these hold, each as a theorem over the
function the host calls, with teeth, and each observable on the deployed
image. The table names what exists and what is missing; §3 turns each gap into
a step.

| | Property, stated as it will be judged | Exists | Missing |
| --- | --- | --- | --- |
| P1 | A named principal reaches the node only over a protected channel: `AUTHINFO` on a clear connection under `protected_only` is 483, a restricted command without a login is 480 and performs nothing, posting allowance follows the authenticated credential, and the secret never crosses in the clear. | `books/nntp-auth` (`fn-auth-gated-command-is-refused-and-not-performed`, `nntp-auth.lisp:1348`), `books/served-tls-prefix`, `host/native/tls.lisp`; PRF-039's three events | PRF-031 carries zero events though its theorem exists; `books/owner-tls-prefix` red; no teeth book for the auth chain; never run on an image (T7) |
| P2 | `240` is emitted only after `fn-sn-finish` consumed this exact pending completion and appended one acknowledgement; `441` refused names its reason; an uncertain outcome is `441 ... do not repost`; and after a kill at any cut of the table the acknowledged article rereads byte-identical. | `fn-sn-new-success-requires-actual-matching-durable-node-completion`; `host/store-node-host.lisp:545` `fn-store-sn-finish`; D13 exit codes; the 14-cut table `tests/campaign/native_cuts.py` | No theorem from the served `240` back to the consumed completion; the cut campaign has run in no image since the 32 KiB repair ([owner-defects](evidence/owner-defects-2026-09-22.md)) (T5) |
| P3 | Reading resumes: local numbers are never reused, a reader pinned before another connection's POST keeps its view, and NEWNEWS answers from the instant *this node* accepted the article, within its budget or refusing. | OBJ-005 keystones; `books/owner` reader pins; PRF-052 over the injector's `Injection-Date` | NNT-006's own note: the pinned view surviving another connection's POST "is NOT established by any run"; `books/owner` red (T6); the store keeps no acceptance stamp (T2) |
| P4 | One owner decides duplicate versus conflict for a held Message-ID. | the decision exists and is deterministic ([duplicate-outcome](evidence/native-duplicate-outcome-2026-09-22.md)) | it is `fn-store-article-match`, `host/store-host.lisp:138`, host code, no theorem (OBJ-002 open item) (T3) |
| P5 | A host fault costs one connection, and a bounded number of sessions is served at once. | `fn-own-fault-keeps-every-other-connection` and four siblings, `books/owner-fault.lisp:128-170`; `max-conns` | PRF-040 carries zero events and no `owner-fault` teeth book exists (T14) |
| P6 | The operator stands the node up, adds groups, principals and peers, and changes configuration live, from one binary with no Python, and a reconfiguration is a journal transaction no reader half-sees. | verbs in `docs/operator.md`; `books/owner-config`, `books/native-admin`; `host/owner-host.lisp:214,232,610,1005` call `fn-ocfg-step`, `fn-ocfg-reconfig-refusal`, `fn-ocfg-open-peer`, `fn-ocfg-open` | PRF-028's four events say "no host line calls any `fn-ocfg-` function", which is no longer true; `native-admin`/`native-operator` red on guards (T8) |
| P7 | Two nodes exchange both ways: transit is the post path, no loop is accepted in either direction, a held Message-ID is refused at offer and transfer, a restart delivers exactly one copy, only Path and Xref differ across transit, and the feed logs in over TLS. | K1, K2 inbound, K3 (PRF-042, 12 events); outbound feed `books/owner-feed`; 915 measured byte-identical loopback exchange | PRF-029 (outbound loop freedom) zero events though `fn-own-feed-target-is-offerable` exists at `owner-feed.lisp:790`; K5 `fn-feed-replay-is-the-live-feed-modulo-inflight` open; no octet-preservation theorem; PRF-047/051 (outbound TLS, AUTHINFO) zero events; never TLS (T9) |
| P8 | An agent's post carries a signature another agent can check without trusting fn, and the reader shows the verdict acceptance recorded. | `books/hybrid-signature`, `hybrid-store`, `stx-*`; kind-4 events written by `hybrid-author` on the control socket | `fn-stxe-profile-supportedp` returns `nil` for every profile (`stx-evidence-records.lisp:61`); S6 `:fn-verified` not built; `fn-sig-verify` is constrained and unattached (`docs/architecture.md`), so the article arm of `fn-sn-finish` cannot evaluate a verdict on a signed article in the image; PRF-023 open on the accepted-statement arm (T10, T4) |
| P9 | The node keeps every accepted article until explicit release and refuses a new obligation it cannot afford. | D03; `fn-retain-admit-preserves-statep`; `V0-CAP-REFUSE` refused on 915 | RET-002's note: "no keystone states that an unaffordable obligation is refused" (T11) |
| P10 | Every process-death cut the campaign takes is a crash point the model expresses, the campaign passes on the production image, and the platform's durability claim is stated with its qualification. | K1 to K4 (PRF-041), `native_cuts.py` names a `fn-bs-*-program` coordinate per cut; K7 for the four authority boundaries | `byte-store-keystones` red; the campaign has run in no image at the current cuts; K0 general preservation, K5, K6, K8 and one platform profile open (T5, T16) |
| P11 | A node carries another node's articles as bundles across an outage: a bundle is authored, forwarded and delivered only through the node machine, a restarted node never reuses a creation sequence, expiry and staging exhaustion are decided by the machine, and an application receipt is what discharges the sender's obligation, never a carrier ACK. | `books/bp-node` (two ends), `bp-node-machine` (outbound lifecycle, PRF-046 three events), `bp-primary*`, `bp-fragment`, `tcpcl-*` C1 to C4, `bp-sequence-*` (PRF-045), the dtn7-rs exchange ([record](evidence/bp-dtn7-w11-2026-09-21.md)), `tools/tcpcl_lab.py` fn-to-fn `adu` | `fn-bpn-step`, its state, reassembly, dispatch and status reports "none exists" (`specs/bp-design.md` §1.5.1); T1 to T6 unproved; the contact scheduler (`books/scheduler`) has no native caller, `tools/scheduler.py` is Python; nothing in `fn-bp` calls `fn-retain-release` (review naivety 6); the interrupted contact-plan run exists only under the mock BPA ([four-node lab](../tests/evidence/2026-09-21-four-node-lab.md)) (T12) |

### 2.2 v0 and v1

**v0 is one image, deployed on hbox and persvati, on which P1 to P11 hold as
theorems over the host-called subjects with teeth, and one matrix run on that
image agrees with every row it reaches.** Its deployment happens at T0, before
most of the properties are proved; the node's page says at every deploy which
of P1 to P11 hold on it and which do not. Nothing in v0 is a signature-security
claim (A-CRYPTO), a claim about peer honesty (A-PEER), or flight readiness.
The durability claim v0 makes is exactly what T16 qualifies, and until T16
lands it is process death on Linux.

**v1 is, in dependency order:** (a) LTP (decision 5), against the node
machine T12 leaves; (b) the Message-ID index on the served path (T17, from
`w28/nntp-msgid-index`), the per-group index, measured cost sentences; (c)
substrate S4 and S5 (policy on transit, membership epochs) once two policied
nodes exist; (d) compaction and reclamation (STO-007, RET-005/006, D13
pruning), which D03 does not need until capacity refuses; (e) BPSec (packet 8
of `specs/bp-design.md`); (f) M6: web interface, 9p, private groups (D04).
Each is a step list of its own when it starts, in this shape.

### 2.3 What the current v0 shape is for, item by item

| Item in the current v0 shape | Disposition | Why |
| --- | --- | --- |
| v0.1 server | v0, as T0/T5/T6/T7 | the node agents use |
| v0.2 peering K1 to K5 | v0, as T9 | "peering between nodes" is the purpose; K5 restart is what "exactly once" means to an agent |
| v0.2 K6 (BP unification) | v0, inside T12a | one transit decision for NNTP and BP articles is what makes the bundle path the post path (`specs/peering.md` K6 packet) |
| v0.2 K7 (merge theorem over `fn-sys-run`) | v1 (c) | needs the two-node system model that S4/S5 also need |
| v0.2 INN interop | v0, one row in T13 | interoperability is what NNTP buys; INN's side already holds ([inn-lab](evidence/inn-lab-f4e8272-2026-09-20.md)) |
| v0.3 DTN | v0, as T12 (decision 1) | |
| v0.4 TCPCL C1 to C4 | done; the two-node transfer over fn's CL is T12c's gate | |
| v0.4 S0 to S2 | done (`stx-carrier`, `stx-verify`, `stx-invariants` green) | |
| v0.4 S3 | done in shape (D21, the index on `fn-sn-state`) with one open arm | T4 closes the arm |
| v0.4 S4, S5 | v1 (c) | no caller; `specs/substrate-transport.md` §10 says so |
| v0.4 S6 reader exposure | v0, inside T10 | without it a signature is invisible to the agent reading |
| v0.4 LTP | v1 (a) (decision 5) | |
| v0.5 live reconfiguration | v0, as T8 | it is in `dev`; the theorems are owed |
| v0.5 crash model K0, K5 to K8 and one platform profile | v0, as T16 | the paragraph under T5 |
| v0.5 K9 to K12 (journals, frame trailer as detector) | v1 | the FNWF/FNRJ journals those cuts belong to are development-only under D07 |
| v0.5 persisted checkpoints | done in shape; `checkpoint*` red is T0's | |
| v0.5 index adoption | v1 (b) | `msgid-index` is green and unused; nothing measured needs it at v0's scale |
| v0.5 compaction | v1 (d) | D03 |
| v0.6 identity and authority | v0, as T10 (decision 2) | |
| v0.6 include-hygiene backlog | T1 takes the codec half; the rest is v1 tooling | |
| v0.6 one gate over every root | replaced: the image closure green at every convergence is the gate; the rest of the tree is green or retired | the treewide gate is what turned every red into everyone's red |

## 3. B. The steps

Each step is DONE or NOT. DONE means: the theorems named exist over the named
subject, their teeth book exists, `green_check --changed-since --strict` is
clean for the books the step touched and their dependents, the observable
behaviour is measured on an image, and the evidence file named exists. A step
that would need a `partial` row is two steps.

Lane-days are estimates from the record (a freeze lane took four to five
hours to one repair before the tools existed, review F5; the NEWNEWS lane
landed five keystones with teeth in one day; the operator-verbs lane in one).
Tier follows ember's preference: Opus for most, Fable for the seams.

| Step | Name | DONE when | Depends on | Books and host | Days | Tier |
| --- | --- | --- | --- | --- | --- | --- |
| T0 | Green image, deployed node | image closure green; images frozen under `build/images/<rev>/`; `hbox-node-deploy.sh` run; `node_probe.py` exits 0 from the laptop; matrix run on the image; the node's page lists which of P1 to P11 hold | in flight (w31-freeze-3, w32-native-guards) | the eight reds' books | 1 to 2 left, root 0.5 | Opus |
| T1 | Codec boundary | `theory_check --strict` wired into `make check` at zero codec openings; every proof above the seam uses only the seam's constraints; encoded bytes unchanged (a golden-vector control); certify wall of `store-node-invariants` and `feed-connection-invariants` measured before and after | T0 (so the deploy is not held) | §4.1 | 2 seam + 6 to 8 across four cluster lanes | Fable seam, Opus clusters |
| T2a | Acceptance stamp in the record | [`specs/acceptance-stamp.md`](../specs/acceptance-stamp.md) §2.1 to §2.5 and §6: the eleventh field fixed at prepare, schema 1 with schema-0 bytes decoding as `:legacy`, the codec, prepare, finish and replay theorems with teeth, a clock the node cannot use refusing the submission as its own completion kind; the four callers the design found (the signed submission, BP ingress and its receiver books, the checkpoint codec, the D10-a reply path) | T1 (the seam exports the magic and the schema octet) | `records*`, `acceptance*`, `node`, `replay*`, `store-node*`, `hybrid-store`, `bp-ingress`, `checkpoint-codec`, `owner`, `nntp-post`, `peer-inbound`; `host/store-node-host.lisp:443` (prepare), `:549` and `host/owner-host.lisp:415` (finish) | 5 to 7 | Fable |
| T2b | NEWNEWS over the stamp | the design's §2.6: `fn-nntp-newnews-scan-is-the-acceptance-filter` as an equation with an independent filter, no article octet read, the parse budget and its 503 retired; a legacy article dated by the nearest later stamp; NNT-008 restated with the `O(A·G')` sentence; matrix rows `V0-READ-NEWNEWS-STAMP` and `-LEGACY` | T2a | `nntp-responses`, `nntp-newnews`, `nntp-invariants`, `nntp-effects` | 1.5 to 2 | Opus |
| T3 | One owner for duplicate-vs-conflict | `fn-sn-existing-action` in `books/store-node.lisp`; `fn-sn-existing-action-is-duplicate-iff-byte-identical-by-definition` and its refusal sibling state direct case equations (not keystones); `must-fail` per hypothesis; the four host lines call it; `host/store-host.lisp:138` deleted; OBJ-002's open item closed | T2 | `store-node`, `store-node-invariants`, three host files | 1 | Opus |
| T4 | `fn-sn-finish` per arm, index on every arm | one theorem per arm for each of the four keystones the freeze made conditional; the retention and identity arms stated positively; `fn-sn-finish-preserves-indexedp` with no arm hypothesis; PRF-023 events updated; PRF-050's sequence invariant from `w25/prf050-identity-sequence` certified or retired by name | T2 | `store-node-invariants`, `stx-lace`, `stx-index`, `store-prepare-correspondence` | 3 to 4 | Fable |
| T5 | POST is durable end to end | `fn-own-240-follows-consumed-completion`: the `240` effect of the owner on a `(:complete)` event equals `fn-store-sn-finish`'s `:durable`, and no `240` otherwise; the 14-cut campaign passes on the developer image at every cut with the record expectation the table states; NNT-005 `implemented` | T2 | `owner`, `owner-invariants`, `nntp-post`; `host/owner-host.lisp:409-425`; `tests/campaign/native_cuts.py`, `tests/test_native_crash_model.py` | 3 to 4 | Opus |
| T6 | Reader pins and concurrency | `fn-own-read-of-a-pinned-reader-is-stable-under-another-connections-complete`; `max-conns` refusal theorem; measured on the image with two clients (matrix rows `V0-READ-*` pinned across POST); NNT-006 note rewritten | T5 (same books, same lane) | `owner`, `owner-invariants`; `host/native/owner.lisp` | 2 to 3 | Opus |
| T7 | Login and the protected channel as one property | PRF-031 events cited; `tests/acl2/nntp-auth-teeth-tests.lisp` with one `must-fail` per hypothesis of `fn-auth-gated-command-is-refused-and-not-performed` and the two PRF-039 greeting theorems; `owner-tls-prefix` green; `node_probe.py` 483-then-login row on the image | T0 | `nntp-auth`, `nntp-auth-invariants`, `served-tls-prefix`, `owner-tls-prefix` | 2 | Opus |
| T8 | Live reconfiguration: the theorems and the live path | DONE 2026-09-22: the two headline theorems of `specs/reconfiguration.md` stated over `fn-ocfg-step` and the config replay with teeth; PRF-028 curated; the live arm's octet labels and the unpublished second reconfiguration fixed; a live `peer add` test on the developer image | T0 | `owner-config`, `native-admin`, `config-records`; `host/native-admin-host.lisp` | 2 | Opus |
| T8b | The live node adopts a new domain and capacity | a group created live is served before any restart (`GROUP`, `LIST ACTIVE`, `POST` into it) and a capacity change takes effect live; a per-connection domain in `fn-own-conn-okp` and the store re-parameterised, proved against `fn-snt-relation`; `V0-CFG-LIVE` accepted on the image | T2, T4 | `owner`, `owner-invariants`, `store-node*`; `host/native-admin-host.lisp` | 3 to 4 | Opus |
| T9 | Peering complete | (a) PRF-029 cited with teeth; K5 `fn-feed-replay-is-the-live-feed-modulo-inflight` proved or replaced by a K5 theorem over `fn-feed-tick-step` and the FNFD journal the host writes, the open row retired by name; (b) `fn-peer-transfer-stores-the-offered-octets-modulo-path-and-xref`; the peer-row round trip from `w29-peer-row-roundtrip` certified or its open row retired by name; (c) PRF-047/051 cited with teeth; gate: the matrix's two nodes on one box, TLS and AUTHINFO both ways, a `kill -9` of the sender mid-transfer, exactly one copy after restart | T1 for (a) (`feed-journal` is a codec opener); T0 for (b), (c) | (a) `owner-feed`, `peer-feed*`, `feed-journal`; (b) `peer-inbound*`, `path`, `peer-config`; (c) `feed-connection*`, `feed-auth-profile`; `host/native/feed-service.lisp` | 6 to 10 across three lanes | Opus, Fable for (a) |
| T10 | Signatures an agent can check | (a) node: `fn-hsig-subject-body` injectivity; `fn-stxe-profile-supportedp` recognises the hybrid profile and its decoder is proved; the verdict arm of `fn-sn-finish` evaluates in the image (an attachment for `fn-sig-verify` in the pattern of `books/crypto-attach.lisp`, or an observed-verdict argument, named in `specs/identity.md`); the portable carrier from `recovery/portable-hybrid-authorship` decided against `FN-Statement` (one carrier per signature kind); (b) reader: S6 `HDR :fn-verified` with the three-token rendering and `fn-stx-reader-verdict-is-the-recorded-verdict`; (c) client: `principal new` derives the id from a seed, `fn_client.py post --sign`; a second agent verifies with its own keyring and no fn code; OBJ-003/OBJ-007 `implemented` | T4, T1 | (a) `hybrid-*`, `stx-evidence-records`, `crypto-attach`, `host/native/hybrid-control.lisp`, `signatures.lisp`; (b) `nntp-responses`, `nntp-effects`, `nntp-invariants`; (c) `tools/fn_client.py`, `host/native/operator.lisp` | 8 to 12 across three lanes | Fable (a), Opus |
| T11 | Capacity refusal keystone | `fn-retain-admit-refuses-unaffordable-obligation` with teeth; RET-002 `implemented`; `V0-CAP-REFUSE` on the image | T0 | `retention`, `retention-invariants` | 1 | Sonnet |
| T12 | DTN | (a) the node machine: `fn-bpn-statep`, the bundle list, `fn-bpn-step`, `fn-bpn-trace`, reassembly through `bp-fragment`, dispatch (deliver versus forward), status reports; T1 to T6 of `specs/bp-design.md` §1.6 certified with the teeth its packet 3 names; `host/native/bp.lisp` receive and forward call `fn-bpn-step`; K6: the inbound transit decision of an ADU is `fn-peer-decide-transfer`; (b) the bundle store: the FNBS record family and the `(:bpn-sequence n)` frontier (packet 1), `fn-bpn-replay-journal-is-trace`, PRF-045 closed over the host's recover/reserve, the process-death cuts re-targeted at FNBS; (c) contacts: the contact scheduler native (`books/scheduler` called from `host/native/bp-service.lisp`, `tools/scheduler.py` retired), packet 6's status alignment, and the v0.3 gate: two DTN images and a relay on one box, an interrupted contact, an expiry, staging exhaustion, receipts back, recorded; (d) obligations: `fn-retain-release` called from the BP path on a matching application receipt and never on a carrier ACK, PRF-012's discharge theorem over that caller, RET-004's evidence typed (issuer, nonce, incarnation) | (a) T1's BP cluster; (b) T1; (c) (a), (b); (d) (c) | (a) `bp-node`, `bp-node-machine*`, `bp-fragment*`, `host/native/bp.lisp`; (b) `bp-node-records`, `bp-sequence-*`, `frame`; (c) `scheduler*`, `bp-workflow*`, `host/native/bp-service.lisp`; (d) `bp-release*`, `retention`, `bp-receipt*` | (a) 8 to 12, (b) 3 to 5, (c) 5 to 8, (d) 4 to 6 | Fable (a), Opus |
| T13 | v0 record | the matrix on the v0 image with every reached row agreeing; the INN lab on hbox; the dtn7-rs and ION labs (packet 7, I2 and I3) against the DTN image; the hbox-to-persvati protected exchange as its own row (decision 8); `planning/evidence/v0-<rev>.md` | T5 to T12 | tools and evidence only | 3 | Opus |
| T14 | Registry hygiene | §4.5 done; `ledger.py --check` and `evidence_manifests.py check` green | none | registries, `tests/acl2/owner-fault-tests.lisp` | 1 | root, Sonnet |
| T15 | Retirement | §5 done | decisions 3, 4 | planning tree, worktrees | 0.5 | root |
| T16 | Durability qualified (D14) | (a) K0 `fn-bs-step-preserves-k0-coverage` over the frontier, record, finish and recover programs (`byte-store-programs.lisp:155-256`), K5, K6, K8; (b) one platform profile: hbox's filesystem, torn-write injection through the model's image constructor applied to real files (`specs/crash-model-v2.md` §5.1, §5.2), a power-cut or `dm-flakey` run on a scratch pool, the profile written into `specs/failures.md` and the node's page Since 2026-09-25 (lane k0-general-step) `fn-bs-step-preserves-k0-coverage` covers every create, write, non-authority fsync, staging/record/marker barrier, non-authority unlink, frontier and marker rename, transaction link and the non-commit and commit observations with any outcome, so a program built from those steps is covered at every cut by construction; still open for (a): `(:record-file :ok)`, `(:record-link :ok)`, the staging and transaction barriers' error outcomes and the recovery window, and the per-cut theorems are not yet re-derived from it; a platform run still needs real power loss and the platform's fsync semantics (b). | T5 | (a) `byte-store-relation`, `-program-invariants`, `-keystones`, `-scan`; (b) `tests/campaign/`, `tools/runbooks/` | (a) 6 to 10, (b) 3 to 5 | Fable (a), Opus (b) |
| T17 | Message-ID index on the served path | first step of v1; briefed from `w28/nntp-msgid-index` (§5.2) | T10b | `msgid-index`, `nntp*`, `served`, `owner*` | 3 to 4 | Opus |

**Status at 2026-09-24 (dev `46f2660d`).** Only T8 was marked DONE in this
table when it was written. The records below show later work; none of them
was re-checked against every clause of the DONE definition above, so no
other step is marked DONE here.

- T0: an image was frozen and deployed; the live node runs `da5fd8cb`
  ([node record](evidence/node-hbox-da5fd8cb-2026-09-23.md)). The "node's page
  lists P1 to P11" clause is not re-verified.
- T2a: the acceptance stamp landed
  ([lane evidence](evidence/t2a-acceptance-stamp-4670cc35-2026-09-23.md)) and
  was built into a native image ([daa6c15e](evidence/t2-native-daa6c15e-2026-09-23.md)).
- T2b: NEWNEWS over the stamp was exercised natively on the frozen 329 image
  ([migration record](evidence/t2b-newnews-migration-329-2026-09-23.md)).
- T8: DONE 2026-09-22; live configuration also passed on the `295bbe35`
  image ([record](evidence/native-t8-t10a-295bbe35-2026-09-23.md)).
- T10a: author/reopen tests passed on the `295bbe35` image (same record);
  local author lifecycle is integrated with the scope the
  [wind-down handoff](handoff-2026-09-24-winddown.md) states.
- T12: BP forwarding is integrated, but the final cut's three red roots are
  in the BP progress machine and no image past `863c2141` exists (handoff,
  "Final cut"). Not DONE.
- T16: a bounded private-device observation exists
  ([record](evidence/t16-private-publication-profile-2026-09-24.md)); it is
  not a platform qualification. Not DONE.
- T1, T3 to T7, T8b, T9, T11, T13 to T15, T17: not re-verified.

### 3.1 The steps in detail

**T0.** The subject is the image closure itself. The freeze-3 lane owns the
store-node reds (`fn-snt-record-directory-preserves-relation`,
`fn-sn-known-abort-is-exact-node-abort`, `fn-sn-observed-seed-is-state`,
`fn-spc-candidate-txid-is-frontier-predecessor`, and `checkpoint` if it is
still red on the next wave); the native-guards lane owns the four guard
conjectures and the test assertion. Root's part after both land: one
provisional wave over the default closure, `hbox-image-build.sh`,
`hbox-node-deploy.sh`, `node_probe.py`, the matrix on the image, and the
evidence file `planning/evidence/native-deploy-hbox-<rev>-2026-09-2x.md`.
Then yue, tulip and ember post on it. That is the first usable thing, and it
is before every other step. Its page says: P1, P2's outcomes, P3's numbers,
P4, P5, P6 and P9 are what the image does; P7 holds on loopback only; P8, P10
past process death and P11 do not hold yet.

**T1.** §4.1. It goes second because every proof step after it (T2, T4, T5,
T6, T9a, T12) lives in books that open the record, CBOR or frame codec
book-wide today, and the freeze records say that is where proofs stop
returning. Its control is that encoded bytes do not change: the schema-0
golden vector (`records.lisp:801`) and every golden vector under
`tests/vectors/` decode and re-encode identically before and after.

**T2. The acceptance stamp.** Decision 6. The record is `fn-record-make
sequence txid generation msgid payload groups obligation subject evidence
charge` at schema 0 (`records.lisp:41,158`). The stamp is an eleventh field:
the owner's clock observation under which the record was prepared (D10-a: the
observation `fn-own-read` supplies with the submission), so it is in the
bytes that become durable at the commit, which is what "the instant this node
accepted it" means; there is no second write. Schema 1 carries it; a schema-0
record decodes with the stamp `:legacy`, so the 915 stores and every store on
disk replay unchanged, which is ENC-004's evolution rule made concrete for the
first time. The properties, each a theorem: `fn-record-round-trip` and
`fn-record-accepted-input-is-canonical` at schema 1 and the schema-0
acceptance as `:legacy`; `fn-sn-finish-installs-the-stamp-the-record-carries`
over the article arm (the arm T4 states); `fn-replay-apply-record-installs-the-stamp`;
`fn-nntp-newnews-scan-reports-only-articles-accepted-at-or-after`, restated
over `fn-article-stamp` instead of the `Injection-Date` decoder of
`nntp-responses.lisp:1880-1952`, which then leaves the served path (its 256-
article parse budget was the cost of parsing dates per query; a stamp
comparison is a natural-number test, so the budget theorem is restated as a
bound on candidates, not on parsing). The host lines are `fn-store-sn-prepare`
(`host/store-node-host.lisp:443`) and `fn-owner-prepare`
(`host/owner-host.lisp:304`), which gain the observation argument the owner
already holds. Its teeth: a schema-0 record's stamp is `:legacy`; a NEWNEWS at
an instant after the stamp does not report the article; a stamp cannot be
supplied by the client (the `Injection-Date` header stays what it is, a
claim). Where it goes: **after T1 and before T3, T4, T5, T6.** Before T1, the
widened codec is re-proved inside every book that opens it book-wide, which
is F3's cost paid once more across 55 books; after T1 the change is one field
in the codec books and one accessor exported by the seam, and the books
above see an accessor. Before T4 to T6, because those steps state theorems
over `fn-sn-finish` and the owner, and stating them over a record that is
about to widen means proving them twice. T2 is therefore the one red umbrella
of phase 2, on one lane, on hbox, and it is the reason phase 3 waits for it.
4 to 6 lane-days, Fable, because the change crosses the record, the store
machine and the reader in one batch and the arm theorems of T4 are proved
against its result.

**T3.** `fn-store-article-match` (`host/store-host.lisp:138`) compares payload
and groups of a found article and answers `:duplicate`, `:conflict` or `nil`.
The step moves it into `books/store-node.lisp` as `fn-sn-existing-action`
over `(fn-sn-node s)` and states it: the answer is `:duplicate` exactly when
the held article's payload and groups are the submitted octets and list,
`:conflict` exactly when the Message-ID is held and either differs, `nil`
otherwise; teeth flip each of payload, groups and the binding. Its host
lines are `host/store-node-host.lisp:461,580` and `host/owner-host.lisp:323,953`;
the matrix row `V0-OUT-REFUSED` is the witness. After T2 because both edit
`store-node`.

**T4.** The freeze made four keystones conditional on the article arm
because they were false on the retention and identity arms
([second freeze record](evidence/native-freeze-01fbdad4-2026-09-22.md)). A
hypothesis that names the arm is a claim about one third of the function the
host calls. The step states each arm: what the retention arm publishes (a
retention event, no article, the index unchanged), what the identity arm
publishes (a keyring or verdict event, the index grown by the accepted
statement's delta), and the article arm as before, now with T2's stamp.
`fn-sn-finish-preserves-indexedp` then has no arm hypothesis; the book's own
comment (`store-node-invariants.lisp:1090`) names the three facts the
accepted-statement arm needs. PRF-023 cites the unconditional theorem. The
lane is briefed from `w25/prf050-identity-sequence` (§5.2): its phase-aware
sequence invariant is the fact `fn-spc-candidate-txid-is-frontier-predecessor`
(one of T0's reds) is reaching for.

**T5, and the durability question.** Today
`fn-sn-new-success-requires-actual-matching-durable-node-completion` says the
store cannot acknowledge without a completion, and
`host/store-node-host.lisp:545-560` reports `:durable` only for the transition
that consumed this pending completion. What no theorem says is that the `240`
the connection receives is that report: `host/owner-host.lisp:409` says
"completion is the owner's `(:complete)` event" in a comment. The theorem is
over the owner step `fn-owner-step` calls at `host/owner-host.lisp:211` and
equates the `240` effect on the `(:complete)` event with the durable report.
The campaign half: every cut in `tests/campaign/native_cuts.py` runs against
the developer image built by T0 (`tests/test_native_crash_model.py` runs all
native POST cuts when `FN_NATIVE_CRASH_HOST` names one and refuses to skip
otherwise), and each recovered store shows the record the table expects; a
cut that carries `gap` is a failed step.

*ember asked: "What's the deal with durability / D14? Is this something we
can just address?"* D14 (`planning/decisions.md`) selected "pure crash model
first; qualify one Linux local-filesystem profile before deployment durability
claims". What exists: the byte-level model and K1 to K4 (every crash image of
a related store scans, is kernel-admissible, is reproduced by the constructor,
and reopens with every acknowledged record; PRF-041), K7 for the four native
authority boundaries, and the 14 process-death cuts each with a byte-program
coordinate. What is missing, plainly: (i) **K0**, that the host's own
programs keep the byte store related to the kernel state, is proved for
initialization and the first frontier program under input contracts
(PRF-044) and open for "general syscall preservation, recovery
establishment, retained-history composition, config-history refinement,
existing/retry initialization" (`specs/crash-model-v2.md:1923`); every K1
to K4 theorem takes the relation as a hypothesis, so today they describe a
store the host has not been proved to produce; (ii) **K5, K6, K8** (stable
prefix at the byte level, no partial transaction visible, the completed fence
removes the choice) are open; (iii) **no platform profile**: nothing has
injected a torn write into a real file or cut power on a real pool, and the
deployed filesystem (hbox's) has no stated profile; the review's APFS
`F_FULLFSYNC` finding is a macOS development matter and not the deployed
box's. So the durability claim the node can make today is "an acknowledged
article survives process death on Linux, in the cuts the campaign takes", and
it can make that claim once T5's campaign runs on the image. Closing D14 is
two bounded steps, not one: T16a, the proofs (Fable, 6 to 10 lane-days: K0
general preservation over the four programs, then K5/K6/K8, which follow the
shape K1 to K4 already have); and T16b, the profile (Opus, 3 to 5 lane-days:
the image-import differential check of §5.1 against real files on hbox,
torn-write injection per §5.2, one power-cut or `dm-flakey` run on a scratch
pool, and the profile sentence in `specs/failures.md`). Neither blocks the
deployed node; both are v0 steps (phase 5), and until T16b lands the node's
page says "power loss unqualified". Yes, it can be addressed; it is about
nine to fifteen lane-days, and the proof half is the harder one.

**T6.** The owner pins a reader's archive at open (`books/owner.lisp:18`,
`:504`). The theorem: for a connection pinned at version `v`, `fn-own-read`
after another connection's `(:complete)` answers exactly what it answered
before. NNT-006's note says no run establishes it; the matrix's two-readers
rows are the run. `max-conns` gets its refusal theorem beside it. Same lane
as T5, after it, because both edit `owner-invariants`.

**T7.** The theorems exist; the registry and the teeth do not. PRF-031's
statement names `fn-auth-gated-command-is-refused-and-not-performed`
(`books/nntp-auth.lisp:1348`) and carries zero events. The step adds the
teeth book, cites the events, turns `owner-tls-prefix` green with the
freeze-3 pattern (state the arm, do not open the codec), and records the
483-then-login probe on the image. It touches no codec opener, so it runs in
phase 0 beside T0.

**T8.** `specs/reconfiguration.md` says "this document contains no proved
theorem". Its two headline claims become theorems over `fn-ocfg-step` and
`fn-own-reconfigure`, which `host/owner-host.lisp:214` and `:229-267` call.
The live-admin review's codec finding is already repaired
(`fn-nctrl-admin-argv-encode`, `books/native-control.lisp:188`); the step
records that with a live `peer add` test, which that review said did not
exist.

**T9.** Three lanes on disjoint books. (a) The feed: PRF-029's theorem
exists (`fn-own-feed-target-is-offerable`, `owner-feed.lisp:790`) and is
uncited; K5's general equation is open because "the live side" was never
built (`specs/peering.md` §4 K5 row): the step either builds the live emitter
as a machine and proves the equation, or states K5 over `fn-feed-tick-step`
and the FNFD journal the host actually writes and retires the open row by
name. (b) Inbound: an octet-preservation theorem, that what `fn-peer-transfer`
stores is the offered octets with Path prepended and Xref removed and nothing
else (RFC 5537 §3.6), which the 915 run measured and no book states; and the
peer-row round trip. (c) Outbound transport: PRF-047 and PRF-051 name their
theorems and carry zero events; the step cites them with teeth. The gate is
the matrix's two nodes on one box (decision 8): TLS, AUTHINFO both ways, a
post on each arriving on the other, `kill -9` of the sender mid-transfer,
exactly one copy after restart, recorded.

**T10.** The verdict the node records at acceptance is what an agent reads
back (S6, `specs/substrate-transport.md` §5); the node holds no signing key
and attaches nothing (departure 3, §10). Three things are missing in the
node and one in the client. `fn-stxe-profile-supportedp`
(`stx-evidence-records.lisp:61`) returns `nil` for every profile, so a
correctly signed kind-4 event is `:unsupported-profile` to every reader
(hybrid review, finding 2). The article arm of `fn-sn-finish` calls
`fn-stx-verdict-of-octets`, which reaches `fn-sig-verify`, constrained in
`books/crypto-seam.lisp:109-124` with no attachment in `books/` or `host/`;
how the image evaluates that arm on a signed article has to be named and
tested before anything else in this step. S6 is a shared-struct change to
`nntp-responses`, `nntp-invariants` and `nntp-effects` (the OVER extension is
declined in favour of `HDR` alone, as §5 allows). The client gains `--sign`
with the key file it already refuses to read unless mode 0600.
`fn-hsig-subject-body` injectivity (hybrid review, finding 3) is the theorem
the step proves first. The carrier question (§5.2, branch 6) is decided in
(a).

**T12.** Decision 1 puts the DTN path in v0. The contract is
[`specs/bp-node-machine.md`](../specs/bp-node-machine.md), revised on
2026-09-22 against [gpt-6's review](review-2026-09-22-bp-node-machine.md);
its §11 replaces the four steps T12a to T12d with slices whose briefs,
boxes, sizes and acceptance traces (BP-R01 to BP-R24) are stated there:
A1 the machine, the TCPCL refusal and the two-process article-and-receipt
round trip with its crash cuts on the real owner Store (hbox, Fable, 7 to
9 days); A2 the records and the replay theorems (3 to 4); A3 the
obligation release, the receipt outbox, the scheduler runner and K6
(persvati, 5 to 6, K6 gated on T1's BP-receiver cluster); B the serialized
service loop, routes, the three-process gate with the sender's carrier
discarded and with reports dropped (hbox, Fable, 5 to 7); C1 fragment
lemmas, the fast reassembler and the limits table (2 to 3); C2 the fragment
families in the machine (after B, 3 to 4); D1a the status-report codec (1 to
2) and D1b minimal deletion-report generation and consumption as B's first
batch; D2 the rest of the reports, the administrative path and independent
wire vectors (2 to 3); E journal exhaustion, rotation and the operating
envelope (after B, 2 to 3). After the second review's contract patch the
slices total 37 to 50 lane-days against the 20 to 31 the four steps
carried; each slice's first commit is its rows of the spec's counterexample
suite (§11.1); the receive path merges only with A2's replay theorems
certified.
D07 stands: the scheduler's policy is `books/scheduler` behind a prepare,
publish, complete runner called from the native host; `tools/scheduler.py`
retires with B. LTP follows (decision 5).

**T16.** The paragraph under T5.

**T11, T13, T14, T15, T17** are as the table says.

### 3.2 The critical path

Two chains of about equal length run to v0, and they share T1:

```
T0 ─ deploy ─ T1(seam+store) ─ T2 ─┬─ T4 ─ T10a ─ T10b ─┐
                                   └─ T5 ─ T6 ──────────┤
                 T1(BP cluster) ─ T12a ─ T12c ─ T12d ────┼─ T13 = v0
                                   T9a/b/c ──────────────┤
                                   T16a/b ───────────────┘
```

The critical path to *a deployed node agents use* is T0 alone. The critical
path to *v0* is the longer of the two chains: T0, T1 (seam and store cluster),
T2, T4, T10a, T10b, T13, about 26 to 36 lane-days sequential; and T0, T1 (BP
cluster), T12a, T12c, T12d, T13, about 24 to 35. T1 is on both on purpose: it
is the change that makes the proofs after it return. Summing the table, v0 is
about 75 to 110 lane-days in all.

The five-lane phase schedule that was §3.3 was removed on 2026-09-24; it
was superseded by ember's 2026-09-23 width correction. Lane width and the
compute budget are in [how we work](how-we-work.md).

## 4. C. Structural steps

### 4.1 The codec boundary (T1)

Finding F3: a book that opens `fn-record-codec-vocabulary` at the top puts
the record codec into every proof in it; when the bounded CBOR profile made
the codecs larger on 2026-09-21, proofs across the tree stopped returning.
`theory_check` names 74 books, 17 theories: the CBOR pair
(`books/cbor.lisp:425-430`), the record triple (`records.lisp:818-840`), the
frame vocabularies (`frame-octets.lisp:263`, `frame.lisp:247-256`),
`fn-stmt-internals` (`statement.lisp:788`), and the checkpoint, config and
provenance codecs.

The shape, with its precedent in the tree. `books/crypto-seam.lisp`
constrains `fn-digest` in an `encapsulate`; `books/crypto-attach.lisp`
attaches `books/sha256.lisp`'s definition with `defattach` after discharging
every constraint; `books/byte-store-frame.lisp:317-320` and
`byte-store-txn-name.lisp:289` do the same for the frontier and name
codecs. The step does it for the four codec families:

1. A seam book per family (`books/cbor-seam.lisp`, `records-seam.lisp`,
   `frame-seam.lisp`, `statement-seam.lisp`): an `encapsulate` constraining
   the encoder, the exact decoder and the accepted-input recognizer, exporting
   exactly the properties the books above use today, which the registries
   already name (round trip both ways, accepted-input canonicality, the
   input and work bounds, the guard facts, kind dispatch on a decoded record).
   The local witnesses are the real definitions, so satisfiability is proved
   once. The bounded-item streaming proofs of `w27/bounded-event-profiles`
   (§5.2) are constraints of the CBOR seam, which is where they were headed.
2. An attach book per family, `defattach`ing the real definitions, included
   by the image build files and by the test books that evaluate ground
   vectors. Evaluation in the image is unchanged; `defattach` adds no axiom.
3. Every book above the seam includes the seam, not the codec. A proof that
   needed the codec body is a proof that was reasoning about the wrong
   thing; each such site is repaired by stating the fact it needed as a
   constraint (if it is a codec property) or as a theorem in the codec's own
   invariants book (if it is a record-shape fact; the record accessors and
   recognizers are not codecs and stay concrete).
4. `tools/theory_check.py --strict` in `make check`, so a new book cannot
   reopen a codec.

Order and size: the seam books and one cluster (store: `store-files*`,
`store-node*`, `store-observed*`, `store-prepare-correspondence`, `replay`,
`config-records`, `node-config`, `checkpoint*`) first, two days, Fable, since
that cluster is where the freeze paid; then the BP receiver cluster (hbox,
from the day the seam books exist, because T12a needs it), the
stx/identity/lace cluster and the frame/anchor/transfer-journal cluster
(persvati, phase 2), one lane each. The measurement that decides the step is
the certify wall of `books/store-node-invariants` and
`feed-connection-invariants` (the one that timed out four times, review F2)
before and after, on the same box with its load named.

### 4.2 The article match into a book (T3). §3.1.

### 4.3 The `fn-sn-finish` arms and the indexedp gap (T4). §3.1.

### 4.4 The acceptance stamp as a schema step (T2). §3.1.

### 4.5 Registry findings, and what each row should say

Found by reading `proofs.json`, `proof-events.json`, `requirements.json`,
the ledger and `green_check` against each other. The exact edits are §7.

1. **`certified` over red books.** PRF-036 cites theorems in
   `store-node-traces` and `store-observed` (red); PRF-037 cites
   `checkpoint-codec` (red); PRF-041 cites `byte-store-keystones` (red).
   A `certified` status is a claim about bytes no run has accepted.
   Structural fix, T14: `ledger.py --check` fails a `certified` target whose
   cited book `green_check` reads red or never, so this cannot recur.
2. **Stale `pending_subject` notes on PRF-028.** All four events say "No
   host line calls any `fn-ocfg-` function". `host/owner-host.lisp:214`
   calls `fn-ocfg-step`, `:232` `fn-ocfg-reconfig-refusal`, `:610`
   `fn-ocfg-open-peer`, `:1005` `fn-ocfg-open`.
3. **Eleven `in-progress` targets with zero events**: PRF-009, 027, 029,
   031, 033, 038, 040, 047, 049, 050, 051. For 029, 031, 033, 038, 040 the
   theorem the status text names exists in a book (`owner-feed.lisp:790`,
   `nntp-auth.lisp:1348`, `owner-invariants.lisp:869`, `bp-bundle-invariants`
   and `bp-node` per PRF-038's own note, `owner-fault.lisp:128-170`); the
   events were never curated. For 047 and 051 the status text names
   `fn-fc-step` theorems the lane should cite if they exist in
   `feed-connection-invariants`. For 009, 027, 049, 050 no theorem exists
   yet.
4. **`implemented` rows whose own notes walk the claim back.** NNT-006 ("a
   reader's pinned snapshot surviving another connection's POST is NOT
   established by any run"); REP-002 ("convergence across two real peers is
   the K3 seam, which no book states"); STO-005 ("one kill point only, and a
   SIGKILL is not a power loss"); NNT-005 is `specified` and its note still
   says `books/owner` "does not certify", which stopped being the reason on
   2026-09-20.
5. **Three `pending_subject` events on functions with no caller** (PRF-011,
   PRF-016 on `fn-transfer-missing-ranges`; PRF-025 on
   `fn-stx-commits-of-batch`). These are v1 features, not missing evidence
   (`docs/proofs.md`, assurance scope).
6. **PRF-037's subject.** `fn-cpc-validp` has no caller; the served restore
   path is `host/checkpoint-host.lisp` to `fn-checkpoint-restore`.
7. **`unreachable-in-composition`.** `fn-sn-fence-node` and
   `fn-sn-resolve-node` are marked at `store-node-invariants.lisp:631` and
   kept "as documentation"; the rule allows the mark. No change. The
   `:duplicate` branch of `fn-bpr-accept-request` the independent review
   called unreachable in production (§4, last row) carries no mark; T12a
   decides it.
8. **The 61 suspect-shaped theorems** are all uncited and most are named
   `-unfolds`, `-by-definition`, `-is-no-op` as the rule asks. No change.

## 5. D. What to retire

### 5.1 Rows, tables, the release criterion

The v0 checklist in `milestones.md` ("Historical snapshot", six per-wave
tables) and the six `planning/evidence/fiber-*-2026-09-20.md` records as the
definition of v0; §3's table replaces them (decision 3). The
`planning/v0-matrix.json` selected run: it is the Python service at
`3f68944` on 2026-09-21; the first native run root publishes replaces it, and
until then the file says it is superseded. The "one gate over every root"
release criterion (§2.3, last row).

### 5.2 The seven checkpointed branches: each one's disposition

Decision 4. Worktrees are removed (root is doing it); branches stay until the
step named has taken what it takes, then are deleted with the step's landing
note naming the commits it took. Measured with `git log dev..<branch>` and
`git diff --stat dev...<branch>` at `d69e9952`.

| Branch | What it holds | Disposition |
| --- | --- | --- |
| `w27/bounded-event-profiles` (7 ahead, 266 behind; `cbor*`, `statement*`, `stx-*-records`, `store-events`, `byte-store-frame`, `host/store-host.lisp`) | bounded item streaming codec proofs; "validate exact item streams once"; "gate publication by ACL2 profile and kind"; a WIP generalization (`2e1ee241`, uncertified). `30908693` of it is already on `dev`. | **T1's brief.** Take: the bounded streaming correspondence and single-validation theorems as constraints of the CBOR and record seams. Drop: `2e1ee241` (the lane rewrites it against the seam) and the `host/store-host.lisp` change (T1 touches no host decision). |
| `w25/prf050-identity-sequence` (9 ahead, 185 behind; `store-node`, `store-prepare-correspondence`, `owner-prepare-correspondence`, new `store-identity-sequence-invariants`, both prepare host files) | the phase-aware journal-sequence invariant, fast identity/retention staging callers, and their relation teeth; PRF-050's target | **T4's brief.** Take: `store-identity-sequence-invariants` and the two teeth commits; the invariant is what `fn-spc-candidate-txid-is-frontier-predecessor` (a T0 red) needs stated. Drop: `3d81f0af` (duplicate of the bounded-streaming commit above) and the host-file edits, which T4 re-derives against T2's record. PRF-050's events come from what T4 certifies. |
| `w28/nntp-msgid-index` (9 ahead, 158 behind; `msgid-index`, `nntp*`, `served`, `owner*`, `peer-inbound`) | the trie on the served Message-ID path, the pinned-index owner refresh, the indexed dispatch boundary | **T17's brief, first step of v1.** Reason it is not v0: it rewrites the same served chain T10b rewrites, and nothing measured needs it at v0's scale ([shared-owner cost](evidence/native-shared-owner-2026-09-21.md) motivates it without a served-path measurement). Take: all nine commits as the starting point, re-proved over T10b's chain. |
| `w26/reclaim-keystone-teeth` (2 ahead, 128 behind; `1c827183` one tooth, `e7d110d5` 126,343 lines of archived certification logs) | the crash-image premise tooth for the reclaim keystone; logs | **Retired.** `1c827183` is cherry-picked into the v1 compaction step's brief when it opens; `e7d110d5` is dropped, because logs are not evidence (manifests are, `planning/evidence-index.md`) and 126 k lines in the tree is a cost with no reader. Delete the branch after the cherry-pick is recorded. |
| `w29-peer-row-roundtrip` (2 ahead, 192 behind; `peer-config.lisp`) | the rows-to-record round trip factored by components; the general theorem `fn-cfg-peer-of-rows-of-peer-rows` still absent on `dev` | **T9b's brief.** Take: the component decomposition. Acceptance: the general round trip certified, or the open row in `specs/peering.md` retired with the injectivity witnessed on ground records named as the covered scope. |
| `recovery/portable-hybrid-authorship` (3 ahead, 173 behind; new `books/hybrid-carrier.lisp`, not on `dev`) | a portable `FN-Authorship` carrier for the hybrid signature over the exact source; its source projection; mutable relay fields deliberately refused | **T10a's brief.** Take: the carrier book and its projection as the design input. The step decides one carrier per signature kind: `FN-Statement` (S1, certified) carries statements over content ids; the hybrid authorship signature covers the exact source bytes (D01) and so needs its own carrier or a stated reason it does not. Drop: nothing yet; the quiescence note's "not ACL2-admitted" commits are re-admitted by the step or dropped by name in its landing note. |
| `w26/owner-tls-overlay` (2 ahead, 142 behind; `store-files-invariants.lisp`) | Store append teeth generalized to tagged events | **Retired as superseded.** `dev` `0b0d96a0` ("Keep the Store append teeth from inducting on a theorem that is false") landed the repaired teeth. Root confirms with `git diff dev...w26/owner-tls-overlay -- books/store-files-invariants.lisp` that no theorem statement in the branch is absent from `dev`, records that in the retirement commit, and deletes the branch. |

The three detached worktrees under `build/` (`nntp-guards-work`,
`wire-guards-work`, `workflow-host-work`, at 2026-09-18 commits) are removed;
their content is the 2026-09-18 assurance and composed-store batches, landed.
The eight "recoverable packets" of the recovery note are either landed
(STARTTLS, operator admin, config namespace, BP publication, per `now.md`) or
are T12's (`w18/bp-lifecycle-assurance`, `w19/bp-app-fast-invariant`,
`w19/bp-authored-wire`): T12a's brief names those three branches as inputs
the same way, and their disposition is written in its landing note.

### 5.3 Documents that mislead, and why

| Document | Why it misleads now | Disposition |
| --- | --- | --- |
| `planning/now.md` | 384 lines in which each dated paragraph supersedes the one below it; "Current integration checkpoint" describes `773e9ae3`, superseded by 915 and then by this | rewrite to §7.2. Done 2026-09-24: the log is `planning/archive/now-2026-09-24.md` and now.md is one entry page |
| `planning/milestones.md` | the checklist (§5.1), the "earlier landing notes", and M0 to M6 whose bullets describe 2026-09-18 | §7.1 |
| `planning/swarm-cycles.md` | pre-crash Codex staffing and C1 to C3 packets; the roles section defines names this plan retires | archive to `planning/archive/`; `docs/README.md` "What should happen next" points here |
| `wide-capability-cycle-2026-09-21.md`, `recovery-2026-09-21.md`, `quiescence-2026-09-21.md`, `astra-reorientation-2026-09-21.md`, `handoff-to-codex-2026-09-19.md` | each was the plan for a day that is over; the quiescence note says "resume only on user instruction", which ember has given | archive; the branches are §5.2 |
| `planning/deputies/BOARD.md` and `deputies/*.md` | an append-only board of W12/W13 claims and cluster briefs for lanes that no longer exist | archive. Not done as of 2026-09-24: books, tests, tools and evidence records still cite `planning/deputies/` paths |
| `planning/assurance-closure.md` | a matrix whose cells say "Certified" in prose beside registries that are the ledger | archive; anything in it not in a registry note becomes one |
| `planning/evidence-index.md` | 23 record rows for 181 files in `planning/evidence/` and 64 in `tests/evidence/` | either `tools/evidence_manifests.py` generates it from the records' headers or it is retired; do not hand-extend it. Retired 2026-09-24 to `planning/archive/evidence-index.md` |
| `docs/operator.md` | its first half describes the Python development service as the operator path, against D07 | rewrite around `packaging/fn-native` and the hbox runbook; the Python half moves to `docs/development.md` |
| `docs/implementation.md` | a 2026-09-18 component table | replace with a pointer to the ledger and §2.1 |
| `specs/substrate-transport.md` §8 | the packet table names `books/statement-field.lisp` and `statement-transit.lisp`, which never existed (its own footnote says so) | replace the table with the landed book names and T10 |
| `specs/peering.md` | a design section followed by three dated status sections (waves 6, 11 and the native witness) | one status section, K1 to K7 each with its theorem or its step |
| `specs/bp-design.md` packet table | its packet 5 says the Python BPA tools are deleted; they are not, and under D07 they are development tooling | T12a's landing note says which survive as development oracles |

**Roles.** This plan proposed retiring the names Astra, Terra, Sol and Luna
with `swarm-cycles.md`. In fact the Codex swarm kept using them as GPT-6
role names through 2026-09-24. Claude-coordinated lanes are named by their
worktree (`build/lanes/<name>`), and every lane's model is written in its
brief.

## 6. What v0 does not claim

Anything about power loss until T16b, and then only the profile T16b names;
that Ed25519 or ML-DSA-65 are secure or correctly implemented (A-CRYPTO,
libsodium and OpenSSL are trust); that TLS provides confidentiality (the
handshake is a host facility, `docs/architecture.md`); that a peer is honest
(A-PEER); LTP; flight readiness. Each is written on the deployed node's page,
with the date it last changed.

## 7. Edits root makes

These are the edits as planned on 2026-09-22. Where later work overtook
them, [now.md](now.md) and the [decision register](decisions.md) govern.

### 7.1 `planning/milestones.md`

Replace lines 1 to 10 ("Post-reboot status" and both "Current task"
paragraphs) with:

> Current task (2026-09-22): the step list in
> [the trajectory plan](plan-2026-09-22-trajectory.md) §3; the current step
> is T0, the green image and the hbox node. The phase schedule is §3.3; the
> loop a lane follows is [how we work](how-we-work.md). The decisions of
> 2026-09-22 are the plan's §0.

Replace the "Release shape: v0 and v1" section with the plan's §2.2 verbatim
and a link to §3. Move the "v0 checklist" section and the "Earlier landing
notes" section under a new heading `## Retired: the six-wave shape and its
checklist (2026-09-20 to 2026-09-22)` with one sentence above them: "Retired
by decision 3 of 2026-09-22; kept as history; the fiber records under
`planning/evidence/fiber-*` are evidence for the dates they name and define
nothing." M0 to M6 stay under `## Earlier milestones`.

### 7.2 `planning/now.md`

Replace the whole file with:

> # Current work
>
> The plan is [plan-2026-09-22-trajectory](plan-2026-09-22-trajectory.md);
> the loop is [how-we-work](how-we-work.md). The deployed node is the frozen
> `915d5c72` image on persvati until T0 lands; its page is
> `docs/agents.md`. Live lanes: `w31-freeze-3` (T0, the store reds),
> `w32-native-guards` (T0, the native guard conjectures); root runs T14 and
> T15. The current phase is 0. The dated narrative this file carried is in
> `planning/archive/now-2026-09-22.md` and in the evidence records it links.

and move the old file to `planning/archive/now-2026-09-22.md`.

### 7.3 `planning/decisions.md`

Append to the resolution log:

> ### 2026-09-22: the eight questions of the trajectory plan
>
> ember answered the eight questions in `plan-2026-09-22-trajectory.md` §0,
> quoted there. Consequences: DTN is v0 (A06 and the purpose); native author
> signatures are v0 (D02, D09); LTP follows the node machine; the acceptance
> stamp is a v0 schema step (ENC-004's first exercise); the six-wave release
> shape, its checklist and the fiber records are retired; the lane worktrees
> are removed with every checkpointed branch dispositioned in the plan's
> §5.2; the Codex role names are retired; five lanes converge every two to
> three batches; peering is measured on one box first.

### 7.4 `planning/requirements.json`

- OBJ-002 note, append: "Open item: `fn-store-article-match`
  (`host/store-host.lisp:138`) decides duplicate-versus-conflict in host code;
  T3 moves it into `books/store-node` with its theorem."
- NNT-005 note, replace with: "`books/nntp-post` and `books/owner` certify at
  their last green digests; what is missing is the theorem from the served
  `240` to the consumed completion (`fn-own-240-follows-consumed-completion`)
  and the native cut campaign on an image; both are T5."
- NNT-006 note, replace the last sentence with: "The pinned view surviving
  another connection's POST is T6; the keystones cover the projection and the
  index halves."
- NNT-008 note, replace with: "NEWNEWS answers from the injector's stamp
  until T2 writes the acceptance instant into the record; then it answers
  from this node's own acceptance and the parse budget leaves the served
  path."
- REP-002 note, append: "Two-node convergence with restart is T9's gate."
- STO-005 note, replace "Open: one kill point only, and a SIGKILL is not a
  power loss." with "The 14-cut campaign on an image is T5; power loss is
  T16b."
- RET-002 note, append: "T11 states the refusal keystone."

### 7.5 `planning/proofs.json` and `planning/proof-events.json`

- PRF-036, PRF-037, PRF-041: status `in-progress`; note prefixed with
  "Certified at <run id> over an older digest; `store-node-traces`,
  `store-observed` (036), `checkpoint-codec` (037), `byte-store-keystones`
  (041) are red at their current digest per `green_check`; T0 re-establishes
  them."
- PRF-028: remove the four `pending_subject` notes; each event gains
  "host lines `host/owner-host.lisp:214` (`fn-ocfg-step`), `:232`
  (`fn-ocfg-reconfig-refusal`), `:610` (`fn-ocfg-open-peer`), `:1005`
  (`fn-ocfg-open`)"; T8 states the two headline theorems.
- PRF-029: events `fn-own-feed-target-is-offerable`,
  `fn-own-feed-targets-omit-no-offerable-peer` (both `books/owner-feed`).
  PRF-031: event `fn-auth-gated-command-is-refused-and-not-performed`
  (`books/nntp-auth`). PRF-033: events
  `fn-own-observe-refusal-names-a-contradiction` (`books/owner-invariants`)
  and `fn-post-without-a-clock-refuses-with-the-clock-line`
  (`books/nntp-post`). PRF-038: the seven theorems its note names in
  `books/bp-bundle-invariants` and `books/bp-node`. PRF-040: the five
  `fn-own-fault-*` theorems of `books/owner-fault.lisp:128-170`; note
  "teeth book owed, T14". PRF-047, PRF-051: the `fn-fc-step` theorems the
  status text names, if `ledger.py --check` accepts them; otherwise status
  `planned`.
- PRF-009, PRF-027, PRF-049, PRF-050: status `planned`, note unchanged, plus
  "no event yet; T12d (009 stays v1), T2 (027), T9c (049), T4 (050)".
- PRF-011, PRF-016, PRF-025: the `pending_subject` events move under a
  `deferred` key on the target with the note "no caller; v1".
- PRF-037 additionally: note "`fn-cpc-validp` has no caller; the served
  restore path is `host/checkpoint-host.lisp` to `fn-checkpoint-restore`;
  v1 checkpoint adoption".
- Then `python3 tools/ledger.py --write` and `--check`.

### 7.6 `AGENTS.md`, `docs/README.md`

`AGENTS.md`, "Evidence and handoff": add "A lane is briefed from
`planning/how-we-work.md` and its step in the current plan." `docs/README.md`,
"What should happen next?": "[The trajectory plan](../planning/plan-2026-09-22-trajectory.md)
§3 and its phase schedule; [how we work](../planning/how-we-work.md)."

### 7.7 The archive moves of §5.3

After decisions 3 and 4 are recorded (§7.3): `git mv` the listed planning
documents to `planning/archive/`, fix the links `make check` reports, and
commit them as one retirement commit whose message names this plan.
