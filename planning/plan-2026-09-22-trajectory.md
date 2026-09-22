# Trajectory to a node agents use, and what comes after — 2026-09-22

Status: a plan. It changes no registry, book, host file, tool or test. Where a
registry row or a document is wrong it says what the row should say and root
makes the edit (§7). Every number is a tool's, taken at `dev` `d69e9952`; every
statement about the past names the record it comes from. The two lanes in
`build/lanes/w31-freeze-3` and `build/lanes/w32-native-guards` are untouched.

Why this exists: [the proof-engineering review](review-2026-09-22-proof-engineering.md)
explains why a night produced no image, and ember asked that the old plans not
be resumed as they are: bigger steps, properties stated up front, no partial or
placeholder rows. The v0 checklist in [milestones](milestones.md) is a table of
`partial`, `open`, `blocked` and `done (with a caution)` cells, several walked
back in place; [now.md](now.md) is 384 lines of dated narrative that supersede
one another; the [wide capability cycle](wide-capability-cycle-2026-09-21.md)
ran twelve capability lanes at once and produced the five commits of
2026-09-21 that landed behaviour under invariant books nobody recertified
(review F4). None of those is the plan.

## 0. Questions for ember

Each needs your call. A recommendation is written under each; none is taken
until you say so.

**Q1. Is DTN part of "v0, a node agents can use", or is it v1?** A06 makes
BPv7 central and says to integrate it early; the purpose says "eventually
disconnected and DTN operation". Today the production image includes the BP,
TCPCL and freshness-anchor books: of the 62 roots `tools/proof_artifacts.py
roots --profile default` names, 19 are `bp-*`, `tcpcl-*`, `anchor-*`,
`app-journal` and `journal-publish`, and 35 of the closure's 164 books are
reached only through them (§2.3). *Recommendation:* v0 is NNTP node plus
peering; DTN is v1's first release. Add a `node` image profile without those
19 roots (closure 164 to about 130 books, codec-opening books 55 to 44 by my
count), keep the `dtn` profile as it is, and keep the BP books certified in
the tree. A06 is not reversed: the DTN work stays live, it just stops being on
the path to the first node anyone uses. If you say DTN is v0, T14 in §3 moves
onto the critical path and the image stays as it is.

**Q2. Do native author signatures (D02, D09) have to land before the first
deployed node counts as v0?** D02 selected native signatures for the first
release and its consequence text says not every post must be signed.
*Recommendation:* v0 closes with signatures (T9) but the node deploys and is
used by yue, tulip and you before T9, on password-authenticated principals
over STARTTLS. Agents cannot verify each other's posts until T9's S6 exposure
lands, and the plan says so on the node's page.

**Q3. Retire the six-wave v0 shape, its checklist and the six fiber records
as the definition of v0, and let [milestones](milestones.md) carry §3's step
list instead?** *Recommendation:* yes. The records stay as evidence; they stop
being the plan.

**Q4. Remove the lane worktrees and the Codex role names?** `git worktree
list` prints 106 entries; 105 are under `build/lanes/` and only two are live.
The seven "preserved unmerged work" branches of the
[quiescence note](quiescence-2026-09-21.md) survive worktree removal as
branches, and §5 says which step each one feeds. Astra/Terra/Sol/Luna are
`gpt-5.6-*` staffing names ([swarm-cycles](swarm-cycles.md) "Roles").
*Recommendation:* remove every worktree except the two live ones, keep every
branch, and stop using the role names; a lane is named by its step.

**Q5. The LTP question.** [The feasibility study](ltp-feasibility.md) shows a
pinned ION carried an fn ADU over LTP/UDP; milestones lists "the LTP question
decided" as a v0.4 gate. *Recommendation:* decide it as "not before v1 DTN;
feasibility recorded; the BP primary-block machine (T14) comes first", which
is what the independent review's naivety 4 asked.

**Q6. An acceptance stamp beside the article.** NEWNEWS answers from the
injector's `Injection-Date`; the store keeps no arrival stamp, so NEWNEWS is
a statement about the injecting agent's claim, not about this node
(`docs/implementation.md`, NNT-008 note). Adding the stamp is a change to the
article record, a shared struct under the store and reader clusters (a red
umbrella). *Recommendation:* v1. Agents
poll by local number with the client's watermark (`docs/agents.md`), which is
a statement about this node already.

**Q7. Width.** *Recommendation:* at most three lanes editing `books/` at once,
each on a declared, disjoint include-closure, plus any number of host/tool
lanes; root merges one batch at a time behind one provisional wave and the
merge gate ([how we work](how-we-work.md)). Say if you want more or fewer.

**Q8. The second node.** Peering needs two nodes agents actually reach.
*Recommendation:* hbox and persvati, both on the same image, protected
exchange between them (the run [the 915 record](evidence/native-peering-915d5c72-2026-09-21.md)
says it did not do: TLS, two hosts). Laptop nodes come after.

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

A node agents can use is one on which these hold, each as a theorem over the
function the host calls, with teeth, and each observable on the deployed
image. The table names what exists and what is missing; §3 turns each gap into
a step.

| | Property, stated as it will be judged | Exists | Missing |
| --- | --- | --- | --- |
| P1 | A named principal reaches the node only over a protected channel: `AUTHINFO` on a clear connection under `protected_only` is 483, a restricted command without a login is 480 and performs nothing, posting allowance follows the authenticated credential, and the secret never crosses in the clear. | `books/nntp-auth` (`fn-auth-gated-command-is-refused-and-not-performed`, `nntp-auth.lisp:1348`), `books/served-tls-prefix`, `host/native/tls.lisp`; PRF-039's three events | PRF-031 carries zero events though its theorem exists; `books/owner-tls-prefix` red; no teeth book for the auth chain; never run on an image (T6) |
| P2 | `240` is emitted only after `fn-sn-finish` consumed this exact pending completion and appended one acknowledgement; `441` refused names its reason; an uncertain outcome is `441 ... do not repost`; and after a kill at any cut of the table the acknowledged article rereads byte-identical. | `fn-sn-new-success-requires-actual-matching-durable-node-completion`; `host/store-node-host.lisp:545` `fn-store-sn-finish`; D13 exit codes; the 14-cut table `tests/campaign/native_cuts.py` | No theorem from the served `240` back to the consumed completion; the cut campaign has run in no image since the 32 KiB repair ([owner-defects](evidence/owner-defects-2026-09-22.md)) (T4) |
| P3 | Reading resumes: local numbers are never reused, a reader pinned before another connection's POST keeps its view, NEWNEWS answers within its budget or refuses. | OBJ-005 keystones; `books/owner` reader pins; PRF-052 | NNT-006's own note: the pinned view surviving another connection's POST "is NOT established by any run"; `books/owner` red (T5) |
| P4 | One owner decides duplicate versus conflict for a held Message-ID. | the decision exists and is deterministic ([duplicate-outcome](evidence/native-duplicate-outcome-2026-09-22.md)) | it is `fn-store-article-match`, `host/store-host.lisp:138`, host code, no theorem (OBJ-002 open item) (T2) |
| P5 | A host fault costs one connection, and a bounded number of sessions is served at once. | `fn-own-fault-keeps-every-other-connection` and four siblings, `books/owner-fault.lisp:128-170`; `max-conns` | PRF-040 carries zero events and no `owner-fault` teeth book exists (T12) |
| P6 | The operator stands the node up, adds groups, principals and peers, and changes configuration live, from one binary with no Python, and a reconfiguration is a journal transaction no reader half-sees. | verbs in `docs/operator.md`; `books/owner-config`, `books/native-admin`; `host/owner-host.lisp:214,232,1005` call `fn-ocfg-step`, `fn-ocfg-reconfig-refusal`, `fn-ocfg-open` | PRF-028's four events say "no host line calls any `fn-ocfg-` function", which is no longer true; `native-admin`/`native-operator` red on guards (T7) |
| P7 | Two nodes exchange both ways: transit is the post path, no loop is accepted in either direction, a held Message-ID is refused at offer and transfer, a restart delivers exactly one copy, only Path and Xref differ across transit, and the feed logs in over TLS. | K1, K2 inbound, K3 (PRF-042, 12 events); outbound feed `books/owner-feed`; 915 measured byte-identical loopback exchange | PRF-029 (outbound loop freedom) zero events though `fn-own-feed-target-is-offerable` exists at `owner-feed.lisp:790`; K5 `fn-feed-replay-is-the-live-feed-modulo-inflight` open; no octet-preservation theorem; PRF-047/051 (outbound TLS, AUTHINFO) zero events; never two hosts, never TLS (T8) |
| P8 | An agent's post carries a signature another agent can check without trusting fn, and the reader shows the verdict acceptance recorded. | `books/hybrid-signature`, `hybrid-store`, `stx-*`; kind-4 events written by `hybrid-author` on the control socket | `fn-stxe-profile-supportedp` returns `nil` for every profile (`stx-evidence-records.lisp:61`); S6 `:fn-verified` not built; `fn-sig-verify` is constrained and unattached (`docs/architecture.md`), so the article arm of `fn-sn-finish` cannot evaluate a verdict on a signed article in the image; PRF-023 open on the accepted-statement arm (T9, T3) |
| P9 | The node keeps every accepted article until explicit release and refuses a new obligation it cannot afford. | D03; `fn-retain-admit-preserves-statep`; `V0-CAP-REFUSE` refused on 915 | RET-002's note: "no keystone states that an unaffordable obligation is refused" (T10) |
| P10 | Every process-death cut the campaign takes is a crash point the model expresses, and the campaign passes on the production image. | K1 to K4 (PRF-041), `native_cuts.py` names a `fn-bs-*-program` coordinate per cut | `byte-store-keystones` red; the campaign has run in no image at the current cuts; K0 and power loss stay out of v0 by D14 (T4, v1 T15) |

### 2.2 v0 and v1

**v0 is one image, deployed on hbox and persvati, on which P1 to P7, P9 and
P10 hold as theorems over the host-called subjects with teeth, P8 lands as the
closing step (Q2), and one matrix run on that image agrees with every row it
reaches.** Nothing in v0 is a durability claim past process death (D14), a
signature-security claim (A-CRYPTO) or a two-host DTN claim.

**v1 is, in dependency order:** (a) DTN: the BP node machine T1 to T6 of
`specs/bp-design.md` §1.5 with a caller, TCPCL between two hosts, an
interrupted contact-plan run with expiry and staging exhaustion, receipts, and
the LTP decision; (b) qualified durability: K0 and K5 to K8 of
`specs/crash-model-v2.md`, one Linux profile under D14, power-loss evidence;
(c) scale: the Message-ID trie on the reader path, the per-group index, the
acceptance stamp (Q6), measured cost sentences; (d) substrate S4 and S5
(policy on transit, membership epochs) once two policied nodes exist;
(e) compaction and reclamation (STO-007, RET-005/006, D13 pruning), which D03
does not need until capacity refuses; (f) M6: web interface, 9p, private
groups (D04). Each is a step list of its own when it starts, in this shape.

### 2.3 What the current v0 shape is for, item by item

| Item in the current v0 shape | Disposition | Why |
| --- | --- | --- |
| v0.1 server | v0, as T0/T4/T5/T6 | the node agents use |
| v0.2 peering K1 to K5 | v0, as T8 | "peering between nodes" is the purpose; K5 restart is what "exactly once" means to an agent |
| v0.2 K6 (BP unification), K7 (merge theorem over `fn-sys-run`) | v1 | need the DTN path and a two-node system model that does not exist |
| v0.2 INN interop | v0, one row in T11 | interoperability is what NNTP buys; INN's side already holds ([inn-lab](evidence/inn-lab-f4e8272-2026-09-20.md)) |
| v0.3 DTN | v1 (Q1) | no agent use depends on it; the books stay certified |
| v0.4 TCPCL C1 to C4 | v1 (Q1) | certified and hosted, "two-node transfer over fn's CL" is a DTN gate |
| v0.4 S0 to S2 | done (`stx-carrier`, `stx-verify`, `stx-invariants` green) | |
| v0.4 S3 | done in shape (D21, the index on `fn-sn-state`) with one open arm | T3 closes the arm |
| v0.4 S4, S5 | v1 | no caller; `specs/substrate-transport.md` §10 says so |
| v0.4 S6 reader exposure | v0, inside T9 | without it a signature is invisible to the agent reading |
| v0.4 LTP | v1 (Q5) | |
| v0.5 live reconfiguration | v0, as T7 | it is in `dev`; the theorems are owed |
| v0.5 crash model K0, K5 to K11 | v1 | D14: no durability claim before qualification; v0 claims process death only |
| v0.5 persisted checkpoints | done in shape; `checkpoint*` red is T0's | |
| v0.5 index adoption | v1 | `msgid-index` is green and unused; nothing measured needs it at v0's scale |
| v0.5 compaction | v1 | D03 |
| v0.6 identity and authority | v0, as T9 (Q2) | |
| v0.6 include-hygiene backlog | T1 takes the codec half; the rest is v1 tooling | |
| v0.6 one gate over every root | replaced: the image closure green at every merge is the gate; the rest of the tree is green or retired | the treewide gate is what turned every red into everyone's red |

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
| T0 | Green image, deployed node | image closure green; images frozen under `build/images/<rev>/`; `hbox-node-deploy.sh` run; `node_probe.py` exits 0 from the laptop; matrix run on the image | in flight (w31-freeze-3, w32-native-guards) | the eight reds' books | 1 to 2 left, root 0.5 | Opus |
| T0b | `node` image profile | `host/native/build-node.lisp`, `PROFILES["node"]` in `tools/proof_artifacts.py`, runbooks build it; `proof_artifacts roots --profile node` closure counted | Q1, T0 | build files, `tools/proof_artifacts.py`, `tools/runbooks/` | 1 | Sonnet |
| T1 | Codec boundary | `theory_check --strict` wired into `make check` at zero codec openings; every proof above the seam uses only the seam's constraints; certify wall of `store-node-invariants` measured before and after | T0 (so the deploy is not held) | §4.1 | 2 seam + 6 to 8 across four cluster lanes | Fable seam, Opus clusters |
| T2 | One owner for duplicate-vs-conflict | `fn-sn-existing-action` in `books/store-node.lisp`; theorem `fn-sn-existing-action-is-duplicate-iff-byte-identical` and its refusal sibling; `must-fail` per hypothesis; `host/store-node-host.lisp:461,580` and `host/owner-host.lisp:323,953` call it; `host/store-host.lisp:138` deleted; OBJ-002's open item closed | T0 | `store-node`, `store-node-invariants`, three host files | 1 | Opus |
| T3 | `fn-sn-finish` per arm, index on every arm | one theorem per arm for each of the four keystones the freeze made conditional (`-records-the-acceptance-verdict`, `-is-actual-durable-completion`, `-installs-exact-article-and-archive-pin`, `fn-sn-replay-is-actual-live-durable-completion`), the retention and identity arms stated positively; `fn-sn-finish-preserves-indexedp` with no arm hypothesis; PRF-023 events updated | T1 | `store-node-invariants`, `stx-lace`, `stx-index` | 2 to 3 | Fable |
| T4 | POST is durable end to end | `fn-own-240-follows-consumed-completion`: the `240` effect of `fn-own-*` on a `(:complete)` event equals `fn-store-sn-finish`'s `:durable`, and no `240` otherwise; the 14-cut campaign passes on the developer image at every cut with the record expectation the table states; NNT-005 `implemented` | T1, T3 | `owner`, `owner-invariants`, `nntp-post`; `host/owner-host.lisp:409-425`; `tests/campaign/native_cuts.py` | 3 to 4 | Opus |
| T5 | Reader pins and concurrency | `fn-own-read-of-a-pinned-reader-is-stable-under-another-connections-complete`; `max-conns` refusal theorem; measured on the image with two clients (matrix rows `V0-READ-*` pinned across POST); NNT-006 note rewritten | T1 | `owner`, `owner-invariants`; `host/native/owner.lisp` | 2 to 3 | Opus |
| T6 | Login and the protected channel as one property | PRF-031 events cited; `tests/acl2/nntp-auth-teeth-tests.lisp` with one `must-fail` per hypothesis of `fn-auth-gated-command-is-refused-and-not-performed` and the two PRF-039 greeting theorems; `owner-tls-prefix` green; `node_probe.py` 483-then-login row on the image | T0 | `nntp-auth`, `nntp-auth-invariants`, `served-tls-prefix`, `owner-tls-prefix` | 2 | Opus |
| T7 | Live reconfiguration DONE | the two headline theorems of `specs/reconfiguration.md` (no reader observes a half change; a crash at any instant recovers the live generation) stated over `fn-ocfg-step` and `fn-own-reconfigure`; PRF-028 notes corrected; `V0-CFG-LIVE` accepted on the image | T0, T1 | `owner-config`, `native-admin`, `config-records`; `host/native-admin-host.lisp:14-32` | 2 | Opus |
| T8 | Peering complete | PRF-029 cited with teeth (outbound loop freedom); `fn-feed-replay-is-the-live-feed-modulo-inflight` proved or replaced by a stated K5 theorem over `fn-feed-tick-step` plus the live emitter; `fn-peer-transfer-stores-the-offered-octets-modulo-path-and-xref`; PRF-047/051 cited with teeth; protected exchange hbox to persvati both ways with a `kill -9` restart delivering one copy, recorded | T1 | three disjoint clusters: (a) `owner-feed`, `peer-feed*`, `feed-journal`; (b) `peer-inbound*`, `path`; (c) `feed-connection*`, `feed-auth-profile`; `host/native/feed-service.lisp` | 6 to 10 across three lanes | Opus, Fable for (a) |
| T9 | Signatures an agent can check | `principal new` derives the id from a seed; `fn_client.py post --sign`; `fn-stxe-profile-supportedp` recognises the hybrid profile and its decoder is proved; the verdict arm of `fn-sn-finish` evaluates in the image (an attachment for `fn-sig-verify` in the pattern of `books/crypto-attach.lisp`, or an observed-verdict argument, named in `specs/identity.md`); S6 `HDR :fn-verified` with the three-token rendering and `fn-stx-reader-verdict-is-the-recorded-verdict`; a second agent verifies with its own keyring and no fn code; OBJ-003/OBJ-007 `implemented` with keystones | T3, T1 | `hybrid-*`, `stx-evidence-records`, `nntp-responses`, `nntp-effects`, `crypto-attach`; `host/native/hybrid-control.lisp`, `signatures.lisp`; `tools/fn_client.py` | 8 to 12 across two lanes | Fable design, Opus |
| T10 | Capacity refusal keystone | `fn-retain-admit-refuses-unaffordable-obligation` with teeth; RET-002 `implemented`; `V0-CAP-REFUSE` on the image | T0 | `retention`, `retention-invariants` | 1 | Sonnet |
| T11 | v0 record | the matrix on the v0 image with every reached row agreeing; the INN lab (`tests/inn/`) on hbox against the image; `planning/evidence/v0-<rev>.md` | T4 to T10 | tools and evidence only | 2 | Opus |
| T12 | Registry hygiene | §4.5 done; `ledger.py --check` and `evidence_manifests.py check` green | none | registries, `tests/acl2/owner-fault-tests.lisp` | 1 | root, Sonnet |
| T13 | Retirement | §5 done | Q3, Q4 | planning tree, worktrees | 0.5 | root |
| T14 | v1 DTN | per §2.2 (a) | v0 | | later | |
| T15 | v1 qualified durability | per §2.2 (b) | v0 | | later | |

### 3.1 The steps in detail

**T0.** The subject is the image closure itself. The freeze-3 lane owns the
store-node reds (`fn-snt-record-directory-preserves-relation`,
`fn-sn-known-abort-is-exact-node-abort`, `fn-sn-observed-seed-is-state`,
`fn-spc-candidate-txid-is-frontier-predecessor`, and `checkpoint` if it is
still red on the next wave); the native-guards lane owns the four guard
conjectures and the test assertion. Root's part after both land: one
provisional wave over the default (or `node`, Q1) closure, `hbox-image-build.sh`,
`hbox-node-deploy.sh`, `node_probe.py`, the matrix on the image, and the
evidence file `planning/evidence/native-deploy-hbox-<rev>-2026-09-2x.md`.
Then yue, tulip and ember post on it. That is the first usable thing, and it
is before every other step.

**T1.** §4.1. It goes second because every proof step after it (T3, T4, T5,
T7, T8) lives in books that open the record codec book-wide today, and the
freeze records say that is where proofs stop returning.

**T2.** `fn-store-article-match` (`host/store-host.lisp:138`) compares payload
and groups of a found article and answers `:duplicate`, `:conflict` or `nil`.
The step moves it into `books/store-node.lisp` as `fn-sn-existing-action`
over `(fn-sn-node s)` and states it: the answer is `:duplicate` exactly when
the held article's payload and groups are the submitted octets and list,
`:conflict` exactly when the Message-ID is held and either differs, `nil`
otherwise; teeth flip each of payload, groups and the binding. Its host
lines are the four listed; the matrix row `V0-OUT-REFUSED` is the witness.

**T3.** The freeze made four keystones conditional on the article arm
because they were false on the retention and identity arms
([second freeze record](evidence/native-freeze-01fbdad4-2026-09-22.md)). A
hypothesis that names the arm is a claim about one third of the function the
host calls. The step states each arm: what the retention arm publishes (a
retention event, no article, the index unchanged), what the identity arm
publishes (a keyring or verdict event, the index grown by the accepted
statement's delta), and the article arm as before. `fn-sn-finish-preserves-indexedp`
then has no arm hypothesis; the book's own comment (`store-node-invariants.lisp:1090`)
names the three facts the accepted-statement arm needs. PRF-023 cites the
unconditional theorem.

**T4.** Today `fn-sn-new-success-requires-actual-matching-durable-node-completion`
says the store cannot acknowledge without a completion, and
`host/store-node-host.lisp:545-560` reports `:durable` only for the transition
that consumed this pending completion. What no theorem says is that the
`240` the connection receives is that report: `host/owner-host.lisp:409`
says "completion is the owner's `(:complete)` event" in a comment. The
theorem is over `fn-own-*` (the function `fn-owner-step` at
`host/owner-host.lisp:211` calls) and equates the `240` effect on the
`(:complete)` event with the durable report. The campaign half: every cut in
`tests/campaign/native_cuts.py` runs against the developer image built by
T0 and each recovered store shows the record the table expects (`absent`,
`either`, `present`); the record names any cut that carries `gap`, and a
`gap` is a failed step, not a passing one (AGENTS rule 6).

**T5.** The owner pins a reader's archive at open (`books/owner.lisp:18`,
`:504`). The theorem: for a connection pinned at version `v`, `fn-own-read`
after another connection's `(:complete)` answers exactly what it answered
before. NNT-006's note says no run establishes it; the matrix's two-readers
rows are the run. `max-conns` gets its refusal theorem beside it.

**T6.** The theorems exist; the registry and the teeth do not. PRF-031's
statement names `fn-auth-gated-command-is-refused-and-not-performed`
(`books/nntp-auth.lisp:1348`) and carries zero events. The step adds the
teeth book, cites the events, turns `owner-tls-prefix` green with the
freeze-3 pattern (state the arm, do not open the codec), and records the
483-then-login probe on the image.

**T7.** `specs/reconfiguration.md` says "this document contains no proved
theorem". Its two headline claims become theorems over `fn-ocfg-step` and
`fn-own-reconfigure`, which `host/owner-host.lisp:214` and `:229-267` call.
The live-admin review's codec finding is already repaired
(`fn-nctrl-admin-argv-encode`, `books/native-control.lisp:188`); the step
records that with a live `peer add` test, which that review said did not
exist.

**T8.** Three lanes on disjoint closures. (a) The feed: PRF-029's theorem
exists (`fn-own-feed-target-is-offerable`, `owner-feed.lisp:790`) and is
uncited; K5's general equation
(`fn-feed-replay-is-the-live-feed-modulo-inflight`) is open because "the
live side" was never built (`specs/peering.md` §4 K5 row): the step either
builds the live emitter as a machine and proves the equation, or states K5
over `fn-feed-tick-step` and the FNFD journal the host actually writes and
retires the open row by name. (b) Inbound: an octet-preservation theorem,
that what `fn-peer-transfer` stores is the offered octets with Path prepended
and Xref removed and nothing else (RFC 5537 §3.6), which the 915 run
measured and no book states. (c) Outbound transport: PRF-047 and PRF-051
name their theorems and carry zero events; the step cites them with teeth.
The gate: hbox and persvati, TLS, AUTHINFO both ways, a post on each
arriving on the other, `kill -9` of the sender mid-transfer, exactly one
copy after restart, recorded.

**T9.** The verdict the node records at acceptance is what an agent reads
back (S6, `specs/substrate-transport.md` §5); the node holds no signing key
and attaches nothing (departure 3, §10). Three things are missing in the
node and one in the client. `fn-stxe-profile-supportedp` (`stx-evidence-records.lisp:61`)
returns `nil` for every profile, so a correctly signed kind-4 event is
`:unsupported-profile` to every reader (hybrid review, finding 2). The
article arm of `fn-sn-finish` calls `fn-stx-verdict-of-octets`, which
reaches `fn-sig-verify`, constrained in `books/crypto-seam.lisp:109-124`
with no attachment in `books/` or `host/`; how the image evaluates that arm
on a signed article has to be named and tested before anything else in this
step. S6 is a shared-struct change to `nntp-responses`, `nntp-invariants`
and `nntp-effects` (the OVER extension is declined in favour of `HDR` alone,
as §5 allows). The client gains `--sign` with the key file it already refuses
to read unless mode 0600. `fn-hsig-subject-body` injectivity (hybrid review,
finding 3) is the theorem the step proves first.

**T10, T11, T12, T13** are as the table says.

### 3.2 The critical path and what runs beside it

```
T0 ─ deploy ─ T1 ─ T3 ─ T4 ─ T5 ─┐
                  │              ├─ T8 ─ T9 ─ T11 = v0
                  └─ T7 ─────────┘
beside the path, on disjoint books:  T2 (after T0), T6 (after T0),
                                     T10 (any time), T12 (now), T0b (Q1)
```

The critical path to *a deployed node agents use* is T0 alone. The critical
path to *v0* is T0, T1, T3, T4, T5, T8, T9, T11, about 32 to 46 lane-days on
the path and 41 to 55 in all, summed from the table. T1 is on the path on purpose: it is the change
that makes T3, T4, T5 and T8 proofs return.

### 3.3 How the plan uses the gate and the wave

One batch is one lane's landing. Before it reports, the lane certifies its
own closure (its books, their dependents, `green_check --changed-since
<base> --strict` clean in its worktree). Root runs one provisional wave
(`tools/triage.py`) over the image closure with the branch merged locally
(`--no-ff`), reads every independent red in one report, and merges only when
the wave names none the branch introduced; otherwise `git reset --hard
ORIG_HEAD` and the lane fixes what the wave named. The width limit (Q7,
[how we work](how-we-work.md)) is three book lanes at once on disjoint
closures declared at launch, so a wave can attribute every red to one lane.
T1 is the exception that proves the rule: its cluster lanes touch
overlapping closures, so they land one at a time with a wave each. After a
batch that touched the image closure, root rebuilds the image the same day;
a node that agents use is redeployed at most once a day and only from a
frozen image with its manifest.

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
   once.
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
that cluster is where the freeze paid; then the BP receiver cluster, the
stx/identity/lace cluster and the frame/anchor/transfer-journal cluster, one
lane each, one wave each. The measurement that decides the step is the
certify wall of `books/store-node-invariants` and `feed-connection-invariants`
(the one that timed out four times, review F2) before and after, on the same
box with its load named.

### 4.2 The article match into a book (T2). §3.1.

### 4.3 The `fn-sn-finish` arms and the indexedp gap (T3). §3.1.

### 4.4 The `node` image profile (T0b, Q1)

`host/native/build.lisp` includes 47 books and `ld`s the host files for the
store, owner, auth, admin, feed, BP, TCPCL and anchor. A `build-node.lisp`
without the BP, TCPCL and anchor includes, and without the BP, TCPCL and anchor bridge files under `host/` and
`host/native/`, is the image agents use; `build-dtn.lisp`
stays the DTN image. `tools/proof_artifacts.py` gains `PROFILES["node"]`;
`hbox-image-build.sh` builds it first. By my resolver the default profile's
closure is 165 books and the node subset 130; the record's count for the
default is 164 (my resolver counts one test root twice or an include the
runner skips, and the runner's number is the one to cite).

### 4.5 Registry findings, and what each row should say

Found by reading `proofs.json`, `proof-events.json`, `requirements.json`,
the ledger and `green_check` against each other.

1. **`certified` over red books.** PRF-036 cites theorems in
   `store-node-traces` and `store-observed` (red); PRF-037 cites
   `checkpoint-codec` (red); PRF-041 cites `byte-store-keystones` (red).
   A `certified` status is a claim about bytes that no run has accepted. Row
   edit: status `in-progress` for all three until their books are green at
   their current digest, with the note "certified at <run> over <digest>;
   the book has changed since". Structural fix, T12: `ledger.py --check`
   fails a `certified` target whose cited book `green_check` reads red or
   never, so this cannot recur.
2. **Stale `pending_subject` notes on PRF-028.** All four events say "No
   host line calls any `fn-ocfg-` function". `host/owner-host.lisp:214`
   calls `fn-ocfg-step`, `:232` `fn-ocfg-reconfig-refusal`, `:1005`
   `fn-ocfg-open`, `:610` `fn-ocfg-open-peer`. Row edit: drop the
   `pending_subject` notes, name those lines, and T7 states the theorems
   over them.
3. **Eleven `in-progress` targets with zero events**: PRF-009, 027, 029,
   031, 033, 038, 040, 047, 049, 050, 051. For 029, 031, 033, 040, 047 and
   051 the theorem the status text names exists in a book
   (`owner-feed.lisp:790`, `nntp-auth.lisp:1348`, `owner-invariants.lisp:869`,
   `owner-fault.lisp:128-170`, the `fn-fc-step` books); the events were
   never curated into `proof-events.json`. Row edit: cite them (T6, T8, T12)
   and add the teeth books the rule requires; `owner-fault` has none. For
   009, 027, 038, 049, 050 with no theorem yet: status `planned`, which is
   the registry's word for stated and unproved.
4. **`implemented` rows whose own notes walk the claim back.** NNT-006 ("a
   reader's pinned snapshot surviving another connection's POST is NOT
   established by any run"); REP-002 ("convergence across two real peers is
   the K3 seam, which no book states"); STO-005 ("one kill point only, and a
   SIGKILL is not a power loss"); NNT-005 is `specified` and its note still
   says `books/owner` "does not certify", which stopped being the reason on
   2026-09-20. Row edits: NNT-006 and REP-002 keep `implemented` with the
   note rewritten to the scope the keystones cover and the step (T5, T8)
   that closes the rest; STO-005's note names the cut table and T4; NNT-005's
   note names T4 and drops the historical sentence.
5. **Three `pending_subject` events on functions with no caller** (PRF-011,
   PRF-016 on `fn-transfer-missing-ranges`; PRF-025 on
   `fn-stx-commits-of-batch`). These are v1 features, not missing evidence
   (`docs/proofs.md`, assurance scope). Row edit: move the events to a
   `deferred` note on the target so they stop counting toward `in-progress`.
6. **PRF-037's subject.** `fn-cpc-validp` has no caller; the served restore
   path is `host/checkpoint-host.lisp` to `fn-checkpoint-restore`. Either the
   host calls the validator (a v1 checkpoint-adoption step) or the target is
   `planned`. Row edit: `planned`, note naming the caller it waits for.
7. **`unreachable-in-composition`.** `fn-sn-fence-node` and
   `fn-sn-resolve-node` are marked at `store-node-invariants.lisp:631` and
   kept "as documentation"; the rule allows the mark. No change. The
   `:duplicate` branch of `fn-bpr-accept-request` the independent review
   called unreachable in production (§4, last row) carries no mark; T14
   decides it.
8. **The 61 suspect-shaped theorems** are all uncited and most are named
   `-unfolds`, `-by-definition`, `-is-no-op` as the rule asks. No change.

## 5. D. What to retire

**Rows and tables.** The v0 checklist in `milestones.md` ("Historical
snapshot", six per-wave tables) and the six `planning/evidence/fiber-*-2026-09-20.md`
records as the definition of v0; §3's table replaces them (Q3). The
`planning/v0-matrix.json` selected run: it is the Python service at
`3f68944` on 2026-09-21; the first native run root publishes replaces it, and
until then the file says it is superseded. The "one gate over every root"
release criterion (§2.3, last row).

**Lanes and worktrees (Q4).** Remove every worktree under `build/lanes/`
except `w31-freeze-3` and `w32-native-guards`, and the three under `build/`
(`nntp-guards-work`, `wire-guards-work`, `workflow-host-work`, all detached at
2026-09-18 commits). Keep every branch. The seven checkpointed branches of
the quiescence note feed these steps: `w27/bounded-event-profiles` (T1: the
codec cost is what the seam removes; its bounded-profile proofs land behind
the seam), `w25/prf050-identity-sequence` (T3 and T9), `w28/nntp-msgid-index`
(v1 scale), `w26/reclaim-keystone-teeth` (v1 compaction),
`w29-peer-row-roundtrip` (T8b), `recovery/portable-hybrid-authorship` (T9),
`w26/owner-tls-overlay` (T6; check first whether `served-tls-prefix` already
carries it). The eight "recoverable packets" of the recovery note are either
landed (STARTTLS, operator admin, config namespace, BP publication, per
`now.md`) or DTN (v1).

**Documents that mislead, and why.**

| Document | Why it misleads now | Disposition |
| --- | --- | --- |
| `planning/now.md` | 384 lines in which each dated paragraph supersedes the one below it; "Current integration checkpoint" describes `773e9ae3`, superseded by 915 and then by this | rewrite to one screen: the image, the live lanes, the current step, a link here |
| `planning/milestones.md` | the checklist (§5 above), the "earlier landing notes", and M0 to M6 whose bullets describe 2026-09-18 | keep M0 to M6 as history under "Earlier milestones"; the release shape becomes §2.2 and §3 |
| `planning/swarm-cycles.md` | pre-crash Codex staffing and C1 to C3 packets; the roles section defines names this plan retires | archive to `planning/archive/`; `docs/README.md` "What should happen next" points here |
| `wide-capability-cycle-2026-09-21.md`, `recovery-2026-09-21.md`, `quiescence-2026-09-21.md`, `astra-reorientation-2026-09-21.md`, `handoff-to-codex-2026-09-19.md` | each was the plan for a day that is over; the quiescence note says "resume only on user instruction", which ember has given | archive; the worktree table's branches are named above |
| `planning/deputies/BOARD.md` and `deputies/*.md` | an append-only board of W12/W13 claims and cluster briefs for lanes that no longer exist | archive |
| `planning/assurance-closure.md` | a matrix whose cells say "Certified" in prose beside registries that are the ledger; the rule says counts and statuses live in the generated ledger and the registries | archive; anything in it not in a registry note becomes one |
| `planning/evidence-index.md` | 23 record rows for 181 files in `planning/evidence/` and 64 in `tests/evidence/` | either `tools/evidence_manifests.py` generates it from the records' headers or it is retired; do not hand-extend it |
| `docs/operator.md` | its first half describes the Python development service as the operator path, against D07 | rewrite around `packaging/fn-native` and the hbox runbook; the Python half moves to `docs/development.md` |
| `docs/implementation.md` | a 2026-09-18 component table | replace with a pointer to the ledger and §2.1 |
| `specs/substrate-transport.md` §8 | the packet table names `books/statement-field.lisp` and `statement-transit.lisp`, which never existed (its own footnote says so) | replace the table with the landed book names and §3's T9 |
| `specs/peering.md` | a design section followed by three dated status sections (waves 6, 11 and the native witness) | one status section, K1 to K7 each with its theorem or its step |

**Roles.** Astra, Terra, Sol, Luna: retired with `swarm-cycles.md`. A lane is
named by its step (`t8a-feed`), and its model is written in its brief.

## 6. What v0 does not claim

Durability past process death on Linux (D14); anything about power loss;
that Ed25519 or ML-DSA-65 are secure or correctly implemented (A-CRYPTO,
libsodium and OpenSSL are trust); that TLS provides confidentiality (the
handshake is a host facility, `docs/architecture.md`); that a peer is honest
(A-PEER); DTN; flight readiness. Each is written on the deployed node's page.

## 7. Edits root makes

In `planning/proofs.json` and `proof-events.json`: §4.5 items 1 to 6, with
`ledger.py --write`. In `requirements.json`: §4.5 item 4; OBJ-002's note
gains "open item: `fn-store-article-match` is host code (T2)"; NNT-008's
note names Q6. In `milestones.md`: the release shape section is replaced by
§2.2 and a link to §3; the checklist and landing notes move under "Earlier
milestones". In `now.md`: the rewrite in §5. In `AGENTS.md`: no rule
changes; the "Evidence and handoff" section gains one sentence, "a lane is
briefed from `planning/how-we-work.md`". In `docs/README.md`: "What should
happen next" points at this file and `how-we-work.md`. The archive moves in
§5 happen after Q3 and Q4.
