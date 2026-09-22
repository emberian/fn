# Current work: native service composition and consolidation

**Resumed 2026-09-21 evening (Claude session), narrowly.** The [quiescence
checkpoint](quiescence-2026-09-21.md) still describes every lane's preserved
tip; none has been restarted. The one active line of work is the native v0
matrix: the full driver now runs against the native image and reaches 123 of
192 rows on the frozen `915d5c72` image
([record](evidence/native-matrix-915-2026-09-22.md)). Its four disagreements
are one gap, the native node's missing path identity. The next steps in order
are: give the native node a path identity (config key or operator verb) so
loop suppression can fire (done, `policy set path-identity`, dbf2e1ab);
freeze `dev` once into a new image so the AUTH, live-administration and
STARTTLS rows can move; run the matrix on it; stand up one reachable node and
use it. The v0.5/v0.6 lanes stay checkpointed until that node exists.

The first freeze attempts (hbox, 2026-09-22 02:15Z and 02:29Z) found `dev`
red in four books no lane had certified at their current digests
(stx-evidence-records, checkpoint-compaction, hybrid-store, feed-connection);
the first two are repaired (28fb4bd0), the other two are the freeze lane's.
Opus lanes run under `build/lanes/w31-*`: freeze (landed 27dc5a21 without
an image: the closure went from 111 to 130 of 164 books, one shape under
every red, [record](evidence/native-freeze-c28ffc30-2026-09-22.md); still
red by name: `store-node-invariants` at `fn-sn-finish-preserves-state` and
`nntp-auth` at `fn-auth-clear-principal-peer`), freeze-2 (landed 13f50de7, 140 of
164: five commits on 2026-09-21 had changed the machine under invariant
books nobody recertified, so exported statements were false in the shape
the machine has; four books now certify, five theorems carry the
hypotheses their arms need and `fn-sn-finish-preserves-indexedp` is
registered open on the accepted-statement arm under PRF-023,
[record](evidence/native-freeze-01fbdad4-2026-09-22.md); still red by
name: `store-node-traces` at `fn-snt-record-directory-preserves-relation`,
whose relation predates the retention and identity arms, and `checkpoint`
at `fn-checkpoint-restore-rejects-frontier-reuse`), freeze-3 (a fresh lane
on those two, the 22 books behind them, then the images), treewide-reds (landed ad0cdefd: five proof repairs
outside the image closure with their manifests, `msgid-index` certified for
the first time; its territory reads 186 of 243 roots green, and every root
still red sits above `hybrid-store` or `feed-connection-invariants`, which
are the freeze lane's; `feed-connection-invariants` is red by the 1800 s
timeout because its hint opens every state recognizer, a diagnosis handed
to the freeze lane), and
matrix-driver (landed 8935d992: AUTHINFO, live groups, the wildcard listener
and an independent client are measurements on the native slice; on 915 the
credential rows carry that image's exit 5, `V0-CFG-LIVE` is a real refusal
and the two nntplib rows are the slice's first accepted independent rows; it
reruns on the new image). Two more landed overnight: agent-client (acfb4964:
`tools/fn_client.py`, the way agents and humans read and post on the
deployed node over STARTTLS and AUTHINFO, [docs/agents.md](../docs/agents.md),
tested only against a fake node so far) and duplicate-outcome (9890b318: the
matrix's "duplicate submission answers refused or accepted by race" was the
harness re-stamping `Date` on every article build; the node answered the
octets it was given every time,
[record](evidence/native-duplicate-outcome-2026-09-22.md); open item it
found and did not fix: `fn-store-article-match` in `host/store-host.lisp`,
the duplicate-versus-conflict comparison, is program-mode host code with no
theorem naming it, against "one owner per decision").
green-audit landed earlier (d667a874, `tools/green_check.py` in `make
check`); with the treewide and freeze manifests in the tree it reads dev as 323
green, 84 red, 0 never and 0 absent at current digests; the reds are the
cascade behind the two books above, and the treewide territory is being
recertified on persvati from this head. Root landed `tools/node_probe.py` (a0745f4b), the client the deploy
step runs from the laptop: STARTTLS, the 483 before it, login, a post and a
fresh-connection reread, on the deploy gate's exit scale. The hbox freeze,
matrix-provision and node-deploy sequences are `tools/runbooks/`. persvati
was unreachable from the coordinator's machine from about 01:50Z to 03:00Z
(an ARP loss on that side; the box never rebooted) and is back in the plan.

Updated 2026-09-21. The goal remains the full selected two-peer v0 and v1/M6
scope in [milestones](milestones.md#release-shape-v0-and-v1). Component tests
and certificates do not establish that release. D07 requires a Python-free
node, operator CLI and runtime helpers; Python remains development tooling.

Post-reboot orientation: [recovery status and next cycles](recovery-2026-09-21.md)
records surviving main/lane work, the development-test memory incident and the
remaining pillars. Recovered remote results are now archived. Process-group
containment is integrated, with bounded cleanup after leader death. Current
priority is frozen native service qualification alongside continued wide
implementation, with the full selected release scope retained.

The user has now selected a [wide capability cycle](wide-capability-cycle-2026-09-21.md):
parallel service/peering, BP/DTN, preservation, identity and crash-correspondence
implementation, with focused checks per lane and combined gates per frozen batch.
Usage remaining does not narrow the release scope.

## Current integration checkpoint

The next production/developer/DTN image preserves the `773e9ae3` executable
feature boundary, with an explicit descendant commit for required proof-only
prerequisite repairs. The preceding affected closure on persvati terminated
with one primary signature-carrier bound proof failure; its source `09677bf1`
was a prerequisite-cache batch. That carrier repair now has
[focused source-matched certification](evidence/stx-carrier-bound-proof-2026-09-21.md).
Image manifests will name the actual descendant revision and input hashes. The earlier combined
`8e8d1080` attempt failed in statement and provenance codec proofs. Focused
repairs have real certificates; the combined successor result remains pending.

Native bidirectional exchange, duplicate suppression and restart/requeue have
[scoped immutable-image evidence](evidence/native-peering-915d5c72-2026-09-21.md)
for `915d5c72`. That source is older than the combined freeze. A further [matrix witness run](evidence/v0-native-peering-915-2026-09-21.md)
has reproduced selected exchange/requeue cases with the actual running executable
and core observed through `/proc`; its failed receiver-setup attempt and corrected
run are archived separately. Protected exchange between hbox
and persvati, live configuration, and current-image recovery remain queued.

The native hybrid enrollment/author control join is integrated: exact-source
field admission and both primitive observations feed the shared durable
submission path. A missing-enrollment history fixture is now ACL2-generated;
its native startup test must fault while retaining exact observed files. The
local hybrid Store/control test books execute after repairing a missing fixture
constructor dependency; this is source evaluation, not new certification.
Portable `FN-Authorship` propagation and real native hybrid author/restart
qualification remain active work.

Selected-prefix compaction tests now enumerate repeated unlink interruptions
and preserve actual event bytes across candidate and selection cuts. Their
runtime campaign awaits the source-matched image. General selected-suffix preservation through actual reclaim-program prefixes
and admissible model crashes now has source-evaluated proof events; focused
certification is queued, and physical power-loss correspondence remains open. Tagged-event append proof repair
and hypothesis teeth are integrated; focused certification remains pending.
The persistent Message-ID trie and builder uniqueness definitions are integrated,
with source-evaluated correspondence events. The live reader still uses its old
lookup path until the maintained owner/pinned-reader join lands; no measured
speedup or fresh certificate is claimed for the trie.

The dated narrative below preserves earlier gates and their narrower scopes;
this checkpoint supersedes their descriptions of the next active image.

## Integrated and under validation

Main contains native owner/operator help/status/recover/run, feed intent and
resolution persistence, safe FNFD names and a total observation budget,
cross-session BP receive evidence, application journals, checkpoint/anchor
persistence, and selected initializer retry paths. The standalone store wrapper
calls a proved prepare refinement that omits per-prepare history replay;
the shared owner now calls the corresponding proved owner projection. BP lifecycle append uses an
ACL2-owned namespace and carried frontier instead of rescanning retained files.
The listener's admitted loopback addresses now come from an ACL2 projection.
Native AUTHINFO loads the bounded ACL2 credential profile before bind; its
scoped login and reader-versus-peer runtime evidence is archived. BP lifecycle
publication now uses the shared immutable publication machine.
Native public control/posting and orderly SIGTERM are integrated with separate
ACL2 closure and exact-raw Darwin runtime evidence. The control resource
followup now bounds active clients, total frame time and accumulation work,
with scoped witnesses and a [source-pinned Linux image run](evidence/native-control-linux-build-2026-09-21.md).
That image does not qualify later whole-main changes.
Transaction namespace recovery now uses bounded observation and ACL2-issued
sequence/name pairs, with a source-matched developer Store image witness.
The native outbound feed is now activated through public owner lifecycle hooks;
public principal, group/capacity and peer administration are joined. STARTTLS,
connection fault isolation, ACL2 peer address selection, BP authored-wire
publication and maintained application-state projections are also integrated.
Configuration namespace recovery now preserves all observed entries during
sorting. The joined source awaits a fresh native image and runtime matrix;
these integrations are not a claim that the combined service passes.

The current main includes the first authoritative Store-event integration:
article transactions and BP undertaking/release events share the allocator,
publication barriers and ordered recovery. Acceptance-verdict, keyring-snapshot
and atomic article-plus-verdict codecs have also landed. The shared identity
writer/replay join remains in progress; component codecs do not establish that
historical trust is durably recovered. Physical checkpoint packing/reclamation, hybrid primitive verification, and
principal-authenticated inbound peering are integrated in source. Large-record
decoding and persisted resource profiles, arbitrary partial-reclamation
correspondence, durable enrolled-key binding, and outbound AUTHINFO remain
active joins; none is implied complete by the component integrations.

The first frozen combined source `f7190d69` failed certification because native
administration omitted its peer-config dependency. Repair `55e6d00a` then
exposed an insufficient proper-list guard. Focused repair `8071a825` passed the
five affected roots under persvati job `run-20260921T165123Z-ea6a`, reusing
qualified unchanged dependencies. Production image construction exposed an
ACL2-reader/raw-Lisp boundary error in profile selection; `09612ff7` repaired
that boundary and built production, developer and DTN images. Its runtime batch
then exposed fresh initialization being sent through the nonempty recovery
observation. Repair `e96e8a39` separates those ACL2 entries. Its focused and
profile certification, production rebuild, and initialization followed by
new-process recovery smoke passed; the runtime batch then exposed an incorrectly nested native connection handler.
Frozen repair `0626d428` restored handler and unwind structure; its production
batch passed storage/recovery, authentication, operator/control and TLS tests,
while BP startup and one platform-specific socket-close expectation failed.
Repair `7b23b6a5` preserves the absent-journal startup state in the fast
ACL2 configuration projection and accepts Linux reset as closure of a malformed
TLS connection. Those failed cases passed after repair. Final `8c231978` built
production, developer and DTN images and passed the focused transit-EOF and
incomplete-POST SIGTERM regressions. The [archived repair gate](evidence/native-freeze-gate-2026-09-21.md)
distinguishes every source, certification, runtime batch and final image hash;
it does not imply all cases ran against the final byte-identical image.
A subsequent [two-node attempt](evidence/native-peering-8c231978-2026-09-21.md)
found that the old frozen operator did not dispatch public peer administration.
That dispatch is already present on main; the older qualification lane is
porting it narrowly before retrying real peering. No two-node release claim
follows from the repaired service tests.
The remote origin is `/home/ember/fn-gates/freeze-f7190d69`; exact source
revisions and manifest digests, rather than that directory name, identify each
input. Later main integrations are outside this frozen gate.

Outbound authenticated TLS and live administration are now integrated in main.
Focused raw transport tests pass, including handshake rejection and retry
cleanup; their scope is not a two-node service qualification. Inbound transit roles now bind to authenticated configured principals, with
public administration syntax and an explicit legacy source-address profile.
Outbound AUTHINFO over the selected transport policy is the next active
peering join; TLS server authentication alone does not provide that login. The developer-only
native process-death cuts and K7 supporting facts are integrated; their native
fault campaign awaits the next combined image.

The previous qualified combined source is `03eb3ba3`, with retained persvati job
`run-20260921T095031Z-5cf4`. Certification, both same-origin image builds, scoped runtime suites and the
public operator loopback witness passed; see the [frozen evidence](evidence/native-owner-integrated-2026-09-21.md). Later main changes
are not part of that frozen source and must receive their own integration gate.
The earlier `76901c1` closure/build passed; its live listener wakeup defect was
repaired in the current frozen batch. Historical Python matrix disagreements
remain recorded and are not reclassified by component certificates.

The next wide source batch also includes outbound AUTHINFO with ACL2-rendered
commands, exact opened-descriptor credential checks, large Store-event codecs,
a new explicit physical profile preserving legacy reads, ordered durable identity
context, and compaction reclaim crash programs. Native author submission now includes its live-owner control join in source;
its real primitive/restart runtime test remains pending. Profile admission and expected-refusal cleanup
must compose before the next image is frozen. Large-event and partial-deletion
witnesses are source/component evidence; full caller guards and native fault
execution remain open. The [crypto review](review-2026-09-21-hybrid-cross-model.md)
identified and prompted repair of the Ed25519 observation-size mismatch; general
subject injectivity was completed in the subsequent scoped batch below.

The next source batch now separates the carried journal sequence from the
allocation frontier. Refused reservations may burn transaction identifiers
without consuming journal positions. An actual Store-machine trace covers
enrollment, atomic signed acceptance, observed reopen and recovery barriers,
such a refusal, and subsequent legacy and retention commits. Source evaluation
passes; the current integrated certification remains open. Native kind-4
historical verdicts survive recovery; legacy `fn-r` live verdict observations
have no durable representation and are deliberately absent after reopen.

The native distribution has landed with [task-local installation evidence](evidence/native-distribution-qualification-2026-09-21.md)
for frozen `8c231978`: relocated SBCL, installed core, owner startup and SIGTERM,
with no Python child observed. Public principal administration now composes the
existing ACL2 credential planner and durable executor. Its new public route
awaits image qualification. The two-node investigation also found a concrete
native feed conversion defect: cached peer identifiers were byte vectors where
ACL2 expects lists. Main repairs that boundary and includes a regression that
fails against the old constructor; the older image gate is applying the same
repair before continuing exchange tests.

The earlier combined successor froze `df21773d` for certification on persvati.
Hybrid control review identified boundary-call and test-harness defects, plus
the need to compose source-derived article admission and durable outbound feed
intent; these repairs are included in the later `773e9ae3` image freeze. An inner
kind-4 writer alone is not the complete author-posting workflow. Hybrid subject
injectivity books and concrete counterexamples now have
[source-matched certification](evidence/hybrid-injectivity-certification-2026-09-21.md)
on hbox; root checked every selected closure source digest against main. The
initial failed attempt used older CBOR source and remains separately recorded.
The shared native publication helper now has a dynamic raw-source witness for
refusal followed by a valid commit, and distinct indeterminate/fault fencing;
PRF-050 and SCN-027 record its narrower scope. Combined-image preflight found
obsolete BP reverse-retention join includes. Those have been removed, with a
literal build-input existence regression; the current workflow projects the
authoritative Store into workflow state. The frozen gate is taking that repair
and the independently certified node-config capacity-preservation proof fix.
The read-only Claude review in tmux `fn-w29-recovery-review` completed against
`31f49d78`; its [disposition](review-2026-09-21-recovery-cross-model.md) records
a repaired recovery defect. Identity replay failure now forces a recovery
fault even when embedded article replay succeeds, preserving the observed
history instead of successfully opening an empty node. Positive mixed-history
and negative missing-enrollment traces execute from current ACL2 sources;
fresh certification and native corrupt-history startup remain open.

The native peering investigation has also repaired the pure administration
call boundary and the unimplemented transit drain branch. A taken peer article
now goes through the ACL2 transfer decision, durable feed intent, shared Store
attempt and transit outcome. Earlier runs never reached that Store attempt.
The repaired path has the scoped frozen-image two-peer evidence above;
current-main and protected cross-host qualification remain separate gates. The served counted fast transition is integrated with
[focused correspondence evidence](evidence/native-served-fast-path-w26-2026-09-21.md);
its current outer-owner closure still needs certification.

The [shared-owner cost run](evidence/native-shared-owner-2026-09-21.md) measures
real control posting and NNTP reads. Its launcher/core timeline required
reconciliation because a shared artifact path was rebuilt; the record retains
that provenance limitation. Future gates use revision-specific immutable image
paths. The measurements motivate maintained Message-ID indexing, with bounded
generation ownership rather than an unbounded memoization cache.

Portable hybrid authorship is a separate active implementation packet. The
local kind-4 acceptance event alone does not transmit signatures. A distinct
versioned `FN-Authorship` carrier will preserve the selected exact source and
both signatures across NNTP and BP, leaving existing `FN-Statement` subjects
unchanged. Carrier keys remain evidence; receiver-local durable enrollment
controls authority. Its codec/projection work proceeds alongside the live
author-control join, with transport and recovery obligations still open.

## Parallel paths to the next service batch

[Active lane assignments](swarm-cycles.md#current-staffing-and-integration-checkpoint)
own these complete paths and their source-pinned evidence:

- Native control composition, credential administration, outbound NNTP feed I/O and
  group/capacity administration, through the existing ACL2 policy and shared
  serialized owner. Control and BP submission share completion machinery;
  lifecycle hooks and orderly SIGTERM must compose without deadlocks.
- Native BP application join is integrated with a scoped lost-reply/restart
  witness. Receipt-decision barrier failure now has a scoped native recovery witness.
  Next is maintained joined-state assurance and removing redundant retained-state
  scans; carrier ACKs are not application acceptance.
- Actual BP lifecycle invariant/effects, configuration namespace
  bounds, and wider syscall/model correspondence.
- Measured native shared-owner service cost after prepare correspondence adoption.
  Standalone measurements do not qualify concurrent service.

Root integrates coherent packets and uses both hbox and persvati with owned
closures and a frozen combined batch. Terra handles bounded implementation,
Sol substantial implementation/proof debugging, and Astra cross-project
convergence and difficult residual questions. Cross-model review runs in the
existing Claude tmux session on bounded source-pinned subjects; it is not a
serial approval gate.

## Assurance and consolidation

The [consolidation audit](duplication-audit-2026-09-21.md) records demonstrated
competing decisions, repeated scans and misleading contracts. Active repairs
include transaction/configuration namespace parsers and pre-allocation bounds,
native lifecycle shutdown and connection-local fault isolation. Initializer
expected-link classification and post-link uncertainty repairs are integrated.
Moving a semantic twin from Python to raw Lisp does not close it. A separate
logical specification and a proved efficient representation remain intentional.

Every new reachable behavior carries its caller, invariant, byte, crash and
resource obligations in the [registries](requirements.json), [proof targets](proofs.json)
and scenarios. Physical adapter correspondence, protected native transport,
complete operator/identity workflows, long-lived retention/release/restore,
full two-peer feature coverage and broader v1 work remain open. Preserve native
author signatures, exact source bytes with separate projections, indefinite
retention until authorized release, NNTP/CLI before web, and deferred private
group cryptography. D09 selects mandatory Ed25519 plus ML-DSA-65 over the
framed exact authored bytes. Custody/recovery authority and D11 remain open;
choosing a signature suite does not choose those policies.

Historical progress is retained in source-pinned evidence and
[milestone landing notes](milestones.md#earlier-landing-notes), not repeated here
as competing statements of current status. A scaffold pass is structural
validation; no component result is a mission-readiness claim.
