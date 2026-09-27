# gpt-6's review of the wave-5 addendum (2026-09-26, dev 30965e6e): the calls

Read against planning/review-request-2026-09-26-wave5.md. gpt-6 inspected published dev at
30965e6e (one commit after the addendum's 027204b0) and reviewed the branch-only continuations'
reported designs without rerunning them. Adopted by the coordinator the same night; every call
below is applied to a lane or recorded as a decision (the applications are listed at the end).

## The calls

| Question | gpt-6's recommendation |
| --- | --- |
| Catalog step 7 and reader pins | Yes to migrating the retrieval arms first; yes to refreshing the view on successful GROUP/LISTGROUP; the view must cover ALL observable versioned facts, not only visibility. |
| Checkpoint pipeline before the catalog | Yes: merge the independently correct pipeline. Coalesce publication requests and bound each step; publishing more often cannot fix insufficient throughput. |
| Cancellation and posting-account secrets | One protected root, two domain-separated derived keys (HKDF, versioned info labels). Preserve D25: a same-source retry is a duplicate; generated server metadata is not the authored source. |
| World-stripped release image | Approve world reduction and build-residue removal; NOT the "63 observed lookups are complete" argument. Ship after a closed runtime-dependency check and failure-path qualification; keep the unstripped image as reference. No direct raw calls. |
| Proof-architecture lane | Assign an owner now, attached to the catalog boundary; postpone bulk deletion until the catalog's actual host integration. |
| Public exposure | No exposed streaming path with PKT-600 outstanding. Require resource-containment and physical-crash evidence for the actual exposed release/profile; narrower exposure when a capability is genuinely disabled. |

D33 to D36 stand.

## 1. Catalog reads
Migrate the retrieval arms first; keep parsing, authentication, error precedence and submission
ownership shared. NNT-042 as: "A successful GROUP or LISTGROUP acquires a fresh coherent view and
performs that command's normal selection effects. Other reads remain on that view until the next
specified refresh boundary. A failed selection leaves the previous view and cursor unchanged."
This is an explicit specification change (specs/nntp.md today: another connection keeps its pin
until the control channel advances it; POST advances the poster's own pin), not a representation
optimization. The real question: every fact read through v must have a well-defined historical
value. Settle three cases at the step-7/8 join: HISTORICAL CONTEXT (fn-cat$a-redecide updates a
row's context in place: a reader pinned before a redecision must not obtain the new verdict
through an overwritten field; a current-enrollment query is identified as such); PAYLOAD
IDENTITY (reclamation replacing a row's handle: an old view must still resolve its payload:
version the mapping or retain immutable references in the view); PUBLICATION ORDER (withdrawal
records w = len(catalog) and visibility uses v <= w, so right after that export alone a fresh
v = count still sees the target: correct only if the composed transaction publishes the next
version before a fresh reader; incorrect if the host treats the current count as the completed
withdrawal's view). Name the public concept ViewId even if it is a committed-event prefix. Tests
cross old and refreshed views with append, cancel-before-target, cancel-after-target, redecision,
reclamation, over HDR/XHDR, OVER/XOVER, XPAT and counts (no split view between ARTICLE on the
catalog and another arm on an old archive). Rejected: the whole machine at once; refresh on
every command.

## 2. Checkpoints
Merge the pipeline once its own gate passes (file ~315 -> 126 MB at 40k; reopen 63.4 -> 28.8 s;
do not attribute the posting-rate change to it). Policy: ONE publication in flight; ONE coalesced
request for a newer frontier; bounded steps; an explicit recovery-lag policy. Do not cancel an
almost-complete publication for a fresher snapshot. Coalescing does not create capacity: with
capture prefix S, publication time tau(S), commit rate lambda, the suffix at finish is about
lambda * tau(S); if that exceeds K, more captures cannot keep the suffix under K (the 208 POST/s
run). Remedies: cheaper publication, reserved service, a different strategy, or admission
limiting when a promised bound requires it. DECIDE THE PROMISE: K as a fast-path threshold with
full replay permitted (honest fallback) or a guaranteed maximum suffix (enforcement). Remove the
per-step whole-state guard now (a batch of B rows whose entry guard walks all S rows is
O(S^2/B)); bound records visited AND bytes per step; exact continuation positions; bind the
finished checkpoint to the prefix it captured, not the count when the final write returns. The
48.4 s book: a narrow proof-cost repair with an explicit D26 exception, never a silently widened
baseline. Apply the same producer/consumer discipline to the BP rotation checkpoint (the ~700 s
unverified decoder): not another fast encoder.

## 3. Cancellation
Share the secret's lifecycle, not the key: one protected random root; HKDF-derived purpose keys
with versioned info labels fn/cancel-lock/v1 and fn/posting-account/v1, bound to the node
identity, with key epochs recorded. A stable non-recycled internal account id for cancellation
ownership, not the login spelling alone. The root lives in persistent private node state outside
the release directory (restrictive permissions, versioned file), created and durably published at
init; an existing node missing a required secret reports a specific failure, never regenerates.
Backup/export distinguishes the public article archive from the private node-state backup; the
root is never in a content export. Rotation retains enough old material to service cancellation
of older articles (RFC 8315: secret, user id, Message-ID). REJECTED: the D25 consequence. D25
distinguishes the poster's source from fields the injecting node adds; a same-source retry under
the same Message-ID resolves as already stored. Order: authenticate and apply policy; compare the
submitted authored source against the held source identity; for an absent article generate
injection metadata and commit. A permitted same-source retry is a duplicate: it does not transfer
posting ownership, replace the held lock, or entitle the retrying account to the original
poster's key; the same holds for the same account across key rotation. A user-supplied
Cancel-Lock stays user input (no blanket removal of every field of that name); signed-source
bytes are preserved, never edited inside a signing subject. RFC 8315 hashes the Base64-encoded
key, not the raw key; relays preserve the injected fields. Tests: same-source retries across
account and key-epoch changes, changed user-supplied lock fields, unauthorized cancellation by
the retrying account, original-poster cancellation after restart, signed carriage through peers.
Privacy: a stable HMAC posting-account is a linkable pseudonym: describe and authorize that
disclosure explicitly.

## 4. Stripped images
Approve world reduction and build-residue removal as a release implementation; not tree-shaking,
not replacing the LP/ld entry, not bypassing *1* guards (no material speed benefit). The 63
pairs are a discovery tool, not the closure criterion: the retained runtime metadata is a
versioned, build-derived dependency set; qualification-time instrumentation catches accesses
outside it; distinguish a property absent in the full image (default correct) from one omitted by
stripping. Include the catalog's attachments and stobj operations when step 8 enters the image.
Witness: the full image as a differential reference (outcomes and durable state, not only the
transcript) over ordinary traffic, malformed inputs, guard violations, failed crypto
observations, missing runtime dependencies, corrupt checkpoints, full replay, init/import,
capacity refusal, failures during protected stobj updates; deliberately remove a required property
and show the build or runtime check detects it. Stack reduction needs its own deep-input witness.
Ship the stripped image when these pass; keep the full image as the developer/reference artifact;
do not block a first public deployment on slimming if the full image fits its selected budget.

## 5. Proof consolidation: an owner on the catalog boundary
Three deliverables: an entry-and-transition map for R (init, full replay, checkpoint load, import
establish it; completion, withdrawal, redecision and failure/recovery transitions preserve it;
export-preserves-fn-cat$corr is necessary, not the owner correspondence); the complete state-and-
effects boundary theorem, PRF-202 (delta equals refresh) first, before deleting the reference path
it replaces; a staged deletion map after step 8 is host-called and measured (retain reference
functions as specifications, not slow executable graphs for old theorem names). The acceptance
state's second payload field is untouched: step 9 measures the joined owner after load, after
checkpoint recovery and after sustained operation.

## 6. Before strangers
PKT-600 is a release blocker for the exposed streaming path: the served fold consumes multiple
submissions while the owner takes only the first (the theorem's "no later submission" premise).
Repair: a core-owned resumable input operation (consume a span to a semantic barrier, retain the
exact unconsumed suffix and parser state, complete the pending submission by token, resume without
another read); tests: one write, arbitrary fragmentation, boundaries inside terminators, TAKETHIS
without a prior CHECK (RFC 4644 permits it). Until then: reject the command at the boundary
(omitting a capability label is not disabling a handler). Hostile-input gate on the selected
artifact and public configuration: semantic, resource and fault containment; PKT-605 (capacity vs
memory, including live changes, handshake/output/pin costs; trusted exemptions never bypass the
global budget). Power-loss gate: the oracle outside the crashed device; acknowledged operations
are a subset of recovered-accepted; a pre-publication refusal never becomes acceptance; identity
bindings and local numbers never reassigned; retention obligations never lost; exercise init,
frontier publication, record/marker ordering, checkpoint selection, pack retirement, release,
interrupted recovery then another crash, near-full states; scope Linux and OpenBSD evidence
separately. Staged rollout: private peers, then the qualified reader/posting surface, with BP or
streaming withheld until their input paths are ready.

## 7. D34 needs an import-publication proof
Keep D34. Import writes a staged ROOT.import-XXXX, admits it, renames onto ROOT, with no modeled
publication program: give import a small explicit publication program (complete and fence staged
contents, validate, publish without overwriting an unrelated destination, fence the parent
namespace); an ambiguous rename/barrier outcome is classified by what is known ("no store was
created" is not a safe universal answer); add its cuts to the physical-crash campaign. Distinguish
Store-history export from complete node backup (secrets, peer journals, consumer state, other
persistence domains; the archive being the newest history).

## 8. The smaller decisions
PKT-582: bare `init` selects a conservative supported preset within an explicit process budget and
prints it; a requested profile is honored or refused, never silently reduced; detected RAM is not
all available. PKT-587: required-marker birth for an empty Store and coverage for an imported
history; no normal-open exception treating "marker absent and no records" as a new Store.
PKT-584: exact equality scoped to the referenced payload row; named deferral on unobserved free
space. PKT-586: numbers never reused (RFC 3977 §6, not §3.1.1). PKT-579: a provisioned, reliably
mounted node volume whose filesystem identity is required at startup (a missing mount must not
place the Store in the underlying directory); measure the edge machine before any throughput
promise; keep the fsn1 move separate from the DNS cutover authorization.

## Applied by the coordinator (2026-09-26 ~23:30Z)
- catalog-slice-5 (Fable): the three ViewId cases, the NNT-042 wording as a spec change, the
  crossing tests; the arms first.
- checkpoint-pipeline-5 (Fable): coalescing, bounded records+bytes per step, the prefix binding,
  the explicit D26 exception; K decided as a fast-path threshold with full replay permitted until
  ember chooses the guarantee.
- newsreader-cancel-2 and usenet-headers-3: the HKDF root and labels, the internal account id,
  the private node state, D25 preserved, the Base64 detail, the linkable-pseudonym disclosure.
- image-floor-2: world reduction and residue only; the dependency set with instrumentation; the
  differential witness; the full image kept; PKT-582's new shape.
- transit-pipelining: the core-owned resumable input operation and the TAKETHIS-without-CHECK test.
- bp-checkpoint-open: the pipeline's discipline, not an encoder.
- power-loss: the oracle outside the device; the properties and boundaries.
- New lanes: import-publication (D34's program, its cuts into the crash campaign);
  catalog-boundary-owner (Fable: the entry map, PRF-202, the staged deletion map).
- Public node: streaming rejected at the boundary until PKT-600 closes; staged rollout.
- Later lanes: PKT-605 (capacity vs memory), PKT-579 (mount identity at startup).
