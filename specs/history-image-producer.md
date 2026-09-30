# Actual private canonical image writer (PRF-1144 / SCN-1050)

The full obligation is the host-called `fn-hpi-tick`, reached by
`fn-owner-history-image-tick` through native `fnn-hpi-step`. The writer
retains a fixed controller, five fixed page buffers and the existing
`pgs-digest-state`. The caller's actual maintenance admission must reserve
all constructor/child/native/source lifetimes before those allocations;
image growth alone is not that whole-operation admission.

Immutable job source4 is `(epoch (capture-ticket count) 0 0)`; census is
pass0 and the actual source restart supplies emission pass1/row ordinal.
The stage ID is the issued maintenance job ID, naming one private stage
and two spool files for one attempt. Uncertain effects retain that attempt
and its credit until joined cleanup; no host counter creates an identity.

`fn-hpi-begin` derives exact rounded column/pool capacities, calls the actual
canonical layout/domain check and applies the admitted runtime/profile
extent coordinate. `fn-hpi-growth-request` returns exactly ten fields:
`(:checkpoint-growth source4 stage maintenance N T M stage-end 32N 32T)`.
Actual `fn-osj-grow` issues and retains the corresponding exact receipt.
Every step and source offer checks that receipt against the actual funded
pool before child allocation, issue, ACK consumption or buffer reuse.
A generic later maintenance growth invalidates the old receipt, so all
image work must finish before later framed segments grow their own backing.

The stream writes physical zero-page0 separately, then the logical header,
four columns and pool with canonical zero padding. It hashes acknowledged
stage bytes with the existing `pgs-dcb` engine, writes one32-byte data digest
per spool slot, streams341 entries per table with two zero tail words, hashes
acknowledged tables, then streams the full M-page directory from table digests.
Directory hashing covers all M pages. The terminal root uses original
`fn-hpir-root 1 1 N directory-digest`, the fixed16-word/128-byte concrete
record check extracted from `pgs-x-write-rec`, with N data pages. The abstract
`pgs-make-rec` calls constrained `pgs-digest` and cannot be executed; `fn-hpir-root-agrees-with-current-record-writer` connects the complete six-field
root to the actual `pgs-x-write-rec` with no hypotheses. Its proof derives the
checksum representation from actual BLAKE3 output and the concrete word writes;
legal executable reference calls still satisfy their stobj guards. Abstract
digest observation remains a separate named proof obligation.
The writer returns the exact
captured node/salt/count/trail for the outer existing `fn-his-binding`.
Full Store summary and A/F/P/E/R framing/publication stay with the outer
producer; they are not invented or omitted by this canonical image helper.

Write-page effect is
`(:write-page source4 stage serial region logical physical offset 16384 generation)`;
ACK is `(:written source4 stage serial generation :ok/:uncertain)`.
New I/O effects are ten fields
`(tag source4 stage serial kind ordinal offset length generation payload)`,
with tag `:read-stage`, `:write-spool` or `:read-spool`.
Reads return `(tag source4 stage serial kind ordinal generation outcome octets)`,
tag `:image-read` or `:spool-read`; writes return
`(:spool-written source4 stage serial kind ordinal generation outcome)`.
Outcome is `:ok`, `:uncertain` or `:refused`, never a transport ACK.
Response octets are validated in at most64 cells. Only one effect is pending;
exact stage/source/serial/generation and requested coordinate match precedes
consumption. A mismatching completion leaves the continuation unchanged.

The native wrapper retains already-admitted buffers, threads the actual
funded pool and performs no I/O, budget/key/address/hash decisions. Producer
I/O executes only returned effects under its actual stage descriptor authority.
`fnn-hpi-offer` requires the actual new-salt `fn-omk` result; old source header
MKEY is not a substitute. Source rows stay pending through cold byte demands
until `:row-done` with `(:row-emitted rowtoken encoded)` after column3 install.

Status: all writer definitions and guards pass protected source admission.
The complete small decoded-cold-row trajectory compares all9 physical pages,
all7 digest spools, padding/table/directory words, frozen terminal fields and
root against the independently executed `pgs-x-write-rec`. Mutation fixtures
check the live ledger/issued demand antecedents before stale-stage, uncertain
outcome and malformed-octet rejection. These are source runtime fixtures.
General full canonical residual/effect/authority/progress proof, abstract
digest observation, larger table/directory trajectories, initial whole-operation
funding and actual native joined execution remain open. No certificate,
qualified image, deployment, publication or complete checkpoint claim follows.
Physical page0 remains zero as the original snapshot format specifies: its
sole root record is protected by the outer F binding consumed by `fn-his-open`.

The actual funded host wrappers also pass scoped source admission in the same
writer/effect world. A reachable fixture installs the actual pool, obtains
its maintenance and image-growth receipts, drives full zero-page issuance,
and calls the exact native-facing effect projections. Its short-write result
puts the writer in recovery while retaining the pending effect, buffer
generation, complete buffer and live credit. This is a concrete host seam
fixture; it does not establish initial whole-operation allocation adequacy
or replace native syscall/lifetime and general writer proofs.

The proof-only tagged byte/census join connects both resident and decoded
cold children to one canonical residual and length invariant. Tick preserves
that residual; attributed supply preserves it only with the current demand,
exact requested position and byte from the immutable pool. The uniform
census counts an emitted supply byte exactly once. Its supply law explicitly
keeps active success distinct from completed refusal. The actual producer
`fn-hct-tick` completed-row theorem then preserves article count and padded
pool length, assuming the carried prior census, child invariant and exact
row denotation. Five complete positives and fifteen hypothesis-removal
witnesses passed, including a wrong NIL-classifier byte. This does not
establish source lineage, strict productive progress or the whole image
writer invariant.

The tagged pool boundary now preserves the complete concrete page prefix plus
canonical pending words through the actual `fn-hpe-tick` and attributed
`fn-hpe-supply`. The proof reuses the original pack8 and eight-byte-prefix
lemmas. It includes partial words, eighth-byte writes, final padding and
full-page supply without consumption. A proof-only finite schedule calls the
actual tick, supply and page reset; conditional completion yields exactly the
original codec's packed words and byte count for either resident or cold rows.
Seven complete positives and thirteen premise-removal witnesses passed; the
malformed logical-buffer cases are corrupted-state examples. A logical page
transfer proves no physical write acknowledgment or release. Source lineage,
productive termination and whole writer phase/effect/authority remain open.
The final proper-local evidence is
`planning/evidence/history-pool-tagged-refinement-source-2026-09-30.json`;
its proof body took29.39 ACL2 seconds/10,608,053 steps in the composed source
world, with no matched proof-cost or qualification claim.

The actual writer growth call now uses the selected Linux x86-64 signed-long
backing profile, and every retained grant check also checks that profile.
The exact effect projection admits I/O only within its captured target or
spool extent and the signed offset domain. Profile refusal preserves the
complete cursor, ledger, five buffers and digest state. Its oversized-layout
fixture is a corrupted-state case; it does not claim a valid huge census
passes earlier current-format constraints. An actual funded first page,
out-of-extent pending-request mutation and uncertain-write recovery passed
in the same composed source world. The full cold image trajectory was rerun
against the changed controller. This establishes no whole-operation INIT
adequacy, whole writer invariant/progress or native execution claim; exact
source evidence is `planning/evidence/history-image-native-profile-source-2026-09-30.json`.


The supporting `history-image-writer-refinement` safety boundary is now
proved for the actual ten-output `fn-hpi-tick`. Immutable capture and exact
stage receipt remain live through retained steps; successful initial growth
establishes the same authority. Returned `:write`/`:io` alone establishes the
fixed effect tag, pending effect, captured source/stage and monotone serial.
Internal arbitrary-tag helpers retain their own tag constraint. The complete
uncertain-page and uncertain-stream laws preserve the ledger, all five buffers
and digest state. Stream return word `:uncertain` sets the cursor phase to
`:recovery-required`; it is distinct from the page return word
`:recovery-required`. Literal tests reach all four actual I/O phase kinds,
assert complete premises/results, and falsify each omitted premise while
retaining the others. Corrupted phase witnesses use explicitly constructed
matching observations and make no claim that the native executor emits them.
The canonical byte trace still uses an explicit acknowledged-write/read oracle;
A-HPI-POSITIONAL-IO's visible-byte assumption needs exact held FD/private role
and ordered trace composition and does not establish durability. Whole byte
fidelity, productive progress, initial demand and native qualification remain
open. PRF-1144 remains planned with no completion events.


`history-image-private-trace` now connects a full acknowledged write to an
exact later read under A-HPI-POSITIONAL-IO, and connects the actual complete
nine-field read observation to that named visible range. The interleaved
stage/data-spool/table-spool trace carries a stable pairwise-distinct file
identity triple and an explicit visible frame for every untouched role on
every write. A full count on the selected role alone supplies no such frame.
Local functional-instance witnesses exercise all literal read/readback
premises and complete outputs; corrupt abstract bytes and improper payloads
are labelled separately from actual controller-issued operations.

These are conditional proof-only byte-trace laws. Their helper definitions
are not served entries or guard-verified executable implementations. Actual
held FD-to-file identity/nonalias lifetime correspondence and association of
trace payloads with issued HPI effects still need the composed writer proof,
alongside canonical phase invariants, productive progress and whole-operation
INIT/native qualification. The named visible-byte assumptions establish no
durability. Exact source evidence is
`planning/evidence/history-image-private-trace-source-2026-09-30.json`;
PRF-1144 remains planned with no completion events.


The actual `fn-hpi-tick` directory-emission phase now appends the canonical
global `pgs-encode-run` word and grows the concrete scratch to its next
canonical prefix while preserving the ledger, four other buffers and digest
state. Its carried proof invariant relates ordinal/component to page/used
position, remaining words, the captured table count and the exact current
cached digest. The served step does not reevaluate that model. A full small
decoded-row/page/spool trajectory reaches the positive; current-cache
corruption and missing-cache IO demand separately falsify the two literal
premises and complete results.

The earlier coordinate is a continuing directory-word phase law. At that
coordinate, full invariant preservation, page handoff/reset and table packing
with 341 entries and two trailing zero words, whole pool/data/digest/root
fidelity and strict productive progress remained open. No initial/native/
qualification scope is transferred. Exact source
evidence is `planning/evidence/history-image-directory-phase-source-2026-09-30.json`.


The actual continuing `fn-hpi-tick` now also preserves the complete carried
directory invariant, including its concrete canonical prefix. Digest/cache
agreement applies only while the ordinal names an active entry; padding is
zero regardless of an irrelevant cached value. The weakened invariant is
proved preserved. A labelled padding-cache mutation reaches padding by four
actual steps and checks both complete antecedents and conclusions, including
the failure of the former unnecessarily strong cache agreement. The reachable
positive and both literal premise removals also check the full next invariant.

This completes the continuing directory state join, while page handoff/reset,
table packing, whole writer phase/progress, actual effect/FD association and
INIT/native qualification remain open. Runtime bytes are unchanged. Exact
source evidence is
`planning/evidence/history-image-directory-invariant-source-2026-09-30.json`;
PRF-1144 remains planned with no completion events.


Actual full directory-page handoff now preserves the entire concrete buffer
and global entry continuation while issuing the exact captured positional
write effect. The page cursor advances before the ACK; its ordinal/component
never resets to a page-local entry. The selected-scratch ACK context and
actual returned `:written` status imply the core-matched definite ACK,
reset/begin, one buffer-generation advance, retained metadata/layout/cache,
and full ledger/other-buffer/digest frame. Stale ACK serial and corrupted
retained buffer selection are separately labelled literal premise removals;
neither substitutes a host success flag for the core decision.

The complete small decoded-row/page/spool trajectory checks the full page
handoff and exact reset positives, while scratch corruption and missing live
receipt remove the handoff premises individually. Exact source evidence is
`planning/evidence/history-image-directory-handoff-source-2026-09-30.json`.
Cross-page canonical invariant restoration,341-entry tables/two-zero packing,
whole image/progress/effect-to-payload/FD joins, installed source authority
and the full INITIAL runtime/funding envelope still remain open. The existing
signed growth receipt does not establish initial adequacy or native activation.
PRF-1144 stays planned with no completion events; runtime bytes are unchanged.

The nonfinal directory-page handoff now establishes the complete retained
resume invariant from the current canonical invariant, positive remaining
words and actual returned `:write`. Its exact `:written` acknowledgement
then restores the full next-page invariant with empty scratch and unchanged
global entry continuation. Page crossings can occur halfway through an
entry; neither ordinal nor component resets to a local page coordinate.

Seven additional literal phase assertions check both complete positives
and every retained premise removal. They construct a two-page directory
phase using a supported actual layout, actual growth receipt and canonical
scratch filled by `fn-hpb-put`, then call the actual writer for issuance
and ACK. They are labelled constructed phase witnesses, not a complete
large-image trajectory or native run. All ten previous assertions remain.
Exact clean source evidence is
`planning/evidence/history-image-directory-resume-source-2026-09-30.json`.
General 341-entry tables/two-zero packing, full image/progress/effect-to-
payload/FD joins, installed source authority and complete INITIAL/runtime
funding remain open. Runtime is unchanged and PRF-1144 remains planned.


The separate table phase proof now connects actual `fn-hpi-tick` to each
canonical table word, full continuing invariant and complete page handoff.
Each page slices at most 341 six-word entries at its global data ordinal;
the final two words are zero. The cache invariant constrains only the
current active entry, excluding padding. Returned `:write` supplies the
entire 2048-word model page, exact captured positional effect, retained
`:table-digest-start` continuation and full ledger/buffer/digest frame.
These are full call-output statements, not new runtime validation.

Ten new literal assertions check three complete positives and every retained
premise removal for word, tail and page laws. They construct a supported
N517/T2 table phase with actual maintenance admission and live growth
receipt, fill the concrete scratch using `fn-hpb-put`, and call the actual
writer. They are explicitly phase constructions, not a complete large-image
trajectory or native evidence. All seventeen directory assertions remain.
Exact clean source evidence is
`planning/evidence/history-image-table-phase-source-2026-09-30.json`.
The next-table/digest transition relation, full pool/data/digest/root
trajectory and progress, actual effect-to-payload/FD coupling, installed
source authority and complete INITIAL runtime/funding envelope remain open.
Runtime is unchanged; PRF-1144 remains planned with no completion events.


Actual digest-spool settlement now establishes the next canonical metadata
state: the final data-page spool ACK starts table zero, a nonfinal table
spool ACK starts its next table, and the last table spool ACK starts the
full directory at global ordinal/component zero. The carried context names
the supported page/layout relationship and empty scratch. Actual returned
`:continue` plus that context implies the entire table or directory
invariant, with all buffers, ledger and digest state unchanged.

Nine added literal assertions cover all three complete positives and both
retained premise removals. First-table and directory cases follow the actual
small decoded-row image pipeline; second-table is a labelled supported phase
construction. Model digest lists are parameters to these empty-prefix
transition laws. Their relation to actual spool contents still needs the
private byte/digest observation join and is not inferred from an ACK.
Exact combined source evidence is
`planning/evidence/history-image-spool-transition-source-2026-09-30.json`.
All thirty-six assertions pass. Full image residual/progress, private
payload/FD coupling, captured source authority and INITIAL runtime funding
remain open. Runtime is unchanged; PRF-1144 remains planned/events[].


The actual scalar payload accessor `fn-hie-page-byte` now has a full-output
serialization boundary: under its actual live write plan, supported byte
index and selected full concrete page, it returns the corresponding octet
of `pgs-words-le-octets` applied to that retained prefix. All five buffer
selectors use the same boundary. This connects actual native payload
selection to the logical codec without adding another host codec.

Five literal positives are labelled constructed supported page-effect
phases with actual maintenance admission, growth receipt, concrete scratch
writes and issued positional effects. Three mutation/removal fixtures retain
the other facts and distinguish an unwritten cell from refused authority
or selector. Each checks the complete context and complete output, including
the mutated model side. These are not full-image or native witnesses.
The clean source package and all eight assertions are recorded in
`planning/evidence/history-image-effect-payload-source-2026-09-30.json`.
Official local IHS support was source-loaded without matching certificates;
that limitation is explicit in the manifest. Full image/progress, private
spool/digest/root, retained FD roles, installed source authority and complete
INITIAL runtime funding remain open. Runtime is unchanged; PRF-1144 remains
planned with no completion events.


The actual leading-page controller now preserves the complete canonical
zero/header prefix while continuing and hands off its full 2048-word page
with the exact positional effect and retained continuation. The continuing
law frames c/ledger/the other four complete buffers/digest, increments used
once, and retains scratch epoch/lease. The handoff law equates the entire
actual call output to the issued core page effect with all state frames.

Four complete positive witnesses reach these phases from actual admission
and begin/tick. The header witnesses drive zero-page issuance and exact
core ACK first. Each has two separately labelled retained-premise removals:
corrupting word zero removes the invariant but retains the status; removing
the growth receipt retains the invariant but removes the status. Every
complete conclusion is checked, with all buffer cells and every digest
frame compared where the theorem requires an unchanged stobj. All twelve
assertions and the fresh proof-body replay are recorded in
`planning/evidence/history-image-front-source-2026-09-30.json`.
Full pool/column/data, private digest/spool/root and progress, FD/source
authority and INITIAL funding remain open. Runtime is unchanged; PRF-1144
remains planned with no completion events.

The conditional scalar-column carry now reaches the actual `fn-hpi-tick`
entry in `fn-hpi-column-step-preserves-full-canonical-column-carry`.
Its two literal premises are the complete `fn-hpicol-writer-ready-p`
(captured salt, full cursor/census association, and all four canonical
region suffixes) and an actual `:continue`/`:row-done` result. Canonical
columns are projections of the existing FNADTSN2 `adt-rows-cells`/transpose
model; this proof does not introduce another codec. Each accepted column
preserves all four suffixes and the complete next body/controller, with
pool, ledger and digest unchanged. The exact row token/encoded ACK and
completed history/ordinal/padded pool offset advance only at column3.
The proof-only observers are not host entry points or new guard claims.

Four decoded-source trajectory positives assert the complete literal
antecedent and conclusion. Each first establishes that full baseline before
a separately labelled frozen-salt corruption or retained-receipt removal;
the other premise holds and the complete conclusion fails. Expected body
comes from independently executing the actual inner function and restoring
every test buffer word/metadata before calling the outer subject. Full pool
and digest frames are compared. Fresh same-world source evidence is
`planning/evidence/history-image-body-source-2026-09-30.json`.
Full source/pool residual, page ACK/reset/padding, private stage/spool/digest
fidelity, whole-image progress, producer/FD authority, INITIAL and native
qualification remain open; PRF-1144 remains planned with no cited events.

The conditional column page/reset join now reaches actual `fn-hpi-tick` in
`fn-hpi-written-page-preserves-full-canonical-column-carry`. Its four literal
premises are the exact pending column ACK context, the complete original
four-column canonical carry, a full 2048-word selected buffer, and actual
`:written`. It preserves all four next canonical suffixes, resumes `:body`,
retains the entire row cursor and frozen salt, and frames the complete pool,
ledger and digest. The structural companion separately proves exactly one
buffer reset/page and generation advance; all other full buffers are unchanged.
A full prefix's length establishes the empty next suffix after reset.

Four constructed supported full-page phases use real maintenance admission,
begin/growth, actual outer write issuance, exact core observation and ACK.
They compare every literal conclusion, including all backing words and all
digest fields. These are phase witnesses, not full large-image trajectories.
For each column, labelled resume and untouched-column corruption and uncertain
write outcomes remove one premise while affirmatively retaining the others and
failing the complete conclusion. A separately labelled corrupted pending
partial-page fixture retains the other three premises and demonstrates why
used2048 is necessary; its internal reference issuance is explicitly not an
actual outer issuance of a non-full page. The structural law continues to hold
for the canonical/partial mutations because it asserts reset ownership rather
than canonicality. All twenty assertions and a fresh source body replay are in
`planning/evidence/history-image-column-pages-source-2026-09-30.json`.
Actual column issuance/page-payload and padding, full source/pool residual,
private stage/spool/digest/root fidelity, whole-image progress, producer/FD
source authority, INITIAL and native qualification remain open. Runtime is
unchanged; PRF-1144 remains planned with no cited completion events.

The preceding actual column issuance is now bound by
`fn-hpi-column-page-handoff-is-complete-canonical-page`. Its literal premises
are full `fn-hpicol-writer-ready-p` and actual `:write`. The selected prefix
is exactly 2048 words of the original canonical column at its page base.
The entire output equals the existing `fn-hpi-await-region` result over the
retained body/controller; ledger, all five complete buffers and digest are
unchanged. The next controller establishes the exact column ACK context
required by the reset law. This binds canonical payload to the existing
positional issuer without host page math, a new codec or premature row ACK.

Four constructed supported phase positives and two retained-premise mutations
per column check every literal clause. Selected-word corruption removes full
ready carry while retaining actual write; receipt removal retains full ready
carry but removes write. Both fail the complete conclusion. The expected
positional effect and continuation come from independently calling the actual
pure issuer. All twelve assertions and the fresh source body are recorded in
`planning/evidence/history-image-column-handoff-source-2026-09-30.json`.
These are conditional phase/source claims: full source/pool and padding,
private stage/spool/digest/root fidelity, productive progress, actual retained
FD/source authority, INITIAL and native qualification remain open. PRF-1144
remains planned with no cited completion events; runtime is unchanged.

The actual padding branch is now connected to the original canonical model
in `fn-hpi-padding-step-preserves-original-canonical-region` and
`fn-hpi-padding-page-handoff-is-original-canonical-page`. Under complete
padding-ready carry and actual `:continue`, one zero is appended to the
original `fn-hp-wpad` region suffix, used advances once, selected epoch/lease
are retained, and the controller/effect, every other complete buffer, ledger
and digest are unchanged. Under the same carry and actual `:write`, exactly
2048 original padded words are handed to the existing region issuer with the
entire MV output and all buffer/ledger/digest frames. Original ADT padding and
packing laws are reused; no second padding codec or capacity algorithm exists.

Thirty complete literal assertions use actual decoded-source trajectories to
reach both used1 and used2048 in each of five regions. They execute real
maintenance admission/growth, zero/header writes, source supply/columns and
all preceding padded-region writes/ACKs. Each establishes a full reachable
baseline before selected-word corruption or retained-receipt removal. The
mutations affirmatively preserve the other premise and fail the full
conclusion. Every framed backing word and digest scalar/frame is compared.
Fresh proof-body and fixture coordinates are committed in
`planning/evidence/history-image-padding-source-2026-09-30.json`.
Padding ACK/reset/region advance, full source/pool and whole-image/private
trace/progress, actual retained FD/source authority, INITIAL and native
qualification remain open. Runtime is unchanged; PRF-1144 remains planned
with no cited completion events.

Definite padding write acknowledgment is now composed in
`fn-hpi-written-padding-page-preserves-complete-canonical-carry`. Exact
padding ACK context, complete original five-region carry, selectedused2048
and actual `:written` preserve every next original canonical suffix, including
the pool, while resuming pad with the original body and padding region. Its
structural companion proves that only the issued buffer/page/generation is
reset/advanced; capacities and salt remain fixed, pending ownership clears,
and every other complete buffer plus effect/ledger/digest is framed.

Twenty-five complete literal assertions drive real decoded-source trajectories
through current full-page issuance and exact ACK. Resume corruption,
untouched-region corruption, and actual uncertain outcomes each affirm all
other premises and fail the complete conclusion. A separately labelled
corrupted pending counter/empty-buffer at capacity retains canonical carry
but demonstrates why the full-buffer premise is required; it is not a
reachable real issuance claim. Structural ownership remains true under the
canonical/full mutations. Every backing word and digest field is compared.
Fresh source/fixture evidence is committed in
`planning/evidence/history-image-padding-pages-source-2026-09-30.json`.
Region advance, full source/pool and private stage/spool/digest/root/progress,
actual retained FD/source authority, INITIAL and native qualification remain
open. Runtime is unchanged; PRF-1144 remains planned with no cited events.

Actual padding scheduling is now connected in
`fn-hpi-complete-padding-region-advances-with-canonical-carry` and
`fn-hpi-complete-padding-starts-digest-with-canonical-carry`. A complete
region context, original five-region carry, selectedpage-at-cap and actual
`:continue` give exactly the region increment, retain the canonical carry,
and frame every buffer/effect/ledger/digest. At final region5, explicit
completed page counts and the five-region invariant establish that all
five used tails are empty. Actual `:continue` then gives exactly the
`:data-digest-start` phase update and unchanged canonical fields/frames.
This names scheduling completion; canonicality of earlier physical pages
still depends on the actual acknowledged-write trace and role/FD assumptions.

Thirty complete literal assertions run actual decoded-source trajectories
through each region's prior writes and ACKs, and through allfive regions for
the final boundary. Body-phase/buffer corruption and receipt removal affirm
all other premises and fail the full conclusion. Five unfinished-region
alternatives are reachable zero-insertion branches with page-at-cap false;
a premature final-region mutation is explicitly corrupted state. Fresh
source/fixture evidence is in
`planning/evidence/history-image-padding-phase-source-2026-09-30.json`.
Full source/pool/private stage/spool/digest/root fidelity, finite progress,
actual retained FD/source authority, INITIAL and native qualification remain
open. Runtime is unchanged; PRF-1144 stays planned with no cited events.

The actual executor byte boundary is now joined to the original padded page
in `fn-hie-padding-page-byte-is-original-canonical-octet`. Its two premises
are the complete original canonical padding-ready carry before the actual
`fn-hpi-tick`, and the complete executor byte context after that step. The
conclusion is the entire `fn-hie-page-byte` output: `:octet` and the selected
byte of the original `fn-hp-wpad` region page. The proof reuses the existing
retained-page serialization boundary. Actual issuance selects the retained
region and preserves all five page buffers. An explicit write-status
premise was proved implied by the retained two premises and removed.

Fifteen complete literal assertions drive actual decoded-source trajectories
through prior writes and ACKs to all five regions. Each positive compares
all 16384 actual executor bytes and complete byte context with the original
canonical page. Selected-word corruption removes canonical carry while
retaining executor context; stale stage removes executor context while
retaining canonical carry. Both fail the complete byte output. The matching
source coordinate is
`planning/evidence/history-image-canonical-payload-source-2026-09-30.json`.
This establishes issued canonical padding payloads, not private-file truth.
Actual stable FD/role association and named positional write/read/frame
trace coupling, complete source/pool/image/digest/root trajectory, finite
progress, installed source authority, INITIAL and native qualification
remain open. Runtime is unchanged; PRF-1144 remains planned with no cited
completion events.

`fn-hpicopy-issued-padding-payload-is-original-canonical-page` joins the
complete payload observation to the original canonical padded page. Its
proof-only `fn-hpicopy-page` observes exactly the native executor's fixed
16384 calls to `fn-hie-page-byte`, stopping on refusal. Under original
padding-ready carry and complete executor context, the whole output is
`:complete` plus the full original page. This is a list observation of the
existing scalar/vector copy boundary, not another served codec or a claim
that compiler/runtime marshalling is proved. The exact native loop source
is frozen in the accompanying evidence coordinate.

`fn-hpicopy-issued-padding-write-has-canonical-visible-roles` composes that
payload with the named positional write and all three untouched-role frame
relations. Under original padding-ready carry and the complete private step
predicate, the entire visible target/data-spool/table-spool view is the
original canonical target splice and both unchanged spools. Executor context
was proved implied by these two premises and removed. Files are the stable,
pairwise distinct retained role identities; correspondence to actual live
FDs/inodes and the serialized native scratch is an explicit caller/trust
obligation. Full syscall counts do not establish the named assumptions.

Twenty-five complete assertions cover all five actual decoded-source pages
and local-witness instances of the named physical assumptions. They check
the complete payload and all three role outputs, with canonical-word and
stale-stage mutations, lying writes, and independent data-spool corruption.
The last retains the exact target write and every other role frame. A local
functional instance ties these model assertions to the exact public theorem.
The matching source coordinate is
`planning/evidence/history-image-page-copy-source-2026-09-30.json`.
Whole source/pool/image/spool/digest/root trajectory and finite progress,
installed source authority, INITIAL, durability/publication and native
qualification remain open. Runtime is unchanged; PRF-1144 stays planned
with no cited completion events.

## Actual action scheduling continuation

The native FnNHPiAction takes one existing funded writer step under the extent lock and releases that lock before at most one existing positional executor call. It returns the full effect and observation unchanged for the next quantum. The caller holds its action lock through the returned I/O and retains the observation; no retry, stage creation or publication occurs here.

FnHPIEffectObservationDisposition is the guarded ACL2 scheduling projection. Only complete successful ACK envelopes permit the next action; an exact pre-I/O refusal stays refused, while uncertainty, lost post-I/O authority and malformed envelopes require recovery. This is not ACK authentication: actual FnHPITick still checks pending effect/source/stage/serial/generation/live grant. Its direct unfold is uncited.

The protected hpia1 test root freshly loaded two proper-local source dependencies and twelve target forms in 0.03 ACL2 seconds /748 steps. Its source token and new observation-book hashes are frozen in the manifest. The isolated SBCL test runs the real native wrapper with core/executor test doubles: all writer aliases are replaced, I/O runs outside the extent lock, uncertainty/refusal/retained results pass unchanged, and a throwing executor is called only once. This is scheduling evidence, not physical I/O or qualification.

Snapshot owner joins the actual emission callsite and retains a distinct stage holder. Actual measured→installed-current source authority, writer initialization, INITIAL runtime/allocator, stage FD/receipt lifecycle and outer publication remain open. The original hpie2 proofs stay at their archived earlier PMN/SMD coordinate; this tiny gate does not recreate that world.

## Bounded preparation implementation

FnHPIPBegin creates a fixed thirteen-cell preparation continuation from the source producer's count/padded-pool observations and retained source/maintenance/stage/metadata. FnHPIPTick runs one existing FnHCCCapTick. Column and pool capacities finish independently; only then does the controller call actual FnHPIBegin with the existing selected signed backing profile. The native FnNHPIPreparationStep advances the returned core continuation once, retaining it on continue/refused and replacing it with the actual writer only on prepared. No host capacity computation, file opening, backing growth or source restart occurs in this helper.

The actual recovery-only initializer must derive source4, count/pool, node/salt and frozen log coordinate from the installed same-operation source producer. Native supplied metadata is not an authority ABI. Snapshot owner retains that bridge and stage lifecycle; no live OSN capture is substituted during recovery.

The finite hpip1 source world admitted fourteen exact frozen runtime definitions, including all three new preparation guards (0.81 ACL2 seconds /1,829 steps). Six executable MV-LET component assertions passed in the same world (0.00 seconds/0 proof steps), covering complete empty constructor output, individual column/pool doubling quanta, invalid census and mismatched maintenance frontier. The original executable MV-NTH assertions were refused and are retained in the log; no definition changed during that repair. Pagestore-exec used nine exact cached books; snapshot-source-token was source-loaded under proper local scoping. This is exact component admission, not a normal whole HPI include proof. Form balance, strict theory and native macro order pass. The image-free real SBCL wrapper test with explicit core/executor doubles passes, including all intermediate/refused/prepared alias cases. No physical, installed-runtime or qualification evidence is implied.

The source intentionally advances the integrated implementation while normal convergence remains active. The original HPI world expired after archived earlier proofs; this checkpoint does not recreate it or launch a duplicate broad bootstrap. The full include/refinement context and genuine initializer remain separate integration obligations; no earlier broad-world evidence is transferred.
