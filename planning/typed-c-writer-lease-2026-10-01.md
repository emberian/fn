# Typed C semantic lease and durable completion

Source design handoff to owner and portfolio; no admission/proof/runtime claim.

## Chosen boundary

Use the existing singleton `fn-owner-history-semantic-source` STATE slot for a
distinct configuration lease. Do not manufacture an E APR token, reserve an E
Store event, or treat an ATS/account preparation receipt alone as semantic
writer permission. A new internal acquisition transition checks the actual
registered configure holder and acquires the shared writer slot once.

Lease10, zero based:

0. `:history-config-source`
1. original account operation ID
2. actual selector account-turn token
3. captured installed parent6
4. canonical owner epoch
5. actual E count F
6. base configuration generation
7. `(:configuration-record sequence generation txid)`
8. SAME typed configuration record
9. phase: preparing/prepared/persisting/published/uncertain

The selector token supplies an already issued, retained identity. The new
checked lease transition supplies semantic exclusion. There is no second PRS
issuance merely to rename the operation, and every actual allocating preparation
step still needs its genuine compiled BODY/resource source and ATS turn.

## Acquisition and exclusion

The internal owner entry reads the CURRENT holder14 itself. It requires its
actual selection to be `:configure`, matching live selector custody, current
canonical epoch, generation, E count, authority namespace/revision and installed
parent6. Require no existing shared semantic lease, no E APR CURRENT, no ordinary
OC staged record, no owner/node pending stage, and SF ready. Retain a pre-call
acquisition intent before publishing the C lease or changing semantic state.

Construct the record once with the existing `fn-cfg-record-make`, the SAME
`fn-catd-next` typed marker, and the actual core clock stamp. Its sequence is the
base configuration generation, generation is base+1, and txid is actual
`fn-state-next-txid` at acquisition. These are the existing C lineage
coordinates checked by `fn-acj-commit`; the C sequence is not E count or E
identity-next. Check the selected runtime/codec domains before incrementing.

**Keep the typed record only in lease field8.** `fn-ocfg-statep` permits only
ordinary `fn-cfg-recordp` records in OC.staged, and that recognizer requires an
ordinary delta list. A typed `fn-cacm-recordp` marker does not satisfy it. Do not
widen the foundational OC invariant merely to borrow its pending slot.

Consequently actual E APR BEGIN, ordinary reconfiguration, identity/keyring,
reset/reclaim and other semantic writer entries must refuse when this shared
lease is held. The legacy `fn-ocfg-step` staged test alone is insufficient.
Neither E BEGIN nor ordinary C staging may overwrite a C lease. Existing
connection/clock/queue shell activity may continue; the final install overlays
the current shell. Parent6/epoch and the actual retained C lease are rechecked
before publication and at completion. The actual writer-gate cohort must land
with this entry; a recognizer alone does not establish serialization.

## Preparation

Portfolio calls `fn-acj-commit` once with the SAME record, genuine jointly
produced preparation and actual begin/current E cuts, retaining full8 unchanged.
Its successful result carries CP, root, cut, metadata, root carry, next config
and residual preparation. No generic full4 `fn-ccp-publish` substitutes for it.

Prepare the existing plan6:

`(:history-install-plan :C StoreFields14 preparedView10 preparedConfig preparedPostingConfig)`

`preparedConfig` is full8 field6. Build config-history extension and posting
configuration in bounded continuation phases before persistence. In particular,
do not execute chronological append or whole `fn-oag-post-config` at the final
fence. Generic CFGp does not justify reusing old posting configuration when
future-generation group rows are possible. Reuse needs the actual maintained
prefix relation; otherwise use the bounded fold. Preserve all other Store
fields according to the genuine typed-C semantic producer, not guessed copies.

The C publication prepares a new history Source9 identity with unchanged F and
forest/root. Its source/publication identity can use the internally read unique
selector PRS nonce, as already agreed for same-pool publication identities.
No E row, including NIL, is appended to implement a C publication.

## Durable identity and final publication

The selected native journal operation retains SAME encoded `fn-cacm-encode`
bytes and its core-generated target/publication plan before I/O. Completion is
bound to that registered operation:

`(:history-config-completion leaseIdentity Ccoord4 actualJournalReceipt)`

The generation scalar returned by old `fnn-admin-publish` is insufficient for
this boundary by itself. Ccoord4 is an expected identity, not durability
evidence. The actual immutable-journal operation's durable outcome must be
consumed once and must match the retained record/plan/lease. No SF E completion
receipt or transport acknowledgement is accepted.

On genuine durability, fixed assembly installs prepared Store/config/posting
config, CP/root/metadata/canonical/source together over CURRENT owner shell and
CURRENT pins. Preserve actual SF files and E frontier/count; do not call
`fn-sf-core-completion`, generic C replay, or an E append. Consume the retained
full8 and advance the account job through `fn-catd-published` once. Keep the
published receipt until repeated completion can be recognized without reusing
old admission authority, then retire through actual custody cleanup.

An explicitly prewrite refusal may release only its matching C lease and
retained private preparation. An ambiguous write, or mismatch after reported
durability, fences for recovery and retains custody. It cannot restore the old
owner or continue accepting mutations.

## Minimal implementation ownership and checks

Owner owns C lease/acquisition/gates, native registered journal receipt, and
current-shell completion. Portfolio owns saved full8, bounded Store/history/
posting plan production. Existing account custody owns actual selector lifetime;
ATS cleanup remains with its outer turn. Runner integrates the exact cohort.

Check reachable positive C publication with unchanged E F/root; E/C exclusion
in both orders; same generation with wrong txid/lease/record refusal; typed C
never entering ordinary OC.staged; changed parent before write; ambiguous or
durable mismatch fencing; repeated completion; and preservation of current
connections/pins/clock updates during preparation/persistence.

## Retaining C preparation across ATS turns

The actual account CURRENT10 remains `:reserved` while C preparation yields.
Its reservation intent6 binds the old ATS slot/nonce at fields4/5; ordinary
epilogue settlement accepts only `:promoted`. Do not promote an unfinished C
job merely to make that epilogue return, or issue another account reservation.

Captured owns the additive suspension/resume transitions in the account actor;
owner owns the outer epilogue disposition and actual C/journal eligibility.
Keep the current record width. Add `:suspended` as retained account custody,
but do not let the reserved receipt/BODY getter accept it directly.

`fn-owner-account-turn-suspend-current(slot,nonce,ATS,pool,STATE)` returns
MV3(word,pool,STATE). Called by the real epilogue after scheduler/private
per-turn alias cleanup, it checks the actual current reserved account receipt,
holder14, C writer/source/base/preparation, and absence of an active journal
operation. It changes only CURRENT phase and retained output, not the ledger:

`(:account-config-suspension holder14 sourceKey6 base8 prepState lease10)`

This fixed6 is CURRENT.output8. SourceKey is actual holder[2]/CURRENT[5]; lease
is the actual `fn-owner-account-config-source` value. CURRENT token, demand,
operation, original source, request, job and original reservation intent remain
unchanged. Replace the previous suspension payload on a later yield; never
build a chain of prior suspension wrappers.

The current concrete lease phase is `:acquired`. Current preparation13 phases
`:groups` and `:history` yield; `:semantic-joins` can be retained as explicitly
pending, without claiming an executable continuation exists. Intent, refusal,
uncertainty, or a started journal operation is not this preparation-yield arm.
The actual C producer owns its eligibility getter; do not infer absence from a
new placeholder getter returning NIL. Later real phases join this roster with
their source. A separate journal continuation is outside this narrow arm.

Successful parking returns `:account-turn-retained`. The outer wrapper may
then finish its own ATS ticket exactly once. This word grants neither PRS
refund nor deletion of the semantic lease. Raw/ambiguous finish fences the
pool; no resumption is possible from that cut.

The actual native binding uses the SAME fixed control slot on subsequent
account quanta. `fn-owner-account-adoption-resume(slot,nonce,ATS,pool,STATE)`
returns the existing MV5(word,result,ATS,pool,STATE). It starts under fresh
phase2 authority, derives the real `:account-config-resume` BODY cost from the
retained operation/source/subphase, prepays it, then requires:

* actual same-pool `:owner-control` BODY ownership;
* the same slot as original intent[4], and new nonce greater than intent[5];
* actual suspended CURRENT token/holder/source and still-current C lease,
  parent, epoch and captured semantic source.

Under the existing ATS invariant, entering that same slot with a fresh nonce
requires the previous receipt to have left. A supplied larger integer alone
establishes nothing. Preserve original intent fields0..3, replace only its
slot/nonce fields4/5, retain the suspension roots and restore `:reserved`.
Do not replay its original ledger proposal or replace its original resource
result with a per-resume result. Tick dispatches this branch before ordinary
selection and returns the SAME configure operation ID; the native driver then
executes one preparation/publication step. It never calls `fn-catd-next` or
`fn-act-reserve` again for this operation.

If source lookup/prepayment refuses before semantic work, leave the suspended
job unchanged. A checked fresh phase2 ticket can finish while the old claim
remains retained; `fn-ats-finish-owned` handles gate-owned as well as BODY-owned
receipts. Unknown outcome still fences. Suspension and rebinding themselves
leave C/U/NEXT unchanged; fresh ATS entry separately spends its genuine new
turn identity as usual.

The original PRS claim must cover the actual retained preparation peak across
all these steps, including old/new aliases and eventual cleanup. Retaining a
one-quantum-only claim does not enlarge it. Physical reports no installed
same-token demand-growth producer. If the actual source does not establish
that peak, refuse before accumulating further roots; transport supplies no
new positive resource authority. Epoch request debit remains per fresh turn.

Teeth: successful repeated suspend/resume with constant account token and
claim; only ATS entry spends additional identities; same old ticket cannot
resume; wrong slot/source/holder refuses; unknown finish stays fenced; source
refusal preserves the suspended job; no repeated selection; and all retained C
roots survive until genuine terminal promotion/cleanup. The E alias-clear4 is
never used to clear this C continuation.
