# Snapshot maintenance resource authority (PRF-1142, SCN-1048)

A captured snapshot is one operation. Admission precedes root acquisition,
source capture, payload view and every new buffer, file or write. The lease
retains all phase resources through actual return/join, relinquished aliases
and definite staging/spool cleanup or publication. A timeout does not refund.

The initial constructor must derive five fixed 2048-u64 page states, native
page conversion, authenticated reader/digest, parser/codec/context stacks,
ordered suffix, old/new root and payload-view coexistence, cleanup and all
source/target/spool descriptors. Its nonzero disk footprint is the actual
FNSI wrapper/header base. Census precedes target/spool creation; final encoded
sizes cannot be guessed from row count. Current resident-suffix size carry
and compiled runtime envelopes are not yet installed, so initial adequacy
and served activation remain explicitly open.

The actual writer emits ten fields:
`(:checkpoint-growth source4 stage maintenance N T M stage-end data-spool table-spool)`.
The immutable source4 names capture/pass/initial ordinal, separate from child
row ordinals. Source epoch equals the maintenance epoch; total source count
is distinct from the maintenance suffix count. Stage is exactly the unique ACL2-issued maintenance job ID;
one job owns one stage/spool set and never silently restarts another under
its grant. Stage-end is `16384 + 16384*(1+M+N+T)` and the spools are exactly
`32*N` and `32*T`. No whole image or digest list is materialized for demand.

`fn-osj-grow(ledger, maintenance, source4, stage, request)` verifies this
identity and size request, requires three previously reserved private FDs,
and calls `fn-pmn-grow` with only the additional disk difference. It returns
`(mv grant-or-refusal ledger)`. Success returns those ten fields tagged
`:checkpoint-funded` and retains that complete receipt in the maintenance
row. The known newly-grown first row is replaced without another lookup.
Refusal preserves the original ledger.

`fn-osj-grant-livep(grant, ledger)` requires the exact retained receipt and maintenance binding,
its worker/identity ownership and descriptor/disk credit. The writer must
recheck it before backing initialization or write effects. Unknown later
frame/arena bytes require their own actual growth before append; this grant
covers only the image and named metadata spools. `fn-pmn-release` remains
permitted only after definite joined cleanup; the initial host lifecycle and
physical cleanup fidelity are still required composition proofs.

This is safe-attempt ownership, not the complete accepted-obligation rescue
reserve. Source proofs about the actual ledger functions do not establish
selected-runtime allocation, a qualified image or deployment.

The actual funded-pool stobj boundary is
`fn-owner-snapshot-growth(maintenance,source4,stage,request,pool)` and
`fn-owner-snapshot-grant-livep(grant,pool)`. Both require funded mode. A named
refinement equates the actual host-called growth and resulting ledger to
`fn-osj-grow`; an unfunded instance cannot obtain the backing grant.
