# Internal allocation epoch (STO-10001, PRF-1154)

The single existing page-read pool appends installation, allocation mode,
epoch, occupied allocator bytes L0, cumulative prepaid allocator bytes A,
active allocating turns, and collection nonce. The prior ledger, pool mode
and incoming carrier retain their positions. This is a new pool10 constructor
coordinate; old pool3 allocation evidence does not transfer.

The internal scalar implementation is `books/allocation-epoch.lisp`; actual
same-pool update subjects are `books/allocation-epoch-pool.lisp`. These guarded
functions provide no public installer, supplied tariff, observation or turn
receipt authority. Their `*-internal` suffix marks an integration restriction,
not an access-control mechanism. There is no served callsite yet.

An immutable installation associates the exact selected runtime, image,
profile and pool with an immediate integer domain, physical budget, a qualified
affine allocator footprint envelope, collector and external resident reserves,
ordinary allocation headroom, and source-derived gate, collection and resume
allowances. The representation predicate does not install or authenticate that
association. The selected runtime must establish the footprint envelope,
including allocator region acquisition, slack, fragmentation and rounding.
It is not a resident-set measurement.

Before allocating control evaluation, entry prepays Qgate and counts an
allocating turn. Before allocating the chosen operation body, its internal
source evaluator supplies the corresponding body allowance. Checked subtraction
precedes addition; no intermediate accepted sum exceeds the installed immediate
domain. Ordinary admission preserves reserved cleanup/control/collector
headroom. An unavailable gate or body yields and closes admission by entering
draining. Gate allocation remains charged after a refused body.

A increases monotonically between qualified collection observations. Returning
logical grants, closing a socket, unlinking a node or settling a turn never
refunds A. `fn-aec-logical-ledger-release-cannot-refund-allocation` frames the
actual existing ledger keeper against the allocation field. Active-turn return
is internal only after consuming the actual same-pool scheduling-turn receipt
once. A retained connection-holder binding is not a scheduling-turn receipt;
these scalar fields cannot independently authenticate completion.

Collection requires draining and zero admitted allocating turns. Collection
control is prepaid before nonce issuance; collecting with no nonce retains the
issuance intent. The nonce comes from the existing shared PRS issuer, not an
epoch-local counter. Raw uncertainty fences while retaining charge, epoch,
installation, nonce, active turns, ledger and incoming carrier.

Only a matching completed selected observation under the closed process-wide
barrier resets L0 and sets A to Qresume, increments epoch, and may reopen entry.
The public completion boundary must take only the nonce and internally obtain
association/epoch/nonce/status and raw geometry from the selected primitive;
ACL2 derives occupied bytes. The scalar observation arguments here are an
internal projection after that derivation. Automatic collection never resets A.
Mismatch, deferred collection, impossible occupancy, overflow or uncertainty
retains accounting and requires recovery. A valid observation lacking ordinary
headroom keeps draining and retains its completed nonce, preventing a repeated
collection loop. A breached promised collection reserve is recovery, not an
ordinary connection refusal.

The native barrier, genuine installation producer, source tariffs, selected
collector observation conversion, shared nonce issuance, and once-only turn
receipt joins remain open. No live GC or daemon activation is implied by the
internal source proof. Root owns those composition boundaries.

## Executable scenario

`tests/acl2/allocation-epoch-tests.lisp` uses an explicitly synthetic internal
installation. It exercises prepaid entry/body, refused body with retained gate,
once-only turn settlement, active-worker collection refusal, collection
prepayment/nonce, matched reset with nonzero suffix, insufficient post-collection
capacity, replay refusal, uncertain/deferred/stale observations, immediate-domain
exhaustion and cleanup headroom. Literal positive and hypothesis-removal teeth
cover entry/body/turn/reset/footprint preservation; corrupted-state cases are
marked separately and evaluated as total logical functions outside executable
guards. These fixtures establish no real runtime installation.
