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
native collector composition and once-only turn
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

## Internal native collector join (PRF-1158, PRF-1159)

Installation cell 1 is association6:
`(:allocation-epoch-association runtime-coordinate profile-coordinate pool-coordinate page-octets dynamic-reservation)`.
The runtime coordinate binds selected executable, image and source units;
profile and SAMEpool identities remain immutable. This shape predicate does
not confer installation authority. No pool field is added by this refinement.

`fn-aec-pool-collect-observed-internal(requested-nonce, observed-association,
observed-epoch, observed-nonce, status, pages, page-octets, reservation, pool)`
returns `(word, pool)`. The nonce-only native wrapper obtains these scalar
observations from its installed, preallocated primitive carrier. ACL2 checks
the installed association and geometry; it checks pages against reservation
divided by page size before multiplying. The installed reservation is already
bounded by the immediate domain. Thus rejected observations cannot construct
an oversized product, and accepted occupied bytes match installed geometry.
The checked dynamic prefix is not total process residency; other spaces and
external resources belong to their separately qualified baseline/envelope.

`fn-aec-pool-collection-request-internal(pool)` returns
`(word, association, epoch, nonce, pool)`. It prepays Qcollect and retains the
collecting intent before invoking the actual existing `fn-prs-issue` with the
fixed identity demand `(0 0 0 0 1)`. The actual ledger supplies baseline, budget,
charged resources and NEXT. The committed ledger contains NEXT+1; the returned
and retained collection nonce is the exact old NEXT. Existing binding roots
remain unchanged. No new counter, demand parameter or binding-list allocation
is introduced. Constant-size resource scalar checks prevent overflow in the
existing issuer's arithmetic. Refused issuance retains Qcollect and enters
recovery; a repeated request in recovery remains `:recovery-required`.

Collector identity rescue remains an explicit installation/composition
obligation. This code does not fabricate rescue capacity: exhausted identities
produce recovery after the retained prepaid intent. A completed collector nonce
stays spent in shared PRS accounting.

A gate-owned turn whose body was not prepaid when draining begins yields with
unchanged A, then consumes its already prepaid no-effect epilogue. A body-owned
turn continues its prepaid closure while draining, without another entry/body
call. The worker-slot receipt integration owns those distinctions.

Additional exact scenarios are in `allocation-epoch-observation-tests.lisp`
and `allocation-epoch-collection-request-tests.lisp`: actual same-pool raw
completion, installed geometry mismatch, stale request/epoch/nonce, deferred
collector, reservation overflow, shared nonce issuance and replay, worker drain,
identity exhaustion, and the draining gate-owned yield. Native process-wide
barrier, genuine installation/source tariffs and once-only turn producer remain
separate joins; these tests use explicitly synthetic producer fixtures.
