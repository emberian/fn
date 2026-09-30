# Cold recovery source authority

PRF-1149 and SCN-1054 cover the actual cold issuer and final install. This
work is in progress; the installed canonical producer and initial funding
remain unavailable until their own actual joins complete.

A cold issuer is not a live `source4` capture. The successful loader retains
its original checked plan, parsed checkpoint root, actual R-run byte region
and child 1, F log position/frontier and carried prefix count. The region
is provenance of that successful decode; the loader releases its octet buffer,
so this descriptor grants no borrowed byte range or physical reread lease. Loader replacement
increments a nonreused generation. The issuer reads these from ACL2 STATE,
requires canonical reset/unavailable state, and binds a monotone recovery
ticket to the current process epoch and loader generation. No host argument
stands for a verified root, region or final event count.

The typed `(:recovery-source ticket process-epoch ack-serial)` token belongs
to a nine-cell cursor. Each actual same-pass SSR completion supplies its
ORIGINAL context and txid fold. The context's maintained next count advances
the cursor, and the acknowledgment serial advances even for an empty funded
chunk. Repeated or stale tokens, reset epochs and replaced loader generations
cannot advance it. The existing byte/parser/intern/update resource reservation
must occur before allocation; source authority grants no memory, disk or IDs.

The final installer reads count, frontier and CP from the actual completed
recovery Store, checks them against the carried producer, and seals a new
live `source4`. Canonical state is installed in that same action with the
actual fullctx6 field carries, CP7 carries, canonical pool and physical row
count. No serving or live query capture occurs before installation. A failure
leaves canonical state unavailable and does not borrow an old owner's source.

The initial definitions and metadata guards are bounded. Their general
same-pass provenance/refinement, actual loader/SSR caller wiring, namespace
representability, admission before every allocation and native restart
trajectory are still open. Recognition of a descriptor shape proves no disk
or cryptographic integrity; authenticity must follow from the actual loader.

The actual start/observe entry points are in `host/recovery-source-host.lisp`,
which includes the loader metadata implementation directly. The final Store
installer is in `host/recovery-source-install-host.lisp`; that dependency split
preserves its body and does not narrow the whole recovery/install obligation.

The actual `fnn-recover` entry performs `fnn-payload-startup-reset :recovery`
before nursery/load/SSR. In the allowed quiescent interval, the actual arena
reset and canonical epoch reset share one lifecycle exclusion. Serving or
draining refuses before mutable STATE or Store mutation. The final installer
preserves that issued epoch and must not reset it after parsing. Literal
recording barrier tests cover both reset-first and start/capture-first schedules,
plus actual entry ordering; their STATE/nursery/loader adapters are explicit
doubles. Exact source admission is in
`planning/evidence/recovery-reset-source-2026-09-30/coordinate.json`.
