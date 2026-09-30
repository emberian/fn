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

Current loader metadata availability also gates token readout, every observe and
final installation. Repeating decoder finish without an active load clears
metadata without a new generation; the old token then refuses with unchanged
STATE. Every new decode entry advances the generation. No graph equality is
used to establish either fence. The exact source and recording scope are in
`planning/evidence/recovery-source-live-metadata-2026-09-30/coordinate.json`.

The sized observer calls the actual public observation once, then records fixed-six carry metadata only against its exact `:counted` successor and issued epoch/loader generation. The final installer reads `fn-owner-recovery-source-sized-readout` internally using its frozen token. Native must never supply final fields or refresh a stale token. A legitimate seed observation before the suffix loop can advance the issuer serial without replay, including an empty suffix. Unavailable metadata leaves replay usable but canonical readiness unavailable. Source and recording evidence is `planning/evidence/recovery-sized-observer-source-2026-09-30/coordinate.json`.

The live suffix fold begins at zero, while the issued checkpoint frontier may be positive. The initial `fn-owner-recovery-source-observe-seed-sized` derives the retained issuer frontier in ACL2, requires serial0 and exact prefix count, and delegates to the same sized observer. It changes no suffix fold. The exact native suffix function then uses one produced SSR decision and one lexical-token observation per chunk. Final `fn-owner-recovery-source-install-sized` reads pending ORIGINAL fields internally; its production source admission and full native/physical qualification remain open.

The resident suffix now obtains aligned snapshot child carries from the same
chunk parser that returns its wire events. `fn-srss-decode` preserves the
complete old `fn-srs-decode` result, including failures, and its successful
side result corresponds to those exact rows. `fnn-recover-record-chunks-sized`
retains the existing chunk schedule; `fnn-recover-suffix-intern` forwards the
returned carries unchanged to the one actual sized intern worker. The old
full-replay decoder remains separate. There is no second parse or whole-row
resummary in the host. The source component and native forwarding recordings
are in `planning/evidence/snapshot-suffix-native-join-2026-09-30/`; recording
core/STATE doubles do not establish loader provenance, installed CP7/pool/row
correspondence, INITIAL adequacy or native image qualification.
