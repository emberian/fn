# RELEASE producer and recovery consumer

The source-only consumer packet in `tests/recovery-release-dispatch-support.lisp`
requires an actual authenticated selected journal at its RELEASE cursor. It
drives `fn2-turn` and the existing device adapter; it never sets auth or stage13,
nor invokes the worker, harvest hook, observer or pending decrement directly.
Its positive result requires issue11, pending12, loaded13 with pending0 and
current authorization, then actual checker progress. Refusal controls change
the issued completion generation/count or selected source generation and retain
the original journal bytes, physical lease, cursor, filled/count and identity.

The connected constructor in `tests/recovery-release-connected-unit.lisp`
creates the real image, retires an actual allocation for the frozen map,
publishes the actual checkpoint, stages/submits/polls RELEASE, crashes, and
drives actual selected boot to the observed release-begin stage11. It then
copies the descriptor sector from the same simulator image into the existing
device adapter view. Four independent full-history assert-events require the
positive packet and wrong-generation, short-completion and stale-source
refusals. A missing antecedent returns failure. This source depends on the
new authenticated submission implementation; the submit/poll API was frozen
with its owner while implementation was in progress. No Lisp execution or
admission has run, and these assertions are not claimed as passing witnesses.

Actual producer work is mandatory, not deferred: capacity owner owns the
source-bound `pack-staged` to B journal admission, persisted lifecycle dispatch
and ambiguity retention. Current generic `fn2-commit-admit-txn` rejects RELEASE;
its whitelist must not be expanded as an authority shortcut. Allocation-codec
owner owns the consumer packet and its generated disk/history setup; restore
owner supplies the unchanged actual image/create/publication/crash helper
extraction from checkpoint-cold-path. Parent owns dispatch and orchestration.
The test-only maintenance entry enters the parked catalog actor and makes no
automatic scheduler activation claim. A codec-generated disk history is not
an actual production crash-run witness.

The public recovery release checker remains blocked at private stage8. Prefix
obligation reconstruction, archived installation-J authentication and actual
final identity/protection/epoch ownership joins still gate physical reuse.
Neither this packet nor producer submission grants FREE permission.
