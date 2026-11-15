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
new authenticated submission implementation, composed from capacity owner
`d1fd21f26` and `121be600f`. Actual image executor startup configures its
protected singleton workspace before foreground; the fixture checks the
maintained group identity and never substitutes a configured-count flag.
No Lisp execution or
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

The narrower LIVE root is `tests/release-allocation-live-unit.lisp`. It calls
the same extracted `fn2-rrc-producer` once and stops before process death. Its
strict assertion requires actual persisted typed dispatch and accepted poll,
the exact three stamped evidence obligations, returned or retired workspace
ownership, and the unchanged RETIRE_PENDING target. A second real poll must
retain the same persisted batch/event and evidence. It does not force the
generation-retirement branch; that separate capacity fixture has its stated
synthetic authorization scope. The four recovery assertions and every original
producer binding are preserved by the AST extraction recipe and its controls.

This narrows runtime, not the production compilation world. Actual image
creation and the executor import the recovery/assembly core even without
running cold restart. The frozen static local include graph contains 440
files, with no missing local include; system books and macro-generated
dependencies are outside this count. Compared with root `5c36665eb`, 194 source
blobs match, 50 differ and 196 are new. All ten listed producer/coordinator/
dispatcher runtime books match coherent cold `608ad5b50` byte for byte.
`tools/fixtures/release_live_closure.json` records those exact source blobs;
it is not an admission result or certificate/cache key. Retired-return fix
`7a8b3a1bb` is composed. No Lisp assertion, guard or runtime gate has run.
