# Deleted article payload retirement

Source investigation at `04508c855ed409fd426ce6297097ef1d445693b6`; no
runtime or proof qualification, and no FREE activation.

## Actual authority and entry

The next producer must obtain an accepted, version-bound last-claim withdrawal
from the journal/C publication path. Allocation owner `EVENT`, a withdrawn
visibility bit, an empty physical-I/O pin count, or checkpoint-edge withdrawal
is insufficient. The actual ordinary retirement coordinator remains the only
writer of a retirement member and installs RETIRE_PENDING only from persisted
settlement.

The proposed C maintenance actor owns a resumable article source, the copied
full stored-source and location commitment, the authenticated physical payload
walk, one pending allocation identity, and its exact retirement batch/event.
Its source operation takes its retained actor identity, not a caller-supplied
article, allocation list, cut, event, or readiness assertion. A successful
withdrawal publication or a real protection/source transition schedules it;
ordinary allocator ownership is not a garbage queue.

A durable tombstone may retain historical location commitments for the retirement
walk without asserting that those historical references are live payload claims.
That distinction must be implemented by both actual readers and checkpoint
semantic walkers before it can support progress. The actor must preserve the
source across refused admission and retain uncertain submission until recovery.
Each step handles one real source entry, manifest entry, allocation or settlement;
no served step revalidates the whole store.

## Concrete current source

| Source | Observed behavior | Consequence |
| --- | --- | --- |
| `ordered.lisp`, schema2 | Fields0..12 are article,birth,state,version,source,bytes,lines,location-unit,location-epoch,location-allocation,location-kind,stored-source,location-hashes. | Fields11/12 are distinct commitments and must travel with the full placement tuple. |
| `txn.lisp`, `fn2-txn-put-article` | The served append writes LIVE, version1, article/birth from the newly assigned event. | A physical allocation owned by that event is not evidence that a particular article has been deleted. |
| `machines-c-successor.lisp`, `fn2-succ-reads-key` | Latest-schema insert does not require the unique/union old-key lookup. | Generic latest publication is not an accepted compare/version withdrawal contract. |
| `machines-c-bind.lisp`, `fn2-succ-publish` | Publishing the actual B batch changes bound transactions and private overlays to published and advances the C frontier. | Any retirement source must bind to this actual persisted/publication chain, not a supplied event number. |
| `format-events.lisp` | Withdrawal has article, authorization Ref and outcome; keyed mutation has expected-prior-version and new-value Ref. | A version-bound withdrawal requires an actual producer/consumer joining these subjects. No such served withdrawal producer/replay case was found in this source. |
| `cursor.lisp`, `art-lookup`/`art-bind` | Location scalars and field12 are copied, then the C read row is released before BODY block issuance. The lookup does not inspect article-state. | Neither pin0 nor a withdrawn bit establishes no active or future reader. |
| `cursor-kind.lisp` | The retained BODY lease is a storage window; the declared observer is read-result. | The current cursor declaration does not acquire a payload promised-read lifetime across I/O gaps. |
| `checkpoint-cbase-*` | Physical catalog promises cover the retained full checkpoint closure. | They can protect old physical catalog payloads through query gaps, but cannot stand in for a fresh resident article never checkpointed. |
| `retirement-coordinator.lisp` | Submit uses the actual selected batch and intent barrier; checkpoint-active admission is refused. Poll distinguishes pending/refused/accepted/uncertain. | A checkpoint-held source cannot simply submit an ordinary retirement while retaining its C token. |

The current article schema also cannot use an existing version-only dependency:
`fn2-succ-stage-depend` requires every entry field, and the resolve path rejects
non-scalar source values for dependencies. Article digests and location-hashes
make that a real refusal. A new selected-scalar/version dependency must extend
the generator without changing full-dependency semantics, or the withdrawal
must use an actual held-source atomic stage join. The existing journal packer
sets expected-prior-version0 for its new inserts; that value is not a deletion
version witness.

D13 reports a preserved whole-BODY source-observer provider, but explicitly says
that provider was not composed into current root099/045. It is not retirement
authority until its actual request-start/final-release hooks and writer drain
are integrated. Release owner reports native payload proof49a is authenticated
USE/classification only; it does not establish query absence, publication or
retirement eligibility.

## Composition and ownership

This lane owns new deleted-payload source/continuation/actor books after the
source contract is reviewed. It reuses the existing physical verifier and
ordinary durable submit/poll chain; it does not create a second retirement
writer. Root owns composition of the actual whole-BODY reader lifetime and
withdrawal authority prerequisites. Release owner owns checkpoint debt/disposal
and cold-edge discharge. D13 owns actual C live adoption/catalog lifetimes.

Before a submit, the actor must have exact current article/version/withdrawal
and stored-location identity, authenticated membership of the allocation in that
payload, and actual clearance of selectable banks, archive/replay, C-base,
queries, custody and other payload obligations. Same-call preflight/submit must
establish the existing retirement intent before yielding. Releasing a held C
source to permit B admission must also exclude resurrection/new claims across
that asynchronous interval; no caller assertion substitutes for this join.

## Counterexample controls required

- Another extent with the same allocation owner EVENT is not this payload.
- LIVE, a newer version, or a withdrawn row without accepted withdrawal evidence
  refuses without submitting.
- A changed stored-source11, vector12, manifest entry or epoch/allocation refuses.
- An old bank, archive, physical C-base, custody or promised query holder vetoes.
- A cursor that copied the location with no I/O pending still blocks retirement
  until its actual object/source lifetime ends.
- The last protection edge can disappear before its catalog/hold becomes
  available; the final availability transition must issue the real dirty wake.
- Exact non-submission/refusal can release only evidenced transient state;
  ambiguous persistence retains intent and requires recovery.
- No accepted submission permits FREE until the separate persisted release and
  backend/epoch exclusion protocol succeeds.
