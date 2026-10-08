# Native event split — implementation in progress
The certified bulk START is a logical checkpoint, not the native drain boundary.
`fnn-owner-drain-one` takes one submission before `fnn-log-reserve` and
`fnn-log-publish`; a duplicate/refusal can contribute a deferred member without
any record. The same dispatcher must express those intermediate states.

## Required arms
- `:begin :current` / `:begin :next`: capture the reader view before the drain, enter `:drain`,
  clear that job's member list. No kernel append yet. The current START drops
  any empty idle captures first (the already-grounded preservation repair).
- `:reserve which txid`: existing consume-to at the owner's reservation. A
  refusal can consume an identity without adding a log record.
- `:take which record txid`: existing pipeline take with profile preflight;
  output its verdict and entry length. On :taken, advance history/count and
  the corresponding OCVM working/batch count. On :full, consume no record.
- `:member which outcome`: retain this dependent reply until its barrier.
  Immediate, record-independent refusals retain the existing OCS discipline.
- `:seal which`: close the drained job; publish STARTED/NEXT-STARTED only
  here. An empty job cancels its capture. A job with members but no records
  still carries its dependency on the earlier durable prefix.
- `:append-issue :next`: after next intents and extent readiness, return the
  write plan BEFORE physical append, freeze B and enter `:writing`. Admit
  only after the current append's receipt, including after its fence returned.
- `:io which word`: receipt of one actual effect. Next :writing receipt
  advances to :fence; it does not produce the write plan after the write.
- `:collect`: ACK/release only current's durable prefix; clear the released
  current member list so a subsequent next-append failure cannot release it
  again. Native time-bars/generation custody still apply.
- `:advance`: reader view and next promotion after completion effects. Wait
  while next is :drain/:writing. Promotion depends on an open JOB, not B>0.

Each exported entry calls its literal dispatcher arm; its equation is
unconditional and named -by-definition. The old bulk convenience, if retained
for witnesses, must be a fold of these arms, never a second algorithm.

## Invariant extension (no weakening of durability or failure guarantees)
- Current :drain: OCS idle, KS ready/fenced, D=C, no in-flight kernel records;
  OCVM A counts the open kernel batch, B=0, next idle; reader capture stays C.
- Other current phases retain the committed/inflight/batch partition already
  proved. Current A may be zero for a deferred duplicate/refusal-only job.
- Next :drain has an unpublished OCP open flag. Sealing publishes it even
  when B=0. `open-next` follows the job phase, not positivity of B.
- Behind is true exactly for a nonempty frozen next batch (:writing/:fence).
- Beginning/cancelling a drain cannot fabricate a fence or acknowledge a
  record. Actual gate exclusion spans the START quantum's intermediate arms.
- The existing fn-ocp/OCS admission and complete-after-barrier theorems stand.
  Extend linkedp's reachable phases and prove every new arm preserves it;
  reveals remains the corollary, not a premise or transition guard.

## Physical ordering and native state
- Reserve room for the current append plus one OMAX-bounded next append at
  the current seal. Perform any extent extension in current's off-owner
  :extend phase. Next's write waits for current's append receipt, so it never
  writes into an extent whose extension is still in flight. No extra next
  fdatasync just to extend behind the current fdatasync.
- A barrier certifies its issue-time prefix only. Appended B is frozen, never
  added to that acknowledged prefix merely because the fdatasync returns.
- Existing fn-lgk-relp requires zeros after FRONTIER and exactly one pending
  write. It cannot describe two writes or conservatively undercounted durable
  B. Add a prefix-barrier/multi-write relation, preserving the existing one
  and reusing fn-lgu's safe durable-prefix/crash lemmas.
- Native state must install projections of dispatcher outputs. Existing
  OTM's OCP component and OCVM/actual view capture must be connected, not
  independently stepped alongside an observational X. Preserve disk/clock,
  held submission, time-bars generation, and buffer custody fields.
- Shared mutation synchronization must cover scheduler pick/observation as
  well as kernel receipt and owner quanta. Do not introduce Gate/K inversions
  or treat an unsynchronized snapshot of those fields as a composed state.

## Full/inline deletion still owed
A :full result at fnn-log-take occurs after preparation/reservation. It must
retain and resume that exact prepared candidate across off-owner batch work,
or be prevented by a proved preflight before consuming the submission.
Dropping/refusing an already admitted candidate or guessing a byte bound is
not a replacement. An empty-batch :full needs an explicit unsupported-profile
refusal before publication; profile consistency must cover one legal record.
Bound/BP callers likewise need a commit-before-submit continuation across
quanta. Delete fnn-owner-commit-queued-locked and fnn-log-take's wait/flush
fallback together, closing LOCK-R2-COMMIT-INLINE-LOG-IO without relaxing R2.
