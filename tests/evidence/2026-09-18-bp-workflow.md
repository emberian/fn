# Sender workflow and portable laboratory ADUs

Status: scoped integrated certification and host checks passed on 2026-09-18.
[Exact source hashes, versions, invocations and manifests](2026-09-18-bp-workflow.json)
record revision `b4b3444` plus the adopted changes. ACL2 8.7 on SBCL 2.6.8
certified the two ADU roots and three workflow/record roots. The 33 journal,
crash, fault, boundary, live-workflow and existing ingress host tests passed in
6.527 seconds. These are scoped batches, not a new full-suite checkpoint.

The [ADU codec](../../specs/bp-adu.md) proves typed request/receipt round trips
and exact accepted-input canonicality. It preserves the article as opaque exact
octets and carries portable work/subject/policy/incarnation/terms context. Golden
and malformed vectors exercise version, kind, field count, truncation, trailing
data and size bounds. It remains an experimental profile, separate from D01/D09.

The [sender journal adapter](../../specs/bp-workflow-host.md) now executes actual
ACL2 workflow decisions. The live test commits a real Store article, enqueues
matching work, durably records attempt intent and outcome before its BPA callback,
expires/reopens the attempt, and recovers a later unresolved intent. Wrong
subjects and stale pairs leave durable records unchanged; ordinary completion
after a recovered fence is refused. Submit permission is exact and consumed once.

Integration repairs closed three concrete gaps: permanent transaction-pair
reservation at preparation; ACL2 preflight before record publication; and live
completion gating after restart. Boundary tests also ensure enum/integer checks
precede fixed-form Lisp construction. The base pending-state recognizer was
strengthened to require an actual attempt for attempt-kind pending work, closing
a malformed-state recovery counterexample. Earlier source digests are superseded
for this batch, not relabeled as passing the new claims.

The live workflow test records a BPA callback rather than sending a real bundle.
Actual BP transport and receiver acceptance have separate evidence. Receiver
request persistence, receipt regeneration and the actual return BP path remain
active integration work. General workflow trace invariants are another artifact.
The host framing/hash/UTF-8 and filesystem operations remain explicit assumptions;
these results establish no authenticated remote receipt, physical power-loss
guarantee, or full M4 completion.

A subsequent full Python suite at `67c320f` passed all **108 tests** in
105.023 seconds. Recorded implementation source hashes still matched. This is
the host regression suite, not a new all-roots ACL2 certification.
