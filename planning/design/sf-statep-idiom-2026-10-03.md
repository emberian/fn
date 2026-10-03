# Open design question for Astra (Codex returns Oct 8): the "mbe statep" step idiom

Measured (COST-GATE, image set 45e05c7fd, guards on): POST cost is O(store) per POST: fn-owner-io (2 calls per POST)
92 ms / 11.8 MB at N=1000, exponent 1.0, 99.9% its guard fn-sn-statep (fn-sf-record-listp 63 ms, success check 24 ms,
fn-node-statep 3.5 ms); extrapolated ~9 s / 1.2 GB per call at 100k.

Why the guard cannot simply be narrowed (STAGE-5B): every fn-sf step (store-files.lisp:630-1079: fn-sf-start-frontier,
-frontier-file-result, -frontier-replace-result, -frontier-dir-result, -record-file-result, -record-link-result,
-record-dir-result, -recovery-barrier) is written (if (mbe :logic (fn-sf-statep s) :exec t) STEP s): logically the
identity on an invalid state, executably skipping the test. The mbe obligation guard => (fn-sf-statep s) forces the
whole-log check into every guard up the chain (fn-sn-file-step, fn-rcon-sn-io, fn-rcon-ocfg-io, fn-olr-ocfg-*,
fn-owner-io). The idiom IS the whole-state revalidation AGENTS.md forbids, pushed down a layer.

Options: (1) redefine the fn-sf step family as unconditional steps with shape guards, restating the twin equalities
(fn-rcon-ocfg-io-is-ocfg-step etc.) under (fn-sn-statep s); fan-in is store-files' whole closure. (2) raw dispatch over
the carried relation (STAGE-5B's plan; needs the carrier move and tiers B/C). Interim: a single-pass mbe :exec twin of
fn-sf-record-listp (~3x constant factor), STAGE-5B after tier A.
Question: is (1) the better long-run design for this family (the idiom recurs elsewhere: find every instance), or is
(2) sufficient?
