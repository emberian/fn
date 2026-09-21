# Recovery composition review disposition

Claude Code 2.1.278, requested model `sonnet`, ran read-only in tmux
`fn-w29-recovery-review` against detached source `31f49d78`. The process exited
zero. The [prompt](evidence/recovery-review-2026-09-21/prompt.txt) and
[response](evidence/recovery-review-2026-09-21/claude-review.txt) are preserved.
The review is source analysis, not certification or runtime evidence.

* **Identity-only recovery failure: confirmed and repaired.** The ordinary
  node replay can succeed on a self-bound kind-4 event without its historical
  enrollment, while identity replay fails. The old `fn-sn-recover` then left
  files `:recovering` and kept the seed node, letting observed open succeed
  with no live articles. The repair makes either replay failure a file-phase
  fault and preserves the observed history. The composed negative witness
  separately establishes structural validity, successful ordinary replay,
  failed identity replay, failed observed open, and inability to complete
  recovery barriers. Existing successful mixed-history traces also execute.
* **Whole-history prepare replay: partly confirmed.** The review missed the
  ordinary served article path's existing `fn-opc-prepare` correspondence.
  Identity and retention preparation still call `fn-sf-prepare-record` and
  replay retained history. Removing those scans needs an incremental maintained
  relation and an actual-caller correspondence, currently open under PRF-050.
* **Journal cursor congruence: confirmed proof obligation.** The maintained
  sequence relation must account for `:completing`/`:completed`, where durable
  history includes the event but finish has not advanced the cursor. It must
  also permit burned allocator reservations. This is assigned under PRF-050;
  source inspection and passing traces do not discharge it.

Validation of the recovery repair used ACL2 8.7 / SBCL 2.6.8, a fresh process
with a 2 GiB heap, and `ld` of
`tests/acl2/store-identity-traces-tests.lisp`, followed by
`FN-SIT-LD-COMPLETE`. A 120-second supervisor bounded execution. All assertions
reached the final marker with no ACL2 failure. The
[log](evidence/recovery-review-2026-09-21/source-evaluation.log) records stale
and missing dependency certificate warnings: this is source evaluation,
**not fresh certification or guard verification**. The current integrated
closure and native corrupted-history startup test remain required.
