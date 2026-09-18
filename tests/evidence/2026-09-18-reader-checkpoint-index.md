# Reader guards, checkpoint, index and BP ingress — 2026-09-18

This follow-on batch adds logical checkpoint capture/suffix restore, a derived
group/number index, a legacy BP article admission path, and the remaining NNTP
and article-field base guards. It follows the frozen
[75-root store checkpoint](2026-09-18-composed-store.md).

The initial 12-root invocation passed ten roots and rejected an incomplete copy
of the BP ingress book with a reader EOF. Its dependent test also failed. The
exact frozen ingress source was then copied with its supplied digest checked;
both ingress roots passed a separate corrected run. The
[record](2026-09-18-reader-checkpoint-index.json) retains both manifests and does
not call the initial aggregate invocation successful. The other ten roots were
unchanged. All runs used ACL2 8.7 / SBCL 2.6.8 without trust facilities.

- **Checkpoint:** captured prefix node plus actual suffix replay equals full
  replay, including consumed allocator gaps and final-frontier normalization,
  under the executable admissible-split hypotheses. Restore has no prefix input.
- **Index:** independently stated soundness/completeness over source memberships,
  rebuilt range-query correspondence, and malformed public-input refusal. This
  is a derived list materialization; no performance improvement is claimed.
- **Guards:** all 115 NNTP and 30 semantic-field functions are guard verified.
  A source audit found the 139 existing logical bodies unchanged under MBE logic
  projection, with six new executable helpers. The existing 17 base graphs now
  cover 678 functions; the new index book separately verifies 20 functions.
  NNTP uses one explicit EC-CALL fallback for total wildcard behavior. The host
  remains an interpreted ACL2 bridge; this is not a claim of all-raw execution.
- **Ingress model:** exact legacy article bytes pass through the actual article
  parser, semantic fields, configured group mapping and composed store. Tests
  cover duplicate refusal, recovered binding, malformed input and mismatched
  policy/receipt-eligibility context. Eligibility is not an emitted receipt.

After the guard changes, 17 socket/partition tests passed, as did independent
Python 3.9.6 `nntplib` traffic against a reopened store. The unchanged storage
suite was already checked in the preceding 67-test batch.

Physical checkpoint encoding/publication/selection, host index adoption,
complete RFC injection, signed provenance, and actual BP workflow/receipt
composition remain separate work. The broader PRF-008/010 targets are in progress.
