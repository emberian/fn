# LANEDUMP reader-surface (dev lane, PRF-110)

Brief: build/coordinator/queue/reader-surface.txt. Base dev 00b0a846.
Record: planning/evidence/reader-surface-2026-09-25.md.

## Done (certified; manifests certify-20260925T102606Z-3884875 + certify-20260925T110938Z-144928)
- PKT-110: CAPABILITIES lists XPAT (RFC 3977 s3.3.3 private label). Rule kept:
  RFC 2980 s2.9 joins extra arguments into ONE pattern (INN does the same);
  the OR is the wildmat comma; case-sensitive per RFC 3977 s4.2. The spike's
  "second argument does not OR" was a misreading of s2.9, not a defect.
  books/nntp-xpat.lisp: fn-nntp-step-pinned-xpat-is-the-xpat-response,
  fn-nntp-xpat-alternation-is-or, fn-auth-capability-lines-advertise-xpat;
  teeth tests/acl2/nntp-xpat-tests.lisp. fn_web.py /search sends the reader's
  wildmat verbatim (no client-side pattern building).
- PKT-091: fn-sbud-post-boundary-refusal renders the POST boundary refusal;
  host/native/io.lisp fnn-validate-post-boundary prints its octets (keystone
  fn-sbud-post-boundary-refusal-is-nil-exactly-when-admitted).
- Step 3: search moved to the node; unread already from LIST COUNTS; threading
  not moved (no node verb, client presentation) -- table in the record.
- Registry: PRF-110, NNT-014 (new), STO-005 += PRF-110, SCN-052, spec NNT-014.
- tin phase + four V0-CLIENT-TIN-* rows written in tools/v0_matrix.py
  (tools/tin_drive.sh, tools/nntp_wire_log.py).

## Blocked / open
- ALL native work: no dev image builds (books/poster-bytes-buffer red since
  D32; lane pbb-d32). hbox tree /tank/fn/scratch/reader-surface (img.sh).
  Open: image observation of XPAT label + refusal text; PKT-111 matrix run
  (--publish-current; add control.cancel to node A's store for the cancel
  row); PKT-158 INN supplied-Path (--inn); PKT-074 D23 chain
  (tests.test_native_hybrid_author -k d23; after peer-carriage lands the
  relay needs `peer budget`).
- make check: ledger stale (generated, deputy's) and the four tin rows
  missing from planning/v0-matrix.json until a matrix run publishes it.
- Dev-red, not caused here: store-reclaim(-tests), poster-bytes-buffer,
  octets-stobj-tests.
- Not lifted to fn-served-step (subject theorem is at fn-nntp-step-pinned).
- tin on hbox PATH: ~/.cargo/bin/tin -> spike build.
