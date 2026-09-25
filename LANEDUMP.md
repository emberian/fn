# LANEDUMP k0-rest (PKT-080, then the rest of PKT-086), from dev 534a68d3

Registry: PRF-041 extended (PRF-105 not used). Record:
planning/evidence/k0-rest-2026-09-25.md.

## Summary

- 2a61305f PKT-080: the coverage of fn-bs-k0-coveredp is generic over the
  :root name (fn-bs-k0s-root-rename-pendingp, was -marker-pendingp; the
  marker is its instance). The :rename arm admits any :root name but the
  frontier, and onto config.json only from a fenced, allocated inode passing
  fn-bs-config-okp. New books/byte-store-k0-step-bridge-root:
  fn-bs-k0-state-checkpoint-cuts-relation-by-step,
  fn-bs-k0-profile-cuts-relation-by-step and the any-outcome step theorems
  at their pairs. Farm run-20260925T100549Z-fdd9 passed (manifest
  certify-20260925T100619Z-3650007).
- eb3ff4f9 PKT-086: books/byte-store-k0-authority-error,
  fn-bs-k0a-authority-fsync-error-preserves-relation. It covers the
  :root/:transactions barriers' error outcomes (the K7 pair-11 EIO for any
  related state, and root EIO over a pending frontier rename) as a new
  :fsync-dir arm. Farm run-20260925T101716Z-6446 passed (manifest
  certify-20260925T101807Z-3786953). Every book is under 10 s in runs 2 and 3.
- Registry: PRF-041 events and notes; the renamed
  fn-bs-k0m-root-rename-crash-is-a-resolution-crash. Backlog PKT-080 is
  ticked and PKT-086 narrowed. make check: only the stale ledger remains.

## Open (named)

- :mkdir / :link-eexist (needs a pre-init relation).
- The recovery window (fn-bs-replay-matches-scan per step, P-RECOVER).
- The in-process re-recovery at host/native/admin.lisp:107 (depends on the
  recovery window).
- The marker book was 10.4 s in run 1 under load (6.3 s of it an include)
  and was not remeasured.
