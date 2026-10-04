# Recheck of the 44 `.spw` horse findings at origin/dev, 2026-10-04

Lane `spw-audits`. Base `origin/dev` 32b2fa366. Source: `.spw/audits/{entries,exits,bounds,consistency}/`, written
on 10-03 by four read-only "horse" lanes (44 claimed defects: entries 13, exits 16, bounds 6, consistency 9).
Every cited site was re-read at 32b2fa366 (full current definition, not the finding's text). The horse commit
shas were all rewritten on integration; the dev sha is given (the horse sha in brackets where it differs).
Method limit: source reading plus a few cheap `python3.12 -m unittest tests.test_native_*` and `sbcl --script`
runs. No ACL2, no image, no hbox. FIXED means the code at HEAD closes the described scenario; it is not a
certificate claim.

## Totals

| audit | claimed | FIXED | STILL-PRESENT | REFUTED | UNCLEAR |
|---|---|---|---|---|---|
| entries | 13 | 13 | 0 | 0 | 0 |
| exits | 16 | 16 | 0 | 0 | 0 |
| bounds | 6 | 4 | 2 | 0 | 0 |
| consistency | 9 | 9 | 0 | 0 | 0 |
| **all** | **44** | **42** | **2** | **0** | **0** |

Both STILL-PRESENT findings (B007, B010) are already repair-ledger items (S046, S013). Nothing was refuted:
the 10-03 "17 confirmed / 27 plausible" split no longer matters, because the wave that landed since fixed
the plausible ones too. What remains is residual work around the fixes (next section), one regression of the
fixes' own evidence (R1), and the D27 list (last section).

## Residuals the fixes left, and one regression of their evidence

These are not the 44 findings coming back; they are named residuals or same-pattern sites found while
re-reading. Each is filed as a ledger item (owner unassigned, source `spw-recheck-2026-10-04`).

| id | where (HEAD) | what | item |
|---|---|---|---|
| R1 | `tests/native_feed_cleanup_source.lisp` (route-table half), `native_application_cleanup_source`, `native_arena_return_source`, `native_bp_lock_return_source`, `native_immutable_close_source`, `native_command_cleanup_source-mock`, `native_export_terminal_source-mock`, `native_node_secret_return_source-mock`, `native_bp_profile_return_source-mock`; `native_rotation_cleanup_source` no longer exists | The EX "actual-source" witnesses exit 1 at HEAD. cd4673a17 gave `fnn-unwind-cleanups` an escape path (`fnn-escape-cleanup-failed`, io.lisp:557-612) and patched only eight older `*_raw` harnesses with `tests/unwind_cleanups_prelude.lisp`; these fixtures load the real macro by text extraction without it, or still assert that a refusal-class primary always survives a faulting cleanup (changed deliberately). Re-run by this lane: 9 of 13 existing files exit 1; passing: store_cleanup, owner_install_cleanup, checkpoint_cleanup-mock, log_terminal. The fixes are present in source; their witnesses no longer demonstrate them. Six more were renamed `-mock` by f7a1265e8 and back no claim. | SPW-R1 |
| R2 | io.lisp:4400, 4412, 5200, 5379, 5512, 5603, 5694, 5714, 5949, 6590, 6602; anchor.lisp:405; hybrid-control.lisp:298; operator.lisp:1091 | EX12's stated residual ("wider CLI direct unwind cleanup"): offline commands around `fnn-store-close` still use bare `unwind-protect`; a close error during a body error replaces the primary and a refusal is never escalated. | SPW-R2 |
| R3 | bp-node.lisp:1255-1269, bp-app.lisp:399-408 (outer served cleanup); bp-contact.lisp:56, bp.lisp:728, bp.lisp:808, bp-node.lisp:535, bp-node.lisp:585 | EX06/EX10/E011: hand-rolled outer cleanups drop the cleanup condition when a primary exists (exit class is the primary's, no escalation); `fnn-bps-release` can signal from a plain `unwind-protect`, and in bp.lisp:803-808 a Store-close error skips the release. | SPW-R3 |
| R4 | io.lisp:793 `fnn-read-regular-bounded`, used by `fnn-archive-entry` (io.lisp:4900) and stopped-status `config.json` (io.lisp:5763) | E013/E014 residual: opens without O_NONBLOCK, so a FIFO swapped in between the lstat and the open blocks the import (same race class as the fixed MANIFEST and prefix readers). Needs write access to the archive/store directory. | SPW-R4 |
| R5 | owner.lisp:1203, owner.lisp:1244-1250 | EX01 residual: failed-open path swallows a physical close failure with `ignore-errors` (no debt); `fnn-owner-feed-append-locked` closes the journal unguarded before `fnn-indeterminate`, so a close failure replaces the indeterminate. | SPW-R5 |
| R6 | owner.lisp:1548-1655 (install rollback), `fnn-open-live-store` | EX03 residual: rollback is `handler-case ... (error ...)`; a non-ERROR serious condition or a throw during startup bypasses both rollbacks (lock/feeds left open, no retained carrier). Reachable only in-process (tests, re-entry). | SPW-R6 |
| R7 | io.lisp:1289-1291 `fnn-log-writer-stop`; operator-live.lisp:166-170 | EX08 residual: a queued `(:swap . fd)` is dropped with no close and no debt if the writer thread died abnormally; `run-code` escalation of the final settlement is skipped when the run escapes (reachability of the second unverified). The related unbounded `:swap` queue push at io.lisp:1301 is already `r72-F7`. | SPW-R7 |
| R8 | books/owner-credits.lisp:282 `fn-mca-initial`, host/owner-host.lisp:1526 `fn-owner-connection-budget` | S-POOL residual: no live rebase of the article-size credit / connection-held allowance; every change of `max-article-octets` is deferred to restart by `fn-lim-article-decision` (limits-live.lisp:221-227). A missing capability, not a reachable inconsistency; the at-restart answer is the documented behavior. | SPW-R8 |

Residuals noted and deliberately not filed: the EX13 close-debt lists have no cap or clearing (stated by the
audit; admission refuses once one exists, so growth is bounded by concurrent writers); EX09 custody is
in-memory and never reset in-process (stated; conservative until restart); E008's trace-file O_TRUNC before
spool ownership (tcpcl.lisp:823) is `S100`; E009's sibling `fnn-open-lock` (io.lisp:2327) is `S070`; E016's
LISTENING-WEB output failure after both actors spawn closes a listener the web actor may still poll
(startup is failing anyway); EX11 leaves `.bp-*-profile-PID-HEX` staging files after a failed replace.

## Per finding

Fixed by: dev sha (horse sha). Site: where the fix is visible at HEAD.

### Entries (13)

| id | finding | class | fixed by | site at HEAD |
|---|---|---|---|---|
| E001 | redeem password send publishes before local return | FIXED | f3b9d5909 (03228b319) | io.lisp:9601 `(setq stage :password)` before send; loss goes to `fn-redeem-lost` at :9613 |
| E004 | TLS client does not clear the error queue | FIXED | b00f5011b (b026608c0) | tls.lisp:575 `fnn-%err-clear-error` before `fnn-%ssl-connect` |
| E005 | BP receipt journal escapes before the caller retains it | FIXED | d9f4fb052 (00428bac6) | bp-app.lisp:306-327 `returned` flag inside `fnn-unwind-cleanups` |
| E006 | list seal retains payload in resident INNER | FIXED | d4f787b5c (c80d05424) | io.lisp:1899 `fnn-seal-octets` via `fnn-seal-live-buffer` (:1913); only `fn-arena-seal-list` left is a test mutation at owner.lisp:8039 |
| E007 | BP resume reads budget outside cleanup | FIXED | 237f6b776 (3a4444ddf) | bp-node.lisp:492-502; main node :1114 inside the cleanup list |
| E008 | TCPCL trace opened before spool acquisition, outside cleanup | FIXED | 3dddc951f (d82c05dc5) | tcpcl.lisp:846-896, 899-917; residual O_TRUNC is S100 |
| E009 | AUTHINFO lock conflates fstat/flock errors with contention | FIXED | 41576f8b0 (47c1ebc92) | auth-admin.lisp:173-196 (EAGAIN/EACCES only), :512-540; sibling `fnn-open-lock` io.lisp:2327 is S070 |
| E010 | admin query/execute cleanup masks the primary | FIXED | 0d925e637 (c7637e1a7) | admin.lisp:717-765; Store close debt io.lisp:2665-2690 |
| E011 | BP service construction leaks spool lock / lifecycle FD | FIXED | 519d3ea7a (17088f4b0), 1de9d1aef | bp-service.lisp:1256-1393, :93-132; residual R3 |
| E012 | non-Linux publication lock classifies every OS error as locked | FIXED | 0496e98b1 (869cbfc8d), 428c6d78e (334468449) | io.lisp:5003-5047 |
| E013 | import MANIFEST opened blocking, no descriptor check | FIXED | 4ec2b829f (58113202a) | io.lisp:5256-5264; residual R4 |
| E014 | stopped-status prefix reader blocking open | FIXED | 252252cf2 (000ebab7e) | io.lisp:5724-5739; residual R4 |
| E016 | web startup/finish/wake-pipe cleanup | FIXED | 6de37169e (0985ca964) | web-host.lisp:913-926, :215-240, :874-908 |

E015 (wording) is true at HEAD (io.lisp import docstring); E002 (tooling) and E003 (doc) are not defects. The
horse evidence JSONs the findings cite (`planning/evidence/horse-entries-*.json`) are not in the tree.

### Exits (16)

All sixteen repair commits are ancestors of HEAD. Since then dev cd4673a17 made `fnn-unwind-cleanups` escalate
a cleanup failure during a body escape through the exit lattice, so "the primary always wins" is no longer
exactly true (a refusal-class primary under a faulting cleanup is replaced, by design); the contract is a
superset of what the audit described.

| id | finding | class | fixed by | site at HEAD |
|---|---|---|---|---|
| EX01 | feed journal cleanup stranded suffix | FIXED | e60931096 (01e4a5e0b) | owner.lisp:1361-1415; residual R5 |
| EX02 | route-table read skipped Store cleanup | FIXED | d8c94940b (1200bf85d) | bp-service.lisp:1488 |
| EX03 | owner-install rollback / retained carrier | FIXED | d8c94940b, eba984639 (fe5ead1b3) | owner.lisp:1548-1655, :982-1004; residual R6 |
| EX04 | `fnn-store-close` hid log/spare close failure | FIXED | d8c94940b | io.lisp:2665 `fnn-store-close`, :8223/:8235 |
| EX05 | checkpoint cleanup scopes | FIXED | 3ac2059a2 (83e657c2d) | checkpoint.lisp, eight macro scopes |
| EX06 | application journal close debt | FIXED | b630850ca (0a67f8121) | workflow.lisp:17-72; residual R3 |
| EX07 | rotation candidate custody | FIXED | ba60d31f6 (70cdc8624) | io.lisp:8254-8375 |
| EX08 | log swap/close custody | FIXED | 9d9110af5 (92d63fb62) | io.lisp:1091-1316, operator-live.lisp:23-178; residuals R7, r72-F7 |
| EX09 | staged arena callback custody | FIXED | 837bbec5f (db2e4c87a), 5f1b89f83 (a7c0843d7) | io.lisp:7707-7786 |
| EX10 | BP lifecycle/spool release debt | FIXED | 1de9d1aef (e88075c84) | bp-service.lisp:93-131, tcpcl.lisp:228-281; residual R3 |
| EX11 | profile replacement uncertainty at issued rename | FIXED | 0580393b2 (f17880205) | bp-node.lisp:623 |
| EX12 | nine offline command exit scopes | FIXED | ff9c51d4a (2c8b9ea45) | io.lisp, nine scopes; stated residual is R2 |
| EX13 | immutable staging close custody | FIXED | 6c308c97a (7f841f24e) | immutable-publish.lisp, io.lisp:5306-5318 |
| EX14 | mutable staged writers share the return ledger | FIXED | 7fa693c05 (9fc9191d0) | io.lisp:3953-3999 |
| EX15 | export manifest custody | FIXED | c53008594 (66df36ce8) | io.lisp:4818-4890 |
| EX16 | node-secret rotation | FIXED | 376e3cdd6 (fa39c4451) | io.lisp:4357-4396 |

The witnesses for most of these exit 1 at HEAD: see R1.

### Bounds (6 defect findings; B004, B005, B008, B009 are not defects)

| id | finding | class | fixed by | site at HEAD |
|---|---|---|---|---|
| B001 | redeem input bounds / credential width | FIXED | b2fc33459 (ea86cf888) | books/native-redeem-input.lisp:6-54; io.lisp:9448-9544 |
| B002 | catch-up retention of whole batches | FIXED | 450a088e5, 61b7985a9; legacy path deleted 62b70b656 | `fn-cu-on-line`/`-step`/`-on-end` gone; spool quota `fn-csp-write` peer-catchup-spool.lisp:90-99; bank lease pull-service.lisp:454-487 |
| B003 | app-journal 4096 lifetime record ceiling | FIXED | 018abdd39 (CAPS-1) | app-journal.lisp:56-190 (profile, default 2^20 records / 2^40 octets); operator verb workflow.lisp:726 |
| B006 | immutable publication FD debt | FIXED | 6c308c97a, 7fa693c05 | immutable-publish.lisp:93-138; io.lisp:5306-5318 |
| B007 | reclaim retains rewritten history | STILL-PRESENT | 2e4c3da60 (1f450325a) for :none/:refused/:dry-run only | checkpoint.lisp:171-190: actual `:reclaim` still pushes every rewritten record onto `history` then replays the whole list (comment at :164-166 says so). Ledger S046 (open). |
| B010 | import retains the whole archive name list | STILL-PRESENT | none | io.lisp:4892 `fnn-archive-read-dir` (full sorted copy of an unbounded `fnn-list-directory`, :813-824); `fnn-import-pass` io.lisp:5252-5253 binds config and records names before any chunk. Ledger S013 (open). |

B004's refutation still holds (`*fn-ncl-max-secret*` 496, file read bound 498). B003 note: the ceiling is now
operator policy and there is no journal reclamation, so a journal at its profile refuses new prepares until an
operator raises it.

### Consistency (9)

| id | finding | class | fixed by | site at HEAD |
|---|---|---|---|---|
| C001 | 9P Tversion reset after definite mount refusal | FIXED | 48c18731b (cde29dc14) | ninep-transport.lisp:42-60 |
| C002 | TCPCL empty transfer never starts (+ native supplied-p residual) | FIXED | 6dc485ef2 (74e8573a7), ec9b1322a | tcpcl-session.lisp:909-942; tcpcl.lisp:626 `bundle-supplied-p`, :779-783 |
| C003 | web POST uncertain 441 collapsed to refusal | FIXED | 8fd9601a4 (aa0060e1a) | web-session.lisp:1598-1642 |
| C004 | removal verification STAT fault shown as Still there | FIXED | dc4e53ce5 (2db0d1fa6) | web-session.lisp:1646-1665 |
| C005 | web redeem lost reply shown as unreachable | FIXED | 1d8e74e21 (72bd810cf) | web-session.lisp:1378-1416 |
| C006 | consumer CLI reissues register after unresolved bootstrap | FIXED | f5f340d04 (37364cfdd) | consumer-reason.lisp:205-224; consumer-local.lisp:76-88 |
| S-TLS | STARTTLS keeps the pre-TLS reader cursor | FIXED | 7b042111d (fbcd9f17a), 87740d810 | nntp-auth.lisp:1601-1627; lemmas :2595-2643 (certification not observed) |
| S-LIM | store-limit decision ignores completion debt | FIXED | ba8f1a948 (f05ff1388) | limits-live.lisp:147-185; owner-host.lisp:1296; store-node-host.lisp:307 |
| S-POOL | live profile growth vs installed pool / article credit | FIXED | 2675f2609 (efcb40089), 0cb87cf03 | admin.lisp:559-641; limits-live.lisp:210-227; residual R8 |

S-TLS, S-LIM and S-POOL are the `tls_reader_reset`, `limit_completion_join` and `live_profile_pool_and_article_join`
records of `consistency/sweep.spw`.

## D27 data ceilings among the 313 bounds constants

Full table (all 313, classed D / W / RFC / N, each by reading its callers):
`planning/spw-bounds-recount-2026-10-04.md`.
Counts: D 19 constants (12 distinct ceilings), W 128, RFC 26, N 135, converted or deleted 5. No constant in the
JSON changed value or file since 9df4a3a4e; the five gone are `*fn-aj-max-records*` and the three `*fn-aj-*-aggregate*`
constants (CAPS-1 018abdd39) and `*fn-cu-max-line*` (450a088e5). CAPS-4 (189d6c832, `[control] max_clients`) is
on `origin/lane/caps` only, not in dev: `*fn-nctrl-max-active-clients*` (native-control.lisp:111) is still
`(fn-profile-limit :control-clients)`.

Not converted, on the caps lane's residual list (design 1.4; none had a ledger item; filed together as SPW-D01):

| constant | file:line | value | caps |
|---|---|---|---|
| `*fn-bpn-machine-max-octets*` with `*fn-bpa-max-octets*` (bp-adu.lisp:31), `*fn-bpa-max-article*` (:37), `*fn-bpb-max-data*` (bp-bundle.lisp:56), `*fn-bpb-max-input*` (:67), `*fn-bpnf-max-held-image*` (bp-node-foundation.lisp:18) | bp-node-machine.lisp:19 (`fn-bpn-machine-limitp` :383) | 2^24 | residual 1 |
| `*fn-bpn-machine-max-records*` | bp-node-machine.lisp:21 | 4096 | residual 2 (custody rows; profile field 9 exists but is not the live cap) |
| `*fn-bpc-max-text*` | bp-primary-cbor.lisp:111 | 1024 | residual 3 (EID) |
| `*fn-bpn-evidence-max-records*` | bp-receive-evidence.lisp:21 | 4096 | residual 5 (lab receive-evidence lifetime) |

(`*fn-bpb-max-blocks*`, 32, bp-bundle.lisp:60, is caps residual 4; read as W: a per-bundle parse bound.)

Not converted and not on the caps list (each filed):

| constant | file:line | value | what data it caps | item |
|---|---|---|---|---|
| `*fn-bpn-machine-max-job-octets*` | bp-node-machine.lisp:20 (uses bp-node-machine-authorization.lisp:208-210) | 131072 | one sender job's encoded bundle, whatever the profile ADU/bundle octets (bp-limits.lisp:10-17 admits it as PKT-294) | SPW-D02 |
| `*fn-pol-max-members*` | policy.lisp:58 | 64 | members of a group policy; profile field 12 exists and nothing reads it | SPW-D03 |
| `*fn-pol-max-name-octets*` | policy.lisp:59 | 128 | a group named 129..256 octets cannot have a policy | SPW-D04 |
| `*fn-record-max-group-name*` | records-shape.lisp:51 | 256 | group-name length, below the RFC 3977 460 | SPW-D05 |
| `*fn-ff-max-observations*` | feed-filename.lisp:22 | 8192 | durable feed journal names; recovery faults past it (about 1170 peers at depth 7) | SPW-D06 |
| `*fn-cpa-clone-max-entries*`, `*fn-cpa-clone-max-bytes*` | checkpoint-auxiliary.lisp:14, :15 | 1e6 / 1 TiB | store size `checkpoint clone` will copy | SPW-D07 |
| `*fn-th-max-authors*`, `*fn-th-max-anchors*`, `*fn-th-max-report-quota*` | topic-history-metadata.lisp:12; topic-history-admission.lisp:8, :9 | 16 / 16 / 64 | topic-history authors, anchors, report quota (experimental surface; low confidence) | SPW-D08 |

Flagged and classed N (finite lifetime counters, refused by name): `*fn-lgs-max-segment*` 999,999 log segments
(store-log-segments.lisp:41); `*fn-native-admin-config-name-limit*` 10^8 configuration generations
(native-admin-shape.lisp:22); `*fn-cbor-max-uint*` / `*fn-sf-max-uint*` the 2^32-1 transaction space (left to P6).
Design rows that read as stale after reading callers: the keyring snapshot is one principal, not the keyring;
`*fn-cc-max-events*` / `*fn-cc-max-octets*` have no callers outside their own book and should be retired;
`*fn-cfg-max-rows*` / `*fn-cfg-max-deltas*` became per-delta work bounds (PRF-171).

## State-machine cards

Seven cards added to `.spw/machines.spw` (`nntp-dispatch`, `owner-commit`, `arena`, `history-journal`,
`pull-catchup`, `checkpoint`, `bp-session`), each with entry, state, transitions (file:line), keystone, and a
coverage line that says what was read in full and what was only skimmed. Findings made while writing them:
- `nntp-dispatch`: the served host path reaches `fn-av-mca-read-span` (served-available-read.lisp), not the
  `fn-scr-*` chain; the two keystones that name the host path describe `fn-scr-step`/`fn-scr-command`, and
  served-available-commands.lisp:329 says the `fn-av-*` chain has no equality theorem to `fn-nntp-command-pinned`.
- `arena`: `fn-arena-forget` / `fn-arf-*` have no host caller (PRF-1235 says it is not wired); everything under
  books/arena-forget.lisp and books/arena-reader-bound.lisp is books-only.
- `owner-commit`: the order of host steps is proved nowhere; the only link is a static check in
  tests/campaign/native_cuts.py.
- `pull-catchup`: no keystone for "a batch is offered only after its digest chain matches" (code at
  peer-catchup-spool.lisp:141; ledger CSP-OWED-DIGEST-MISMATCH, -OFFERS-VERIFIED, -VERDICT). peer-pull.lisp:371,
  :610 still name the deleted `fnn-pull-begin` / `fnn-pull-event`.
- `checkpoint`: no keystone for the intra-batch crash cuts (`fn-bs-scp-batched-program-crash-is-old-or-new`
  named STILL OWED, PRF-1223) or for clone; books/reclaim-cuts.lisp:14 says `:interned` means tombstones were
  interned into the live arena, but the host reaches it after only predicting them (owner.lisp:7998; sealed in
  the swap quantum at :8047).
- `bp-session`: PRF-1276, 1291, 1296, 1309 are still `planned`; no keystone for the converse (a logical receipt
  alone cannot settle a grant), for `fnn-bp-session-abort-all`, or for loop fairness.
- `history-journal`: `fn-jpub-step` (books/journal-publish.lisp:59) with `fnn-immutable-publish-effect` has no
  proofs.json entry.
