# PIN-VALUE report — PASS

All 47 changed ACL2 books (25 production, 22 test books) passed standalone CERTIFY-BOOK on hbox in separate fresh sessions, each followed by illegal-to-certify-message = NIL and a confirmed session stop. The required teeth, erase audit and static gates pass. No remaining reds.

STATEMENTS revision 1 resolves run 1's guard counterexample through total MBE executable projections. Logical bodies and guard T remain unchanged. No commits; one hbox REPL session at a time; no farm/native jobs launched by this run.

## Mechanical audit

The seat audited the retained mechanical edits: 60 A formulas, 0 erase differences against 8c4c8c8d8; allow-list clean. Resume 2 frozen_check.py also compares every existing theorem formula in changed production books with c824a73ee: **947 checked, 0 differences**, after erasing approved A arguments. This includes the nine restated texts; hints are outside the compared formula spans. `erase_check.py` compares exact formula text after removing only the added argument and separator. The five opens take PROFILE last; pure helper functions retain the house arena-last calling convention. STATE callers and their callback reference equations use `(fn-owner-store-profile state)`. The three named hint-only event literals include PROFILE.

## Per-book evidence

Each PASS below is an actual CERTIFY-BOOK in its own fresh hbox session, followed by illegal-to-certify-message = NIL and a stopped session. Exploratory admissions and repaired failures are retained separately in gate-results.json and their logs. The scope is these 47 books at the source closures recorded in cert-results.json. final_audit.py checks that every result still matches the current working tree, successful certificate-write marker, NIL diagnostic and session stop.

| Book | Standalone CERTIFY-BOOK and diagnostic |
|---|---|
| `books/config-owner-advance-invariants.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/config-owner-live-open.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/config-owner-live-read.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/config-owner-read-invariants.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/login-binding-live.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-agent.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-config.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-connection-callback-refinement.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-connection-callbacks.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-host-relation.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-number-bound-join.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-open-carried.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-outcome-pinned.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-prepare-correspondence.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-reclaim-conns.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-reclaim-pass.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-recover-ocl.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-served-invariants.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/owner-store-indexed.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/public-exposure.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/served-catalog-join-frame-conns.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/served-catalog-join-host-arms.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/served-catalog-join-host-entries.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/served-catalog-join-host-views.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `books/transit-same-decision.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/catchup-carried-transit-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/config-owner-live-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/config-owner-publish-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/config-owner-read-invariants-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/login-binding-live-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-agent-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-article-slots-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-config-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-connection-callback-additional-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-connection-callback-captured-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-connection-callback-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-host-relation-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-open-carried-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-reclaim-conns-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-reclaim-ready-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-recover-ocl-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-served-invariants-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/owner-store-indexed-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/productive-read-chain-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/public-exposure-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/served-catalog-join-frame-conns-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |
| `tests/acl2/served-catalog-source-scan-tests.lisp` | PASS CERTIFY-BOOK; illegal-to-certify-message NIL |

## Repairs

- Seat's STATEMENTS revision 1: total MBE executable projections in fn-ocfg-conn-config, fn-ocfg-conn-profile, and fn-orcp-pins-at's profile read; logical bodies unchanged. owner-config fresh load passed with illegal-to-certify-message NIL.
- books/config-owner-live-read.lisp, fn-ocl-read-preserves-historical-relation-repinned: four :use CFG instantiations for pin-set/history helper lemmas now use `(cons (fn-ocfg-config oc) (fn-ocfg-conn-profile oc id))`. The theorem formula is unchanged.
- tests/acl2/owner-config-tests.lisp: stale-pin and completing-state fixture tables wrap CFG in `(cons CFG nil)`; existing assertions unchanged. New rejection tooth deliberately constructs the bare old CFG shape.
- books/owner-connection-callback-refinement.lisp: both carried/reference open :use instances explicitly instantiate PROFILE with `(fn-owner-store-profile state)`, matching their STATE callback equations. Formulas unchanged.
- books/owner-connection-callbacks.lisp now owns the existing `fn-owner-store-profile` definition moved byte-identically from host/owner-host.lisp, whose copy becomes a source reference comment. TASK 1 required this accessor in book callers; previously it existed only in the host and callback admission failed translation. No new logic, guard or hypothesis. Both files are allowed.
- The same pin-value hint class in owner-host-relation (re-pinned read-step) and config-owner-advance-invariants (advanced histories and pin clauses) is transformed by pin_hints.py using tools/lisp_rewrite.py, with three fixtures and an idempotence check. Only :hints subtrees change; current pin-set values and CFG helper instantiations become `(cons (fn-ocfg-config oc) (fn-ocfg-conn-profile oc id))`. Coverage/domain :use instances explicitly bind that CFG value. Formulas remain unchanged.
- Explicit old-shape pin values in config-owner-live-tests (*ocl-t-forged-old-pin*), login-binding-live-tests (*lblt-oc*, *lblt-oc4*) and owner-host-relation-tests (*ohrt-stale*) are widened to `(CFG . NIL)` without changing assertions. fixture_pins.py covers these and the two owner-config fixtures, with three shape fixtures and idempotence checks. This preserves each original counter-witness's intended configuration and its isolated failed hypothesis, rather than introducing an unintended malformed-value failure. The new bare-CFG rejection tooth and the cfg-only mutant remain old-shaped deliberately.
- served-catalog-join-host-entries, fn-sjh-op-ocar-ocfg-open-owner: removed spurious PROFILE from the quoted :in-theory rule list. The arity transformer had mistaken that data list for a function application. mechanical.py now protects theory expressions and has a quoted-rule-list regression fixture. Structural audit of quoted lists headed by any arity-set member found exactly this one spurious insertion; the two owner-store-indexed lists were already unchanged. All theorem formulas are unchanged by this repair.
- owner-reclaim-pass certified with MBE directly in def-loop :body. The named-helper fallback was not needed.
- owner-config-tests line 276: its one old direct `(cdr (fn-ocfg-pin-find ...)) = CFG` ground assertion now projects CAR of that value; the asserted CFG is unchanged. This fixture checks the configuration half of the new pin, as the restated reclaim pin theorem does. No frozen theorem formula changes.
- owner-config-tests ocfg-r-unbound-full: the theorem-generating macro invocation uses fresh PROFILE in its acceptance hypothesis, matching PROFILE in the generated conclusion. This is an argument-only fixture correction; mechanical.py has a corresponding regression/idempotence fixture.
- owner-reclaim-conns: the :use instance of fn-orcn-pin-find-of-pins-at explicitly supplies `(pins (fn-ocfg-pins live-oc))`, matching the widened producer call in the swapped configured owner. Formula unchanged.

## Teeth

PASS in rooted `tests/acl2/owner-config-tests.lisp`: (a) bare CFG rejected despite valid CFG; (b) fresh valid state opens ID 0 with exact profile and configuration, plus an exact copy of open whose sole changed pin value drops PROFILE, with a ground negated result and `must-fail-checked`; (c) IDs 0 and 1 opened under distinct profiles/configurations, with ground checks that both profiles survive a successful advance and a reclaim swap that changes both configuration pins. All three groups PASS in the standalone CERTIFY-BOOK of owner-config-tests, including the translation-checked expected refusal. See pvc-owner-config-tests-certify.log and pvc-owner-config-tests-illegal.log.

## Static gates

Resume 2: erase_check, host_check --attach-order/--world/--build-lists, interface_emit --check, cost_obligations --check and book_roots_check all passed (exit 0). Logs and exit statuses: `pv2-{erase,host-attach,host-world,host-build,interface,cost,roots}.{log,exit}`. The interface tool lists one source-unresolved existing keystone entry, not a gate failure; the roots tool reports 55 declared exclusions and 0 unlisted orphans.

## Outside / remaining reds

See `OUTSIDE.md`. No outside-allow-list hint repair was required; no remaining reds; no theorem formula has been changed beyond the frozen revision and audited argument insertions. Run 1's false guard evidence is retained in owner-config-load.log and guard-counterexample.log. It is resolved, not a remaining RED.

## Reproduction and audit

`cert_queue.py` starts each target with `--upto '#1'` (zero source forms loaded), then uses the house LD / CERTIFY-BOOK driver with portcullis 0, checks a success marker after certificate creation, reads `(@ illegal-to-certify-message)`, and stops the session before the next. No exploratory local events precede certification. `repl.py` delegates to tools/proof_repl.py with the SSH control socket in /tmp.

Commands: `python3 build/pin-value/final_audit.py`, `python3 build/pin-value/erase_check.py`, `python3 build/pin-value/frozen_check.py`. The full per-book command and logs are recorded by cert_queue.py / cert-results.json. Host edits are covered by the requested host/interface static gates. No commit or push was made; the seat owns the certification of record.

Final audit result: **47 current source closures checked; 0 differences**. Source allow-list audit: 0 outside edits; `git diff --check` passes. All session stops are confirmed; no remaining proof or gate work.
