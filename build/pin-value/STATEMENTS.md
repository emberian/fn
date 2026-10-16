# PIN-VALUE statements (A30, 2026-10-16; main ruling B)

Base lane/post 8c4c8c8d8. Plan of record: build/pin-value/plan.py, with its output in plan.txt. The counts below are the script's.
This commit holds the statements: the definitions plus every theorem text whose formula changes in MEANING. Nothing is proved yet. The 60 argument-only formulas, the call sites and the fixtures follow in the proof run, mechanically.

## Definitions (books/owner-config.lisp unless named)
- `fn-ocfg-pin-valuep (v)` = `(and (consp v) (fn-cfgp (car v)))`. The profile half is unconstrained here; PIN4 relates it to the connection's limits, and PIN3 refuses an unadmitted profile (both are P16's).
- `fn-ocfg-pins-okp`: the conjunct `(fn-cfgp (cdr (car pins)))` becomes `(fn-ocfg-pin-valuep (cdr (car pins)))`.
- `fn-ocfg-conn-config (oc id)` = `(car (cdr (fn-ocfg-pin-find id (fn-ocfg-pins oc))))`. Its consumers' formulas stay byte-identical.
- NEW `fn-ocfg-conn-profile (oc id)` = `(cdr (cdr (fn-ocfg-pin-find id (fn-ocfg-pins oc))))`.
- The opens gain PROFILE as their last argument, and a new connection pins `(cons (fn-ocfg-config oc) profile)`:
  - `fn-ocfg-open (oc acfg profile)`
  - `fn-ocfg-open-peer (oc peer acfg profile)`
  - `fn-ocar-ocfg-open (oc acfg profile)` (books/owner-open-carried.lisp)
  - `fn-exp-open (... now profile)` (books/public-exposure.lisp)
  - `fn-ocar-exp-open (... now profile)` (books/owner-open-carried.lisp)
  - The host passes `(fn-owner-store-profile state)` at every STATE call site (plan: CALL SITES).
- `fn-ocfg-step` event shapes:
  - `(:open ACFG PROFILE)`
  - `(:open-peer PEER CFG ACFG PROFILE)`
  - Owner-level `fn-own-step` reads only the earlier elements, so it is unchanged.
- A re-pin keeps the connection's OWN profile. It moves the configuration only:
  - `fn-ocfg-advance`, `fn-ocfg-with-read-owner` and `fn-oop-advance` (books/owner-outcome-pinned.lisp) set `(cons (fn-ocfg-config oc) (fn-ocfg-conn-profile oc id))`.
  - `fn-orcp-pins-at (conns cfg pins)` (books/owner-reclaim-pass.lisp) gives each connection `(cons cfg <its profile in PINS>)`. `fn-orcp-swapped-ocfg` passes the live table.
  - Why: a profile is fixed at open (pinned-charge: admission charges the MAX over live pins). A view move or a reclaim swap never re-profiles a connection.

## Widened theorem texts (8; reason: the pinned value widened from CFG to (CFG . PROFILE))
| Book | Theorem | Old | New |
|---|---|---|---|
| owner-config | fn-ocfg-with-read-owner-pin-iff-survives | `(cons id (fn-ocfg-config oc))` | `(cons id (cons (fn-ocfg-config oc) (fn-ocfg-conn-profile oc id)))` |
| config-owner-live-open | fn-ocl-pin-add-preserves-pins-okp | hyp `(fn-cfgp cfg)` | hyp `(fn-ocfg-pin-valuep cfg)` |
| config-owner-live-read | fn-ocl-pin-set-keeps-pins-okp | hyp `(fn-cfgp cfg)` | hyp `(fn-ocfg-pin-valuep cfg)` |
| config-owner-live-read | fn-ocl-with-read-owner-fields | `(fn-ocfg-pin-set id (fn-ocfg-config oc) ...)` | `(fn-ocfg-pin-set id (cons (fn-ocfg-config oc) (fn-ocfg-conn-profile oc id)) ...)` |
| config-owner-advance-invariants | fn-ocl-pin-set-preserves-pins-okp | hyp `(fn-cfgp cfg)` | hyp `(fn-ocfg-pin-valuep cfg)` |
| owner-host-relation | fn-ohr-with-read-owner-fields | as config-owner-live-read | same |
| owner-reclaim-conns | fn-orcn-pin-find-of-pins-at | `(equal (cdr (pin-find .. (pins-at conns cfg))) cfg)` | `(equal (car (cdr (pin-find .. (pins-at conns cfg pins)))) cfg)` |
| transit-same-decision (P16's text, applied here so the lane certifies) | fn-tsd-found-pin-is-a-configuration (local) | `(fn-cfgp (cdr (pin-find id pins)))` | `(fn-cfgp (car (cdr (pin-find id pins))))` |

None of these is a weakening:
- Each pins-okp hypothesis is the recognizer of the new value type. It plays the same role as before, over the widened value.
- Each value equation states the new value exactly, its configuration half equal to the old value.

## Producer-argument (1)
owner-reclaim-conns fn-orcn-swapped-ocfg-fields: `(fn-orcp-pins-at conns cfg)` becomes `(fn-orcp-pins-at conns cfg (fn-ocfg-pins live-oc))`.

## Argument-only (60 formulas in 18 books; plan.txt "ARGUMENT")
Each formula gains PROFILE at its open call, and nothing else changes. Audit: erase the argument, and the old text must come out byte-equal (C26's check). Grants in hand:
- C26: served-catalog-join-frame-conns, host-arms, host-entries, host-views, and two test books.
- main: owner-store-indexed, owner-agent and public-exposure are A's; argument-only fixture edits are covered by the plan.

## Teeth (owed by the proof run)
- A pin whose value is a bare CFG (the old shape) is refused by `fn-ocfg-pins-okp`, as a ground witness.
- `fn-ocfg-open` with profile P pins exactly P: conn-profile of the new id = P, by a positive witness plus a mutant open that drops PROFILE (refused).
- An advance and a swap keep a connection's profile, with a ground witness of two connections under different profiles.
