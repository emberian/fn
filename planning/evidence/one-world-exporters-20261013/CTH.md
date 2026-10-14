# CTH — r11 guard-proof diagnosis

**Category (ii): `(:REWRITE ADT-TP-NTHCDR-SHORT)` is newly exported into this consumer world by `catalog-paged` → `def-representation-pages`. Disabling exactly that rune admits the unchanged stalled event in 2,127 steps / 0.08 s, with all 24 dev Rules unchanged (dev: 1,443 steps / 0.13 s).** Diagnosis only; no source repair or certification claimed.

## Event and reference

The spinning event is **`VERIFY-GUARDS FN-CTH-HEADER-SEGMENTS`**, source form **#87**, `books/charged-totals-header.lisp:853`. It is not the DEFUN FN-CTH-INSTALLED-SEED near log line 695.

- r11: `build/acl2/certify-20261014T082430Z-3997981/books--charged-totals-header.certify.log:27833`; after K-FRAMES-OF-ONE, it splits into four subgoals and ends at `Subgoal 4'222'` with the 1,800 s LIMIT.
- Dev: `/Users/ember/dev/fn/build/lanes/over/build/acl2/certify-20261014T082350Z-3991883/books--charged-totals-header.certify.log:27877`; Rules summary at :27921, 1,443 steps at :27948. The entire dev book took 54.41 s / 5,506,694 steps; those are book totals, not the stalled event's cost.
- Current HEAD: `58c0146bf9e431b77cf41fdf41295e452dd5db19`. The book is byte-identical to git `e09813667` and the existing FAM5 dev archive: SHA-256 `c6b16f6f25d86ee986d728ab6c119cf252912319966ba5795be6f16a634c9d28`.

## Driving rune and mechanism

`books/def-representation-pages.lisp:140` exports:

```lisp
(defthm adt-tp-nthcdr-short
  (implies (and (<= (len w) (nfix n)) (true-listp w))
           (equal (nthcdr n w) nil)) ...)
```

ACL2 reports a BACKCHAIN rewrite with no backchain limit or loop stopper. Its family is **paged-list length/slice boundary normalization**: an NTHCDR tail becomes NIL on a length bound. It is neither an NTH opener nor an octet-recognizer bridge nor a live-link skip rule.

The [BRR capture](cth-brr-baseline.log) monitors only this rune and prints `cw-gstack :frames 14` without interactive breaks. At :28–97 the stack is simplifying the first clause literal, the instantiated `:USE K-CHUNKS-OF-SHORT` implication. It opens FN-SCC-CHUNKS, enters its recursive long branch, and attempts ADT-TP-NTHCDR-SHORT on `(nthcdr (max 1 (len (fn-scc-program row))) (fn-scc-program row))`. Later captures show the same expansion in the guard's own run-segments expression. Thus the new tail-to-NIL rewrite changes simplification of the supplied short-chunk equality and exposes recursive chunk/length work instead of preserving dev's short proof shape.

The [10 s accumulated-persistence profile](cth-ap-baseline.log) credits ADT-TP-NTHCDR-SHORT with 5 tries / 1,962 frames (3 useful tries / 1,778 frames). The resulting work is dominated by LEN (1,068 tries / 25,284 frames), FN-SCC-LONG-ENOUGHP (265 / 15,604), TAKE (177 / 14,670), and FN-SCC-CHUNKS (6 / 2,359). These are downstream expansion runes; the isolated causal control toggles only ADT-TP-NTHCDR-SHORT. The bounded captures establish runaway simplification, not a proof of an infinite opposing-rune cycle.

## Controlled replay and comparison

All sessions use hbox cached-only proof_repl, no dependency source fallback. HEAD installs 426 cached books, artifact set `2fcae4271142cebed1199925931c8ebb620cbc4c7c123f34a93a1da101ccf9d2`, toolchain `8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`. Its source prefix loads unchanged through #86, with no diagnostic theory edits before the baseline. [Start](cth-start.log), [remaining prefix](cth-prefix.log).

| Attempt | Result | Evidence |
| --- | --- | --- |
| Original theory, 10 s limit, persistence enabled | LIMIT, 718,467 steps; Subgoal 4' chain | [baseline](cth-baseline.log) |
| Disable only ADT-TP-NTHCDR-SHORT | Admits, 2,127 steps / 0.08 s | [first control](cth-nthcdr-off-control.log) |
| Undo back through K-FRAMES-OF-ONE, resend #86, original theory, 5 s limit | LIMIT, 482,239 steps; same chain | [restored baseline](cth-restored-baseline2.log), [restore](cth-restore-prefix.log) |
| Original theory, rune-specific BRR, 2 s limit | LIMIT, 178,695 steps; same chain | [stack capture](cth-brr-baseline.log) |
| Turn BRR off; disable only ADT-TP-NTHCDR-SHORT again | Admits, 2,127 steps / 0.08 s | [final control](cth-final-control.log) |

Dev's 24 Rules and the passing control's 24 Rules are exactly equal; same `:USE K-CHUNKS-OF-SHORT` hint event. [Full lists and empty deltas](cth-rule-comparison.json). Dev includes FN-SCCB-CHUNK-COUNT-IS-LEN-CHUNKS and FN-LG-CHUNK-LEN-BOUNDS; these remain enabled in HEAD and reappear in the passing control. None of the seven runes in the brief occurs in dev's Rules list for this event. This is **not category (i), a census miss**.

A separate cached-only session over the existing FAM5 archive of dev `e09813667`, after the same six top-level includes, reports ADT-TP-NTHCDR-SHORT **absent from both enabled and universal theories**. HEAD reports it enabled before the control and present in the universal theory. [Dev membership](cth-dev-membership.log), [HEAD original membership](cth-suspects2.log), [HEAD universal membership](cth-head-membership.log). ACL2's `pe` records the HEAD import path through memory-model → served-plan-cursor → over-window → served-catalog → catalog-number-index → catalog-view → catalog-relation → catalog-delta → catalog-commit → catalog → catalog-paged → def-representation-pages. [Rune and provenance](cth-nthcdr-pr.log).

## Session-only control and shutdown

Before unchanged source form #87, issue:

```lisp
(in-theory (disable (:rewrite adt-tp-nthcdr-short)))
```

Reproducible setup: `timeout 240 python3 build/vertical-runs/one-world/cth_repl.py start cth-r11-diag books/charged-totals-header --upto '#78' --host hbox --remote-tree /tank/fn/gates/vertical-one-world-cth-diag-repl --cached-only --limit 30 --load-timeout 60 --lane vertical-one-world`, then `send-range` from `'#78'` until `'#87'`. The wrapper redirects local session records into this report directory and disables SSH multiplexing; proof_repl's cache and slot policy are unchanged. [Unchanged target form](cth-target.lisp), [send helper](cth_send.py), [wrapper](cth_repl.py).

Owned sessions **cth-r11-diag** and **cth-dev-diag** were stopped by name through proof_repl; both returned `stopped`. [HEAD stop](cth-head-stop.log), [dev stop](cth-dev-stop.log). No kill commands, commits, source edits, certification jobs, or non-REPL box jobs. All new local artifacts are under `build/vertical-runs/one-world/`.
