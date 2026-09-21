# Independent probe: does native store submission revalidate the whole store per step?

Reviewer: Claude Opus 5, worktree `build/lanes/w13-claude-review`, detached at
**`55d43bf`** (dev head). 2026-09-21. Bounded probe, not a gate.
Measurements on hbox in the certified tree `/tank/fn/lanes/w11-sn-index`,
ACL2 8.7 / SBCL 2.6.8, under `swarm-build` (`SWARM_MEM_MAX=8G`). The
native-codec producer tree was not touched.

## Answer

**No.** On the current host path the core step functions are **not**
guard-checked at runtime, so `fn-sn-statep` does not rescan the retained
store per `fn-sn` step. The `fn-sn-statep` guard is discharged at
**proof** time; at **runtime** the entry point is a `:program`-mode wrapper,
and ACL2 dispatches a `:program`-mode body to raw Lisp, where the inner calls
carry no guard evaluation.

This is the right outcome under D3 ("carry the invariant in state and prove it
preserved"), but it holds for a reason different from the one the source
claims, and nothing pins it. That is the substance of the findings.

## Exact call chain

* `host/native/io.lisp:421-423` — `fnn-counterpart` resolves
  `(find-symbol (symbol-name name) "ACL2_*1*_ACL2")`; `fnn-call:427-441`
  `apply`s it. So the bridge enters at an executable counterpart (`*1*`).
* The names it is handed are host wrappers only — `fn-store-*`, `fn-cfg-*`,
  `fn-reader-*` (enumerated from `io.lisp`); no `fn-sn-*` core name is ever
  passed to `fnn-call`.
* `host/store-node-host.lisp` — **48 of 48** `defun`s declare
  `:mode :program`; there is no `:mode :logic` and no `verify-guards` in the
  file. `:369` is `(fn-sn-io (f-get-global 'fn-store-sn state) operation result)`;
  `:403` is `(fn-sn-prepare s record)`.
* `books/store-node.lisp` — `fn-sn-prepare:226`, `fn-sn-finish:300`,
  `fn-sn-io:346` each declare `:guard (fn-sn-statep s)` and are guard-verified
  (`:241`, `:320`, `:353`). `fn-sn-statep:132-143` conjoins
  `fn-sf-statep (fn-sn-files s)` and `fn-node-statep (fn-sn-node s)`.
* `books/store-files.lisp:327-336` — `fn-sf-statep` walks the retained history
  twice: `fn-sf-record-listp:224` recurses down `(fn-sf-records s)`, and
  `fn-sf-success-listp:255-261` calls `fn-sf-record-has-pairp` against the
  **whole** records list for **each** success, i.e. O(|successes| x |records|).

## Proof-time versus runtime, measured

`fn-sn-io`'s body is `(if (mbe :logic (fn-sn-statep s) :exec t) ...)`, so the
body never runs the recognizer in an execution context. Only the `*1*` guard
check could. Whether it does depends on how the function is entered.

Probe (`/tmp/claude-guard-probe3.lsp`): build real states by driving the real
cycle — reserve, `fn-sn-prepare`, publish, `fn-sn-finish` — N times, then time
100 calls of `(fn-sn-io s :recovery-barrier :ok)` two ways. State sizes were
confirmed to grow 1:1 with N: at N=400, `records`/`successes`/`articles`/`pins`
= 400/400/400/400.

| entry | history 50 | history 400 |
| --- | --- | --- |
| top-level `*1*` call of `fn-sn-io` | 0.03 s / 100 (0.3 ms) | **1.64 s / 100 (16.4 ms)** |
| same call inside a `:program`-mode wrapper | 0.00 s | **0.00 s** |

The `:recovery-barrier` step's body is O(1) (400 raw steps at history 400
measured 0.00 s), so the direct-entry cost is guard cost. 8x the history gives
~55x the per-call cost — the quadratic signature of `fn-sf-success-listp`.

A `trace$` of one top-level `*1*` call on a 50-record state shows the guard
executing, and shows it receiving the whole state:

    1> (FN-SN-STATEP (("fn.letters" "fn.test") 1000000
                      (:STORE-FILES :READY 50 NIL ...
      2> (FN-SF-STATEP (:STORE-FILES :READY 50 NIL ...
      <2 (FN-SF-STATEP T)
      2> (FN-NODE-STATEP ...
      <2 (FN-NODE-STATEP T)
    <1 (FN-SN-STATEP T)

Through the `:program`-mode wrapper the same trace produces no recognizer
entry and the timing is flat in history size. That is the host's shape.

## Findings (3)

### F1 — The absence of rescanning is unpinned, and one word from a quadratic cliff. Severity: medium.

Two facts currently keep the store off the revalidation path: every wrapper in
`host/store-node-host.lisp` is `:program` mode, and `fnn-call` is only ever
handed wrapper names. Neither is asserted anywhere — no lint, no test, no
comment at the definition site, and nothing in the registry. `fnn-counterpart`
(`io.lisp:421`) will resolve *any* symbol in `ACL2_*1*_ACL2`, including
`fn-sn-io` itself.

Concrete consequence, measured above: making one wrapper `:logic` +
`verify-guards`, or passing `fnn-call` a core name, moves the served path from
0.00 s to 16.4 ms per step at 400 retained records, growing quadratically —
roughly 10 s per step at 10,000 records. It would pass certification, pass
`make check`, and show up only as a live service that slows as the store fills.

*Narrow remedy (carried, not "checks off"):* add a static lint to `make check`
that (a) asserts every `defun` in `host/store-node-host.lisp` is `:mode
:program` and (b) asserts every quoted symbol reaching `fnn-call`/`fnn-core`/
`fnn-core-state` names a wrapper defined in `host/*-host.lisp`, not a book
function. Record the D3 property in one sentence at the head of
`host/store-node-host.lisp`, so the next editor knows the mode is load-bearing.

*Evidence needed:* the lint, plus one timing case in the native tests pinning
per-step cost flat across two store sizes.

### F2 — The stated safety property is not the one that holds. Severity: low-medium (documentation of a trust boundary).

`io.lisp:11-18` says core calls go through `fnn-call` "under the same
`guard-checking-on` policy" and that "no book function is called by its raw
symbol, so no unverified guard is bypassed here", and `io.lisp:1718-1719`
faults the image unless `guard-checking-on` is `t`.

Measured: on this path that global is inert. At ACL2's default
`guard-checking-on = t` — the setting the image asserts — the wrapper entry
dispatches to raw Lisp and `fn-sn-statep` is never evaluated on the live state,
at any history size. The guard is a proof obligation that was discharged, not a
runtime check that runs.

Nothing is unsound here, and the outcome is what D3 wants. The defect is that
the trust-boundary text asserts runtime guard enforcement the runtime does not
perform, so a reader auditing the boundary would credit the host with a
validation step it does not take. The honest statement is the D3 one: the state
invariant is carried and proved preserved, and the host never revalidates it.

*Narrow remedy:* correct the two comment blocks to say which property holds and
why, naming the preservation theorem the host actually relies on.

### F3 — A publish cycle is superlinear in retained history even with guards off. Severity: medium, and distinct from F1/F2.

The same probe, on the raw (guard-free) path, building the real cycle:

| records built | total | mean per cycle |
| --- | --- | --- |
| 50 | 0.09 s | 1.8 ms |
| 400 | 27.75 s | 69 ms |

8x the history, 308x the total — per-cycle cost growing roughly O(N^1.75).
This is **body** work, not guard work, so neither F1 nor F2 addresses it. All
four state components grow 1:1 with the history (400/400/400/400), and the
cycle touches structures indexed by them — the duplicate-`Message-ID` check
over `fn-state-articles` and the retention pin list are the obvious candidates.

This is D3 one level down: a served publish walks structures whose length is
the retained history. At 400 articles a publish already averages 69 ms.

*Limit I did not close:* I did not isolate which walker dominates. That needs a
per-function profile of one cycle at two history sizes, which is the next
narrow step rather than something to guess at here.

*Narrow remedy direction:* the same shape as D3's — an indexed structure
carried in state with a proved correspondence to the list it replaces, not
removal of the check. `fn-sn-indexedp` already exists for the index and is
deliberately kept out of `fn-sn-statep` (`books/store-node.lisp:140-142`),
which is the precedent to follow.

## What I could not establish

I measured a faithful **model** of the host entry — a `:program`-mode function
calling `fn-sn-io`, structurally identical to the 48 wrappers — not the real
`fnn-call` -> `*1*fn-snh-*` chain inside a saved `build/fn-host` image. The
structural argument that they behave identically is strong (same mode, same
dispatch rule, and the bridge provably never names a core function), but it is
an argument, not a measurement.

Closing it is cheap and worth doing once: build the native image, open a store
with ~10,000 retained records, and time one submission step against a small
store. If F1's lint lands, that timing case is the natural place to pin it.

No whole-project certification was run, no deployment, and no lane tree was
modified.
