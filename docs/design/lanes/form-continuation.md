# fn2 machine-form seat continuation (present state; rewritten whole after every commit)

Seat: Opus, writes the code; owns layer A's generator and adapter (and A's executor). Brief: main's launch prompt +
`build/coordinator/briefs/FN2-SEAT-COMMON.md`; method `build/coordinator/fn2/WORKFLOW-20261031.md`. Statement:
`build/coordinator/fn2/MACHINE-FORM-20261030.md` §6 (6.10 = what is built, measured and open, rewritten with every landing).

## Landed (dev)
| sha | what |
|---|---|
| d04660248 .. 82eb2bfc2 | G1, probe, P1, P2/P3, G2, P4, per-arm tuples, one shape theorem per function |
| 371c48e4e | the `:local` listener |
| 56b866c35 | G3 1/n: `:repeat` cost, F13 multisets, F10 phase-valued fields |
| 144596771 / 4c7ab8df3 | turn bound from the registry; native-serve serves the seeded store |
| a0556c390 | G3 2/n: paths (F11), holds per path (F14), typed links (F8), `:sub` |
| 8e42831b8 | the three surface sessions share tests/seeded-store.lsp (profile, seeds, seeded ENVELOPE replay); native-session serves it |
| 8a34fab6f (merged ef5e1b992) | G3 3/n: `:genesis`, scribe `:refused`, per-output facts as rule classes, `fn2-shape-one` (defined, unused on dev), park-taken child form, F9 owner lemma |
| (this commit) | `(:park K :F E ...)` named formals + child/rebind fixes in `machine-arms.lisp`; C's `fn2-idc-op-shape` on `fn2-shape-one` (`machines-c-stage` 119s -> 54.4s); `assembly-callbacks` DAG fan-out (`r` from `c`; `d-upload`, `d-txn`, `d-cursor` from `d`) |

## How G3 3/n + Park Named Formals are built (for editing them)
- **Park named formals.** `machine-arms.lisp`: `(:park K :F E ... :steps S)` validates keyword plist tail (`fn2-arms-kw-plistp`), passes `(list* parker 'id (fn2-arms-plist-drop '(:steps) rest))` to `fn2-arms-call` (checking every formal beyond `id` is named), collects `K`'s `:park` operation in `fn2-arms-collect-children` so extra core children (`fn2-accounts`) join the kind's child tuple, and binds non-stobj return values (`fn2-park-ignore-N`) in `fn2-arms-rebind` when a `:park` op returns `(mv code stobj...)`. Unit: `tests/machine-arms-unit.lisp` `fn2-arms-park-wait` (`(:park :principal-reservation :principal row-principal-slot)`) + `must-fail` (`fn2-arms-park-wait-bad`).
- **Genesis.** machines.lisp: `defmachine ... :genesis (STEP ...)` (arm-language kinds only; `:sub-next` desugared),
  stored as declared `:genesis`; `fn2-machine-property K :genesis-arm` is the derived `((PHASE0 K-GENESIS . contract))`.
  machine-arms.lisp: `fn2-arms-arms` takes a last arg GENESIS (t: name `K-GENESIS`, site "GENESIS"); `fn2-arms-genesis-phase`
  = :initial phase or first; genesis ops join `fn2-arms-collect-children`; reachability counts it. defmachine-run checks
  it with `fn2-machine-arms-problem` and path-reports it. executor.lisp: `fn2-exec-genesis-row` (make-event case over
  kind codes = positions in `fn2-machine-names`), `fn2-exec-genesis`, `fn2-exec-rows`; `fn2-init-executor` calls it where
  start-listeners was. Listener: `:genesis ((:charge :steps *fn2-work-small* :runnable t))`. Unit: tests/machine-arms-unit
  `fn2-arms-born` (+ an undeclared-op must-fail).
- **Scribe.** phase `:refused` (holds `:storage-job` only) for both refused-reservation paths; q1-unit pin 111 labels,
  machines-a-unit packed tags (14 :refused).
- **Rule classes.** machine-arms `fn2-arms-ok-shape-events`: per-child P/WFP are `:rule-classes` corollaries of
  K-...-SHAPE (`fn2-arms-ok-rule-classes`); `FN2-ARMS-OK-...-OPEN` stays enabled globally, disabled in shape hints.
- **fn2-shape-one** (end of machines.lisp): per-function predicate FN-SHAPE-OK over (result . OBJS), OF-TUPLE/OPEN,
  FN-SHAPE-ONE (one walk; a computed hint opens OPEN once stable for leaves that are another op's result), then NAME
  stating the claims. Adopted on C's `fn2-idc-op-shape` in `machines-c-successor.lisp` (`machines-c-stage` 119s -> 54.4s).
- **Assembly-callbacks fan-out.** `assembly-callbacks-d-upload`, `assembly-callbacks-d-txn`, and `assembly-callbacks-d-cursor` include `assembly-callbacks-d` directly; `assembly-callbacks-r` includes `assembly-callbacks-c` directly; `assembly-callbacks.lisp` joins `t`, `d-conn2`, `d-upload`, `d-txn`, `d-cursor`.
- **Park-taken child.** machines.lisp taken section: `fn2-machine-park-taken-K-children (id fn2-machines fn2-control)`,
  preserves + rows lemmas, `:child` on the defcost.
- **F9.** arm-children `fn2-pool-hand-accept-owner` (:rule-classes nil).

## Numbers (G3 2/n on forge vs 1/n; 3/n on hbox) are in MACHINE-FORM §6.10. Books over 60 s that are this seat's to
fix: executor (91 s forge), cursor's arms (D's book, the generator's proofs: 108 s forge), assembly-access (61 s),
assembly-init (65 s). After 3/n on hbox: cursor 69 s, executor 74 s. `machines-c-stage` is now 54.4 s (under 60 s).

## Next (in order)
1. `:do` chains over four steps split into disabled sub-functions (carry the chain's bound vars as formals).
2. `:to L` for a hand's target (link triple), the F9 statement over links.
3. Assembly per-child books: assembly-access (2,191 per-field writer events), rows-other, the reference books
   (include + event volume), assembly-init's fn2-core-init-wfp, the executor's per-kind run rewrite.
4. Listener registry arms by family (admission into E's kind); outbound Connect.
5. C's ask: `fn2-read-children-facts` costs ~1.2 s of machines-c-read (measured); no change needed there.

## Boxes
hbox `~/form-g3`: plain copy + `git init` anchor (smoke needs a revision); FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k
ACL2_SYSTEM_BOOKS=/tank/fn/acl2-8.7/books must be exported (python harnesses too). Launch
`(setsid sh build/gN.sh > build/gN.wrap 2>&1 < /dev/null & echo $! > build/gN.pid)`; forge-certify writes
build/certify-named.log (copy it before the next run overwrites it). REPL for the generator: build/gen.lsp pattern
(include machines-a-run, `set-ld-redefinition-action (:doit! . :overwrite)`, ld the new machines/machine-arms, ld the unit).
Forge `/build/lanes/form-base`: push dev to `forge:/build/fn.git` then `git checkout -f --detach origin/dev` there.

## Rules
PID files only; never stash / add -A; named paths; secrets check before push; a book over 60 s is its owner's
to fix; disk pressure: stop and tell.
