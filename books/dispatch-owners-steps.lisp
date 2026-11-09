; THE STORED OWNERS across the core's steps outside the dispatch's stubs:
; the engine's genesis (fn2-init-engine, after fn2-core-init) and the
; sealer's run, the direct (unstubbed) run writing an owner table (its
; overlay arenas' okind is the sealer kind). Each function their closures
; reach that writes an owner table keeps FN2-DH-OWNERS-OK K under its
; chain's hypotheses (dispatch-held.lisp, owner mode); at the commit kind
; those hypotheses are constants other than it, so the stored owners avoid
; the commit kind from init through the engine's genesis, for every
; profile and prior core.
(in-package "ACL2")
(include-book "executor")

(make-event (value (cons 'progn (fn2-dh-chain-forms-m (fn2-dh-postorder-m '(fn2-init-engine fn2-sealer-run) :owners (w state)) nil :owners))))

(defthm fn2-dh-owners-ok-engine-init
  (fn2-dh-owners-ok *fn2-commit-kind* (fn2-init-engine profile (fn2-core-init profile fn2-core)))
  :hints (("Goal" :in-theory '(fn2-dh-owners-ok-init fn2-dh-owners-of-fn2-init-engine (:e equal) (:e not)))))
(defthm fn2-dh-owners-ok-sealer-run
  (implies (fn2-dh-owners-ok *fn2-commit-kind* fn2-core)
           (fn2-dh-owners-ok *fn2-commit-kind* (mv-nth 4 (fn2-sealer-run id budget fn2-core))))
  :hints (("Goal" :in-theory '(fn2-dh-owners-of-fn2-sealer-run (:e equal) (:e not)))))
