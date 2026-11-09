; THE STORED OWNERS across every step of the core: init (fn2-core-init,
; dispatch-owners.lisp), the engine's genesis (fn2-init-engine) and every turn
; (fn2-turn). The turn reaches the dispatched kinds only through their stubs,
; which keep the stored owners at the commit kind (-DISPATCH-OWNERS,
; machines.lisp), and the commit layer's hooks writing an owner table only
; through their constraints (-OWNERS, commit.lisp); every other function its
; closure reaches is opened -- the sealer's run is the direct one writing an
; owner table (its overlay arenas' okind is the sealer kind). Each function their closures
; reach that writes an owner table keeps FN2-DH-OWNERS-OK K under its
; chain's hypotheses (dispatch-held.lisp, owner mode); at the commit kind
; those hypotheses are constants other than it, so the stored owners avoid
; the commit kind from init through the engine's genesis, for every
; profile and prior core.
(in-package "ACL2")
(include-book "executor")

;; The stubs and the hooks as chain facts at the commit kind: their
;; constraints, each under K the commit kind (and a hook's OKIND not it).
(defun fn2-dh-stub-owner-facts (names kv world)
  (declare (xargs :mode :program))
  (if (atom names) nil
    (let* ((run-stub (fn2-columns-sym (car names) "-RUN-STUB"))
           (obs-stub (fn2-columns-col-name 'fn2-machine-observe (fn2-columns-sym (car names) "-STUB"))))
      (if (function-symbolp run-stub world)
          (list* `(table fn2-dh-keeps ',run-stub
                         '((fn2-dh-owners-ok 4 fn2-core (((equal fn2-dh-k ',kv) ,run-stub)) ,(fn2-columns-sym run-stub "-DISPATCH-OWNERS"))))
                 `(table fn2-dh-keeps ',obs-stub
                         '((fn2-dh-owners-ok 1 fn2-core (((equal fn2-dh-k ',kv) ,obs-stub)) ,(fn2-columns-sym obs-stub "-DISPATCH-OWNERS"))))
                 (fn2-dh-stub-owner-facts (cdr names) kv world))
        (fn2-dh-stub-owner-facts (cdr names) kv world)))))
(defun fn2-dh-hook-owner-facts (hooks kv world)
  (declare (xargs :mode :program))
  (cond ((atom hooks) nil)
        ((getpropc (fn2-columns-sym (car hooks) "-OWNERS") 'theorem nil world)
         (cons `(table fn2-dh-keeps ',(car hooks)
                       '((fn2-dh-owners-ok 1 fn2-core
                                           (((equal fn2-dh-k ',kv) ,(car hooks))
                                            ,@(and (member-eq 'okind (formals (car hooks) world))
                                                   `(((not (equal okind fn2-dh-k)) ,(car hooks)))))
                                           ,(fn2-columns-sym (car hooks) "-OWNERS"))))
               (fn2-dh-hook-owner-facts (cdr hooks) kv world)))
        (t (fn2-dh-hook-owner-facts (cdr hooks) kv world))))
(make-event (value (cons 'progn (fn2-dh-stub-owner-facts (fn2-machine-names (w state)) *fn2-commit-kind* (w state)))))
(make-event (value (cons 'progn (fn2-dh-hook-owner-facts (strip-cars *fn2-commit-hook-children*) *fn2-commit-kind* (w state)))))

(make-event (value (cons 'progn (fn2-dh-chain-forms-m (fn2-dh-postorder-m '(fn2-init-engine fn2-turn) :owners (w state)) nil :owners))))

(defthm fn2-dh-owners-ok-engine-init
  (fn2-dh-owners-ok *fn2-commit-kind* (fn2-init-engine profile (fn2-core-init profile fn2-core)))
  :hints (("Goal" :in-theory '(fn2-dh-owners-ok-init fn2-dh-owners-of-fn2-init-engine (:e equal) (:e not)))))
(defthm fn2-dh-owners-ok-sealer-run
  (implies (fn2-dh-owners-ok *fn2-commit-kind* fn2-core)
           (fn2-dh-owners-ok *fn2-commit-kind* (mv-nth 4 (fn2-sealer-run id budget fn2-core))))
  :hints (("Goal" :in-theory '(fn2-dh-owners-of-fn2-sealer-run (:e equal) (:e not)))))
(defthm fn2-dh-owners-ok-turn
  (implies (fn2-dh-owners-ok *fn2-commit-kind* fn2-core)
           (fn2-dh-owners-ok *fn2-commit-kind* (mv-nth 4 (fn2-turn fn2-core))))
  :hints (("Goal" :in-theory '(fn2-dh-owners-of-fn2-turn (:e equal) (:e not)))))
