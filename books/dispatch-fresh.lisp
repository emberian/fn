; FRESHNESS and LENT-OK (commit-durable-all.lisp) across the other kinds'
; observe handlers: a harvest delivers its completion to the owner's observe
; function, and every observe stub keeps the operation table whole
; (-OPS-POOL) and the commit layer's IO units (-KEEPS-UNITS, machines.lisp),
; so no take in the log and no lent unit names an incarnation that changed:
; both are kept, over every log, event and argument.
(in-package "ACL2")
(include-book "commit-durable-all")

(defthm fn2-dfr-env-op-of-ops
  (implies (equal (fn2-core-ops b) (fn2-core-ops a)) (equal (fn2-env-op s b) (fn2-env-op s a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-op))))
(defthm fn2-dfr-heads-kept-of-ops
  (implies (equal (fn2-core-ops b) (fn2-core-ops a)) (fn2-env-op-heads-kept a b))
  :hints (("Goal" :in-theory '(fn2-env-op-heads-kept)
           :use ((:instance fn2-dfr-env-op-of-ops (s (fn2-env-op-heads-kept-witness a b)))))))
;; A step B of A that leaves the operation table and the IO units keeps both.
(defthm fn2-dfr-fresh-lent-of-ops-io
  (implies (and (fn2-env-freshness log a) (fn2-env-lent-ok a)
                (equal (fn2-core-ops b) (fn2-core-ops a))
                (equal (nth *fn2-core-commit-io* b) (nth *fn2-core-commit-io* a)))
           (and (fn2-env-freshness log b) (fn2-env-lent-ok b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-dfr-heads-kept-of-ops fn2-env-units-kept-of-io)
           :use ((:instance fn2-env-fresh-lent-kept)))))

(defun fn2-dfr-events (names world)
  (declare (xargs :mode :program))
  (if (atom names) nil
    (let ((stub (fn2-columns-col-name 'fn2-machine-observe (fn2-columns-sym (car names) "-STUB"))))
      (if (not (function-symbolp stub world)) (fn2-dfr-events (cdr names) world)
        (let ((call `(,stub id event outcome reason count aux0 aux1 fn2-core)))
          (cons `(defthm ,(fn2-columns-sym stub "-FRESH-LENT")
                   (implies (and (fn2-env-freshness log fn2-core) (fn2-env-lent-ok fn2-core))
                            (and (fn2-env-freshness log (mv-nth 1 ,call)) (fn2-env-lent-ok (mv-nth 1 ,call))))
                   :hints (("Goal" :in-theory '(fn2-dispatch-ops-pool fn2-core-ops)
                            :use ((:instance fn2-dfr-fresh-lent-of-ops-io (a fn2-core) (b (mv-nth 1 ,call)))
                                  ,(fn2-columns-sym stub "-OPS-POOL") ,(fn2-columns-sym stub "-KEEPS-UNITS")))))
                (fn2-dfr-events (cdr names) world)))))))
(make-event (value (cons 'progn (fn2-dfr-events (fn2-machine-names (w state)) (w state)))))

;; THE RUN STUBS. A run writes the operation table: it reserves a free op
;; at its generation, issues it, or leaves it. None of those makes an
;; incarnation that has begun and been issued (fn2-env-incarnation-ok) stop
;; being one: every run stub keeps HEADS-ADVANCE (-DISPATCH-HEADS,
;; books/dispatch-heads.lisp), under which FRESHNESS is kept, and LENT-OK
;; with the IO units kept, as every run of a kind whose frame leaves
;; commit-io keeps them (-KEEPS-UNITS). The batch kinds (txn, cns, auth)
;; write commit-io's extents, epochs, counters, readiness and pool rows
;; (fn2-commit-save-pool, -reserve-extent, -release-pool) but never a unit's
;; operation or loan; their runs keep FRESHNESS.
(defthm fn2-dfr-heads-advance-of-kept
  (implies (fn2-env-op-heads-kept a b) (fn2-dfr-heads-advance a b))
  :hints (("Goal" :in-theory '(fn2-dfr-heads-advance fn2-env-incarnation-ok-of-heads))))
(defthm fn2-dfr-freshness-of-advance
  (implies (and (fn2-env-freshness log a) (fn2-dfr-heads-advance a b)) (fn2-env-freshness log b))
  :hints (("Goal" :induct (fn2-env-freshness log a)
           :in-theory (union-theories '(fn2-env-freshness fn2-dfr-incarnation-ok-of-advance) (theory 'minimal-theory)))))
(defthm fn2-dfr-lent-ok-of-advance
  (implies (and (fn2-env-lent-ok a) (fn2-dfr-heads-advance a b) (fn2-env-units-kept a b)) (fn2-env-lent-ok b))
  :hints (("Goal" :in-theory '(fn2-env-lent-ok)
           :use ((:instance fn2-env-units-kept-necc (u (fn2-env-lent-ok-witness b)))
                 (:instance fn2-env-lent-ok-necc (fn2-core a) (u (fn2-env-lent-ok-witness b)))
                 (:instance fn2-dfr-heads-advance-necc
                            (s (nth 1 (fn2-env-io (fn2-env-lent-ok-witness b) b)))
                            (g (nth 2 (fn2-env-io (fn2-env-lent-ok-witness b) b))))))))
(defthm fn2-dfr-fresh-lent-of-advance
  (implies (and (fn2-env-freshness log a) (fn2-env-lent-ok a) (fn2-dfr-heads-advance a b) (fn2-env-units-kept a b))
           (and (fn2-env-freshness log b) (fn2-env-lent-ok b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-dfr-freshness-of-advance fn2-dfr-lent-ok-of-advance))))

(defun fn2-dfr-run-events (names world)
  (declare (xargs :mode :program))
  (if (atom names) nil
    (let* ((stub (fn2-columns-sym (car names) "-RUN-STUB"))
           (call `(,stub id budget fn2-core)) (out `(mv-nth 4 ,call)))
      (cond ((not (function-symbolp stub world)) (fn2-dfr-run-events (cdr names) world))
            ((getpropc (fn2-columns-sym stub "-KEEPS-UNITS") 'theorem nil world)
             (cons `(defthm ,(fn2-columns-sym stub "-FRESH-LENT")
                      (implies (and (fn2-env-freshness log fn2-core) (fn2-env-lent-ok fn2-core))
                               (and (fn2-env-freshness log ,out) (fn2-env-lent-ok ,out)))
                      :hints (("Goal" :in-theory '(fn2-env-units-kept-of-io)
                               :use ((:instance fn2-dfr-fresh-lent-of-advance (a fn2-core) (b ,out))
                                     ,(fn2-columns-sym stub "-DISPATCH-HEADS") ,(fn2-columns-sym stub "-KEEPS-UNITS")))))
                   (fn2-dfr-run-events (cdr names) world)))
            (t (cons `(defthm ,(fn2-columns-sym stub "-FRESH")
                        (implies (fn2-env-freshness log fn2-core) (fn2-env-freshness log ,out))
                        :hints (("Goal" :in-theory '(fn2-dfr-freshness-of-advance ,(fn2-columns-sym stub "-DISPATCH-HEADS")))))
                     (fn2-dfr-run-events (cdr names) world)))))))
(make-event (value (cons 'progn (fn2-dfr-run-events (fn2-machine-names (w state)) (w state)))))
