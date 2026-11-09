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
                   :hints (("Goal" :in-theory '(fn2-dispatch-ops-pool)
                            :use ((:instance fn2-dfr-fresh-lent-of-ops-io (a fn2-core) (b (mv-nth 1 ,call)))
                                  ,(fn2-columns-sym stub "-OPS-POOL") ,(fn2-columns-sym stub "-KEEPS-UNITS")))))
                (fn2-dfr-events (cdr names) world)))))))
(make-event (value (cons 'progn (fn2-dfr-events (fn2-machine-names (w state)) (w state)))))
