; Receipt evidence in the post-crash suffix processed by the history translator.
(in-package "ACL2")
(include-book "../sim/check-history")
(include-book "recovery-receipt-history-proof")
(fn2-book-layer :b)

(defun fn2-rec-wrap-evidence (suffix)
 (declare (xargs :guard (true-listp suffix)))
 (if (endp suffix) nil
   (cons (list :evidence (car suffix)) (fn2-rec-wrap-evidence (cdr suffix)))))

; Rolling back to or past the submitted length cannot erase a batch.
; The log model rejects that observation and the translator returns no trace.
(defthm fn2-rec-translation-rejects-rollback-at-or-beyond-end
 (implies (and (fn2-lm-state-crashed (fn2-history-state-log-state s))
               (<= (len (fn2-lm-state-submitted (fn2-history-state-log-state s))) end))
          (equal (fn2-history-translate-loop (cons (list :evidence (list :rollback end)) rest) s)
                 (list :log-model-refused nil)))
 :rule-classes nil
 :hints (("Goal" :expand ((fn2-history-translate-loop (cons (list :evidence (list :rollback end)) rest) s))
          :in-theory (enable fn2-history-step fn2-history-emit fn2-lm-event-allowedp))))

(local
 (defthmd fn2-rec-output-trace-nth
 (equal (fn2-history-state-trace s) (nth 7 s))))

(local
 (defthm fn2-rec-translated-evidence-extends-trace
 (let ((step (fn2-history-step (list :evidence event) s)))
   (implies (equal (mv-nth 0 step) :ok)
            (equal (fn2-history-state-trace (mv-nth 1 step))
                   (cons event (fn2-history-state-trace s)))))
 :hints (("Goal" :in-theory (e/d (fn2-history-step fn2-history-emit fn2-rec-output-trace-nth nth-update-nth
                          update-fn2-history-state-trace update-fn2-history-state-log-state)
                         (fn2-lm-event-allowedp fn2-lm-step fn2-lm-state-crashed
                          fn2-history-state-log-state fn2-history-state-trace nth update-nth))))))

(local
 (defun fn2-rec-translation-induct (suffix s)
 (declare (xargs :verify-guards nil))
 (if (endp suffix) s
  (mv-let (code next) (fn2-history-step (list :evidence (car suffix)) s)
    (if (eq code :ok) (fn2-rec-translation-induct (cdr suffix) next) s)))))

(local
 (defthm fn2-rec-append-revappend
 (equal (append (revappend x a) y) (revappend x (append a y)))
 :hints (("Goal" :induct (revappend x a)))))

(local
 (defthm fn2-rec-reverse-cons-append
 (implies (true-listp x)
   (equal (append (reverse (cons e x)) y) (append (reverse x) (cons e y))))
 :hints (("Goal" :in-theory (enable reverse)))))

(local
 (defthm fn2-rec-reverse-append-nil
 (implies (true-listp x) (equal (append (reverse x) nil) (reverse x)))
 :hints (("Goal" :in-theory (enable reverse)))))

(defthm fn2-rec-wrapped-evidence-effects
 (implies (and (true-listp suffix) (true-listp (fn2-history-state-trace s))
               (equal (mv-nth 0 (fn2-history-translate-loop (fn2-rec-wrap-evidence suffix) s)) :ok))
          (equal (mv-nth 1 (fn2-history-translate-loop (fn2-rec-wrap-evidence suffix) s))
                 (append (reverse (fn2-history-state-trace s)) suffix)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-rec-translation-induct suffix s)
          :in-theory (e/d (fn2-rec-wrap-evidence fn2-history-translate-loop)
                       (reverse binary-append fn2-history-step fn2-history-state-trace)))))

(local
 (defthm fn2-rec-model-run-after-prefix
 (implies (true-listp prefix)
          (equal (fn2-lm-run (append prefix tail) s)
                 (fn2-lm-run tail (fn2-lm-run prefix s))))
 :hints (("Goal" :induct (fn2-lm-run prefix s)
                 :in-theory (disable fn2-lm-step)))))

(local
 (defthm fn2-rec-prefix-state-after-evidence
 (implies (true-listp prefix)
          (equal (fn2-lm-trace-state (append prefix tail))
                 (fn2-lm-run tail (fn2-lm-trace-state prefix))))
 :hints (("Goal" :in-theory '(fn2-lm-trace-state fn2-rec-model-run-after-prefix)))))

(local
 (defthm fn2-rec-reverse-list-type
 (implies (true-listp x) (true-listp (reverse x)))
 :hints (("Goal" :in-theory (enable reverse)))))

(defthm fn2-rec-successful-translation-retains-receipt
 (let* ((prefix (reverse (fn2-history-state-trace s)))
        (prior (fn2-lm-trace-state prefix))
        (receipt (list :present-frontier :receipt witness))
        (out (fn2-history-translate-loop (fn2-rec-wrap-evidence (cons receipt suffix)) s)))
  (implies (and (true-listp (fn2-history-state-trace s)) (true-listp suffix)
                (equal (mv-nth 0 out) :ok)
                (fn2-lm-state-valid prior) (fn2-lm-event-allowedp receipt prior)
                (not (member-eq :crash (strip-cars suffix))))
           (member-equal (cons :receipt witness)
                         (fn2-lm-state-witnesses (fn2-lm-trace-state (mv-nth 1 out))))))
 :rule-classes nil
 :hints (("Goal" :in-theory '(true-listp fn2-rec-prefix-state-after-evidence fn2-rec-reverse-list-type)
          :use ((:instance fn2-rec-wrapped-evidence-effects
                  (suffix (cons (list :present-frontier :receipt witness) suffix)))
                (:instance fn2-rec-presented-receipt-survives-until-crash
                          (frontier witness) (s (fn2-lm-trace-state (reverse (fn2-history-state-trace s)))))))))

(defthm fn2-rec-translated-detection-has-conflicting-receipt
 (let* ((prior (fn2-lm-trace-state (reverse (fn2-history-state-trace s))))
        (receipt (list :present-frontier :receipt witness))
        (out (fn2-history-translate-loop (fn2-rec-wrap-evidence (cons receipt suffix)) s)))
  (implies (and (true-listp (fn2-history-state-trace s)) (true-listp suffix)
                (equal (mv-nth 0 out) :ok)
                (fn2-lm-state-valid prior) (fn2-lm-event-allowedp receipt prior)
                (not (member-eq :crash (strip-cars suffix)))
                (equal (nth (fn2-rec-witness-outcome assume witness (len recovered) matches)
                            *fn2-rec-witness-outcomes*) :rollback-detected))
           (and (fn2-rec-assumep assume *fn2-rec-assume-frontier*)
                (fn2-lm-conflicting-witness
                   (fn2-lm-state-witnesses (fn2-lm-trace-state (mv-nth 1 out))) recovered))))
 :rule-classes nil
 :hints (("Goal" :in-theory nil
          :use (fn2-rec-successful-translation-retains-receipt
                (:instance fn2-rec-trace-receipt-supports-detection
                 (trace (mv-nth 1 (fn2-history-translate-loop
                      (fn2-rec-wrap-evidence (cons (list :present-frontier :receipt witness) suffix)) s))))))))
