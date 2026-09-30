(in-package "ACL2")
(include-book "../../books/owner-obligation-recovery")
(include-book "owner-recovery-retain-tests")

(defconst *rovrt-rebuilt*
  (fn-owner-orcp-rebuild
   (list (fn-store-retention-event-make :undertake 0 0 0 "hold-a" "subject" "evidence-a" 10)
         (fn-store-retention-event-make :undertake 1 1 1 "hold-b" "subject" "evidence-b" 20))
   (list *fn-cfg-default-record*) 2 4))
(defconst *rovrt-oc* (nth 1 *rovrt-rebuilt*))
(assert-event (not (equal *rovrt-oc* :fault)))
(assert-event (equal (fn-rov-count (nth 6 *rovrt-rebuilt*)) 2))
(assert-event (equal (fn-rov-subject "subject" (nth 6 *rovrt-rebuilt*)) '(2 . 30)))

(in-theory (disable (:executable-counterpart fn-rov-correspondp)
                    (:executable-counterpart fn-vdc-correspondp)
                    (:executable-counterpart fn-rov-owner-correspondp)))

(defthm rovrt-positive-cold-install
  (and (not (equal *orr-oc* :fault))
       (fn-onb-open-okp (fn-ocfg-owner *orr-oc*))
       (fn-rov-owner-correspondp
        (mv-nth 5 (fn-owner-install-extended *orr-oc* (car *orc-carry-rebuilt*)
                   *orr-key* fn-arena fn-cat fn-hist state))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-owner-install-extended
                                      fn-rov-owner-correspondp))))

(defthm rovrt-positive-recovery-swap
  (and (fn-rov-correspondp (nth 6 *rovrt-rebuilt*)
          (fn-retain-pins (fn-rov-oc-ledger *rovrt-oc*)))
       (fn-rov-owner-correspondp
        (mv-nth 2 (fn-owner-orcp-swap *rovrt-rebuilt* state))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rov-build-corresponds
                         (pins (fn-retain-pins (fn-rov-oc-ledger *rovrt-oc*)))))
           :in-theory (e/d (fn-rov-oc-ledger)
                              (fn-owner-orcp-swap fn-rov-owner-correspondp fn-rov-correspondp)))))

; Corrupted rebuilt view retains the actual entry guard but violates the
; sole correspondence hypothesis and the full correspondence conclusion.
(defthm rovrt-corrupt-rebuilt-view
  (let ((bad (update-nth 6 '(100000 . nil) *rovrt-rebuilt*)))
    (and (true-listp bad)
         (not (fn-rov-correspondp (nth 6 bad)
                (fn-retain-pins (fn-rov-oc-ledger (nth 1 bad)))))
         (not (fn-rov-owner-correspondp
               (mv-nth 2 (fn-owner-orcp-swap bad state))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-rov-owner-correspondp fn-rov-correspondp fn-rov-oc-ledger)
                (fn-owner-orcp-swap fn-vdc-correspondp)))))

 ; Refusal is not initialization. Each omitted successful-arm hypothesis
; leaves the deliberately corrupt view in place; the other is affirmed.
(defthm rovrt-fault-removes-nonfault
  (let ((bad (fn-owner-obligation-view-put '(100000 . nil)
               (fn-owner-install-open-ocfg *orr-oc* state))))
    (and (equal :fault :fault)
         (fn-onb-open-okp (fn-ocfg-owner :fault))
         (not (fn-rov-owner-correspondp
          (mv-nth 5 (fn-owner-install-extended :fault nil *orr-key*
                     fn-arena fn-cat fn-hist bad))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-owner-install-extended fn-rov-owner-correspondp
                 fn-rov-correspondp fn-rov-oc-ledger)
                (fn-vdc-correspondp fn-owner-install-open-ocfg
                 fn-rov-owner-ledger-is-oc-ledger)))))

(defthm rovrt-damaged-numbers-remove-open-check
  (let ((bad (fn-owner-obligation-view-put '(100000 . nil)
               (fn-owner-install-open-ocfg *orr-oc* state))))
    (and (not (equal *orr-over-oc* :fault))
         (not (fn-onb-open-okp (fn-ocfg-owner *orr-over-oc*)))
         (not (fn-rov-owner-correspondp
          (mv-nth 5 (fn-owner-install-extended *orr-over-oc* nil *orr-key*
                     fn-arena fn-cat fn-hist bad))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-owner-install-extended fn-rov-owner-correspondp
                 fn-rov-correspondp fn-rov-oc-ledger)
                (fn-vdc-correspondp fn-owner-install-open-ocfg
                 fn-rov-owner-ledger-is-oc-ledger)))))

; These execute the actual guard-verified bodies with local concrete stobjs.
; The quantified relation is checked literally above, not evaluated here.
(defun rovrt-live-witness (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((saved (orr-save *orr-keys* state))
         (state (fn-owner-obligation-view-put '(100000 . nil) state)))
    (mv-let (opened state) (orr-open *orr-oc* state)
      (let ((cold (and (nth 0 opened) (nth 1 opened)
                       (nth 8 opened) (nth 9 opened) (not (nth 3 opened))
                       (equal (fn-owner-obligation-view state)
                              (fn-rov-build (fn-retain-pins (fn-rov-oc-ledger *orr-oc*)))))))
        (mv-let (swapped state) (orr-swap *rovrt-rebuilt* state)
          (let ((swap (and (nth 0 swapped) (not (nth 4 swapped))
                           (equal (fn-owner-obligation-view state) (nth 6 *rovrt-rebuilt*))
                           (equal (fn-rov-owner-ledger state) (fn-rov-oc-ledger *rovrt-oc*)))))
            (mv-let (bad state)
              (orr-swap (update-nth 6 '(100000 . nil) *rovrt-rebuilt*) state)
              (let* ((negative (and (nth 0 bad) (not (nth 4 bad))
                                    (not (equal (fn-rov-count (fn-owner-obligation-view state))
                                                (len (fn-retain-pins (fn-rov-owner-ledger state)))))))
                     (state (orr-restore saved state)))
                (mv (and cold swap negative) state)))))))))
(make-event
 (mv-let (ok state) (rovrt-live-witness state)
   (value (list 'assert-event ok))))
