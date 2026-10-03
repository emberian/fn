; The actual native refusal/abort writers, including their full invariant
; and exact effects on a writer-built nonempty store. The model fixtures
; reach reservation and staging through the real log route.
(in-package "ACL2")
(include-book "../../books/owner-post-carried")
(include-book "owner-prepare-outcome-tests")

(defun opct-live-witness (oc abortp expected fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let* ((original-owner (if (boundp-global 'fn-owner state)
                             (fn-owner-ocfg state) nil))
         (original-carry (fn-owner-retain-carry state))
         (original-pending (if (boundp-global 'fn-owner-cat-pending state)
                               (f-get-global 'fn-owner-cat-pending state) nil))
         (state (fn-owner-install-ocfg oc state))
         (state (fn-owner-retain-carry-put nil state))
         (state (f-put-global 'fn-owner-cat-pending :held-row state))
         (before-invariant (fn-owner-retain-statep state))
         (before-carry (fn-owner-retain-carry state))
         (before-records (fn-sf-records (fn-sn-files (fn-sbud-oc-store oc)))))
    (mv-let (word next)
      (if abortp (fn-pout-known-abort oc fn-arena)
        (fn-pout-refuse-reservation oc fn-arena))
      (mv-let (erp actual state)
        (if abortp (fn-owner-known-abort fn-arena state)
          (fn-owner-refuse-reservation fn-arena state))
        (let* ((ok (and before-invariant
                        (fn-owner-retain-statep state)
                        (not erp) (equal actual expected) (equal actual word)
                        (equal (fn-owner-ocfg state) next)
                        (equal (fn-owner-retain-carry state) before-carry)
                        (equal (fn-sf-records (fn-sn-files
                                              (fn-owner-store state)))
                               before-records)
                        (equal (f-get-global 'fn-owner-cat-pending state)
                               (if (member-eq word '(:refused :aborted))
                                   nil :held-row))))
               (state (fn-owner-install-ocfg original-owner state))
               (state (fn-owner-retain-carry-put original-carry state))
               (state (f-put-global 'fn-owner-cat-pending original-pending state)))
          (mv ok fn-arena state))))))

; Positive literal theorem antecedent/conclusion, accepted resolution words,
; and reachable :fault arms: no reservation or no staged record.
(make-event
 (mv-let (ok fn-arena state)
   (opct-live-witness *lgt-reserved* nil :refused fn-arena state)
   (value (list 'assert-event ok))))
(make-event
 (mv-let (ok fn-arena state)
   (opct-live-witness *lgt-prepared* t :aborted fn-arena state)
   (value (list 'assert-event ok))))
(make-event
 (mv-let (ok fn-arena state)
   (opct-live-witness *lgt-oc0* nil :fault fn-arena state)
   (value (list 'assert-event ok))))
(make-event
 (mv-let (ok fn-arena state)
   (opct-live-witness *lgt-reserved* t :fault fn-arena state)
   (value (list 'assert-event ok))))

; The real stored history is nonempty; these are not empty-store witnesses.
(assert-event (consp (fn-sf-records (fn-sn-files (lgt-store *lgt-oc0*)))))
(assert-event (consp (fn-sf-records (fn-sn-files (lgt-store *lgt-prepared*)))))
