; Actual same-ticket publication entry. The sole selector owns the decision;
; this entry derives it from CURRENT rather than taking an event/Store result.
; The retained executor and bounded prepared wire producer are still absent.
; Named absence precedes every I/O and keeps the original typed reservation.
(in-package "ACL2")
(include-book "account-adoption-operation-host")

(defun fn-owner-account-adoption-publication-step
 (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (let* ((holder (fn-owner-account-adoption-operation state))
        (source (fn-cp-nth 2 holder))
        (kind (fn-cp-nth 0 (fn-cp-nth 3 holder)))
        (runtime-kind (if (eq kind :publish) :account-adoption-publish-e
                       :account-adoption-publish-c)))
  (mv-let (receipt-word token) (fn-owner-account-turn-receipt state)
   (if (not (and (fn-cado-widthp 14 holder)
                 (eq (fn-cp-nth 0 holder) :account-adoption-operation)
                 (member-eq kind '(:publish :configure))
                 (eq receipt-word :account-turn-reserved)
                 (fn-cado-receipt-coordinatep token)
                 (fn-cado-receipt-coordinatep (fn-cp-nth 13 holder))
                 (equal token (fn-cp-nth 13 holder))
                 (fn-owner-account-turn-current-bodyp :operation-select source
                    slot nonce fn-allocation-turn-slots fn-page-read-pool state)))
       (mv :refused :account-publication-source-changed
           fn-allocation-turn-slots fn-page-read-pool state)
    (mv-let (available family)
     (fn-owner-runtime-operation-source runtime-kind fn-page-read-pool state)
     (declare (ignore family))
     (if (not (eq available :runtime-operation-available))
         (mv :unavailable :account-publication-operation-unavailable
             fn-allocation-turn-slots fn-page-read-pool state)
      (mv-let (roles-word roles)
       (fn-owner-runtime-operation-role-table runtime-kind fn-page-read-pool state)
       (declare (ignore roles))
       (if (not (eq roles-word :runtime-operation-available))
           (mv :unavailable :account-publication-role-unavailable
               fn-allocation-turn-slots fn-page-read-pool state)
        (mv-let (resources-word resources)
         (fn-owner-runtime-operation-resources runtime-kind fn-page-read-pool state)
         (declare (ignore resources))
         ; Availability of a compiled recipe is not an executor/storage/wire
         ; receipt. E requires real SF :reserved + original writer backing,
         ; produced row/SAME token, bounded wire stage→HEP offer→admission
         ; Begin/Step→actual SF completion→HistoryCompleteCurrent. C requires
         ; a distinct configuration journal receipt. Neither producer exists
         ; in this cut, so no legacy whole RIS/hist-sync/finish is invoked.
         (mv :unavailable
             (if (not (eq resources-word :runtime-operation-available))
                 :account-publication-resources-unavailable
               (if (eq kind :publish) :account-publication-executor-missing
                 :account-configuration-destination-missing))
             fn-allocation-turn-slots fn-page-read-pool state))))))))))
