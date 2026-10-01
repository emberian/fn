; Actual shared-PRS report identity. Installed complete report recipe remains
; unavailable; this source adds no numeric budget or arbitrary job setter.
(in-package "ACL2")
(include-book "owner-report-capture")
(include-book "owner-inspect-operation")
(include-book "page-read-pool-state")

(defun fn-orc-report-source (fn-page-read-pool state)
  (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
  (mv-let (word source)
    (fn-owner-runtime-operation-resources :owner-control-inspect fn-page-read-pool state)
    (if (and (eq word :runtime-operation-available)
             (true-listp source) (equal (len source) 4)
             (eq (car source) :inspect-report-source)
             (fn-prs-vectorp (nth 1 source))
             (equal (fn-prl-nth 4 (nth 1 source)) 1)
             (fn-prs-vectorp (nth 2 source)))
        (mv :report-source (nth 1 source) (nth 2 source))
      (mv :report-source-unavailable nil nil))))

; Internal upper producer captures original inputs before this call. Their
; construction and retained lifetime must belong to the actual compiled
; source recipe. No native callback accepts CAPTURE/CURSOR/DEMAND as a grant.
(defun fn-orc-reserve-internal
  (request cached kind capture cursor slot nonce fn-allocation-turn-slots
           fn-page-read-pool state)
  (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                  :guard t))
  (cond ((fn-orc-job state)
         (mv :report-busy nil fn-page-read-pool state))
        ((not (and (equal (fn-orc-source state) :stable)
                   (fn-aec-pool-statep fn-page-read-pool)
                   (fn-ats-role-bodyp slot nonce :owner-control
                                     fn-allocation-turn-slots fn-page-read-pool)))
         (mv :report-source-unavailable nil fn-page-read-pool state))
        (t
         (mv-let (source-word demand rescue) (fn-orc-report-source fn-page-read-pool state)
           (if (not (eq source-word :report-source))
               (mv source-word nil fn-page-read-pool state)
             (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
                    (budget (fn-prl-nth 0 ledger))
                    ; This intent's construction is already covered by the
                    ; actual BODY. It holds all inputs across a debit escape;
                    ; it does not yet contain or expose a report identity.
                    (state (f-put-global 'fn-owner-report-job
                             (list :owner-report-reserving nil kind request cached
                                   capture cursor :reserving (fn-prl-nth 2 ledger)
                                   demand) state)))
               (mv-let (word issued charged)
                 (fn-prs-issue budget (fn-prl-baseline ledger) rescue
                               (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
                               (fn-prl-nth 4 budget) demand)
                 (if (not (eq word :admitted))
                     (let ((state (f-put-global 'fn-owner-report-job nil state)))
                       (mv word nil fn-page-read-pool state))
                   ; Debit before any new identity/capture record. Escape
                   ; after this point is recovery, never silent retry/refund.
                   (let* ((fn-page-read-pool
                           (fn-owner-page-read-keep-ledger
                             (fn-prl-build budget charged issued (fn-prl-nth 3 ledger)
                                           (fn-prl-baseline ledger)) fn-page-read-pool))
                          (token (list :owner-report issued))
                          (state (f-put-global 'fn-owner-report-job
                                   (list :owner-report token kind request cached
                                         capture cursor :valid nil demand) state)))
                     (mv :report-reserved token fn-page-read-pool state))))))))))
