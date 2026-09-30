; Internal exact registered-segment job issue. Parent must fetch this child
; from the controller token and persist it with the SAME pool atomically.
; Supplied demand is not a constructor census or native allocation authority.
(in-package "ACL2")
(include-book "bp-controller-registry")
(include-book "bp-controller-checkpoint-operation")
(include-book "page-read-ledger")
(local (include-book "arithmetic-5/top" :dir :system))
(defun fn-bpcc-job-tokenp (token)
  (declare (xargs :guard t))
  (and (consp token) (eq (car token) :bp-job)
       (consp (cdr token)) (natp (cadr token))
       (consp (cddr token)) (fn-bpc-tokenp (caddr token))
       (consp (cdddr token)) (natp (cadddr token))
       (consp (cddddr token)) (natp (car (cddddr token)))
       (null (cdr (cddddr token)))))
; Pending job4: typed token, exact resource claim, phase, borrowed CURRENT.
; CURRENT cannot be replaced while this row exists, including cancellation.
(defun fn-bpcc-segment-reserve (controller slot demand ledger fn-bpc-segment)
  (declare (xargs :stobjs fn-bpc-segment
                  :guard (and (natp slot) (< slot 64))))
  (let* ((row (fn-bpcs-rowsi slot fn-bpc-segment))
         (current (fn-bpn-nth 2 row)))
    (cond ((not (and (fn-bpc-tokenp controller)
                     (equal (mod (caddr controller) 64) slot)
                     (fn-bpc-row-livep (cadr controller) row)))
           (mv :stale-controller nil ledger fn-bpc-segment))
          ((fn-bpn-nth 4 row)
           (mv :controller-busy nil ledger fn-bpc-segment))
          ((not (fn-bpco-checkpoint-operation-p current))
           (mv :checkpoint-unavailable nil ledger fn-bpc-segment))
          ((not (and (fn-prs-vectorp demand)
                     (equal (fn-prl-nth 4 demand) 1)))
           (mv :invalid-checkpoint-demand nil ledger fn-bpc-segment))
          (t
           (mv-let (word next charged)
             (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                           '(0 0 0 0 0) (fn-prl-nth 1 ledger)
                           (fn-prl-nth 2 ledger)
                           (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
             (if (not (eq word :admitted))
                 (mv word nil ledger fn-bpc-segment)
               (let* ((token (list :bp-job (fn-prl-nth 2 ledger) controller
                                   (fn-bpco-checkpoint-epoch current)
                                   (fn-bpco-checkpoint-generation current)))
                      (job (list token demand :reserved current))
                      (ledger1 (fn-prl-build (fn-prl-nth 0 ledger) charged next
                                  (fn-prl-nth 3 ledger) (fn-prl-baseline ledger)))
                      (fn-bpc-segment
                       (update-fn-bpcs-rowsi slot
                         (list (fn-bpn-nth 0 row) (fn-bpn-nth 1 row) current
                               (fn-bpn-nth 3 row) job) fn-bpc-segment)))
                 (mv :checkpoint-reserved token ledger1 fn-bpc-segment))))))))
; Cancellation is retained ownership, never settlement or a refund. Parent
; derives the exact child from the registered controller, not a host row copy.
(defun fn-bpcc-segment-cancel (token slot fn-bpc-segment)
  (declare (xargs :stobjs fn-bpc-segment
                  :guard (and (natp slot) (< slot 64))))
  (let* ((row (fn-bpcs-rowsi slot fn-bpc-segment))
         (job (fn-bpn-nth 4 row)))
    (cond ((not (and (fn-bpcc-job-tokenp token)
                     (equal token (fn-bpn-nth 0 job))
                     (equal (mod (caddr (caddr token)) 64) slot)
                     (fn-bpc-row-livep (cadr (caddr token)) row)))
           (mv :stale-checkpoint fn-bpc-segment))
          ((eq (fn-bpn-nth 2 job) :cancelled)
           (mv :checkpoint-retained fn-bpc-segment))
          (t (let ((fn-bpc-segment
                    (update-fn-bpcs-rowsi slot
                      (list (fn-bpn-nth 0 row) (fn-bpn-nth 1 row)
                            (fn-bpn-nth 2 row) (fn-bpn-nth 3 row)
                            (list token (fn-bpn-nth 1 job) :cancelled
                                  (fn-bpn-nth 3 job))) fn-bpc-segment)))
               (mv :checkpoint-retained fn-bpc-segment))))))
(verify-guards fn-bpcc-job-tokenp)
(verify-guards fn-bpcc-segment-reserve)
(verify-guards fn-bpcc-segment-cancel)
