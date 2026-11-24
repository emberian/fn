; Logical view of all principal request FIFOs. The executor does not walk
; queues to grant a request.
(in-package "ACL2")
(include-book "accounts")
(include-book "machines-directory")

; SEEN contains rows already visited in this or an earlier principal's FIFO.
; At end of chain PREV must be the recorded tail, including for an empty FIFO.
(defun fn2-account-fifo-visit (fuel id prev tail seen fn2-machines)
  (declare (xargs :stobjs fn2-machines :measure (nfix fuel)
                  :guard (and (natp fuel) (fn2-machines-wfp fn2-machines) (true-listp seen))))
  (cond ((equal id *fn2-none*) (if (equal prev tail) seen :invalid))
        ((or (zp fuel) (not (and (natp id) (< id (fn2-machines-rows fn2-machines))))
             (member-equal id seen)
             (not (equal (fn2-machines-ready-prev id fn2-machines) prev))
             (not (equal (fn2-machines-wait-reason id fn2-machines)
                         *fn2-wait-principal-reservation*)))
         :invalid)
        (t (fn2-account-fifo-visit (- fuel 1) (fn2-machines-ready-next id fn2-machines)
                                   id tail (cons id seen) fn2-machines))))

(defthm fn2-account-fifo-visit-list
  (implies (and (true-listp seen)
                (not (equal (fn2-account-fifo-visit fuel id prev tail seen fn2-machines) :invalid)))
           (true-listp (fn2-account-fifo-visit fuel id prev tail seen fn2-machines)))
  :rule-classes :rewrite)

(defun fn2-account-fifos-visit (rows seen fn2-accounts fn2-machines)
  (declare (xargs :stobjs (fn2-accounts fn2-machines) :measure (nfix rows)
                  :guard (and (fn2-accounts-wfp fn2-accounts)
                              (fn2-machines-wfp fn2-machines)
                              (true-listp seen) (natp rows) (<= rows (fn2-accounts-rows fn2-accounts)))))
  (if (zp rows) seen
    (let* ((p (- rows 1))
           (visited (fn2-account-fifo-visit
                     (fn2-machines-rows fn2-machines) (fn2-accounts-wait-head p fn2-accounts)
                     *fn2-none* (fn2-accounts-wait-tail p fn2-accounts) seen fn2-machines)))
      (if (eq visited :invalid) :invalid
        (fn2-account-fifos-visit p visited fn2-accounts fn2-machines)))))
