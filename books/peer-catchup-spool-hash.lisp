; Actual private byte digest cursor used on the immutable normalized spool.
(in-package "ACL2")
(include-book "extent-window-stream")

(defun fn-csp-hash-begin (total lease pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (natp total)))
  (pgs-dcb-begin 0 0 total (list :catchup total) lease pgs-digest-state))

(defun fn-csp-hash-boundp (total lease pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (natp total)))
  (and (equal (pgs-dc-capture pgs-digest-state) (list :catchup total))
       (equal (pgs-dc-lease pgs-digest-state) lease)
       (equal (pgs-dc-total pgs-digest-state) (pgs-dcb-word-count total))
       (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
       (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
       (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
       (<= (* 8 (pgs-dc-pos pgs-digest-state)) total)))

(defun fn-csp-hash-action (total base lease pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (and (natp total) (natp base))))
  (cond ((not (fn-csp-hash-boundp total lease pgs-digest-state)) '(:refused))
        ((eq (pgs-dc-mode pgs-digest-state) :done)
         (list :done (pgs-dcb-result-octets pgs-digest-state)))
        ((pgs-dc-needs-block pgs-digest-state)
         (list :read (+ base (pgs-dcb-next-byte-offset pgs-digest-state))
               (pgs-dcb-read-demand total pgs-digest-state)))
        (t '(:tick))))

(defun fn-csp-hash-tick (total lease pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (natp total) :verify-guards nil))
  (if (or (not (fn-csp-hash-boundp total lease pgs-digest-state))
          (pgs-dc-needs-block pgs-digest-state)
          (eq (pgs-dc-mode pgs-digest-state) :done))
      (mv :refused pgs-digest-state)
    (pgs-dcb-step total nil pgs-digest-state)))

(verify-guards fn-csp-hash-tick :hints (("Goal" :in-theory (enable fn-csp-hash-boundp))))

(defun fn-csp-hash-read (total lease status count fn-octets pgs-digest-state)
  (declare (xargs :stobjs (fn-octets pgs-digest-state)
                  :guard (and (natp total) (natp count)) :verify-guards nil))
  (let ((demand (pgs-dcb-read-demand total pgs-digest-state)))
    (if (or (not (fn-csp-hash-boundp total lease pgs-digest-state))
            (not (pgs-dc-needs-block pgs-digest-state))
            (not (eq status :ok)) (not (equal count demand))
            (not (equal (fn-octets-len fn-octets) count)))
        (mv :refused pgs-digest-state)
      (pgs-dcb-step total (fn-b3x-words 16 0 demand nil 0 0 fn-octets)
                    pgs-digest-state))))

(verify-guards fn-csp-hash-read
 :hints (("Goal" :in-theory (enable fn-csp-hash-boundp)
                   :use pgs-dcb-read-demand-is-bounded)))

(defthm fn-csp-hash-action-read-bounded
  (implies (eq (car (fn-csp-hash-action total base lease pgs-digest-state)) :read)
           (<= (caddr (fn-csp-hash-action total base lease pgs-digest-state)) 64))
  :hints (("Goal" :in-theory (enable fn-csp-hash-action)))
  :rule-classes nil)

(in-theory (disable fn-csp-hash-begin fn-csp-hash-boundp fn-csp-hash-action
                    fn-csp-hash-tick fn-csp-hash-read))
