; Observed-file recovery model for the FNBS creation-sequence frontier.
;
; This is deliberately a model of the files the native host actually reads.
; It does not retain a hidden "rename completed" bit across restart.  A staged
; residue leaves the old final observable; a visible rename makes the new
; final observable.  `confirmed' is a ghost recording only the documented
; directory-fsync physical assumption after a reservation was returned.

(in-package "ACL2")
(include-book "bp-node-records")
(local (include-book "arithmetic/top" :dir :system))

; Observations correspond to the three inputs given to fn-bpn-sequence-recover.
(defun fn-bpn-sf-observationp (x)
  (declare (xargs :guard t))
  (or (equal x :absent) (equal x :malformed)
      (and (true-listp x) (equal (len x) 2) (equal (car x) :valid)
           (fn-bpn-sequence-frontierp (cadr x)))))

(defun fn-bpn-sf-validp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2) (equal (car x) :valid)
       (fn-bpn-sequence-frontierp (cadr x))))

(defun fn-bpn-sf-observed-frontier (x)
  (declare (xargs :guard (fn-bpn-sf-validp x)))
  (cadr x))

; The model delegates the recover decision to the same ACL2 function the host
; calls.  Valid observations are framed by ACL2; malformed is one invalid byte.
(defun fn-bpn-sf-host-recover (observation freshp)
  ;; The concrete frame function's octet-list guard correspondence is not yet
  ;; exported by bp-node-records.  Keep this boundary executable and pin it
  ;; with ground tests; W14 must export that bridge before claiming a fully
  ;; guard-verified correspondence.
  (declare (xargs :guard (fn-bpn-sf-observationp observation)
                  :verify-guards nil))
  (cond ((equal observation :absent)
         (fn-bpn-sequence-recover nil nil freshp))
        ((equal observation :malformed)
         (fn-bpn-sequence-recover '(0) t freshp))
        (t (fn-bpn-sequence-recover
            (fn-bpn-sequence-record-frame
             (fn-bpn-sequence-record (fn-bpn-sf-observed-frontier observation)))
            t freshp))))

; (tag root-parent sequence-parent fresh observed ready frontier confirmed
;      pending authored-rev fenced staged)
(defun fn-bpn-sf-state (root sequence fresh observed ready frontier confirmed
                         pending authored fenced staged)
  (declare (xargs :guard t))
  (list :bpn-sequence-fidelity root sequence fresh observed ready frontier
        confirmed pending authored fenced staged))

(defun fn-bpn-sf-nth (n s)
  (declare (xargs :guard t))
  (if (true-listp s) (nth n s) nil))
(defun fn-bpn-sf-rootp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 1 s))
(defun fn-bpn-sf-sequencep (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 2 s))
(defun fn-bpn-sf-freshp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 3 s))
(defun fn-bpn-sf-observed (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 4 s))
(defun fn-bpn-sf-readyp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 5 s))
(defun fn-bpn-sf-frontier (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 6 s))
(defun fn-bpn-sf-confirmed (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 7 s))
(defun fn-bpn-sf-pending (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 8 s))
(defun fn-bpn-sf-authored (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 9 s))
(defun fn-bpn-sf-fencedp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 10 s))
(defun fn-bpn-sf-stagedp (s) (declare (xargs :guard t)) (fn-bpn-sf-nth 11 s))

(defun fn-bpn-sf-statep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 12)
       (equal (car s) :bpn-sequence-fidelity)
       (booleanp (fn-bpn-sf-rootp s)) (booleanp (fn-bpn-sf-sequencep s))
       (booleanp (fn-bpn-sf-freshp s))
       (fn-bpn-sf-observationp (fn-bpn-sf-observed s))
       (booleanp (fn-bpn-sf-readyp s))
       (fn-bpn-sequence-frontierp (fn-bpn-sf-frontier s))
       (fn-bpn-sequence-frontierp (fn-bpn-sf-confirmed s))
       (or (null (fn-bpn-sf-pending s))
           (fn-bpn-sequence-frontierp (fn-bpn-sf-pending s)))
       (true-listp (fn-bpn-sf-authored s))
       (booleanp (fn-bpn-sf-fencedp s)) (booleanp (fn-bpn-sf-stagedp s))))

(defun fn-bpn-sf-initial ()
  (declare (xargs :guard t))
  (fn-bpn-sf-state nil nil nil :absent nil 0 0 nil nil nil nil))

(defun fn-bpn-sf-authors-belowp (xs n)
  (declare (xargs :guard t))
  (if (not (rationalp n)) nil
    (if (consp xs) (and (natp (car xs)) (< (car xs) n)
                        (fn-bpn-sf-authors-belowp (cdr xs) n))
      (null xs))))

; This is the physical assumption, not a native check: after a returned
; reservation, a later observed valid final cannot precede CONFIRMED.
(defun fn-bpn-sf-observation-admissiblep (s observation)
  (declare (xargs :guard (and (fn-bpn-sf-statep s)
                              (fn-bpn-sf-observationp observation))))
  (cond ((fn-bpn-sf-validp observation)
         (<= (fn-bpn-sf-confirmed s)
             (fn-bpn-sf-observed-frontier observation)))
        ((equal observation :absent)
         (and (fn-bpn-sf-freshp s) (equal (fn-bpn-sf-confirmed s) 0)))
        (t t)))

(defun fn-bpn-sf-safep (s)
  (declare (xargs :guard t))
  (and (fn-bpn-sf-statep s)
       (no-duplicatesp-equal (fn-bpn-sf-authored s))
       (fn-bpn-sf-authors-belowp (fn-bpn-sf-authored s)
                                  (fn-bpn-sf-confirmed s))
       (or (null (fn-bpn-sf-pending s))
           (and (fn-bpn-sf-readyp s)
                (< (fn-bpn-sf-pending s) (fn-bpn-sf-confirmed s))))))

; TODO W14 checkpoint: complete the host-observation transition and trace
; theorem here.  The representation and host-recovery boundary above are the
; committed fidelity replacement for the former restart phase-bit premise.
