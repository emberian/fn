; Concrete one-row history boundary. Caller owns retained current-source
; custody and the genuine installed read turn; this function grants neither.
(in-package "ACL2")
(include-book "consumer-remote-scan")
(include-book "history-columns")

(defun fn-crph-tick (s current-key fn-hist)
 (declare (xargs :stobjs fn-hist :guard t))
 (let ((position (fn-cp-nth 5 s)))
  (if (and (equal (fn-cp-nth 1 s) current-key)
           (eq (fn-cp-nth 8 s) :read)
           (natp position) (< position (nfix (fn-cp-nth 7 s)))
           (< position (fn-hist-count fn-hist)))
      (fn-crps-tick s current-key (fn-hist-at position fn-hist))
    (fn-crps-tick s current-key nil))))

; Proof-only list observer; the served implementation never walks a prefix.
(defun fn-crph-reference (s current-key rows)
 (declare (xargs :guard t :verify-guards nil))
 (let ((position (fn-cp-nth 5 s)))
  (if (and (equal (fn-cp-nth 1 s) current-key)
           (eq (fn-cp-nth 8 s) :read)
           (natp position) (< position (nfix (fn-cp-nth 7 s)))
           (< position (len rows)))
      (fn-crps-tick s current-key (nth position rows))
    (fn-crps-tick s current-key nil))))

(defthm fn-crph-concrete-one-row-read-refines-complete-answer
 (equal (fn-crph-tick s current-key fn-hist)
        (fn-crph-reference s current-key fn-hist))
 :hints (("Goal" :in-theory (e/d (fn-crph-tick fn-crph-reference)
                                  (fn-crps-tick fn-cp-nth)))))

(in-theory (disable fn-crph-tick fn-crph-reference))
