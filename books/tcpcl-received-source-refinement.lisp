; Proof-only abstraction. Full concatenation appears ONLY here, never in the
; source producer/driver. This proposed boundary is not admitted evidence.
(in-package "ACL2")
(include-book "tcpcl-received-source")
(set-verify-guards-eagerness 0)
(defun fn-tcl-source-events-alpha (events)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom events) nil
  (let ((event (car events)))
   (cons (if (eq (fn-cbor-ag-car event) :bundle-segments-received)
          (list :bundle-received (fn-cbor-ag-car (fn-cbor-ag-cdr event))
                (fn-tcl-concat-rev (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr event))) nil))
          event)
         (fn-tcl-source-events-alpha (cdr events))))))
(defun fn-tcl-source-result-alpha (result)
 (declare (xargs :guard t :verify-guards nil))
 (fn-tcl-make-result (fn-tcl-result-session result)
  (fn-tcl-source-events-alpha (fn-tcl-result-events result))
  (fn-tcl-result-unconsumed result)))
; Actual native source driver calls FN-TCL-STEP-SOURCE. The antecedent is the
; maintained valid session/message domain; acceptance and funding are separate.
(defthm fn-tcl-source-step-refines-session-step
 (implies (and (fn-tcl-sessionp s)
               (fn-tcl-messagep m (fn-tcl-segment-mru s))
               (fn-clock-timep now))
  (equal (fn-tcl-source-result-alpha (fn-tcl-step-source s m now))
         (fn-tcl-step s m now)))
 :hints (("Goal" :in-theory (enable fn-tcl-step-source fn-tcl-step
                  fn-tcl-recv-segment-source fn-tcl-recv-segment
                  fn-tcl-complete-source fn-tcl-complete
                  fn-tcl-source-result-alpha fn-tcl-source-events-alpha
                  fn-tcl-settle))))
