; Proof-only abstraction. Full concatenation appears ONLY here, never in the
; source producer/driver. The exact certificate determines admission evidence.
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
; Actual FN-TCL-STEP-SOURCE calls this receiver for transferring segments.
; The only representation hypothesis is proper decoded data. No whole-state
; predicate is needed for this algebraic boundary; malformed data is a separate
; corrupted-state witness, never sanitized into durable acceptance.
(defthm fn-tcl-source-recv-segment-boundary
 (implies (true-listp (fn-tcl-xfer-segment-data m))
  (equal (fn-tcl-source-result-alpha (fn-tcl-recv-segment-source s m now))
         (fn-tcl-recv-segment s m now)))
 :hints (("Goal" :in-theory
  (enable fn-tcl-recv-segment-source fn-tcl-recv-segment
          fn-tcl-complete-source fn-tcl-complete fn-tcl-source-result-alpha
          fn-tcl-source-events-alpha fn-tcl-refuse fn-tcl-stage
          fn-tcl-broken-stream fn-tcl-send-event))))
