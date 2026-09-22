; Executable finite-trace scenarios for the immutable-file storage kernel.
(in-package "ACL2")
(include-book "../../books/store-files-traces")
(include-book "../../books/codec-attach")

(defconst *sf-trace-groups* '("fn.letters" "fn.test"))

(defconst *sf-trace-record-0*
  (fn-record-make 0 0 0 "<trace-zero@example.invalid>" '(90)
                  '("fn.letters" "fn.test")
                  "trace-archive-zero" "trace-content-zero"
                  "trace-release-zero" 2))

(defconst *sf-trace-record-1*
  (fn-record-make 1 1 1 "<trace-one@example.invalid>" '(79)
                  '("fn.letters")
                  "trace-archive-one" "trace-content-one"
                  "trace-release-one" 1))

(defconst *sf-trace-record-2*
  (fn-record-make 2 2 2 "<trace-two@example.invalid>" '(84)
                  '("fn.test")
                  "trace-archive-two" "trace-content-two"
                  "trace-release-two" 1))

; Establish one emitted success.  Configuration is stored once in the trace;
; prepare and recovery events carry no alternate groups or capacity.
(defconst *sf-trace-first*
  (fn-sf-trace-make
   *sf-trace-groups* 10
   (list '(:start-frontier)
         '(:frontier-file :ok)
         '(:frontier-replace :ok)
         '(:frontier-dir :ok)
         (list :prepare-record *sf-trace-record-0*)
         '(:record-file :ok)
         '(:record-link :ok)
         '(:record-dir :ok)
         '(:core-completion 0 0)
         '(:emit-success 0 0))))

(assert-event (fn-sf-tracep *sf-trace-first*))
(defconst *sf-trace-after-first*
  (fn-sf-run-trace (fn-sf-initial-state) *sf-trace-first*))
(assert-event (fn-sf-statep *sf-trace-after-first*))
(assert-event (equal (fn-sf-successes *sf-trace-after-first*)
                     (list (cons 0 0))))

; Two more crash/recovery cycles follow.  The first publishes and acknowledges
; record 1.  The second dies in :record-data-durable, after the record file
; barrier but before any link result was observed (the final-link cut of
; tests/store_crash_child.py), and selects the exact present candidate, so
; recovery retains an unacknowledged tail while both earlier emitted successes
; remain covered.
(defconst *sf-trace-repeated*
  (fn-sf-trace-make
   *sf-trace-groups* 10
   (list '(:crash :old :absent)
         '(:recover)
         '(:recovery-barrier :ok)
         '(:recovery-barrier :ok)
         '(:recovery-barrier :ok)
         '(:recovery-barrier :ok)
         '(:recovery-barrier :ok)
         '(:start-frontier)
         '(:frontier-file :ok)
         '(:frontier-replace :ok)
         '(:frontier-dir :ok)
         (list :prepare-record *sf-trace-record-1*)
         '(:record-file :ok)
         '(:record-link :ok)
         '(:record-dir :ok)
         '(:core-completion 1 1)
         '(:emit-success 1 1)
         '(:start-frontier)
         '(:frontier-file :ok)
         '(:frontier-replace :ok)
         '(:frontier-dir :ok)
         (list :prepare-record *sf-trace-record-2*)
         '(:record-file :ok)
         '(:crash :old :present)
         '(:recover)
         '(:recovery-barrier :ok)
         '(:recovery-barrier :ok)
         '(:recovery-barrier :ok)
         '(:recovery-barrier :ok)
         '(:recovery-barrier :ok))))

(assert-event (fn-sf-tracep *sf-trace-repeated*))
(defconst *sf-trace-final*
  (fn-sf-run-trace *sf-trace-after-first* *sf-trace-repeated*))
(assert-event (fn-sf-statep *sf-trace-final*))
(assert-event (equal (fn-sf-phase *sf-trace-final*) :ready))
(assert-event (equal (fn-sf-records *sf-trace-final*)
                     (list *sf-trace-record-0*
                           *sf-trace-record-1*
                           *sf-trace-record-2*)))
(assert-event (equal (fn-sf-successes *sf-trace-final*)
                     (list (cons 0 0) (cons 1 1))))

; The external claim is deliberately conditional: this list represents only
; successes the environment says were actually emitted before the second trace,
; and it must be covered by the starting state's ghost history.
(defconst *sf-trace-prior-emitted* (list (cons 0 0)))
(assert-event
 (fn-sf-ghost-covers-emittedp *sf-trace-prior-emitted*
                              (fn-sf-successes *sf-trace-after-first*)))
(assert-event
 (fn-sf-record-has-pairp (cons 0 0) (fn-sf-records *sf-trace-final*)))
