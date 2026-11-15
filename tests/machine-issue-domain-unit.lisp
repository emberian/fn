; The obsolete generic issue helper was unreachable in composition and could
; not satisfy zero-descriptor kinds. Actual continuations are kind-generated.
(in-package "ACL2")
(include-book "../books/assembly-callbacks-a")

(defun fn2-issue-domain-mentions (symbol tree)
 (declare (xargs :guard t))
 (if (atom tree) (equal symbol tree)
  (or (fn2-issue-domain-mentions symbol (car tree))
      (fn2-issue-domain-mentions symbol (cdr tree)))))
(defun fn2-issue-domain-callers (symbol world)
 (declare (xargs :verify-guards nil))
 (if (atom world) nil
  (let ((entry (car world)))
   (if (and (eq (cadr entry) 'unnormalized-body)
            (fn2-issue-domain-mentions symbol (cddr entry)))
       (cons (car entry) (fn2-issue-domain-callers symbol (cdr world)))
     (fn2-issue-domain-callers symbol (cdr world))))))
(assert-event
 (and (not (function-symbolp 'fn2-machine-issue-result (w state)))
      (not (fn2-decl-row '(:cost fn2-machine-issue-result) (w state)))
      (not (fn2-issue-domain-callers 'fn2-machine-issue-result (w state)))
      (not (fn2-issue-domain-mentions 'fn2-machine-issue-result
              (table-alist 'fn2-machine-arm-bodies (w state))))
      (not (fn2-issue-domain-mentions 'fn2-machine-issue-result
              (fn2-machine-run-arms (fn2-machine-names (w state)) 0 (w state))))
      (fn2-assert-compliant-p '(fn2-listener-run fn2-echo-run) (w state))))

; Evaluate the actual finish guard without calling FINISH outside its guard.
(make-event
 (value `(defun fn2-issue-domain-finish-guard
                 (id bytes steps descriptors runnable fn2-core)
           (declare (xargs :stobjs fn2-core :verify-guards nil)
                    (ignorable runnable))
           ,(getpropc 'fn2-machine-finish 'guard nil (w state)))))
(defun fn2-issue-domain-counterexample-core (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
      ; The old guard required only core shape, not an admitted kind domain.
      ; Change a valid directory row to the real zero-descriptor kind.
      (fn2-core
       (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
        (fn2-machines)
        (fn2-machines-set-kind 0 *fn2-tls-admit-kind* fn2-machines)
        fn2-core))
      (old-hyp (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                    (natp 0) (<= 0 *fn2-echo-run-bytes*)))
      (fn2-core (fn2-machine-write-pending 0 1 fn2-core))
      (fn2-core (fn2-machine-write-wait-reason 0 *fn2-wait-completion* fn2-core)))
  (mv (and old-hyp (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
           (fn2-machine-idp 0 fn2-core)
           (equal (fn2-machine-kind 0 fn2-core) *fn2-tls-admit-kind*)
           (not (fn2-issue-domain-finish-guard
                  0 0 *fn2-work-mailbox* 1 nil fn2-core)))
      fn2-core)))
(defun fn2-issue-domain-counterexample ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (ok fn2-core) (fn2-issue-domain-counterexample-core fn2-core) ok)))
(assert-event (fn2-issue-domain-counterexample))
