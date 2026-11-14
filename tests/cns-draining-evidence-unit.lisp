; Formula evidence for the ORIGINAL counted CNS obligation. The complete
; logical input comes from actual admitted setup; no replacement obligation.
(in-package "ACL2")
(include-book "../books/square-evidence")
(include-book "cns-draining-contract-unit")

; A logical view of the actual endpoint carries its live guard and ABI.
; This refuses a changed calling convention instead of guessing a wrapper.
(make-event
 (let* ((world (w state))
        (guard (getpropc 'fn2-cns-run 'guard :missing world))
        (guard (sublis-var '((fn2-core . core)) guard)))
  (if (not (and (equal (getpropc 'fn2-cns-run 'formals nil world) '(id budget fn2-core))
                (equal (getpropc 'fn2-cns-run 'stobjs-in nil world) '(nil nil fn2-core))
                (equal (getpropc 'fn2-cns-run 'stobjs-out nil world) '(nil nil nil nil fn2-core))
                (getpropc 'fn2-cns-run 'unnormalized-body nil world)
                (eq (getpropc 'fn2-cns-run 'symbol-class nil world) :common-lisp-compliant)
                (not (equal guard :missing))))
      (er soft 'cns-draining-evidence "Actual CNS run ABI/guard unavailable.")
   (value
    `(defun-nx fn2-cns-draining-observed-guarded (id budget core)
      (declare (xargs :guard ,guard :verify-guards nil))
      (mv-let (b s d r after) (fn2-cns-run id budget core)
       (list b s d r after)))))))

; A conditional equation binds the very guard read above. The shared evidence
; generator must prove ORIGINAL-H => this domain, not add it as a premise.
(make-event
 (let* ((world (w state))
        (row (fn2-decl-row '(:square fn2-cns-draining-counted-independent) world))
        (formula (fn2-decl-statement-body (fn2-decl-get :statement row) world))
        (guard (getpropc 'fn2-cns-draining-observed-guarded 'guard nil world)))
  (mv-let (hyp conclusion) (fn2-evidence-parts formula)
   (declare (ignore hyp))
   (value
    `(defthm fn2-cns-draining-resultp-live-guard-correspondence
      (implies ,guard
       (equal ,conclusion
        (equal (fn2-cns-draining-observed-guarded id budget core)
               (fn2-cns-draining-expected id core))))
      :rule-classes nil
      :hints (("Goal" :use fn2-cns-draining-resultp-unfolds
               :in-theory
               (union-theories '(fn2-cns-draining-observed-guarded
                                 fn2-cns-draining-observed)
                               (theory 'minimal-theory)))))))))

; Add endpoint locators to the SAME original row; do not alter H/C or :proof.
(make-event
 (let ((row (fn2-decl-row '(:square fn2-cns-draining-counted-independent) (w state))))
  (value `(table fn2-squares 'fn2-cns-draining-counted-independent
           ',(fn2-decl-set :sides
               '(:concrete fn2-cns-draining-observed-guarded :reference fn2-cns-draining-expected)
               row)))))

(defun fn2-cns-draining-evidence-payload ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (payload fn2-core)
   (mv-let (ready id sibling fn2-core) (fn2-cns-drain-setup nil fn2-core)
    (mv (list ready id sibling (fn2-test-core-snapshot fn2-core)) fn2-core))
   payload)))
(make-event
 (let* ((payload (fn2-cns-draining-evidence-payload))
        (id (cadr payload)) (sibling (caddr payload)) (before (cadddr payload)))
  (if (not (and (car payload) (natp id) (natp sibling) (not (equal id sibling))))
      (er soft 'cns-draining-evidence "Actual served setup did not produce distinct CNS siblings.")
   (value `(progn
             (defconst *fn2-cns-draining-evidence-id* ',id)
             (defconst *fn2-cns-draining-evidence-sibling* ',sibling)
             (defconst *fn2-cns-draining-evidence-before* ',before))))))

; Execute the actual run, then the actual timer-clearing operation against
; the captured protected sibling. Preserve all four scalar outputs.
(make-event
 (value
  `(defun-nx fn2-cns-draining-observed-sibling-mutant (id budget core)
    (declare (xargs :guard
              ,(getpropc 'fn2-cns-draining-observed-guarded 'guard nil (w state))
              :verify-guards nil))
    (mv-let (b s d r after) (fn2-cns-run id budget core)
     (mv-let (ignored changed)
       (fn2-cns-clear-wait-timer *fn2-cns-draining-evidence-sibling* after)
      (declare (ignore ignored))
      (list b s d r changed))))))

; Logical wrappers are unfolded explicitly; the ground proof still has to
; establish the complete original live antecedent and five-value predicate.
(local (in-theory
         (disable (:executable-counterpart fn2-cns-draining-observed-guarded)
                  (:executable-counterpart fn2-cns-draining-observed-sibling-mutant))))
(make-event
 (let ((bindings (list (list 'id (list 'quote *fn2-cns-draining-evidence-id*))
                       (list 'budget ''4)
                       (list 'core (list 'quote *fn2-cns-draining-evidence-before*)))))
  (value
   (fn2-square-evidence-events-with-correspondence
    'fn2-cns-draining-counted-independent bindings
    (list :kind :mutation :at 'fn2-cns-draining-observed-guarded
          :replace 'fn2-cns-draining-observed-sibling-mutant :bindings bindings)
    'fn2-cns-draining-resultp-live-guard-correspondence nil (w state)))))
(fn2-assert-square-evidence fn2-cns-draining-counted-independent)
(assert-event
 (equal (fn2-decl-get :proof
          (fn2-decl-row '(:square fn2-cns-draining-counted-independent) (w state)))
        '(:owed)))
