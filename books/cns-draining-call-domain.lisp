; The original counted application premise establishes the ACTUAL public
; run interface domain. No new premise or application discharge is added.
(in-package "ACL2")
(include-book "cns-draining-contract")

; These are the native selectors needed by the public guard, not a claim
; about snapshot validity, phase dispatch, contract acceptance or effects.
(defthm fn2-cns-draining-domain-native-id-kind
 (implies (and (fn2-corep core) (fn2-core-wfp core)
               (fn2-cns-draining-domainp id core))
  (and (fn2-machine-idp id core)
       (equal (fn2-machine-kind id core) *fn2-cns-kind*)))
 :hints (("Goal" :do-not-induct t
          :in-theory
          (e/d (fn2-cns-draining-domainp fn2-machine-idp
                fn2-machine-kind fn2-machine-kind-read-code
                fn2-machines-kind fn2-machines-rows fn2-core-machines
                fn2-cns-drain-child fn2-cns-drain-child-index
                fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index)
               (fn2-corep fn2-core-wfp fn2-cns-drain-releasablep
                fn2-pool-semanticp fn2-cns-draining-reservedp)))))

(defun fn2-cns-draining-call-domain-events (world)
 (declare (xargs :verify-guards nil))
 (let* ((row (fn2-decl-row '(:square fn2-cns-draining-counted-independent) world))
        (formula (fn2-decl-statement-body (fn2-decl-get :statement row) world))
        (guard (getpropc 'fn2-cns-run 'guard :missing world))
        (guard (sublis-var '((fn2-core . core)) guard)))
  (if (not (and (fn2-square-rowp 'fn2-cns-draining-counted-independent row world)
                (equal (fn2-decl-get :vars row) '(id budget core))
                (consp formula) (eq (car formula) 'implies) (equal (len formula) 3)
                (equal (getpropc 'fn2-cns-run 'formals nil world) '(id budget fn2-core))
                (equal (getpropc 'fn2-cns-run 'stobjs-in nil world) '(nil nil fn2-core))
                (equal (getpropc 'fn2-cns-run 'stobjs-out nil world) '(nil nil nil nil fn2-core))
                (getpropc 'fn2-cns-run 'unnormalized-body nil world)
                (eq (getpropc 'fn2-cns-run 'symbol-class nil world) :common-lisp-compliant)
                (not (equal guard :missing))
                (subsetp-eq (all-vars guard) '(id budget core))))
      '((make-event
         (er soft 'fn2-cns-draining-call-domain-events
             "Original counted statement or actual public run ABI/guard is unavailable.")))
   `((defthm fn2-cns-draining-original-h-implies-run-guard
       (implies ,(cadr formula) ,guard)
       :rule-classes nil
       :hints (("Goal" :do-not-induct t
                :in-theory
                (disable fn2-corep fn2-core-wfp fn2-cns-draining-domainp
                         fn2-cns-draining-reservedp fn2-pool-semanticp))))))))
(make-event (value (cons 'progn (fn2-cns-draining-call-domain-events (w state)))))
