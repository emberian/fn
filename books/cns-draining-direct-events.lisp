; Proof instances for the actual direct draining body's effect calls.
; The model is unchanged: live terms supply only call arguments and hints.
(in-package "ACL2")
(include-book "core-product-lowering")

(defun fn2-cns-draining-writerp (fn)
  (declare (xargs :verify-guards nil))
  (and (symbolp fn)
       (<= 14 (length (symbol-name fn)))
       (equal (subseq (symbol-name fn) 0 14) "FN2-CNS-WRITE+")))
(defun fn2-cns-draining-effectp (fn)
  (member-eq fn '(fn2-cns-run fn2-core-release fn2-cns-release-ns fn2-cns-lease-release
                 fn2-cns-clear-wait-timer fn2-cns-query-heldp fn2-cns-reclaim)))
(defun fn2-cns-draining-effect-aritiesp (calls)
  (declare (xargs :verify-guards nil))
  (if (atom calls) t
    (and (case (caar calls)
           ((fn2-core-release fn2-cns-release-ns fn2-cns-lease-release)
            (equal (len (car calls)) 7))
           ((fn2-cns-clear-wait-timer fn2-cns-query-heldp) (equal (len (car calls))
              (if (eq (caar calls) 'fn2-cns-query-heldp) 4 3)))
           (fn2-cns-reclaim (equal (len (car calls)) 5))
           (otherwise (fn2-cns-draining-writerp (caar calls))))
         (fn2-cns-draining-effect-aritiesp (cdr calls)))))

; Follow lexical bindings without opening any named operation. Every
; collected argument is expressed in the original ID/BUDGET/CORE inputs.
; This retains the actual intermediate state at the timer and reclaim calls.
(mutual-recursion
 (defun fn2-cns-draining-call-sites (term env)
  (declare (xargs :verify-guards nil :measure (acl2-count term)))
  (cond ((or (atom term) (eq (car term) 'quote)) nil)
        ((consp (car term))
         (append
          (fn2-cns-draining-call-sites-list (cdr term) env)
          (fn2-cns-draining-call-sites
           (caddar term)
           (append (pairlis$ (cadar term) (sublis-var-lst env (cdr term))) env))))
        (t (append
            (and (or (fn2-cns-draining-effectp (car term))
                     (fn2-cns-draining-writerp (car term)))
                 (list (sublis-var env term)))
            (fn2-cns-draining-call-sites-list (cdr term) env)))))
 (defun fn2-cns-draining-call-sites-list (terms env)
  (declare (xargs :verify-guards nil :measure (acl2-count terms)))
  (if (atom terms) nil
    (append (fn2-cns-draining-call-sites (car terms) env)
            (fn2-cns-draining-call-sites-list (cdr terms) env)))))
(defun fn2-cns-draining-calls-of (fn calls)
  (declare (xargs :verify-guards nil))
  (if (atom calls) nil
    (append (and (eq fn (caar calls)) (list (car calls)))
            (fn2-cns-draining-calls-of fn (cdr calls)))))
(defun fn2-cns-draining-sites-closedp (calls)
  (declare (xargs :verify-guards nil))
  (if (atom calls) t
    (and (subsetp-eq (fn2-lower-vars (car calls)) '(id budget core))
         (fn2-cns-draining-sites-closedp (cdr calls)))))

(defun fn2-cns-draining-release-instance (theorem args)
  (declare (xargs :verify-guards nil))
  `(:instance ,theorem (slot ,(nth 0 args)) (gen ,(nth 1 args))
              (id ,(nth 3 args)) (ogen ,(nth 4 args)) (core ,(nth 5 args))))
(defun fn2-cns-draining-release-uses (call)
  (declare (xargs :verify-guards nil))
  (let ((args (cdr call)))
    (append
     (and (eq (car call) 'fn2-cns-lease-release)
          `((:instance fn2-cns-lease-release-is-core-release-by-definition
              (slot ,(nth 0 args)) (gen ,(nth 1 args)) (kind ,(nth 2 args))
              (id ,(nth 3 args)) (ogen ,(nth 4 args)) (core ,(nth 5 args)))))
     (and (eq (car call) 'fn2-cns-release-ns)
          (list (fn2-cns-draining-release-instance
                 'fn2-cns-release-ns-independent-by-definition args)))
     (list (fn2-cns-draining-release-instance 'fn2-cns-core-release-independent args)
           (fn2-cns-draining-release-instance 'fn2-cns-owned-core-release-pool-effect args)
           (fn2-cns-draining-release-instance 'fn2-cns-owned-core-release-pool-accounting args)
           `(:instance fn2-cns-core-release-protected-children
              (slot ,(nth 0 args)) (gen ,(nth 1 args)) (kind ,(nth 2 args))
              (id ,(nth 3 args)) (ogen ,(nth 4 args)) (core ,(nth 5 args)))))))
(defun fn2-cns-draining-effect-uses (calls)
  (declare (xargs :verify-guards nil))
  (if (atom calls) nil
    (let* ((call (car calls)) (fn (car call)) (args (cdr call)))
      (append
       (cond ((member-eq fn '(fn2-core-release fn2-cns-release-ns fn2-cns-lease-release))
              (fn2-cns-draining-release-uses call))
             ((eq fn 'fn2-cns-query-heldp)
              `((:instance fn2-cns-query-held-independent
                  (slot ,(nth 0 args)) (gen ,(nth 1 args)) (core ,(nth 2 args)))))
             ((eq fn 'fn2-cns-clear-wait-timer)
              `((:instance fn2-cns-clear-wait-timer-independent
                  (id ,(nth 0 args)) (core ,(nth 1 args)))))
             ((eq fn 'fn2-cns-reclaim)
              `((:instance fn2-cns-core-reclaim-independent
                  (id ,(nth 0 args)) (ord ,(nth 1 args))
                  (retire ,(nth 2 args)) (core ,(nth 3 args)))))
             (t nil))
       (fn2-cns-draining-effect-uses (cdr calls))))))

; This is the actual WS result consumed by NS, not a model state substituted
; for it. Conservation and distinct-row admission apply before opening NS.
(defun fn2-cns-draining-second-statep (ws ns)
  (declare (xargs :verify-guards nil))
  (equal (nth 5 (cdr ns)) `(mv-nth '1 ,ws)))
(defun fn2-cns-draining-second-release-uses (ws ns)
  (declare (xargs :verify-guards nil))
  (let ((a (cdr ws)) (b (cdr ns)))
    `((:instance fn2-cns-distinct-releasable-after-core-release
        (slot ,(nth 0 a)) (gen ,(nth 1 a))
        (other ,(nth 0 b)) (other-gen ,(nth 1 b))
        (id ,(nth 3 a)) (ogen ,(nth 4 a)) (core ,(nth 5 a)))
      (:instance fn2-cns-independent-release-keeps-second-releasable
        (slot ,(nth 0 a)) (gen ,(nth 1 a))
        (other ,(nth 0 b)) (other-gen ,(nth 1 b))
        (id ,(nth 3 a)) (ogen ,(nth 4 a))
        (pool (fn2-core-pool ,(nth 5 a))))
      (:instance fn2-cns-independent-release-preserves-pool-accounting
        (slot ,(nth 0 a)) (gen ,(nth 1 a))
        (id ,(nth 3 a)) (ogen ,(nth 4 a))
        (pool (fn2-core-pool ,(nth 5 a)))))))

(defun fn2-cns-draining-original-parts (world)
  (declare (xargs :verify-guards nil))
  (let* ((row (fn2-decl-row '(:square fn2-cns-draining-counted-independent) world))
         (formula (fn2-decl-statement-body (fn2-decl-get :statement row) world)))
    (cond ((and (eq (car formula) 'implies) (equal (len formula) 3))
           (list (cadr formula) (caddr formula)))
          ((and (eq (car formula) 'if) (equal (len formula) 4)
                (equal (cadddr formula) ''t))
           (list (cadr formula) (caddr formula)))
          (t (er hard 'fn2-cns-draining-original-parts "Original counted H/C is unavailable.")))))
(mutual-recursion
 (defun fn2-cns-draining-direct-conclusion (term)
  (declare (xargs :verify-guards nil :measure (acl2-count term)))
  (cond ((or (atom term) (eq (car term) 'quote)) term)
        ((consp (car term))
         (cons (list 'lambda (cadar term)
                     (fn2-cns-draining-direct-conclusion (caddar term)))
               (fn2-cns-draining-direct-conclusions (cdr term))))
        (t (cons (if (eq (car term) 'fn2-cns-run) 'fn2-cns-run-draining (car term))
                 (fn2-cns-draining-direct-conclusions (cdr term))))))
 (defun fn2-cns-draining-direct-conclusions (terms)
  (declare (xargs :verify-guards nil :measure (acl2-count terms)))
  (if (atom terms) nil
    (cons (fn2-cns-draining-direct-conclusion (car terms))
          (fn2-cns-draining-direct-conclusions (cdr terms))))))

(defun fn2-cns-draining-proof-event (which world)
  (declare (xargs :verify-guards nil))
  (let* ((fn 'fn2-cns-run-draining)
         (body (getpropc fn 'unnormalized-body nil world))
         (calls (remove-duplicates-equal
                  (fn2-cns-draining-call-sites body '((fn2-core . core)))))
         (lease (fn2-cns-draining-calls-of 'fn2-cns-lease-release calls))
         (ws (fn2-cns-draining-calls-of 'fn2-core-release calls))
         (ns (fn2-cns-draining-calls-of 'fn2-cns-release-ns calls))
         (query-reads (fn2-cns-draining-calls-of 'fn2-cns-query-heldp calls))
         (timers (fn2-cns-draining-calls-of 'fn2-cns-clear-wait-timer calls))
         (reclaims (fn2-cns-draining-calls-of 'fn2-cns-reclaim calls))
         (writers (intersection-eq (strip-cars calls) (all-fnnames body)))
         (readers (fn2-arms-core-reads body world nil)))
    (if (not (and body
                  (equal (getpropc fn 'formals nil world) '(id budget fn2-core))
                  (equal (getpropc fn 'stobjs-in nil world) '(nil nil fn2-core))
                  (equal (getpropc fn 'stobjs-out nil world) '(nil nil nil nil fn2-core))
                  (eq (getpropc fn 'symbol-class nil world) :common-lisp-compliant)
                  (fn2-cns-draining-sites-closedp calls)
                  (fn2-cns-draining-effect-aritiesp calls)
                  (equal (len lease) 1) (equal (len ws) 1) (equal (len ns) 1)
                  (equal (len timers) 1) (equal (len reclaims) 1)
                  (equal (len query-reads) 3)
                  (fn2-cns-draining-second-statep (car ws) (car ns))))
        (er hard 'fn2-cns-draining-proof-event
            "Actual draining ABI/effect or WS-to-NS state changed. Calls: ~x0" calls)
      (let* ((parts (fn2-cns-draining-original-parts world))
             (hyp (car parts)) (conclusion (cadr parts))
             (direct (fn2-cns-draining-direct-conclusion conclusion))
               (held `(equal (fn2-cns-row-lease id core) *fn2-cns-lease-held*))
               (branch-hyp `(and ,hyp ,(if (eq which :held) held `(not ,held))))
               (uses (if (eq which :held) (fn2-cns-draining-effect-uses (append query-reads lease))
                       (append (fn2-cns-draining-effect-uses
                                (append query-reads ws ns timers reclaims))
                               (fn2-cns-draining-second-release-uses (car ws) (car ns)))))
               (open (union-eq readers (set-difference-eq writers
                       '(fn2-core-release fn2-cns-release-ns fn2-cns-lease-release
                         fn2-cns-clear-wait-timer fn2-cns-query-heldp fn2-cns-reclaim)))))
          (if (not (equal (fn2-cns-draining-call-sites conclusion nil)
                          '((fn2-cns-run id budget core))))
              (er hard 'fn2-cns-draining-proof-event
                  "Original C no longer contains the exact public CNS call: ~x0" conclusion)
           (case which
           (:calls `(defconst *fn2-cns-draining-proof-calls* ',calls))
           ((:held :final)
            `(defthm ,(if (eq which :held) 'fn2-cns-draining-held-direct-independent
                         'fn2-cns-draining-final-direct-independent)
               (implies ,branch-hyp ,direct)
               :rule-classes nil
               :hints (("Goal" :do-not-induct t
                        :use (fn2-cns-draining-domain-snapshot-by-definition ,@uses)
                        :in-theory
                        (union-theories
                         (theory 'fn2-cns-draining-native-readers)
                         (e/d (fn2-cns-run-draining ,@open
                               fn2-cns-draining-domainp fn2-cns-draining-resultp
                               fn2-cns-draining-expected fn2-cns-draining-zero-query-expected
                               fn2-cns-draining-query-heldp fn2-cns-drain-query-heldp
                               fn2-cns-drain-release-pool-effect fn2-cns-core-release-expected
                               fn2-cns-owned-pool-release-expected fn2-cns-owned-zero-query-pool-release-expected
                               fn2-cns-core-reclaim-expected fn2-machines-reclaim-list-expected
                               fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index
                               fn2-cns-drain-child fn2-cns-drain-child-index fn2-cns-drain-put-child
                               fn2-cns-drain-put-cells fn2-cns-drain-put-cell fn2-cns-drain-put)
                              (fn2-corep fn2-core-wfp fn2-pool-semanticp fn2-pool-release
                               fn2-cns-drain-releasablep fn2-cns-draining-reservedp
                               fn2-cns-drain-released-pool fn2-cns-drain-cleared-sched
                               fn2-machines-reservation-put fn2-core-release fn2-cns-release-ns
                               fn2-cns-lease-release fn2-cns-clear-wait-timer fn2-cns-query-heldp fn2-cns-reclaim)))))))
           (:direct
            `(defthm fn2-cns-draining-direct-independent
               (implies ,hyp ,direct)
               :rule-classes nil
               :hints (("Goal" :cases (,held)
                        :use (fn2-cns-draining-held-direct-independent
                              fn2-cns-draining-final-direct-independent)
                        :in-theory (theory 'minimal-theory)))))
           (:public
            `(defthm fn2-cns-draining-counted-independent-composed
               (implies ,hyp ,conclusion)
               :rule-classes nil
               :hints (("Goal" :use (fn2-cns-draining-direct-independent
                                    fn2-cns-draining-component-to-public)
                        :in-theory (theory 'minimal-theory)))))
           (otherwise (er hard 'fn2-cns-draining-proof-event "Unknown phase ~x0." which))))))))
