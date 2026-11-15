; Exact full-R contracts for timer-only core helpers. The literal FIFO is
; unchanged. Generic ARM-DEADLINE is intentionally not an opaque leaf: it
; may set a service flag. Positive ARM-DELAY-MS never takes that branch.
(in-package "ACL2")
(include-book "reference-effect-leaves")
(include-book "cns-draining-contract")
(include-book "assembly-callbacks-d-conn")

(defthm fn2-ref-effect-positive-delay-is-future
  (implies (and (natp now) (unsigned-byte-p 32 milliseconds)
                (< 0 milliseconds))
           (< now (+ now (* 1000 milliseconds))))
  :rule-classes (:rewrite :linear))

; Extract only the selected timer row from the existing relation. This is
; not a replacement timer model and imposes no equality on intrusive queues.
(defthm fn2-ref-effect-timer-row-at
  (implies (and (natp i) (natp left) (< i left)
                (not (fn2-ref-timer-row-difference left sched sched-ref)))
    (and (equal (fn2-sched-deadline i sched) (fn2-sched-deadline i sched-ref))
         (equal (fn2-sched-expired i sched) (fn2-sched-expired i sched-ref))))
  :hints (("Goal" :induct (fn2-ref-timer-row-difference left sched sched-ref)
           :in-theory (e/d (fn2-ref-timer-row-difference)
                            (fn2-sched-deadline fn2-sched-expired)))))

(defthm fn2-ref-effect-timer-row-paired-deadline
  (implies (and (not (fn2-ref-timer-row-difference left sched sched-ref))
                (equal (fn2-sched-rows sched) (fn2-sched-rows sched-ref)))
    (not (fn2-ref-timer-row-difference left
           (fn2-sched-set-deadline i value sched)
           (fn2-sched-set-deadline i value sched-ref))))
  :hints (("Goal" :induct (fn2-ref-timer-row-difference left sched sched-ref)
           :in-theory (enable fn2-ref-timer-row-difference fn2-sched-set-deadline
             fn2-sched-deadline fn2-sched-expired fn2-sched-rows
             update-fn2-sched-deadline$ai))))
(defthm fn2-ref-effect-timer-row-paired-expired
  (implies (and (not (fn2-ref-timer-row-difference left sched sched-ref))
                (equal (fn2-sched-rows sched) (fn2-sched-rows sched-ref)))
    (not (fn2-ref-timer-row-difference left
           (fn2-sched-set-expired i value sched)
           (fn2-sched-set-expired i value sched-ref))))
  :hints (("Goal" :induct (fn2-ref-timer-row-difference left sched sched-ref)
           :in-theory (enable fn2-ref-timer-row-difference fn2-sched-set-expired
             fn2-sched-deadline fn2-sched-expired fn2-sched-rows
             update-fn2-sched-expired$ai))))

; Ordinary and reference projections must both commute with the concrete
; core writers used by a helper called on either congruent core carrier.
(defun fn2-ref-effect-timer-lens-events (children writes)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (append (fn2-core-lens-read-events (caar children) writes)
            (fn2-core-lens-read-events
             (fn2-columns-sym (caar children) "-REF") writes)
            (fn2-ref-effect-timer-lens-events (cdr children) writes))))
(make-event
 (let* ((writes (list (assoc-eq 'fn2-core-sched *fn2-core-children*)
                      (assoc-eq 'fn2-core-control *fn2-core-children*)))
        (events (fn2-ref-effect-timer-lens-events *fn2-core-children* writes)))
   (if (member-equal nil writes)
       (er soft 'fn2-ref-effect-timer-lens-events "Actual timer carriers are absent.")
     (value `(progn ,@(fn2-core-lens-missing-events events (w state))
               (deftheory fn2-ref-effect-timer-lenses ',(strip-cadrs events)))))))

; Five timer writes preserve each actual queue/calendar observer. Emit the
; class from live signatures; there is no hand-written scheduler surrogate.
(defun fn2-ref-effect-timer-observer-events (observers writes world)
  (declare (xargs :verify-guards nil
                  :measure (+ (acl2-count observers) (acl2-count writes))))
  (if (atom observers) nil
    (append
     (if (atom writes) nil
       (let* ((fn (car observers)) (writer (car writes))
              (args (getpropc fn 'formals nil world))
              (wargs (getpropc writer 'formals nil world))
              (mutated (subst (cons writer wargs) 'fn2-sched args)))
         (cons
          `(defthm ,(fn2-columns-sym fn
                      (concatenate 'string "-TIMER-FRAME-" (symbol-name writer)))
             (equal (,fn ,@mutated) (,fn ,@args))
             :hints (("Goal" :induct (,fn ,@args)
                      :in-theory (enable ,fn ,writer
                        fn2-sched-set-deadline fn2-sched-set-expired
                        update-fn2-sched-deadline$ai update-fn2-sched-expired$ai
                        fn2-sched-rows fn2-sched-nprincipals
                        fn2-sched-headsi fn2-sched-tailsi fn2-sched-countsi
                        fn2-sched-calendar-length fn2-sched-calendari
                        fn2-sched-principal fn2-sched-in-queue
                        fn2-sched-prev fn2-sched-next))))
          (fn2-ref-effect-timer-observer-events (list fn) (cdr writes) world))))
     (fn2-ref-effect-timer-observer-events (cdr observers) writes world))))
(make-event
 (value (cons 'progn
  (fn2-ref-effect-timer-observer-events
   '(fn2-ref-concrete-queue fn2-ref-queues-difference
     fn2-ref-calendar-difference fn2-ref-links-difference)
   '(fn2-sched-set-deadline fn2-sched-set-expired
     update-fn2-sched-armed-timers update-fn2-sched-earliest-deadline
     update-fn2-sched-scan-min) (w state)))))

(defun fn2-ref-effect-timer-leaf-events (rows world)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let* ((fn (caar rows)) (kind (cadar rows)) (lemma (caddar rows)))
      (if (not (and (function-symbolp fn world)
                    (eq (getpropc fn 'symbol-class nil world) :common-lisp-compliant)
                    (if (eq kind :frame) (fn2-effect-core-abi-p fn world)
                      (and (equal (getpropc fn 'stobjs-out nil world) '(nil))
                           (equal (remove-eq nil (getpropc fn 'stobjs-in nil world)) '(fn2-core))))))
          `((make-event (er soft 'fn2-ref-effect-timer-leaf-events
                           "Actual guard-verified timer ABI missing for ~x0." ',fn)))
        (cons
         `(defthm ,lemma
            ,(fn2-reference-effect-leaf-formula fn kind 'fn2-representation-relation world)
            :rule-classes nil
            :hints (("Goal" :do-not-induct t
                     :in-theory
                     (union-theories (theory 'fn2-ref-effect-timer-lenses)
                      (e/d (,fn fn2-ref-effect-whole-resultp
                            fn2-representation-relation fn2-ref-difference
                            fn2-ref-timer-state-difference fn2-ref-scheduler-difference
                            fn2-ref-core-difference
                            fn2-sched-arm-delay-ms fn2-sched-arm-deadline
                            fn2-sched-clear-deadline fn2-sched-timer-expired-p
                            fn2-ref-effect-positive-delay-is-future
                            fn2-ref-effect-timer-row-at)
                           (fn2-corep fn2-ref-corep fn2-core-wfp
                            fn2-ref-concrete-queue fn2-ref-queues-difference
                            fn2-ref-calendar-difference fn2-ref-links-difference))))))
         (fn2-ref-effect-timer-leaf-events (cdr rows) world))))))

(make-event
 (value (cons 'progn
  (fn2-ref-effect-timer-leaf-events
   '((fn2-cns-arm-wait-timer :frame fn2-ref-effect-cns-arm-wait-timer-frame)
     (fn2-cns-clear-wait-timer :frame fn2-ref-effect-cns-clear-wait-timer-frame)
     (fn2-cns-wait-expired-p :shape fn2-ref-effect-cns-wait-expired-p-shape)
     (fn2-tls-arm-timer :frame fn2-ref-effect-tls-arm-timer-frame)
     (fn2-tls-clear-timer :frame fn2-ref-effect-tls-clear-timer-frame)
     (fn2-tls-expired-p :shape fn2-ref-effect-tls-expired-p-shape)) (w state)))))
