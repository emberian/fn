; Actual guarded member interface: original refutation stays unfinished.
(in-package "ACL2")
(include-book "checkpoint-member-refutation-unit")
(include-book "checkpoint-member-interface-unit")
(include-book "../books/owed-discharge")

; Reuse the counterexample's actual initialized arguments and repair only
; its readonly checkpoint value with the actual setter. No packer model.
(defun-nx fn2-checkpoint-member-positive-arguments ()
 (let ((args (fn2-checkpoint-member-refutation-arguments)))
  (update-nth 7 (fn2-checkpoints-set-checkpoint 0 1 (nth 7 args)) args)))

(local (defun fn2-checkpoint-member-evidence-bindings (args positive index)
 (declare (xargs :verify-guards nil))
 (if (atom args) nil
  (cons (list (car args)
              `(nth ',index (,(if positive
                                  'fn2-checkpoint-member-positive-arguments
                                'fn2-checkpoint-member-refutation-arguments))))
        (fn2-checkpoint-member-evidence-bindings (cdr args) positive (+ 1 index))))))

; Establish the replacement's precise relationship by inspecting the actual
; admitted theorem, old live statement, function ABI and stored guard. This
; is domain restriction with identical C, never a proof of the false original.
(make-event
 (let* ((world (w state))
        (fn 'fn2-checkpoint-installation-pack-member)
        (old 'fn2-checkpoint-installation-pack-member-fields-type)
        (theorem 'fn2-checkpoint-installation-pack-member-fields-type-under-guard)
        (claim 'fn2-checkpoint-installation-pack-member-fields-type-under-guard-claim)
        (args (getpropc fn 'formals nil world))
        (guard (getpropc fn 'guard nil world))
        (row (fn2-decl-row (list :square old) world))
        (old-formula (fn2-decl-statement-body (fn2-decl-get :statement row) world))
        (formula (getpropc theorem 'theorem nil world)))
  (mv-let (old-h old-c) (fn2-evidence-parts old-formula)
   (mv-let (h c) (fn2-evidence-parts formula)
    (mv-let (guard-count outside) (fn2-evidence-hypothesis-cut h guard)
     (declare (ignore outside))
     (if (not (and formula guard
                    (equal args '(c base slot gen okind oslot ogen
                       fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool))
                    (equal args (fn2-decl-get :vars row))
                    (equal (getpropc fn 'stobjs-out nil world) '(nil nil fn2-fields fn2-pool))
                    (equal old-c c)
                    (equal c `(fn2-fieldsp (mv-nth '2 (,fn ,@args))))
                    (subsetp-equal (fn2-evidence-hypotheses old-h)
                                  (fn2-evidence-hypotheses h))
                    (equal guard-count 1)
                    (equal (fn2-decl-get :proof row)
                      '(:refuted fn2-checkpoint-member-original-refuted-instance
                        fn2-checkpoint-installation-pack-member-fields-type-under-guard))))
         (er soft 'member-guarded-evidence "Actual member replacement relationship changed.")
       (value
        `(progn
          (defthm fn2-checkpoint-member-guarded-domain-implies-original-domain
           (implies ,h ,old-h) :rule-classes nil)
          (defthm-owed ,claim ,args ,formula
           :teeth (fn2-checkpoint-member-fields-type-positive-check
                    fn2-checkpoint-member-fields-type-readonly-removal-check)
           :layer :b :boundary :extraction
           :contract (:domain-restriction-of ,old
                      :domain-theorem fn2-checkpoint-member-guarded-domain-implies-original-domain)
           :origin (:function ,fn)
           :doc "Exact admitted guarded FIELDS-TYPE interface of the actual member. Same conclusion and original carrier premises; adds actual stored guard and input recognizers. Original off-guard claim remains refuted and unfinished.")
          (fn2-owed-discharge ,claim ,theorem)))))))))

; Keep proof replay logical, including after this book is included elsewhere.
; Disable raw executable counterparts by actual stobj signatures, not a list
; of convenient model functions. The producer stays opaque and is supplied
; by its admitted guarded theorem or the existing admitted counterexample.
(defun fn2-checkpoint-member-stobj-execs (runes world)
 (declare (xargs :verify-guards nil))
 (if (atom runes) nil
  (let* ((rune (car runes)) (fn (cadr rune))
         (tables '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)))
   (if (and (consp rune) (eq (car rune) :executable-counterpart)
            (intersectp-eq tables
             (append (getpropc fn 'stobjs-in nil world) (getpropc fn 'stobjs-out nil world))))
       (cons rune (fn2-checkpoint-member-stobj-execs (cdr runes) world))
     (fn2-checkpoint-member-stobj-execs (cdr runes) world)))))
(defun fn2-checkpoint-member-ground-hint (positive bindings functions execs minimal world)
 (declare (xargs :verify-guards nil))
 (list :use
       (if positive
           (list (cons :instance
                   (cons 'fn2-checkpoint-installation-pack-member-fields-type-under-guard bindings)))
         'fn2-checkpoint-member-fields-type-readonly-removal-ground)
       :in-theory
       (list 'quote
        (set-difference-equal
         (union-equal functions (union-equal execs minimal))
         (append (fn2-checkpoint-member-stobj-execs execs world)
          '((:definition fn2-checkpoint-installation-pack-member)
            (:executable-counterpart fn2-checkpoint-member-positive-arguments)
            (:executable-counterpart fn2-checkpoint-member-refutation-arguments)
            (:executable-counterpart fn2-checkpoint-member-fields-type-readonly-removal-check)))))))

(make-event
 (let* ((world (w state))
        (name 'fn2-checkpoint-installation-pack-member-fields-type-under-guard-claim)
        (row (fn2-decl-row (list :square name) world))
        (args (fn2-decl-get :vars row))
        (positive (fn2-checkpoint-member-evidence-bindings args t 0))
        (negative (fn2-checkpoint-member-evidence-bindings args nil 0))
        (removed '(fn2-checkpointsp fn2-checkpoints)))
  (value
   (fn2-square-predicate-evidence-events-with-hints
    name positive
    (list :kind :hypothesis-removal :remove removed :occurrences 2 :bindings negative)
    `((fn2-checkpoint-member-ground-hint t ',positive
        (function-theory :here) (executable-counterpart-theory :here) (theory 'minimal-theory) world))
    `((fn2-checkpoint-member-ground-hint nil ',negative
        (function-theory :here) (executable-counterpart-theory :here) (theory 'minimal-theory) world))
    nil world))))
(fn2-assert-square-evidence fn2-checkpoint-installation-pack-member-fields-type-under-guard-claim)
; Even with a proved, witnessed restricted interface, the original is false.
(assert-event
 (let* ((old 'fn2-checkpoint-installation-pack-member-fields-type)
        (row (fn2-decl-row (list :square old) (w state))))
  (and (eq (car (fn2-decl-get :proof row)) :refuted)
       (member-eq old (fn2-owed-names (w state)))
       (equal (nth 2 (fn2-square-counts (list (cons old row)))) 0))))
