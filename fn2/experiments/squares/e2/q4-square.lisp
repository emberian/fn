; E2 Q4: a fold/summary instance of the common correspondence envelope.
; Pass 2 generates statements from roles, then bridges existing proofs to them.
(in-package "ACL2")
(include-book "q4-template")
(include-book "q4-checker")

; Read event tags from the admitted recognizer rather than restating a
; catalogue. Malformed is its complement; the recognizer covers two tags.
(defun sq-q4-quoted-keywords (term)
  (declare (xargs :verify-guards nil))
  (cond ((atom term) nil)
        ((eq (car term) 'quote)
         (if (keywordp (cadr term)) (list (cadr term)) nil))
        (t (union-eq (sq-q4-quoted-keywords (car term))
                     (sq-q4-quoted-keywords (cdr term))))))

(defun sq-q4-cases (world)
  (declare (xargs :verify-guards nil))
  (append (sq-q4-quoted-keywords
           (getpropc 'rs-eventp 'unnormalized-body nil world))
          '(:malformed :composition :converter)))

(defun sq-q4-theorem (case)
  (declare (xargs :verify-guards nil))
  (cond ((eq case :composition) 'rs-summary-adequate)
        ((eq case :converter) 'rs-summarize-related)
        ((eq case :malformed) 'rs-same-reads-of-other)
        (t (intern-in-package-of-symbol
            (concatenate 'string "RS-SAME-READS-OF-" (symbol-name case))
            'rs-eventp))))

(defconst *sq-q4-contract*
  '(:relation rs-same-reads :admissible (rs-h-ok rs-s-ok)
    :step (rs-h-step rs-s-step) :recognizer rs-eventp
    :observation (rs-h-obs rs-s-obs)
    :fold (rs-h-fold rs-s-fold) :converter rs-summarize))

(defun sq-q4-proof-name (case)
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol
   (concatenate 'string "SQ-Q4-GENERATED-" (symbol-name case)) 'sq-q4))

; These are proof adapters, not statement templates. Event statements add
; both post-admissibility conjuncts to the existing relation-only lemmas;
; G0 adds target admissibility. No kind-specific statement is handwritten.
(defun sq-q4-proof-support (case)
  (declare (xargs :verify-guards nil))
  (cond ((eq case :composition) '(rs-summary-adequate))
        ((eq case :converter) '(rs-summarize-related rs-s-ok-of-summarize))
        (t (list (sq-q4-theorem case) 'rs-h-ok-of-step 'rs-s-ok-of-step))))

(defun sq-q4-proof-events (cases contract)
  (declare (xargs :verify-guards nil))
  (if (atom cases) nil
    (let* ((case (car cases)) (support (sq-q4-proof-support case)))
      (cons
       `(defthm ,(sq-q4-proof-name case)
          ,(sq-fs-formula case contract)
          :rule-classes nil
          :hints (("Goal" :use ,support
                   :in-theory
                   (disable rs-h-ok rs-s-ok rs-same-reads rs-eventp
                            rs-h-step rs-s-step rs-h-fold rs-s-fold
                            rs-h-obs rs-s-obs rs-summarize ,@support))))
       (sq-q4-proof-events (cdr cases) contract)))))

(make-event
 (value (cons 'progn
              (sq-q4-proof-events (sq-q4-cases (w state)) *sq-q4-contract*))))

(defun sq-q4-evidence (case)
  (declare (xargs :verify-guards nil))
  (list (list :history '((:read 1)) :summary '(1) :bound 5
              :events (cond ((eq case :read) '((:read 3)))
                            ((eq case :catchup) '((:catchup 3)))
                            ((eq case :malformed) '((:read 0)))
                            ((eq case :composition)
                             '((:read 3) (:catchup 1) (:read 0)))
                            (t nil))
              :scope (list :profile :read-state :domain '(:articles 1 5)
                           :horizon (if (eq case :composition) 3
                                      (if (eq case :converter) 0 1))
                           :unit :fixture
                           :location "fn2/experiments/squares/e2/q4-square.lisp:sq-q4-evidence"))))

(defun sq-q4-requires (case)
  (declare (xargs :verify-guards nil))
  (cond ((eq case :composition)
         '(sq-q4-read sq-q4-catchup sq-q4-malformed
           rs-obs-agree rs-same-reads-init))
        ((eq case :converter)
         '(rs-same-reads-of-step rs-s-ok-of-summarize))
        ((eq case :read)
         '(rs-h-obs-read-of-step rs-s-obs-read-of-read-step))
        ((eq case :catchup)
         '(rs-h-obs-read-of-step rs-s-obs-read-of-catchup-step))
        (t '(rs-h-obs-read-of-step rs-s-obs-read-of-other-step))))

(defun sq-q4-bindings (cases contract)
  (declare (xargs :verify-guards nil))
  (if (atom cases) nil
    (let* ((case (car cases)) (thm (sq-q4-proof-name case))
           (formula (sq-fs-formula case contract))
           (id (intern-in-package-of-symbol
                (concatenate 'string "SQ-Q4-" (symbol-name case)) 'sq-q4)))
      (cons
       (cons case
             (list :id id :vars (sq-fs-vars case) :formula formula
                   :proof (list :proved thm)
                   :schema (if (eq case :converter) :g0 :g1)
                   :origin (list :predicate 'rs-eventp :proof-source (sq-q4-theorem case))
                   :boundary (if (eq case :converter)
                                 :history-to-summary :event-fold)
                   :requires (sq-q4-requires case)
                   :template (if (eq case :converter) :converter
                               (if (eq case :composition) :fold-composition
                                 :fold-summary))
                   :unused-roles
                   (cond ((eq case :converter)
                          '((:contract :step) (:contract :recognizer)
                            (:contract :observation) (:contract :fold)
                            (:sides :source) (:sides :target)))
                         ((eq case :composition)
                          '((:contract :step) (:contract :recognizer)
                            (:contract :converter)))
                         (t '((:contract :observation) (:contract :fold)
                              (:contract :converter))))
                   :sides (cond ((eq case :converter)
                                 '(:source rs-h-obs :target rs-s-obs
                                   :converter rs-summarize))
                                ((eq case :composition)
                                 '(:left rs-h-fold :right rs-s-fold))
                                (t '(:left rs-h-step :right rs-s-step)))
                   :checker (list :function 'sq-q4-checker :case case)
                   :teeth '(:positive sq-q4-positive :negative sq-q4-negative)
                   :evidence (sq-q4-evidence case)))
       (sq-q4-bindings (cdr cases) contract)))))

(make-event
 (value `(defsquare sq-q4
    :template :fold-summary
    :cases-from (sq-q4-cases (w state))
    :bindings (sq-q4-bindings (sq-q4-cases (w state)) *sq-q4-contract*)
    :contract ,*sq-q4-contract*
    :sides (:left (rs-h-step rs-h-fold) :right (rs-s-step rs-s-fold)
            :converter rs-summarize))))

(assert-event (equal (len (sq-q4-cases (w state))) 5))
