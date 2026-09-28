; Teeth for books/defevent.lisp.
;
;   1. The expansion is the hand-written table: the two decision-journal
;      families (books/owner-time-journal.lisp) expand to exactly the defuns
;      that book held before it used the macro (pinned literally here, from
;      its revision 940bc3104), and the book's own definitions are those.
;   2. The table records each family; the round-trip assertion bites (a
;      family whose decoder is not the encoder's inverse cannot be written,
;      so the check is exercised on the generated functions directly).
;   3. One refusal per rule of fn-de-refusal.

(in-package "ACL2")
(include-book "../../books/defevent")
(include-book "../../books/owner-time-journal")
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; 1. The hand-written forms, as they were.

(defconst *fn-det-hand*
  '((defun fn-otm-op-of-kind (kind)
      (declare (xargs :guard t))
      (cond ((eq kind :clock) 1) ((eq kind :served) 2) ((eq kind :issue) 3)
            ((eq kind :return) 4) ((eq kind :space) 6) (t 0)))
    (defun fn-otm-kind-of-op (op)
      (declare (xargs :guard t))
      (cond ((eql op 1) :clock) ((eql op 2) :served) ((eql op 3) :issue)
            ((eql op 4) :return) ((eql op 6) :space) (t nil)))
    (defun fn-otm-word-code (w)
      (declare (xargs :guard t))
      (case w
        (:issued 1) (:returned 2) (:recovered 3) (:recovered-from-stall 4)
        (:became-slow 5) (:became-stalled 6) (:none 7) (:clock-regressed 8)
        (:fault 9) (:became-full 10) (:space-recovered 11) (:space-unobserved 12)
        (otherwise 0)))))

(defun fn-det-defuns (events)
  (declare (xargs :mode :program))
  (cond ((atom events) nil)
        ((and (consp (car events)) (eq (car (car events)) 'defun))
         (cons (car events) (fn-det-defuns (cdr events))))
        (t (fn-det-defuns (cdr events)))))

(defun fn-det-family (name w)
  (declare (xargs :mode :program))
  (cdr (assoc-eq name (table-alist 'fn-events w))))

; The macro's expansion of each family, from the kvs the book's form gave
; (the table holds them), is the hand-written defuns, form for form.
(assert-event
 (equal (append (fn-det-defuns
                 (cdr (fn-de-expand 'fn-otm-op (fn-det-family 'fn-otm-op (w state)))))
                (fn-det-defuns
                 (cdr (fn-de-expand 'fn-otm-word (fn-det-family 'fn-otm-word (w state))))))
        (append *fn-det-hand*
                '((defun fn-otm-wordp (w)
                    (declare (xargs :guard t))
                    (and (member-eq w '(:issued :returned :recovered :recovered-from-stall
                                        :became-slow :became-stalled :none :clock-regressed
                                        :fault :became-full :space-recovered
                                        :space-unobserved))
                         t))))))

; The generated functions answer as the hand-written ones did.
(assert-event (equal (fn-otm-op-of-kind :space) 6))
(assert-event (equal (fn-otm-kind-of-op 6) :space))
(assert-event (equal (fn-otm-word-code :became-stalled) 6))
(assert-event (and (fn-otm-wordp :space-unobserved) (not (fn-otm-wordp :start))))

; ---------------------------------------------------------------------------
; 2. The table.

(assert-event (equal (cadr (assoc-keyword :version (fn-det-family 'fn-otm-op (w state)))) 1))
(assert-event (equal (strip-cars (cadr (assoc-keyword :reserved
                                                      (fn-det-family 'fn-otm-op (w state)))))
                     '(0 5 7)))

; ---------------------------------------------------------------------------
; 3. Refusals.

(defconst *fn-det-ok*
  '(:version 1 :var k :codes ((:a 1) (:b 2)) :otherwise 0
    :reserved ((0 :none "none")) :encode fn-det-enc :decode fn-det-dec :code-var c))

(assert-event (null (fn-de-refusal 'fam *fn-det-ok*)))
(assert-event (equal (car (fn-de-refusal 'fam (list* :version 0 (cddr *fn-det-ok*))))
                     :bad-version))
(assert-event (equal (car (fn-de-refusal 'fam '(:version 1 :var k :codes ((:a 1) (:b 1))
                                                :otherwise 0 :encode e)))
                     :duplicate-code))
(assert-event (equal (car (fn-de-refusal 'fam '(:version 1 :var k :codes ((:a 1) (:a 2))
                                                :otherwise 0 :encode e)))
                     :duplicate-kind))
(assert-event (equal (car (fn-de-refusal 'fam '(:version 1 :var k :codes ((:a 1) (:b 5))
                                                :otherwise 0 :reserved ((5 :note "a note"))
                                                :encode e)))
                     :code-is-reserved))
(assert-event (equal (car (fn-de-refusal 'fam '(:version 1 :var k :codes ((:a 1))
                                                :otherwise 1 :encode e)))
                     :otherwise-is-a-code))
(assert-event (equal (car (fn-de-refusal 'fam '(:version 1 :var k :codes ((a 1))
                                                :otherwise 0 :encode e)))
                     :bad-codes))
(assert-event (equal (car (fn-de-refusal 'fam '(:version 1 :var k :codes ((:a 1))
                                                :otherwise 0 :reserved ((0 "unnamed"))
                                                :encode e)))
                     :bad-reserved))
(assert-event (equal (car (fn-de-refusal 'fam '(:version 1 :var k :codes ((:a 1))
                                                :otherwise 0 :encode e :decode d)))
                     :bad-decode))
(assert-event (equal (fn-de-refusal 'fam '(:version 1 :var k :codes ((:a 1))
                                           :otherwise 0 :encode e :id 3))
                     '(:unknown-keyword :id)))
(assert-event (equal (car (fn-de-refusal 'fam '(:version 1 :var k :codes ((:a 1))
                                                :otherwise 0 :encode e
                                                :recorded ((x "")))))
                     :bad-recorded))
(must-fail-checked (defevent fam :version 1 :var k :codes ((:a 1) (:b 5))
                     :otherwise 0 :reserved ((5 :note "a note")) :encode fn-det-e)
                   :unchecked "defevent's refusal is its claim; the assert-event above names the rule")

; An accepted family through the macro, and its generated functions.
(defevent fn-det-fam
  :version 2
  :var k
  :codes ((:a 1) (:b 3))
  :otherwise 0
  :reserved ((0 :none "no event") (2 :c "retired at version 2"))
  :encode fn-det-enc
  :decode fn-det-dec
  :code-var c
  :recognizer fn-det-kindp)
(assert-event (and (equal (fn-det-enc :b) 3) (equal (fn-det-dec 3) :b)
                   (null (fn-det-dec 2)) (not (fn-det-kindp :c))))
