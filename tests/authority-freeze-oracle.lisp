; Independent temporal specification controls, not served evidence or certification.
; The observer supplies committed authority snapshots and freeze events. No call
; to CNS, authority-allows, consumer-model, or the handler under test is made.
(in-package "ACL2")

(defun fn2-af-intersects (xs ys)
  (if (endp xs) nil
    (or (member-equal (car xs) ys)
        (fn2-af-intersects (cdr xs) ys))))

; Every delivered item is (checked-head original-streams). An article may be
; readable through any original stream, but every check uses the same head.
(defun fn2-af-items (items head readable)
  (if (endp items) t
    (and (equal (caar items) head)
         (fn2-af-intersects (cadar items) readable)
         (fn2-af-items (cdr items) head readable))))

; Authority snapshot = (head consume readable-streams). This checker concerns
; read/wait views, not append retry outcomes, cursor mutations or fetch policy.
(defun fn2-af-freeze (snapshot view items result)
  (and (consp snapshot)
       (cond ((not (cadr snapshot))
              (and (equal result :access) (endp items)))
             ((not (equal view (car snapshot)))
              (and (equal result :rebase-required) (endp items)))
             (t (and (equal result :accepted)
                     (fn2-af-items items (car snapshot) (caddr snapshot)))))))

; Events:
; (:publish principal snapshot)
; (:freeze request principal view items result)
; (:send request)
; Snapshots must come from actual publication observations, never from replies
; produced by the implementation being checked. Frozen answers survive later
; publications; send is deliberately not another authority decision.
(defun fn2-af-history (events snapshots frozen)
  (if (endp events) t
    (let ((event (car events)))
      (cond
       ((equal (car event) :publish)
        (and (equal (len event) 3)
             (fn2-af-history (cdr events)
                             (acons (cadr event) (caddr event) snapshots)
                             frozen)))
       ((equal (car event) :freeze)
        (and (equal (len event) 6)
             (not (assoc-equal (cadr event) frozen))
             (fn2-af-freeze (cdr (assoc-equal (caddr event) snapshots))
                            (nth 3 event) (nth 4 event) (nth 5 event))
             (fn2-af-history (cdr events) snapshots
                             (acons (cadr event) t frozen))))
       ((equal (car event) :send)
        (and (equal (len event) 2)
             (assoc-equal (cadr event) frozen)
             (fn2-af-history (cdr events) snapshots frozen)))
       (t nil)))))

; Whole model antecedent: a known publication, matching request identity,
; current view, consume, and every item's own streams at the same head.
(assert-event
 (fn2-af-history
  '((:publish alice (10 t (a b)))
    (:freeze (1 7) alice 10 ((10 (a)) (10 (x b))) :accepted)
    (:publish alice (11 nil nil)) (:send (1 7))) nil nil))
; The same selection, but revoke precedes freeze: access, no delivered items.
(assert-event
 (fn2-af-history
  '((:publish alice (10 t (a b))) (:publish alice (11 nil nil))
    (:freeze (1 7) alice 10 nil :access) (:send (1 7))) nil nil))
(assert-event
 (not (fn2-af-history
  '((:publish alice (10 t (a b))) (:publish alice (11 nil nil))
    (:freeze (1 7) alice 10 ((10 (a))) :accepted)) nil nil)))
; Even unrelated grant changes invalidate the old view while consume remains.
(assert-event
 (fn2-af-freeze '(11 t (a b c)) 10 nil :rebase-required))
(assert-event
 (not (fn2-af-freeze '(11 t (a b c)) 10 '((10 (a))) :accepted)))
; Fresh view alone does not repair mixed-head page evidence.
(assert-event
 (not (fn2-af-freeze '(11 t (a b)) 11 '((10 (a)) (11 (b))) :accepted)))
; Membership must be the article's original streams, not the query stream.
(assert-event
 (not (fn2-af-freeze '(11 t (a)) 11 '((11 (b c))) :accepted)))
(assert-event (not (fn2-af-history '((:send (1 7))) nil nil)))
(assert-event
 (not (fn2-af-history
  '((:publish alice (10 t (a)))
    (:freeze (1 7) alice 10 ((10 (a))) :accepted)
    (:freeze (1 7) alice 10 ((10 (a))) :accepted)) nil nil)))
