(in-package "ACL2")
(include-book "../../books/article-stream-owner")
(include-book "../../books/owner-resource-line")

; Teeth of fn-asto-an-unavailable-preflight-is-answered-in-its-place
; (books/article-stream-owner.lisp) and fn-orln-preflight-line-is-a-403
; (books/owner-resource-line.lisp): a retrieval whose preflight read did not
; come in time is answered 403 in the preflight's place, nothing else of its
; plan moved.

(defconst *asot-capture* '(expected-conn auth-view-peer selection :article server scan pin nil))
(defconst *asot-before* (list :reply (fn-osch-text "211 1 1 1 fn.test")))
(defconst *asot-after* (list :reply (fn-osch-text "205 closing")))
(defconst *asot-plan*
  (list nil *asot-before* (list :article-preflight *asot-capture*) *asot-after*))
(defconst *asot-line* (fn-orln-preflight-line :unavailable 1000 6000 nil))

; REACHABLE POSITIVE, complete antecedent and conclusion: the deadline's 403
; replaces the preflight; the current window, the entry before it and the
; entry after it are the plan's.
(assert-event
 (let ((p (fn-asto-plan-unavailable *asot-plan* *asot-line*))
       (rest (fn-splan-rest *asot-plan*)))
   (and (fn-asto-preflight-planp *asot-plan*)
        (consp p)
        (equal (fn-splan-cur p) (fn-splan-cur *asot-plan*))
        (equal rest (append (fn-asto-preflight-prefix rest)
                            (cons (fn-asto-preflight-entry rest)
                                  (fn-asto-preflight-suffix rest))))
        (fn-asto-preflight-entryp (fn-asto-preflight-entry rest))
        (not (fn-asto-preflight-restp (fn-asto-preflight-prefix rest)))
        (equal (fn-splan-rest p)
               (append (fn-asto-preflight-prefix rest)
                       (cons (fn-nntp-reply-effect *asot-line*)
                             (fn-asto-preflight-suffix rest))))
        ;; the literal plan: before, the 403, after
        (equal p (list nil *asot-before* (list :reply *asot-line*) *asot-after*))
        (equal (take 3 *asot-line*) '(52 48 51))
        ;; no preflight remains: the host renders it as an ordinary plan
        (not (fn-asto-preflight-planp p)))))

; The named refusal (P12) gives its own 403 the same way.
(assert-event
 (let* ((line (fn-orln-preflight-line :read-resources-unavailable 0 0 nil))
        (p (fn-asto-plan-unavailable *asot-plan* line)))
   (and (equal line (fn-orln-unavailable-line :read-resources-unavailable))
        (equal (take 3 line) '(52 48 51))
        (equal p (list nil *asot-before* (list :reply line) *asot-after*)))))

; Only the FIRST preflight is answered (a later one is a later request's).
(assert-event
 (let* ((second (list :article-preflight '(other)))
        (plan (list nil (list :article-preflight *asot-capture*) second))
        (p (fn-asto-plan-unavailable plan *asot-line*)))
   (and (fn-asto-preflight-planp plan)
        (equal p (list nil (list :reply *asot-line*) second))
        (equal (fn-asto-preflight-entry (fn-splan-rest plan))
               (list :article-preflight *asot-capture*)))))

; HYPOTHESIS REMOVAL: a plan with no preflight (a render that went cold
; after its first window was written; an OVER cursor) is not answered: NIL,
; and the keystone's conclusion (consp p) fails.
(assert-event
 (let* ((plan (list nil *asot-before* (list :article-cursor '(cursor)) *asot-after*))
        (p (fn-asto-plan-unavailable plan *asot-line*)))
   (and (not (fn-asto-preflight-planp plan))
        (equal p nil)
        (not (consp p)))))

; HYPOTHESIS REMOVAL of fn-orln-preflight-line-is-a-403: any other word
; gives no line (and so no plan: the host keeps its termination).
(assert-event
 (and (equal (fn-orln-preflight-line :serve 0 0 nil) nil)
      (equal (fn-orln-preflight-line :admitted 0 0 nil) nil)
      (equal (fn-orln-preflight-line '(:wait 50) 0 0 nil) nil)))

; The two lines are distinct: the deadline's names its wait, the refusal
; names the pool.
(assert-event
 (not (equal (fn-orln-preflight-line :unavailable 0 0 nil)
             (fn-orln-preflight-line :read-resources-unavailable 0 0 nil))))
