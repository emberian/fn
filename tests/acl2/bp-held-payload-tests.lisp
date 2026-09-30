; Teeth for books/bp-held-payload.lisp (lane bp-catalog): the receipt's
; byte comparison by handle, on a live arena and in the logic.
(in-package "ACL2")
(include-book "../../books/bp-held-payload")
(include-book "catalog-record-tests")
(include-book "must-fail-checked")

; A request whose article field (position 9) is ART.
(defun bphht-req (art)
  (declare (xargs :guard t))
  (list :bpa-request 1 2 3 4 5 6 7 8 art))
(assert-event (equal (fn-bpa-request-article (bphht-req *crt-art*)) *crt-art*))

; The exec path on a live arena: intern the wire record (its payload sealed,
; the held record carrying the handle), then compare requests in place.
; Positive witness of fn-bphh-request-article-matches-is-wire: fn-arena-p
; holds (a live stobj), the in-place answer is T and so is the list model's
; over the materialized record.  Non-degenerate: a changed octet, a proper
; prefix and an extension each answer NIL, as the list model does.
(defun bphht-run (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((fn-arena (fn-arena-clear fn-arena)))
    (mv-let (held fn-arena)
      (fn-cat-intern-list *crt-w* nil 0 fn-arena)
      (mv (list (fn-bphh-request-article-matches (bphht-req *crt-art*) held fn-arena)
                (equal (fn-bpa-request-article (bphht-req *crt-art*))
                       (fn-record-payload (fn-held-wire-of held fn-arena)))
                (fn-bphh-request-article-matches (bphht-req *crt-art-bad*) held fn-arena)
                (fn-bphh-request-article-matches
                 (bphht-req (take (1- (len *crt-art*)) *crt-art*)) held fn-arena)
                (fn-bphh-request-article-matches
                 (bphht-req (append *crt-art* '(10))) held fn-arena)
                (equal (fn-bpa-request-article (bphht-req *crt-art-bad*))
                       (fn-record-payload (fn-held-wire-of held fn-arena))))
          fn-arena))))

(defun bphht-exec ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (bphht-run fn-arena) result)))

(assert-event (equal (bphht-exec) (list t t nil nil nil nil)))

; PRF-215 literal positives: fn-bphh-octets-at-p-is-equal-payload and
; fn-bphh-request-article-matches-is-wire. The existing live execution above
; covers the boundary's positive/mutated payloads; here affirmatively assert
; the sole arena hypothesis and each theorem's complete equality.
(defthm bphht-literal-positive
  (let* ((held (mv-nth 0 (fn-cat-intern-list *crt-w* nil 0 nil)))
         (arena (mv-nth 1 (fn-cat-intern-list *crt-w* nil 0 nil)))
         (request (bphht-req *crt-art*)))
    (and (fn-arena-p arena)
         (equal (fn-bphh-octets-at-p *crt-art* 0 0 arena)
                (equal *crt-art* (fn-arena-payload 0 arena)))
         (equal (fn-bphh-request-article-matches request held arena)
                (equal (fn-bpa-request-article request)
                       (fn-record-payload (fn-held-wire-of held arena))))))
  :rule-classes nil)

; Hypothesis removal (fn-arena-p): over a value that is not an arena (a
; payload that is not a true list) the retained parts hold (a handle, the
; octets of the slice) while the hypothesis fails and the conclusion fails:
; the in-place walk accepts what the list model refuses.
(defthm bphht-not-an-arena
  (not (fn-arena-p '((1 2 . 3))))
  :rule-classes nil)
(defthm bphht-walk-accepts
  (equal (fn-bphh-octets-at-p '(1 2) 0 0 '((1 2 . 3))) t)
  :rule-classes nil)
(defthm bphht-list-model-refuses
  (equal (equal '(1 2) (fn-arena-payload 0 '((1 2 . 3)))) nil)
  :rule-classes nil)
(must-fail-checked
 (defthm bphht-equation-without-arena
   (equal (fn-bphh-octets-at-p '(1 2) 0 0 '((1 2 . 3)))
          (equal '(1 2) (fn-arena-payload 0 '((1 2 . 3)))))
   :rule-classes nil))

; PRF-215 hypothesis removal for the request wrapper's exact equation:
; the same improper payload refutes fn-arena-p; the in-place walk accepts
; the request while the materialized record comparison refuses it.
(defthm bphht-request-without-arena
  (let ((held (mv-nth 0 (fn-cat-intern-list *crt-w* nil 0 nil))))
    (and (not (fn-arena-p '((1 2 . 3))))
         (not (equal (fn-bphh-request-article-matches
                       (bphht-req '(1 2)) held '((1 2 . 3)))
                     (equal (fn-bpa-request-article (bphht-req '(1 2)))
                            (fn-record-payload
                             (fn-held-wire-of held '((1 2 . 3)))))))))
  :rule-classes nil)
(must-fail-checked
 (defthm bphht-request-equation-without-arena
   (let ((held (mv-nth 0 (fn-cat-intern-list *crt-w* nil 0 nil))))
     (equal (fn-bphh-request-article-matches
             (bphht-req '(1 2)) held '((1 2 . 3)))
            (equal (fn-bpa-request-article (bphht-req '(1 2)))
                   (fn-record-payload (fn-held-wire-of held '((1 2 . 3)))))))
   :rule-classes nil))
