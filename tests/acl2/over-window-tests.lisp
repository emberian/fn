; over-window-tests.lisp -- teeth for books/over-window.lisp (lane join-f2-10).
;
; The fixture is served-catalog-tests' three-article catalog (fn.test 1, 2, 3;
; fn.other 1).  Positive witnesses evaluate BOTH sides of the keystone
; fn-ovw-run-is-over-range-cat on it at W = 1, 2 and 7 (the reply is really
; split: the first quantum at W = 1 leaves a live cursor); the empty range
; (423, and 420 for XOVER) and no group (412).  Hypothesis removal for
; fn-ovw-run-is-reply: a non-natural K, the retained hypothesis holding and
; the conclusion failing.  Mutation: the first quantum alone is not the reply
; (the windowed reply is never truncated by stopping early).

(in-package "ACL2")
(include-book "../../books/over-window")

(defconst *ovwt-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *ovwt-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *ovwt-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *ovwt-w0* (fn-record-make 0 1 1 "<a@x>" *ovwt-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *ovwt-w1* (fn-record-make 1 2 2 "<b@x>" *ovwt-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *ovwt-w2* (fn-record-make 2 3 3 "<c@x>" *ovwt-p2* '("fn.test") "o" "s" "e" 1 5))

(defun ovwt-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *ovwt-a* (list *ovwt-p0* *ovwt-p1* *ovwt-p2*))
(defconst *ovwt-r0* (fn-cat-assign (ovwt-held *ovwt-w0* 0 nil) nil))
(defconst *ovwt-r1* (fn-cat-assign (ovwt-held *ovwt-w1* 1 nil) (list *ovwt-r0*)))
(defconst *ovwt-r2* (fn-cat-assign (ovwt-held *ovwt-w2* 2 nil) (list *ovwt-r0* *ovwt-r1*)))
(defconst *ovwt-c* (list *ovwt-r0* *ovwt-r1* *ovwt-r2*))

(defun ovwt-session (group)
  (fn-nntp-make-session t group nil t))

(defconst *ovwt-range* (fn-record-string-octets "1-10"))
(defconst *ovwt-past* (fn-record-string-octets "7-9"))

; The old reader's reply octets.
(defmacro ovwt-old (session token legacyp)
  `(fn-served-reply-octets
    (cdr (fn-nntp-over-range-cat ,session 3 ,token ,legacyp *ovwt-a* *ovwt-c*))))

;; POSITIVE: the keystone's conclusion, both conjuncts, at three widths; the
;; reply is a 224 with three lines ending in the dot.
(defthm ovwt-keystone-witness
  (let ((s (ovwt-session "fn.test")))
    (and (equal (car (fn-nntp-over-range-cat s 3 *ovwt-range* nil *ovwt-a* *ovwt-c*)) s)
         (equal (fn-ovw-octets s 3 *ovwt-range* nil 1 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-range* nil))
         (equal (fn-ovw-octets s 3 *ovwt-range* nil 2 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-range* nil))
         (equal (fn-ovw-octets s 3 *ovwt-range* nil 7 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-range* nil))
         (equal (take 3 (ovwt-old s *ovwt-range* nil)) '(50 50 52))
         (equal (last (ovwt-old s *ovwt-range* nil) ) '(10))
         (equal (len (fn-ovw-lines "fn.test" 1 3 3 *ovwt-a* *ovwt-c*)) 3)))
  :rule-classes nil)

;; The reply is really windowed: at W = 1 the start probes nothing, the first
;; quantum sends the status line and ONE line and leaves a live cursor at 2.
(defthm ovwt-first-quantum
  (let* ((s (ovwt-session "fn.test"))
         (cur (mv-nth 1 (fn-ovw-start s 3 *ovwt-range* nil *ovwt-c*))))
    (and (equal (mv-nth 0 (fn-ovw-start s 3 *ovwt-range* nil *ovwt-c*)) nil)
         (equal cur (fn-ovw-cursor "fn.test" 1 3 3 nil t))
         (equal (mv-nth 1 (fn-ovw-step cur 1 *ovwt-a* *ovwt-c*))
                (fn-ovw-cursor "fn.test" 2 3 3 nil nil))
         (equal (len (fn-ovw-lines "fn.test" 1 (fn-ovw-hi 1 3 1) 3 *ovwt-a* *ovwt-c*)) 1)
         ;; MUTATION: the first quantum alone is a strict prefix, not the reply
         (not (equal (mv-nth 0 (fn-ovw-step cur 1 *ovwt-a* *ovwt-c*))
                     (ovwt-old s *ovwt-range* nil)))))
  :rule-classes nil)

;; POSITIVE, the refusals: a range past the group's high (423; XOVER 420) and
;; no group selected (412), all equal to the old reader.
(defthm ovwt-refusals-witness
  (let ((s (ovwt-session "fn.test")) (n (ovwt-session nil)))
    (and (equal (fn-ovw-octets s 3 *ovwt-past* nil 2 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-past* nil))
         (equal (take 3 (ovwt-old s *ovwt-past* nil)) '(52 50 51))
         (equal (fn-ovw-octets s 3 *ovwt-past* t 2 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-past* t))
         (equal (take 3 (ovwt-old s *ovwt-past* t)) '(52 50 48))
         (equal (fn-ovw-octets n 3 *ovwt-range* nil 2 *ovwt-a* *ovwt-c*) (ovwt-old n *ovwt-range* nil))
         (equal (take 3 (ovwt-old n *ovwt-range* nil)) '(52 49 50))))
  :rule-classes nil)

;; HYPOTHESIS REMOVAL (fn-ovw-run-is-reply without (natp k)): K = :x, the
;; retained (natp top) holds, the conclusion fails (the step reads K as 0 and
;; sends the lines; the specification's range from :x is empty).
(defthm ovwt-run-is-reply-needs-natp-k
  (and (not (natp :x))
       (natp 3)
       (not (equal (fn-ovw-run (fn-ovw-cursor "fn.test" :x 3 3 nil t) 2 *ovwt-a* *ovwt-c*)
                   (fn-ovw-reply (fn-ovw-lines "fn.test" :x 3 3 *ovwt-a* *ovwt-c*) nil t))))
  :rule-classes nil)
