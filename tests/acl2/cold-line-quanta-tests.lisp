; cold-line-quanta-tests.lisp -- books/cold-line-quanta.lisp against the
; realizer it models (lane cold-line).  The model's cache size is the
; realizer's (books/payload-extent.lisp fn-arx-read-cache-entries), and the
; served quantum is strictly below it.
(in-package "ACL2")
(include-book "../../books/cold-line-quanta")
(include-book "../../books/payload-extent")

(defthm clqt-cache-is-the-realizers
  (and (equal *fn-clq-cache-entries* (fn-arx-read-cache-entries))
       (< (fn-clq-payload-quantum) (fn-arx-read-cache-entries)))
  :rule-classes nil)

;; The 45e05c7fd line in the model: forty reads in one quantum never finish
;; in 1,000 runs from an empty cache; as quanta of the served size they finish.
(defthm clqt-forty-reads
  (let ((d '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
             21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40)))
    (and (not (mv-nth 1 (fn-clq-resume d nil 8 1000)))
         (mv-nth 1 (fn-clq-line (fn-clq-chunks d (fn-clq-payload-quantum)) nil 8))
         (equal (len (fn-clq-chunks d (fn-clq-payload-quantum))) 10)
         (<= (mv-nth 0 (fn-clq-line (fn-clq-chunks d (fn-clq-payload-quantum)) nil 8)) 50)))
  :rule-classes nil)
