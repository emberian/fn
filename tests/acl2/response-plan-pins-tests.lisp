(in-package "ACL2")
(include-book "../../books/response-plan-pins")

; A real execution prefix: first response captured at generation 0, a
; retirement advances the epoch, second response captured at generation 1.
(defconst *rpint-first*
  (mv-list 3 (fn-rpin-step nil (fn-arpn-initial) '(:acquire 11))))
(defconst *rpint-retired*
  (mv-list 2 (fn-arpn-step (second *rpint-first*) '(:retire (page-a)))))
(defconst *rpint-second*
  (mv-list 3 (fn-rpin-step (first *rpint-first*) (first *rpint-retired*) '(:acquire 12))))

; Complete antecedent and conclusion of funded preservation, with two
; outstanding responses.  Cancelling the first leaves the second's hold.
(defthm rpint-funded-preservation-positive
  (let* ((owners (first *rpint-second*)) (st (second *rpint-second*))
         (next (mv-list 3 (fn-rpin-step owners st '(:release 11)))))
    (and (fn-arpn-okp st)
         (<= (fn-rpin-count-at 1 owners) (fn-arpn-pins-of 1 (second st)))
         (<= (fn-rpin-count-at 1 (first next)) (fn-arpn-pins-of 1 (second (second next))))
         (equal next '(((12 . 1)) (1 ((1 . 1)) ((0 page-a))) :released))
         (equal (fn-rpin-owner 12 (first next)) '(12 . 1))))
  :rule-classes nil)

(defthm rpint-acquire-positive
  (let* ((owners (first *rpint-first*)) (st (first *rpint-retired*))
         (next (mv-list 3 (fn-rpin-step owners st '(:acquire 12)))))
    (and (fn-arpn-okp st) (natp 12) (not (fn-rpin-owner 12 owners))
         (equal (third next) :acquired)
         (equal (fn-rpin-owner 12 (first next)) (cons 12 (first st)))
         (equal (fn-arpn-pins-of 1 (second (second next)))
                (+ 1 (fn-arpn-pins-of 1 (second st))))))
  :rule-classes nil)

(defthm rpint-acquire-without-natural-id
  (let* ((owners nil) (st (fn-arpn-initial))
         (next (mv-list 3 (fn-rpin-step owners st '(:acquire bad)))))
    (and (fn-arpn-okp st) (not (natp 'bad)) (not (fn-rpin-owner 'bad owners))
         (not (equal (third next) :acquired))))
  :rule-classes nil)

(defthm rpint-acquire-without-fresh-id
  (let* ((owners (first *rpint-first*)) (st (second *rpint-first*))
         (next (mv-list 3 (fn-rpin-step owners st '(:acquire 11)))))
    (and (fn-arpn-okp st) (natp 11) (fn-rpin-owner 11 owners)
         (not (equal (third next) :acquired))))
  :rule-classes nil)

(defthm rpint-acquire-without-arena-invariant-corrupted-state
  (let* ((owners nil) (st '(1 ((5 . 1) (1 . 2)) nil))
         (next (mv-list 3 (fn-rpin-step owners st '(:acquire 13)))))
    (and (not (fn-arpn-okp st)) (natp 13) (not (fn-rpin-owner 13 owners))
         (equal (third next) :acquired)
         (not (equal (fn-arpn-pins-of 1 (second (second next)))
                     (+ 1 (fn-arpn-pins-of 1 (second st)))))))
  :rule-classes nil)

; Hypothesis removal: initial underfunding, retaining the arena invariant.
(defthm rpint-without-funding
  (let* ((owners '((11 . 0) (12 . 0))) (st '(0 ((0 . 1)) nil))
         (next (mv-list 3 (fn-rpin-step owners st '(:release 11)))))
    (and (fn-arpn-okp st)
         (not (<= (fn-rpin-count-at 0 owners) (fn-arpn-pins-of 0 (second st))))
         (not (<= (fn-rpin-count-at 0 (first next))
                  (fn-arpn-pins-of 0 (second (second next)))))))
  :rule-classes nil)

; Corrupted-state hypothesis removal: insertion before an out-of-order
; table loses the older row's apparent refcount; funded relation retained.
(defthm rpint-without-arena-invariant-corrupted-state
  (let* ((owners '((11 . 1) (12 . 1))) (st '(1 ((5 . 1) (1 . 2)) nil))
         (next (mv-list 3 (fn-rpin-step owners st '(:acquire 13)))))
    (and (not (fn-arpn-okp st))
         (<= (fn-rpin-count-at 1 owners) (fn-arpn-pins-of 1 (second st)))
         (not (<= (fn-rpin-count-at 1 (first next))
                  (fn-arpn-pins-of 1 (second (second next)))))))
  :rule-classes nil)

; Duplicate capture does not replace the first generation or allocate a
; second hold; cancellation and its duplicate settle exactly once.
(assert-event
 (equal (mv-list 3 (fn-rpin-step (first *rpint-second*) (second *rpint-second*) '(:acquire 11)))
        (list (first *rpint-second*) (second *rpint-second*) :duplicate)))
(assert-event
 (let* ((once (mv-list 3 (fn-rpin-step (first *rpint-second*) (second *rpint-second*) '(:release 11)))))
   (equal (mv-list 3 (fn-rpin-step (first once) (second once) '(:release 11)))
          (list (first once) (second once) :absent))))

; Mutation: releasing an arbitrary generation (0, the cancelled reader's)
; cannot settle the outstanding response at generation 1.
(assert-event
 (not (equal (nth 0 (mv-list 2 (fn-arpn-step (second *rpint-second*) '(:unpin 0))))
             (nth 1 (mv-list 3 (fn-rpin-step (first *rpint-second*) (second *rpint-second*) '(:release 12)))))))
