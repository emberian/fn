(in-package "ACL2")
(include-book "../../books/nov-span-window")

; A real folded value, stopped between CR and LF. One consumed source
; octet may emit nothing; the exact pending CR belongs to the continuation.
(defthm nswt-split-fold-positive
  (let* ((arena '((65 13 10 9 66)))
         (first (fn-nsw-step 0 0 5 nil 2 arena))
         (next (fn-nsw-step 0 (mv-nth 1 first) (mv-nth 2 first)
                            (mv-nth 3 first) 1 arena)))
    (and (equal first '((65) 2 3 t 2))
         (equal next '(nil 3 2 nil 1))
         (equal (append (mv-nth 0 first) (mv-nth 0 next)
                         (fn-nsw-remaining 0 (mv-nth 1 next) (mv-nth 2 next)
                                             (mv-nth 3 next) arena))
                (fn-nov-scrub '(65 13 10 9 66)))))
  :rule-classes nil)

; A bare CR is normalized to SP, with the following octet left unread.
; This is a corrupted source witness, distinct from a valid header fold.
(defthm nswt-unpaired-cr-corrupted-source
  (let* ((arena '((13 65))) (first (fn-nsw-step 0 0 2 nil 1 arena))
         (next (fn-nsw-step 0 1 1 t 1 arena)))
    (and (equal first '(nil 1 1 t 1))
         (equal next '((32) 1 1 nil 1))
         (equal (append (mv-nth 0 first) (mv-nth 0 next)
                         (fn-nsw-remaining 0 1 1 nil arena))
                (fn-nov-scrub '(13 65)))))
  :rule-classes nil)

(defthm nswt-progress-positive
  (let* ((at 0) (left 2) (pending nil) (fuel 1)
         (r (fn-nsw-step-aux 0 at left pending fuel nil '((13 10)))))
    (and (natp left) (posp fuel) (or (< 0 left) pending)
         (< (+ (* 2 (mv-nth 2 r)) (if (mv-nth 3 r) 1 0))
            (+ (* 2 left) (if pending 1 0)))
         (natp at) (natp (mv-nth 1 r)) (natp (mv-nth 2 r))
         (<= (mv-nth 2 r) left)
         (equal (+ (mv-nth 1 r) (mv-nth 2 r)) (+ at left))
         (<= (- left (mv-nth 2 r)) (nfix fuel))
         (<= (mv-nth 4 r) (nfix fuel))
         (<= (len (mv-nth 0 r)) (nfix fuel))
         (fn-octet-listp nil) (fn-octet-listp (mv-nth 0 r))))
  :rule-classes nil)

(defthm nswt-progress-without-natural-left-corrupted-state
  (let* ((left 1/2) (pending nil) (fuel 1)
         (r (fn-nsw-step-aux 0 0 left pending fuel nil '(nil))))
    (and (not (natp left)) (posp fuel) (or (< 0 left) pending)
         (not (< (+ (* 2 (mv-nth 2 r)) (if (mv-nth 3 r) 1 0))
                 (+ (* 2 left) (if pending 1 0))))))
  :rule-classes nil)

(defthm nswt-progress-without-positive-fuel
  (let* ((left 2) (pending nil) (fuel 0)
         (r (fn-nsw-step-aux 0 0 left pending fuel nil '((13 10)))))
    (and (natp left) (not (posp fuel)) (or (< 0 left) pending)
         (not (< (+ (* 2 (mv-nth 2 r)) (if (mv-nth 3 r) 1 0))
                 (+ (* 2 left) (if pending 1 0))))))
  :rule-classes nil)

(defthm nswt-progress-without-active-state
  (let* ((left 0) (pending nil) (fuel 1)
         (r (fn-nsw-step-aux 0 0 left pending fuel nil '(nil))))
    (and (natp left) (posp fuel) (not (or (< 0 left) pending))
         (not (< (+ (* 2 (mv-nth 2 r)) (if (mv-nth 3 r) 1 0))
                 (+ (* 2 left) (if pending 1 0))))))
  :rule-classes nil)

(defthm nswt-residual-positive
  (let* ((arena '((65 13 10 9 66)))
         (r (fn-nsw-step-aux 0 0 5 nil 2 '(90) arena)))
    (equal (append (mv-nth 0 r)
                   (fn-nsw-remaining 0 (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) arena))
           (append (revappend '(90) nil) (fn-nsw-remaining 0 0 5 nil arena))))
  :rule-classes nil)

(defthm nswt-position-without-natural-start-corrupted-state
  (let* ((at -1) (left 0)
         (r (fn-nsw-step-aux 0 at left nil 1 nil '(nil))))
    (and (not (natp at)) (natp left) (not (natp (mv-nth 1 r)))))
  :rule-classes nil)

(defthm nswt-position-without-natural-left-corrupted-state
  (let* ((at 0) (left -1)
         (r (fn-nsw-step-aux 0 at left nil 1 nil '(nil))))
    (and (natp at) (not (natp left)) (not (natp (mv-nth 2 r)))))
  :rule-classes nil)

(defthm nswt-output-without-octet-accumulator-corrupted-state
  (let ((acc '(256)))
    (and (not (fn-octet-listp acc))
         (not (fn-octet-listp (mv-nth 0 (fn-nsw-step-aux 0 0 0 nil 1 acc '(nil)))))))
  :rule-classes nil)

(defthm nswt-slice-positive
  (let ((at 1) (arena '((65 13 10 9 66))))
    (and (natp at)
         (equal (fn-nsw-source 0 at 3 arena) (take 3 (nthcdr at (nth 0 arena))))
         (equal (fn-nsw-source 0 at 3 arena) '(13 10 9))))
  :rule-classes nil)

(defthm nswt-slice-without-natural-start-corrupted-state
  (let ((at -1) (arena '((65 66))))
    (and (not (natp at))
         (not (equal (fn-nsw-source 0 at 2 arena) (take 2 (nthcdr at (nth 0 arena)))))))
  :rule-classes nil)

; Mutation: dropping the carried CR before the next quantum changes the
; folded field from A<TAB>B to A<SP><TAB>B after scrubbing.
(defthm nswt-lost-cr-mutation
  (let* ((arena '((65 13 10 9 66)))
         (first (fn-nsw-step 0 0 5 nil 2 arena)))
    (and (equal (mv-nth 3 first) t)
         (not (equal (append (mv-nth 0 first) (fn-nsw-remaining 0 2 3 nil arena))
                     (fn-nov-scrub '(65 13 10 9 66))))))
  :rule-classes nil)

; Actual guard-verified arena execution, including a quantum that emits no
; byte and a final drain of the two normalized value bytes.
(assert-event
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list '(65 13 10 9 66) fn-arena))
        (first (mv-list 5 (fn-nsw-step 0 0 5 nil 2 fn-arena)))
        (next (mv-list 5 (fn-nsw-step 0 2 3 t 1 fn-arena)))
        (last (mv-list 5 (fn-nsw-step 0 3 2 nil 2 fn-arena))))
   (mv (and (fn-arena-p fn-arena)
            (equal first '((65) 2 3 t 2))
            (equal next '(nil 3 2 nil 1))
            (equal last '((32 66) 5 0 nil 2)))
       fn-arena))
 :stobjs-out '(nil fn-arena))
