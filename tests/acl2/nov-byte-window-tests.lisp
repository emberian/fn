(in-package "ACL2")
(include-book "../../books/nov-byte-window")

; Reachable mixed cached-field pieces, numeric/delimiter bytes and empty
; optional fields. The accumulator is already produced prefix owned here.
(defthm nbwt-residual-positive
  (let* ((pieces '("abc" (9) "" "de" (13 10))) (pos 1)
         (next (mv-list 4 (fn-nbw-step-aux pieces pos 4 '(88) 0))))
    (and (fn-nbw-piecesp pieces) (natp pos)
         (equal (append (first next) (fn-nbw-remaining (second next) (third next)))
                (append (revappend '(88) nil) (fn-nbw-remaining pieces pos)))
         (equal (first next) '(88 98 99 9))
         (equal (second next) '(nil "" "de" (13 10)))
         (equal (third next) 0) (equal (fourth next) 4)))
  :rule-classes nil)

; Corrupted metadata: a dotted byte list whose tail is a string turns into
; a new string piece at runtime. Retain the natural-offset hypothesis.
(defthm nbwt-without-pieces-invariant-corrupted-state
  (let* ((pieces '((65 . "BC"))) (pos 0)
         (next (mv-list 4 (fn-nbw-step-aux pieces pos 1 nil 0))))
    (and (not (fn-nbw-piecesp pieces)) (natp pos)
         (not (equal (append (first next) (fn-nbw-remaining (second next) (third next)))
                     (fn-nbw-remaining pieces pos)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (pieces pos fuel acc used)
                                  (fn-nbw-step-aux pieces pos fuel acc used)))
                  :in-theory (e/d (fn-nbw-step-aux fn-nbw-remaining)
                                 ((:executable-counterpart fn-nbw-step-aux))))))

; Corrupted continuation: a negative offset repeats the first character.
; The logical witness unfolds the guard-invalid call rather than raw CHAR.
(defthm nbwt-without-natural-offset-corrupted-state
  (let* ((pieces '("AB")) (pos -1)
         (next (mv-list 4 (fn-nbw-step-aux pieces pos 1 nil 0))))
    (and (fn-nbw-piecesp pieces) (not (natp pos))
         (not (equal (append (first next) (fn-nbw-remaining (second next) (third next)))
                     (fn-nbw-remaining pieces pos)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (pieces pos fuel acc used)
                                  (fn-nbw-step-aux pieces pos fuel acc used)))
                  :in-theory (e/d (fn-nbw-step-aux fn-nbw-remaining)
                                 ((:executable-counterpart fn-nbw-step-aux))))))

(defthm nbwt-output-and-work-positive
  (let ((next (mv-list 4 (fn-nbw-step-aux '("abcdef") 0 3 nil 0))))
    (and (natp 3) (natp 0)
         (<= 0 (fourth next)) (<= (fourth next) (+ 0 3))
         (<= (len (first next)) (+ (len nil) 3))
         (equal next '((97 98 99) ("abcdef") 3 3))))
  :rule-classes nil)

(defthm nbwt-without-natural-budget
  (let ((next (mv-list 4 (fn-nbw-step-aux '("abcdef") 0 -1 nil 0))))
    (and (not (natp -1)) (natp 0)
         (not (<= (fourth next) (+ 0 -1)))
         (not (<= (len (first next)) (+ (len nil) -1)))))
  :rule-classes nil)

; Mutation: resetting the offset when a socket paces the next quantum
; duplicates already produced bytes; a continuation must keep its offset.
(defthm nbwt-offset-reset-mutation
  (let* ((first (mv-list 4 (fn-nbw-step '("abcdef") 0 2)))
         (bad (mv-list 4 (fn-nbw-step (second first) 0 2))))
    (and (fn-nbw-piecesp (second first)) (natp (third first))
         (not (equal (append (first first) (first bad)
                             (fn-nbw-remaining (second bad) (third bad)))
                     (fn-nbw-remaining '("abcdef") 0)))))
  :rule-classes nil)

; Positive progress can produce no byte: an empty optional field still
; consumes work and strictly reduces the complete remaining demand.
(defthm nbwt-empty-piece-bounded-progress
  (let* ((pieces '("" "abc")) (pos 0) (fuel 1)
         (next (mv-list 4 (fn-nbw-step pieces pos fuel))))
    (and (fn-nbw-piecesp pieces) (natp pos) (posp fuel) (consp pieces)
         (fn-nbw-piecesp (second next)) (natp (third next))
         (< 0 (fourth next)) (<= (fourth next) fuel)
         (<= (len (first next)) fuel)
         (< (fn-nbw-demand (second next) (third next)) (fn-nbw-demand pieces pos))
         (equal (append (first next) (fn-nbw-remaining (second next) (third next)))
                (fn-nbw-remaining pieces pos))
         (equal next '(nil ("abc") 0 1))))
  :rule-classes nil)

(defthm nbwt-progress-without-positive-budget
  (let* ((pieces '("abc")) (pos 0) (fuel 0)
         (next (mv-list 4 (fn-nbw-step pieces pos fuel))))
    (and (fn-nbw-piecesp pieces) (natp pos) (not (posp fuel)) (consp pieces)
         (not (< (fn-nbw-demand (second next) (third next))
                 (fn-nbw-demand pieces pos)))))
  :rule-classes nil)

(defthm nbwt-progress-without-live-pieces
  (let* ((pieces nil) (pos 0) (fuel 1)
         (next (mv-list 4 (fn-nbw-step pieces pos fuel))))
    (and (fn-nbw-piecesp pieces) (natp pos) (posp fuel) (not (consp pieces))
         (not (< 0 (fourth next)))))
  :rule-classes nil)

(defthm nbwt-progress-without-valid-pieces-corrupted-state
  (let* ((pieces '((65 . "BC"))) (pos 0) (fuel 1)
         (next (mv-list 4 (fn-nbw-step-aux pieces pos fuel nil 0))))
    (and (not (fn-nbw-piecesp pieces)) (natp pos) (posp fuel) (consp pieces)
         (not (< (fn-nbw-demand (second next) (third next))
                 (fn-nbw-demand pieces pos)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (pieces pos fuel acc used)
                                  (fn-nbw-step-aux pieces pos fuel acc used)))
                  :in-theory (e/d (fn-nbw-step-aux fn-nbw-demand)
                                 ((:executable-counterpart fn-nbw-step-aux))))))

(defthm nbwt-progress-without-natural-offset-corrupted-state
  (let* ((pieces '("AB")) (pos -1) (fuel 1)
         (next (mv-list 4 (fn-nbw-step-aux pieces pos fuel nil 0))))
    (and (fn-nbw-piecesp pieces) (not (natp pos)) (posp fuel) (consp pieces)
         (not (< (fn-nbw-demand (second next) (third next))
                 (fn-nbw-demand pieces pos)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (pieces pos fuel acc used)
                                  (fn-nbw-step-aux pieces pos fuel acc used)))
                  :in-theory (e/d (fn-nbw-step-aux fn-nbw-demand)
                                 ((:executable-counterpart fn-nbw-step-aux))))))
