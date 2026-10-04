; Finite scheduling potential for the actual retained LIST row renderer.
; Logical references only: no piece/string walk occurs at production start.
(in-package "ACL2")
(include-book "list-row-cursor")

(local (in-theory (disable (tau-system))))

(defun-nx fn-lsr-piece-work (piece)
  (if (eq (fn-cur-at 0 piece) :number) 22
    (+ 2 (if (stringp (fn-cur-at 1 piece)) (length (fn-cur-at 1 piece)) 0))))

(defun-nx fn-lsr-pieces-work (pieces)
  (if (consp pieces)
      (+ (fn-lsr-piece-work (car pieces)) (fn-lsr-pieces-work (cdr pieces)))
    0))

(defun-nx fn-lsr-remaining-work (cur)
  (let* ((pieces (fn-cur-at 0 cur))
         (phase (fn-cur-at 1 cur))
         (offset (nfix (fn-cur-at 2 cur)))
         (digits (fn-cur-at 5 cur))
         (first (if (fn-cur-at 6 cur) 1 0))
         (value (fn-cur-at 1 (fn-cur-at 0 pieces)))
         (chars (if (stringp value) (length value) 0))
         (future (+ 3 first (fn-lsr-pieces-work (if (consp pieces) (cdr pieces) nil)))))
    (cond ((not cur) 0)
          ((eq phase :piece) (+ 3 first (fn-lsr-pieces-work pieces)))
          ((eq phase :text) (+ 1 (nfix (- chars offset)) future))
          ((eq phase :build) (+ (nfix (- 21 offset)) future))
          ((eq phase :digits) (+ 1 (len digits) future))
          ((eq phase :cr) 2)
          ((eq phase :lf) 1)
          (t 1))))

(defthm fn-lsr-remaining-work-natp
  (natp (fn-lsr-remaining-work cur))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fn-lsr-remaining-work))))

; The carried digit shape covers the only phase whose potential uses a
; partially built decimal. No supplied data is scanned to establish it per step.
(defthm fn-lsr-one-finite-progress
  (implies (and cur (fn-lsr-statep cur))
           (< (fn-lsr-remaining-work (mv-nth 1 (fn-lsr-one cur)))
              (fn-lsr-remaining-work cur)))
  :hints (("Goal" :in-theory
           (e/d (fn-lsr-one fn-lsr-remaining-work fn-lsr-pieces-work
                 fn-lsr-piece-work fn-lsr-statep)
                (fn-cur-at fn-lsr-make)))))

(in-theory (disable fn-lsr-piece-work fn-lsr-pieces-work fn-lsr-remaining-work))
