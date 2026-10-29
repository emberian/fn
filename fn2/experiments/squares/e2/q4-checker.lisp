; E2 Q4 executable evidence adapter; theorem formulas retain the unbounded
; DEFUN-SK relation. Runtime checks use the canonical converter and explicit
; finite query bounds; they are evidence, never a replacement for the proof.
(in-package "ACL2")
(include-book "read-state-teeth")

(defun sq-q4-field (key plist)
  (declare (xargs :verify-guards nil))
  (cadr (member-eq key plist)))

(defun sq-q4-queries-agree (h s bound)
  (declare (xargs :verify-guards nil))
  (if (zp bound) t
    (and (equal (rs-h-obs-read h bound) (rs-s-obs-read s bound))
         (equal (rs-h-obs-count h bound) (rs-s-obs-count s bound))
         (sq-q4-queries-agree h s (1- bound)))))

(defun sq-q4-event-case (e)
  (declare (xargs :verify-guards nil))
  (if (rs-eventp e) (car e) :malformed))

(defun sq-q4-positive ()
  (declare (xargs :verify-guards nil))
  (let* ((h '((:read 1))) (s '(1))
         (j '((:read 3) (:catchup 1) (:read 0)))
         (h2 (rs-h-fold h j)) (s2 (rs-s-fold s j)))
    (and (rs-h-ok h) (rs-s-ok s) (equal s (rs-summarize h))
         (rs-h-ok h2) (rs-s-ok s2) (equal s2 (rs-summarize h2))
         (sq-q4-queries-agree h2 s2 5))))

; Tooth 1 evaluates the exact false step obligation for count-at-2 equality.
; Equality of counts at EVERY bound would identify the set, so that is not
; the weak relation being rejected here.
(defun sq-q4-count-only-refused ()
  (declare (xargs :verify-guards nil))
  (and (rs-h-ok *rs-s1*) (rs-h-ok *rs-s2*)
       (rs-count2-rel *rs-s1* *rs-s2*)
       (not (rs-count2-rel (rs-h-step *rs-s1* '(:read 1))
                          (rs-h-step *rs-s2* '(:read 1))))))

; Tooth 2 checks the related admissible pre-state and disagreement on N=2.
(defun sq-q4-off-by-one-refused ()
  (declare (xargs :verify-guards nil))
  (let* ((h '((:read 1))) (s '(1)) (e '(:read 3))
         (h2 (rs-h-step h e)) (bad (rs-s-bad-step s e)))
    (and (rs-h-ok h) (rs-s-ok s) (equal s (rs-summarize h))
         (rs-eventp e) (equal (car e) :read)
         (not (equal (rs-h-obs-read h2 2) (rs-s-obs-read bad 2)))
         (equal (rs-h-obs-read h2 2) nil)
         (equal (rs-s-obs-read bad 2) t))))

(defun sq-q4-negative ()
  (declare (xargs :verify-guards nil))
  (and (sq-q4-count-only-refused) (sq-q4-off-by-one-refused)))

(defun sq-q4-checker (row sample)
  (declare (xargs :verify-guards nil))
  (let* ((case (sq-q4-field :case row))
         (h (sq-q4-field :history sample))
         (s (sq-q4-field :summary sample))
         (j (sq-q4-field :events sample))
         (bound (sq-q4-field :bound sample))
         (converter (eq case :converter))
         (composition (eq case :composition))
         (matched (or converter composition
                      (and (consp j) (null (cdr j))
                           (equal case (sq-q4-event-case (car j))))))
         (pre (and (rs-h-ok h) (natp bound)
                   (or converter
                       (and (rs-s-ok s) (equal s (rs-summarize h))))))
         (h2 (if converter h (rs-h-fold h j)))
         (s2 (if converter (rs-summarize h) (rs-s-fold s j))))
    (cond ((not matched) '(:reached 1 :exercised 0 :verdict :unexercised))
          ((not pre) '(:reached 1 :exercised 1 :verdict :fail))
          ((and (rs-h-ok h2) (rs-s-ok s2)
                (equal s2 (rs-summarize h2))
                (sq-q4-queries-agree h2 s2 bound)
                (sq-q4-positive) (sq-q4-negative))
           '(:reached 1 :exercised 1 :verdict :pass))
          (t '(:reached 1 :exercised 1 :verdict :fail)))))

(assert-event (sq-q4-positive))
(assert-event (sq-q4-count-only-refused))
(assert-event (sq-q4-off-by-one-refused))
(assert-event
 (equal (sq-q4-checker '(:case :read)
                       '(:history ((:read 1)) :summary (1)
                         :events ((:read 3)) :bound 5))
        '(:reached 1 :exercised 1 :verdict :pass)))
(assert-event
 (equal (sq-q4-checker '(:case :catchup)
                       '(:history ((:read 1)) :summary (1)
                         :events ((:read 3)) :bound 5))
        '(:reached 1 :exercised 0 :verdict :unexercised)))
(assert-event
 (equal (sq-q4-checker '(:case :read)
                       '(:history ((:read 1)) :summary (2)
                         :events ((:read 3)) :bound 5))
        '(:reached 1 :exercised 1 :verdict :fail)))
