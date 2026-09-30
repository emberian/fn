(in-package "ACL2")
(include-book "../../books/over-byte-range-relation")

(defun-nx obrr-emit-conclusionp (s fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (let ((r (fn-obc-one s fn-arena fn-cat)))
  (and (fn-npw-piecesp (nth 4 (mv-nth 1 r)) fn-arena)
  (equal (append (mv-nth 0 r)
                 (fn-obc-actual-old-residual (mv-nth 1 r) fn-arena fn-cat))
         (fn-obc-actual-old-residual s fn-arena fn-cat)))))

(defun-nx obrr-conclusionp (s fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (let ((r (fn-obc-one s fn-arena fn-cat)))
  (equal (append (mv-nth 0 r)
                 (fn-obc-actual-old-residual (mv-nth 1 r) fn-arena fn-cat))
         (fn-obc-actual-old-residual s fn-arena fn-cat))))

(defthm obrr-emit-positive-complete
 (let ((s (fn-obc-make (fn-ovw-cursor "fn.test" 2 3 0 nil nil)
                       nil :emit nil '((65 66)) 0))
       (fn-arena nil) (fn-cat nil))
  (and (equal (nth 2 s) :emit)
       (fn-npw-piecesp (nth 4 s) fn-arena) (natp (nth 5 s))
       (obrr-emit-conclusionp s fn-arena fn-cat)
       (equal (fn-obc-actual-old-residual s fn-arena fn-cat)
              '(65 66 46 13 10))))
 :rule-classes nil)

(defthm obrr-exhaustion-owed-and-advanced-positive
 (let ((fn-arena nil) (fn-cat nil))
  (and
   (let ((s (fn-obc-begin (fn-ovw-cursor "fn.test" 4 3 0 nil t) nil)))
    (and (equal (nth 2 s) :seek)
         (< (nfix (nth 2 (nth 0 s))) (nfix (nth 1 (nth 0 s))))
         (obrr-conclusionp s fn-arena fn-cat)
         (equal (fn-obc-actual-old-residual s fn-arena fn-cat)
                (fn-ovw-status (fn-ovw-empty-text nil)))))
   (let ((s (fn-obc-begin (fn-ovw-cursor "fn.test" 4 3 0 t nil) nil)))
    (and (equal (nth 2 s) :seek)
         (< (nfix (nth 2 (nth 0 s))) (nfix (nth 1 (nth 0 s))))
         (obrr-conclusionp s fn-arena fn-cat)
         (equal (fn-obc-actual-old-residual s fn-arena fn-cat) '(46 13 10))))))
 :rule-classes nil)

; Corrupted-state literal hypothesis removal: unsupported phase.
(defthm obrr-emit-phase-removal
 (let ((s (fn-obc-make (fn-ovw-cursor "fn.test" 1 2 0 nil nil)
                       nil :bad nil '((65)) 0))
       (fn-arena nil) (fn-cat nil))
  (and (not (equal (nth 2 s) :emit))
       (fn-npw-piecesp (nth 4 s) fn-arena) (natp (nth 5 s))
       (not (obrr-emit-conclusionp s fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal hypothesis removal: negative position.
(defthm obrr-emit-position-removal
 (let ((s (fn-obc-make nil nil :emit nil '("AB") -1))
       (fn-arena nil) (fn-cat nil))
  (and (equal (nth 2 s) :emit)
       (fn-npw-piecesp (nth 4 s) fn-arena) (not (natp (nth 5 s)))
       (not (obrr-emit-conclusionp s fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal hypothesis removal: unbound scalar span.
(defthm obrr-emit-pieces-removal
 (let ((s (fn-obc-make nil nil :emit nil '((:span 0 0 2 nil nil)) 0))
       (fn-arena nil) (fn-cat nil))
  (and (equal (nth 2 s) :emit)
       (not (fn-npw-piecesp (nth 4 s) fn-arena)) (natp (nth 5 s))
       (not (obrr-emit-conclusionp s fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal hypothesis removal: unsupported phase.
(defthm obrr-exhaustion-phase-removal
 (let ((s (fn-obc-make (fn-ovw-cursor "fn.test" 4 3 0 nil nil)
                       nil :bad nil nil 0))
       (fn-arena nil) (fn-cat nil))
  (and (not (equal (nth 2 s) :seek))
       (< (nfix (nth 2 (nth 0 s))) (nfix (nth 1 (nth 0 s))))
       (not (obrr-conclusionp s fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal hypothesis removal: missing seek range.
(defthm obrr-exhaustion-bound-removal
 (let ((s (fn-obc-begin nil nil))
       (fn-arena nil) (fn-cat nil))
  (and (equal (nth 2 s) :seek)
       (not (< (nfix (nth 2 (nth 0 s))) (nfix (nth 1 (nth 0 s)))))
       (not (obrr-conclusionp s fn-arena fn-cat))))
 :rule-classes nil)
