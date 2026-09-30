(in-package "ACL2")
(include-book "../../books/nov-piece-window")

(defconst *npwt-pieces*
  '((:decimal 123 nil) (9) "cached" (9)
    (:span 0 0 5 nil (:origin 7)) (9) (:decimal 0 nil) (13 10)))
(defconst *npwt-arena* '((65 13 10 9 66)))
(defconst *npwt-row* '(49 50 51 9 99 97 99 104 101 100 9 65 32 66 9 48 13 10))

; Literal full antecedent and conclusion of the mixed-cursor keystone.
; This quantum finishes numerical setup and emits only its first digit.
(defthm npwt-bounded-progress-positive
  (let* ((pieces *npwt-pieces*) (pos 0) (fuel 4) (arena *npwt-arena*)
         (r (fn-npw-tick pieces pos fuel arena)))
    (and (fn-npw-piecesp pieces arena) (natp pos) (posp fuel) (consp pieces)
         (fn-npw-piecesp (mv-nth 1 r) arena)
         (natp (mv-nth 2 r)) (fn-cbor-octet-listp (mv-nth 0 r))
         (< 0 (mv-nth 3 r)) (<= (mv-nth 3 r) fuel)
         (<= (len (mv-nth 0 r)) fuel)
         (equal (append (mv-nth 0 r)
                        (fn-npw-remaining (mv-nth 1 r) (mv-nth 2 r) arena))
                (fn-npw-remaining pieces pos arena))
         (< (fn-npw-demand (mv-nth 1 r) (mv-nth 2 r)) (fn-npw-demand pieces pos))
         (equal (mv-nth 0 r) '(49))))
  :rule-classes nil)

(defthm npwt-without-pieces-shape-corrupted-state
  (let* ((pieces '((:decimal 0 bad-tail))) (pos 0) (fuel 1) (arena nil)
         (r (fn-npw-tick pieces pos fuel arena)))
    (and (not (fn-npw-piecesp pieces arena)) (natp pos) (posp fuel) (consp pieces)
         (not (equal (append (mv-nth 0 r)
                             (fn-npw-remaining (mv-nth 1 r) (mv-nth 2 r) arena))
                     (fn-npw-remaining pieces pos arena)))))
  :rule-classes nil)

(defthm npwt-without-natural-position-corrupted-state
  (let* ((pieces '("AB")) (pos -1) (fuel 1) (arena nil)
         (r (fn-npw-tick pieces pos fuel arena)))
    (and (fn-npw-piecesp pieces arena) (not (natp pos)) (posp fuel) (consp pieces)
         (not (equal (append (mv-nth 0 r)
                             (fn-npw-remaining (mv-nth 1 r) (mv-nth 2 r) arena))
                     (fn-npw-remaining pieces pos arena)))))
  :rule-classes nil)

(defthm npwt-without-positive-fuel
  (let* ((pieces *npwt-pieces*) (pos 0) (fuel 0) (arena *npwt-arena*)
         (r (fn-npw-tick pieces pos fuel arena)))
    (and (fn-npw-piecesp pieces arena) (natp pos) (not (posp fuel)) (consp pieces)
         (not (< 0 (mv-nth 3 r)))
         (not (< (fn-npw-demand (mv-nth 1 r) (mv-nth 2 r))
                 (fn-npw-demand pieces pos)))))
  :rule-classes nil)

(defthm npwt-without-live-pieces
  (let* ((pieces nil) (pos 0) (fuel 1) (arena nil)
         (r (fn-npw-tick pieces pos fuel arena)))
    (and (fn-npw-piecesp pieces arena) (natp pos) (posp fuel) (not (consp pieces))
         (not (< 0 (mv-nth 3 r)))
         (not (< (fn-npw-demand (mv-nth 1 r) (mv-nth 2 r))
                 (fn-npw-demand pieces pos)))))
  :rule-classes nil)

(defthm npwt-complete-mixed-row
  (let ((r (fn-npw-tick *npwt-pieces* 0 100 *npwt-arena*)))
    (and (equal (mv-nth 0 r) *npwt-row*) (null (mv-nth 1 r))
         (equal (fn-npw-remaining *npwt-pieces* 0 *npwt-arena*) *npwt-row*)))
  :rule-classes nil)

(defthm npwt-origin-pin-and-split-fold
  (let* ((pieces '((:span 0 0 5 nil (:origin 7))))
         (r (fn-npw-tick pieces 0 2 *npwt-arena*))
         (s (fn-npw-tick (mv-nth 1 r) (mv-nth 2 r) 1 *npwt-arena*)))
    (and (equal r '((65) ((:span 0 2 3 t (:origin 7))) 0 2))
         (equal s '(nil ((:span 0 3 2 nil (:origin 7))) 0 1))))
  :rule-classes nil)

; Empty fields and zero spend finite setup/end transitions and still drain.
(defthm npwt-empty-fields-and-zero
  (let ((r (fn-npw-tick '("" nil (:chars) (:decimal 0 nil)) 0 10 nil)))
    (and (equal (mv-nth 0 r) '(48)) (null (mv-nth 1 r))
         (equal (mv-nth 3 r) 6)))
  :rule-classes nil)

; General numerical continuation renders every digit; no ten-digit clamp.
(defthm npwt-wide-number-continuation
  (let* ((pieces '((:decimal 123456789012345678901234567890 nil)))
         (a (fn-npw-tick pieces 0 10 nil))
         (b (fn-npw-tick (mv-nth 1 a) (mv-nth 2 a) 100 nil)))
    (and (null (mv-nth 0 a)) (consp (mv-nth 1 a))
         (equal (mv-nth 0 b) (fn-record-string-octets "123456789012345678901234567890"))
         (null (mv-nth 1 b))))
  :rule-classes nil)

; Mutating only the pending-CR carry changes the row's exact residual.
(defthm npwt-lost-fold-carry-mutation
  (not (equal (fn-npw-remaining '((:span 0 2 3 nil (:origin 7))) 0 *npwt-arena*)
              (fn-npw-remaining '((:span 0 2 3 t (:origin 7))) 0 *npwt-arena*)))
  :rule-classes nil)

; Guard-verified concrete arena execution through the full mixed loop.
(assert-event
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list '(65 13 10 9 66) fn-arena))
        (a (mv-list 4 (fn-npw-tick *npwt-pieces* 0 4 fn-arena)))
        (b (mv-list 4 (fn-npw-tick (mv-nth 1 a) (mv-nth 2 a) 100 fn-arena))))
   (mv (and (fn-arena-p fn-arena) (equal (mv-nth 0 a) '(49))
            (equal (append (mv-nth 0 a) (mv-nth 0 b)) *npwt-row*)
            (null (mv-nth 1 b))) fn-arena))
 :stobjs-out '(nil fn-arena))
