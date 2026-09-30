(in-package "ACL2")
(include-book "../../books/nov-column-pieces")

(defconst *npwt-column-facts*
  '(123456789012345678901234567890 nil 10000000000
    (nil nil nil (nil t "S" "F" "D" "<m>" ""))))

; Literal full antecedent and conclusion of the constructor refinement.
(defthm npwt-column-wide-positive
  (let ((facts *npwt-column-facts*) (octets 123456789012345678901234567890))
    (and (fn-hnov-p (fn-hf-nov facts)) (natp octets) (natp (fn-hf-body-lines facts))
         (equal (fn-npw-remaining (fn-npw-column-pieces 7 facts octets) 0 nil)
                (fn-nbw-remaining (fn-nbw-column-pieces 7 facts octets) 0))))
  :rule-classes nil)

(defthm npwt-column-without-natural-octets-corrupted-state
  (let ((facts *npwt-column-facts*) (octets -1))
    (and (fn-hnov-p (fn-hf-nov facts)) (not (natp octets))
         (natp (fn-hf-body-lines facts))
         (not (equal (fn-npw-remaining (fn-npw-column-pieces 7 facts octets) 0 nil)
                     (fn-nbw-remaining (fn-nbw-column-pieces 7 facts octets) 0)))))
  :rule-classes nil)

(defthm npwt-column-without-natural-lines-corrupted-state
  (let ((facts '(0 nil -1 (nil nil nil (nil t "S" "F" "D" "<m>" "")))))
    (and (fn-hnov-p (fn-hf-nov facts)) (natp 0)
         (not (natp (fn-hf-body-lines facts)))
         (not (equal (fn-npw-remaining (fn-npw-column-pieces 7 facts 0) 0 nil)
                     (fn-nbw-remaining (fn-nbw-column-pieces 7 facts 0) 0)))))
  :rule-classes nil)

(defthm npwt-column-without-shape-corrupted-state
  (let ((facts '(0 nil 0 (nil nil nil (nil t (:decimal 1 nil) "F" "D" "<m>" "")))))
    (and (not (fn-hnov-p (fn-hf-nov facts))) (natp 0)
         (natp (fn-hf-body-lines facts))
         (not (equal (fn-npw-remaining (fn-npw-column-pieces 7 facts 0) 0 nil)
                     (fn-nbw-remaining (fn-nbw-column-pieces 7 facts 0) 0)))))
  :rule-classes nil)

; Actual guarded runtime: capture fixed references, yield mid-decimal setup,
; resume, and compare the complete semantic row including its CRLF.
(assert-event
 (let* ((pieces (fn-npw-column-pieces 7 *npwt-column-facts*
                                    123456789012345678901234567890))
        (a (mv-list 4 (fn-npw-tick pieces 0 30 fn-arena)))
        (b (mv-list 4 (fn-npw-tick (mv-nth 1 a) (mv-nth 2 a) 150 fn-arena))))
   (mv (and (fn-npw-piecesp pieces fn-arena)
            (consp (mv-nth 1 a)) (null (mv-nth 1 b))
            (equal (append (mv-nth 0 a) (mv-nth 0 b))
                   (append (fn-nov-line 7 '(:ok (83) (70) (68) (60 109 62) nil
                                           123456789012345678901234567890 10000000000))
                           '(13 10)))) fn-arena))
 :stobjs-out '(nil fn-arena))
