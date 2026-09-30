(in-package "ACL2")
(include-book "../../books/snapshot-held-remap")
(defconst *ohrt-binding*
 (fn-ab-make :native-source (append *fn-ab-subject-head* (make-list 32 :initial-element 0))))
(defconst *ohrt-wire*
  (fn-record-make 0 0 0 "<one@example>" '(1 2 3) '("fn.test")
                  "p" "c" "r" 1 841000000 *ohrt-binding*))
(defconst *ohrt-valid* (fn-held-plain *ohrt-wire* 3))
; Complete actual held-shape preservation antecedent and conclusion.
(assert-event
 (and (fn-held-p *ohrt-valid*) (natp 7)
      (fn-held-p (fn-orm-held *ohrt-valid* 7))))
; Literal removals: retain the other hypothesis, fail the omitted one
; and affirmatively fail the complete shape conclusion.
(assert-event
 (and (fn-held-p *ohrt-valid*) (not (natp :bad))
      (not (fn-held-p (fn-orm-held *ohrt-valid* :bad)))))
(assert-event
 (and (not (fn-held-p nil)) (natp 7)
      (not (fn-held-p (fn-orm-held nil 7)))))
(defconst *ohrt-row* '(4 3 2 "<x@fn>" 99 (("fn.test" . 3)) nil nil nil 17 9
                      (12 2 1 nil) (verdict delta 2) (("fn.test" . 3)) nil))
; Unconditional actual slot-update and full borrowed-tail boundaries.
(assert-event (equal (fn-orm-held *ohrt-row* 7) (update-nth 4 7 *ohrt-row*)))
(assert-event
 (and (equal (fn-orm-tail 5 (fn-orm-held *ohrt-row* 7)) (fn-orm-tail 5 *ohrt-row*))
      (equal (fn-orm-metadata (fn-orm-held *ohrt-row* 7)) (fn-orm-metadata *ohrt-row*))))
; Arbitrary appended fields are borrowed, not inferred or recomputed. This
; generic list witness does not assert acceptance of another Store format.
(defconst *ohrt-extended* (append *ohrt-row* '((:binding original-subject))))
(assert-event
 (and (equal (fn-orm-held *ohrt-extended* 8) (update-nth 4 8 *ohrt-extended*))
      (equal (fn-orm-tail 5 (fn-orm-held *ohrt-extended* 8)) (fn-orm-tail 5 *ohrt-extended*))
      (equal (fn-orm-metadata (fn-orm-held *ohrt-extended* 8)) (fn-orm-metadata *ohrt-extended*))
      (equal (nth 15 (fn-orm-held *ohrt-extended* 8)) '(:binding original-subject))))
(assert-event
 (let ((new (fn-orm-held *ohrt-row* 7)))
   (and (equal (fn-held-sequence new) (fn-held-sequence *ohrt-row*))
        (equal (fn-held-txid new) (fn-held-txid *ohrt-row*))
        (equal (fn-held-generation new) (fn-held-generation *ohrt-row*))
        (equal (fn-held-msgid new) (fn-held-msgid *ohrt-row*))
        (equal (fn-held-payload new) 7)
        (equal (fn-held-groups new) (fn-held-groups *ohrt-row*))
        (equal (fn-held-obligation-id new) (fn-held-obligation-id *ohrt-row*))
        (equal (fn-held-content-subject new) (fn-held-content-subject *ohrt-row*))
        (equal (fn-held-release-evidence new) (fn-held-release-evidence *ohrt-row*))
        (equal (fn-held-charge new) (fn-held-charge *ohrt-row*))
        (equal (fn-held-stamp new) (fn-held-stamp *ohrt-row*))
        (equal (fn-held-facts new) (fn-held-facts *ohrt-row*))
        (equal (fn-held-context new) (fn-held-context *ohrt-row*))
        (equal (fn-held-numbers new) (fn-held-numbers *ohrt-row*))
        (equal (fn-held-withdrawn new) (fn-held-withdrawn *ohrt-row*))
        (equal (fn-held-binding new) (fn-held-binding *ohrt-row*)))))
(assert-event
 (equal (fn-held-wire (fn-orm-held *ohrt-row* 7) '(1 2 3))
        (fn-held-wire *ohrt-row* '(1 2 3))))

; Actual current held16 descriptor survives the remap, including when the
; natural handle crosses its canonical encoded-width boundary.
(assert-event
 (let ((new (fn-orm-held *ohrt-valid* 256)))
  (and (fn-held-p *ohrt-valid*) (natp 256) (fn-held-p new)
       (equal (fn-held-binding new) *ohrt-binding*)
       (equal (fn-orm-metadata new) (fn-orm-metadata *ohrt-valid*))
       (equal (fn-held-wire new '(1 2 3)) (fn-held-wire *ohrt-valid* '(1 2 3))))))
