(in-package "ACL2")
(include-book "../../books/snapshot-row-remap")
(include-book "../../books/codec-attach")
(defconst *orm-wire*
  (list (fn-record-make 0 0 0 "<one@example>" '(1 2 3) '("fn.test")
                        "p" "c" "r" 1 841000000)
        (fn-record-make 1 1 0 "<two@example>" '(4 5) '("fn.test")
                        "p" "c" "r" 1 841000001)))
(defun orm-intern-with-orphan ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (let ((fn-arena (fn-arena-seal-list '(99 99) fn-arena)))
        (fn-intern-events *orm-wire* nil 9 fn-arena))
      rows)))
(defconst *orm-rows* (orm-intern-with-orphan))
(defconst *orm-row* (car *orm-rows*))
(defconst *orm-new* (fn-orm-row *orm-row* 0))
; Actual intern under generation9, with an orphan before it.  The captured
; context must stay9 while the handle changes1->0; no nil0 recontext here.
(assert-event
 (and (fn-store-event-p *orm-row*) (natp 0)
      (equal (fn-held-payload *orm-row*) 1)
      (equal (fn-hc-generation (fn-held-context *orm-row*)) 9)
      (fn-store-event-p *orm-new*)
      (equal (fn-orm-projection *orm-new*) (fn-orm-projection *orm-row*))
      (equal (fn-held-sequence *orm-new*) (fn-held-sequence *orm-row*))
      (equal (fn-held-txid *orm-new*) (fn-held-txid *orm-row*))
      (equal (fn-held-generation *orm-new*) (fn-held-generation *orm-row*))
      (equal (fn-held-msgid *orm-new*) (fn-held-msgid *orm-row*))
      (equal (fn-held-payload *orm-new*) 0)
      (equal (fn-held-groups *orm-new*) (fn-held-groups *orm-row*))
      (equal (fn-held-obligation-id *orm-new*) (fn-held-obligation-id *orm-row*))
      (equal (fn-held-content-subject *orm-new*) (fn-held-content-subject *orm-row*))
      (equal (fn-held-release-evidence *orm-new*) (fn-held-release-evidence *orm-row*))
      (equal (fn-held-charge *orm-new*) (fn-held-charge *orm-row*))
      (equal (fn-held-stamp *orm-new*) (fn-held-stamp *orm-row*))
      (equal (fn-held-facts *orm-new*) (fn-held-facts *orm-row*))
      (equal (fn-held-context *orm-new*) (fn-held-context *orm-row*))
      (equal (fn-held-numbers *orm-new*) (fn-held-numbers *orm-row*))
      (equal (fn-held-withdrawn *orm-new*) (fn-held-withdrawn *orm-row*))))
(assert-event
 (and (fn-store-event-p *orm-row*) (<= (len *orm-row*) 15)
      (fn-held-p *orm-row*) (natp 0) (fn-held-p *orm-new*)
      (equal (fn-held-wire *orm-new* '(1 2 3))
             (fn-held-wire *orm-row* '(1 2 3)))))
; Whole logical capture refinement, all retained rows and complete conclusion.
(assert-event
 (and (fn-orm-rowsp *orm-rows*) (natp 0)
      (fn-orm-rowsp (fn-orm-capture *orm-rows* 0))
      (equal (len (fn-orm-capture *orm-rows* 0)) (len *orm-rows*))
      (equal (fn-orm-project-rows (fn-orm-capture *orm-rows* 0))
             (fn-orm-project-rows *orm-rows*))))
(defconst *orm-cursor* (fn-orm-begin *orm-rows*))
(defconst *orm-tick* (fn-orm-tick *orm-cursor*))
; Complete literal continuation antecedent/conclusion, not merely :continue.
(assert-event
 (and (member-equal (fn-orm-at 0 *orm-cursor*) '(:remap :reverse))
      (true-listp (fn-orm-at 1 *orm-cursor*))
      (equal (fn-orm-value *orm-cursor*)
             (if (equal (car *orm-tick*) :continue)
                 (fn-orm-value (nth 1 *orm-tick*)) (nth 1 *orm-tick*)))))
; Complete positive row-progress branch and executable cursor preservation.
(assert-event
 (let ((next (nth 1 *orm-tick*)))
   (and (equal (car *orm-tick*) :continue)
        (equal (fn-orm-at 0 *orm-cursor*) :remap)
        (consp (fn-orm-at 1 *orm-cursor*))
        (equal (fn-orm-at 0 next) :remap)
        (equal (fn-orm-at 1 next) (cdr (fn-orm-at 1 *orm-cursor*)))
        (natp (fn-orm-at 2 *orm-cursor*))
        (implies (equal (fn-orm-at 0 *orm-cursor*) :remap)
                 (fn-orm-rowsp (fn-orm-at 1 *orm-cursor*)))
        (true-listp (fn-orm-at 1 *orm-cursor*))
        (true-listp (fn-orm-at 3 *orm-cursor*))
        (true-listp (fn-orm-at 4 *orm-cursor*))
        (natp (fn-orm-at 2 next))
        (implies (equal (fn-orm-at 0 next) :remap)
                 (fn-orm-rowsp (fn-orm-at 1 next)))
        (true-listp (fn-orm-at 1 next))
        (true-listp (fn-orm-at 3 next))
        (true-listp (fn-orm-at 4 next)))))
(defun orm-run-test (cursor fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) :fuel-exhausted
    (let ((tick (fn-orm-tick cursor)))
      (if (equal (car tick) :continue)
          (orm-run-test (nth 1 tick) (- fuel 1)) tick))))
(assert-event
 (let ((done (orm-run-test *orm-cursor* 8)))
   (and (equal (car done) :done)
        (equal (nth 1 done) (fn-orm-capture *orm-rows* 0)))))
; Corrupted private cursor, phase hypothesis removed; remaining-list retained.
(assert-event
 (let* ((cursor '(:bad nil 0 nil nil)) (tick (fn-orm-tick cursor)))
   (and (not (member-equal (fn-orm-at 0 cursor) '(:remap :reverse)))
        (true-listp (fn-orm-at 1 cursor))
        (not (equal (fn-orm-value cursor)
                    (if (equal (car tick) :continue)
                        (fn-orm-value (nth 1 tick)) (nth 1 tick)))))))
 ; Corrupted private cursor in the logical model, proper remaining-list
; removed; execution does not evaluate the ill-guarded logical continuation.
(defthm orm-corrupt-improper-cursor-tooth
 (let* ((cursor '(:reverse 7 0 nil nil)) (tick (fn-orm-tick cursor)))
   (and (member-equal (fn-orm-at 0 cursor) '(:remap :reverse))
        (not (true-listp (fn-orm-at 1 cursor)))
        (not (equal (fn-orm-value cursor)
                    (if (equal (car tick) :continue)
                        (fn-orm-value (nth 1 tick)) (nth 1 tick))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-orm-at fn-cp-nth fn-orm-value
                                     fn-orm-tick revappend))))
; Corrupted source shape: natural handle kept; complete conclusion fails.
(defthm orm-corrupt-source-row-tooth
 (and (natp 0) (not (fn-store-event-p nil))
      (not (and (fn-store-event-p (fn-orm-row nil 0))
                (equal (fn-orm-projection (fn-orm-row nil 0))
                       (fn-orm-projection nil)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-orm-row fn-store-event-p))))
; Corrupted handle argument: actual interned source shape retained, natural
; handle removed, and the complete shape/projection conclusion fails.
(defthm orm-corrupt-negative-handle-tooth
 (and (fn-store-event-p *orm-row*) (not (natp -1))
      (not (and (fn-store-event-p (fn-orm-row *orm-row* -1))
                (equal (fn-orm-projection (fn-orm-row *orm-row* -1))
                       (fn-orm-projection *orm-row*)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-orm-row fn-store-event-p fn-orm-held
                                     fn-held-p fn-held-internals
                                     fn-record-internals))))

; Arena abstraction witnesses: source has the actual orphan+interned payload
; order; target has canonical order.  These logical teeth are not a file-copy
; or producer native claim. The physical writer/load must establish this map.
(defthm orm-alpha-payload-map-positive-tooth
 (and (fn-store-event-p *orm-row*) (natp 0)
      (implies (fn-held-p *orm-row*)
               (equal (fn-row-bytes (fn-orm-row *orm-row* 0) '((1 2 3) (4 5)))
                      (fn-row-bytes *orm-row* '((99 99) (1 2 3) (4 5)))))
      (equal (fn-row-wire-of (fn-orm-row *orm-row* 0) '((1 2 3) (4 5)))
             (fn-row-wire-of *orm-row* '((99 99) (1 2 3) (4 5)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-row-bytes fn-row-wire-of fn-orm-row
                                     fn-orm-held fn-held-p fn-held-internals
                                     fn-record-internals))))
; Mutation witness: wrong target payload. All retained theorem hypotheses
; are checked, payload correspondence fails, and exact wire alpha fails.
(defthm orm-alpha-wrong-payload-mutation-tooth
 (and (fn-store-event-p *orm-row*) (natp 0)
      (not (implies (fn-held-p *orm-row*)
                    (equal (fn-row-bytes (fn-orm-row *orm-row* 0) '((7) (4 5)))
                           (fn-row-bytes *orm-row* '((99 99) (1 2 3) (4 5))))))
      (not (equal (fn-row-wire-of (fn-orm-row *orm-row* 0) '((7) (4 5)))
                  (fn-row-wire-of *orm-row* '((99 99) (1 2 3) (4 5))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-row-bytes fn-row-wire-of fn-orm-row
                                     fn-orm-held fn-held-p fn-held-internals
                                     fn-record-internals))))

; Composite made by the actual intern, with its own held context and an
; orphan source handle. The original stxa is retained by pointer; the held
; payload's correspondence is checked separately from wire projection.
(defconst *orm-stxa*
  (fn-stxa-make 0 0 0 9 '(112) '(99)
                (fn-record-encode-impl (car *orm-wire*))
                (fn-stxe-encode
                 (fn-stxe-make 0 0 0 "<one@example>" :unverified
                                *fn-stx-token-signature* 9 '(112)))))
(defun orm-composite-intern-with-orphan ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (row fn-arena)
      (let ((fn-arena (fn-arena-seal-list '(99 99) fn-arena)))
        (fn-intern-event *orm-stxa* nil 9 fn-arena))
      row)))
(make-event `(defconst *orm-composite* ',(orm-composite-intern-with-orphan)))
(defconst *orm-composite-new* (fn-orm-row *orm-composite* 0))
(assert-event
 (and (fn-store-event-p *orm-composite*) (natp 0)
      (fn-hstxa-p *orm-composite*)
      (equal (fn-held-payload (fn-hstxa-held *orm-composite*)) 1)
      (equal (fn-hc-generation (fn-held-context (fn-hstxa-held *orm-composite*))) 9)
      (fn-store-event-p *orm-composite-new*)
      (equal (fn-held-payload (fn-hstxa-held *orm-composite-new*)) 0)
      (equal (fn-hstxa-stxa *orm-composite-new*) *orm-stxa*)
      (equal (fn-orm-projection *orm-composite-new*)
             (fn-orm-projection *orm-composite*))))
(defthm orm-composite-complete-alpha-positive-tooth
 (and (fn-store-event-p *orm-composite*) (natp 0)
      (equal (fn-orm-payload-bytes *orm-composite-new* '((1 2 3)))
             (fn-orm-payload-bytes *orm-composite* '((99 99) (1 2 3))))
      (equal (fn-orm-retained-alpha *orm-composite-new* '((1 2 3)))
             (fn-orm-retained-alpha *orm-composite* '((99 99) (1 2 3)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-orm-payload-bytes fn-orm-retained-alpha
                                     fn-orm-projection fn-orm-metadata
                                     fn-row-bytes fn-hstxa-p fn-hstxa-held
                                     fn-hstxa-stxa fn-held-p fn-held-internals
                                     fn-record-internals))))
(defthm orm-composite-wrong-held-payload-mutation-tooth
 (and (fn-store-event-p *orm-composite*) (natp 0)
      (not (equal (fn-orm-payload-bytes *orm-composite-new* '((7)))
                  (fn-orm-payload-bytes *orm-composite* '((99 99) (1 2 3)))))
      (not (equal (fn-orm-retained-alpha *orm-composite-new* '((7)))
                  (fn-orm-retained-alpha *orm-composite* '((99 99) (1 2 3))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-orm-payload-bytes fn-orm-retained-alpha
                                     fn-orm-projection fn-orm-metadata
                                     fn-row-bytes fn-hstxa-p fn-hstxa-held
                                     fn-hstxa-stxa fn-held-p fn-held-internals
                                     fn-record-internals))))
