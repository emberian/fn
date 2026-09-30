(in-package "ACL2")
(include-book "../../books/group-number-source-pending")
(include-book "../../books/group-number-source-update")
; Fixture coordinates are this leaf's held-record dependency world. The
; private mandatory-binding16 owner assembly must replay with its real row.
(defun fn-tgnp-held (groups)
  (declare (xargs :guard t))
  (list 0 7 0 "<a@x>" 0 groups "o" "s" "e" 1 5
        (fn-hf-make 100 14 2 nil)
        (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0) nil nil))
(defun fn-tgnp-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-assign-cursorp c))
          (member-eq (fn-gns-at 0 c) '(:done :refused))) c
    (fn-tgnp-run (1- fuel) (fn-gns-assign-step c))))
(defconst *tgnp-held* (fn-tgnp-held '("fn.test" "fn.other")))
(defconst *tgnp-old* (fn-held-with-numbers (fn-tgnp-held '("fn.test")) '(("fn.test" . 7))))
(defconst *tgnp-catalog* (list *tgnp-old*))
(defconst *tgnp-root*
  (fn-gns-group-set "fn.test" 0 0 (fn-gns-group-value 7 nil) nil))
; PC constructor is the ACTUAL one moved intact; held numbers are absent.
(defconst *tgnp-pending* (fn-pc-make '(7 . 1) 1 *tgnp-held* :plan :reservation))
(defconst *tgnp-done* (fn-tgnp-run 200 (fn-gns-pending-begin *tgnp-pending* *tgnp-root* 0)))
(assert-event
 (and (fn-pc-p *tgnp-pending*) (not (fn-held-numbers (fn-pc-held *tgnp-pending*)))
      (fn-gns-assign-cursorp *tgnp-done*) (eq (fn-gns-at 0 *tgnp-done*) :done)
      (equal (fn-gns-at 7 *tgnp-done*) (fn-pc-held *tgnp-pending*))
      (equal (fn-gns-assign-denotation *tgnp-done*)
        (fn-gns-assigned-memberships (fn-record-groups (fn-pc-held *tgnp-pending*))
                                   (fn-gns-at 2 *tgnp-done*)))
      (fn-gns-groups-high-matchp (fn-record-groups (fn-pc-held *tgnp-pending*))
                                (fn-gns-at 2 *tgnp-done*) *tgnp-catalog*)
      (equal (fn-gns-at 5 (fn-gns-pending-result *tgnp-done*))
             (fn-cat-assign (fn-pc-held *tgnp-pending*) *tgnp-catalog*))
      (equal (fn-gns-at 6 (fn-gns-pending-result *tgnp-done*))
             '(("fn.test" . 8) ("fn.other" . 1)))
      (equal (fn-gns-at 8 *tgnp-done*) '(7 . 1))
      (equal (fn-gns-at 9 *tgnp-done*) 1)
      (equal (fn-gns-at 11 *tgnp-done*) 0)))
; High-correspondence hypothesis removal for the actual assign-numbers
; equation: no other retained hypotheses, and both source functions execute.
(assert-event
 (and (not (fn-gns-groups-high-matchp '("fn.test") nil *tgnp-catalog*))
      (not (equal (fn-gns-assigned-memberships '("fn.test") nil)
                   (fn-cat-assign-numbers '("fn.test") *tgnp-catalog*)))))
; Removal: terminal phase, with original-held, denotation and high relation
; retained. Beginning state cannot supply an assigned row.
(assert-event
 (let ((c (fn-gns-pending-begin *tgnp-pending* *tgnp-root* 0)))
   (and (not (eq (fn-gns-at 0 c) :done))
        (equal (fn-gns-at 7 c) (fn-pc-held *tgnp-pending*))
        (equal (fn-gns-assign-denotation c)
          (fn-gns-assigned-memberships (fn-record-groups (fn-pc-held *tgnp-pending*)) (fn-gns-at 2 c)))
        (fn-gns-groups-high-matchp (fn-record-groups (fn-pc-held *tgnp-pending*)) (fn-gns-at 2 c) *tgnp-catalog*)
        (not (equal (fn-gns-at 5 (fn-gns-pending-result c))
                     (fn-cat-assign (fn-pc-held *tgnp-pending*) *tgnp-catalog*))))))
; Corrupted-state removal: original-held correspondence. Other hypotheses
; hold; changing Message-ID affirmatively changes the returned row.
(assert-event
 (let ((c (update-nth 7 (update-nth 3 "<other@x>" *tgnp-held*) *tgnp-done*)))
   (and (eq (fn-gns-at 0 c) :done)
        (not (equal (fn-gns-at 7 c) (fn-pc-held *tgnp-pending*)))
        (equal (fn-gns-assign-denotation c)
          (fn-gns-assigned-memberships (fn-record-groups (fn-pc-held *tgnp-pending*)) (fn-gns-at 2 c)))
        (fn-gns-groups-high-matchp (fn-record-groups (fn-pc-held *tgnp-pending*)) (fn-gns-at 2 c) *tgnp-catalog*)
        (not (equal (fn-gns-at 5 (fn-gns-pending-result c))
                     (fn-cat-assign (fn-pc-held *tgnp-pending*) *tgnp-catalog*))))))
; Corrupted-state removal: carried denotation; other hypotheses all hold.
(assert-event
 (let ((c (update-nth 5 '(("fn.test" . 9) ("fn.other" . 1)) *tgnp-done*)))
   (and (eq (fn-gns-at 0 c) :done)
        (equal (fn-gns-at 7 c) (fn-pc-held *tgnp-pending*))
        (not (equal (fn-gns-assign-denotation c)
          (fn-gns-assigned-memberships (fn-record-groups (fn-pc-held *tgnp-pending*)) (fn-gns-at 2 c))))
        (fn-gns-groups-high-matchp (fn-record-groups (fn-pc-held *tgnp-pending*)) (fn-gns-at 2 c) *tgnp-catalog*)
        (not (equal (fn-gns-at 5 (fn-gns-pending-result c))
                     (fn-cat-assign (fn-pc-held *tgnp-pending*) *tgnp-catalog*))))))
; Removal: initial high/catalog correspondence, with every other premise.
(assert-event
 (let ((c (fn-tgnp-run 200 (fn-gns-pending-begin *tgnp-pending* nil 0))))
   (and (eq (fn-gns-at 0 c) :done)
        (equal (fn-gns-at 7 c) (fn-pc-held *tgnp-pending*))
        (equal (fn-gns-assign-denotation c)
          (fn-gns-assigned-memberships (fn-record-groups (fn-pc-held *tgnp-pending*)) (fn-gns-at 2 c)))
        (not (fn-gns-groups-high-matchp (fn-record-groups (fn-pc-held *tgnp-pending*)) (fn-gns-at 2 c) *tgnp-catalog*))
        (not (equal (fn-gns-at 5 (fn-gns-pending-result c))
                     (fn-cat-assign (fn-pc-held *tgnp-pending*) *tgnp-catalog*))))))
