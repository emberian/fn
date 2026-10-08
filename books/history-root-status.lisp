; fn: the history-root refresh's status as a line of `status' and `health'
; (lane s-heap2, 2026-10-08).
;
; A refused history-root refresh used to leave the whole history in the
; heap with nothing said (host/native/owner.lisp discarded the refresh's
; word).  ACL2 classifies the word (books/history-root-credit.lisp
; fn-hroot-refresh-status) and this book renders the classification as its
; own line, appended after the report like the exposure and limit lines
; (host/native-live-status-host.lisp), so `health' keeps its states and exit
; codes: the line is not a health state.  A building (or never-asked)
; status renders nothing, so every report the node answered before stays
; byte-identical.
(in-package "ACL2")
(include-book "history-root-credit")
(include-book "native-live-status")
(include-book "history-capture-state")

(defun fn-hrs-line (status)
  (declare (xargs :guard t))
  (cond ((and (true-listp status) (equal (len status) 5)
              (equal (car status) :history-root) (equal (cadr status) :refused)
              (natp (nth 3 status)) (natp (nth 4 status)))
         (append (fn-nls-text "history-root: refused reason=")
                 (fn-nls-reason-words (nth 2 status))
                 (fn-nls-field "asked" (nth 3 status))
                 (fn-nls-field "available" (nth 4 status))
                 *fn-nls-lf*))
        ((and (consp status) (equal (car status) :history-root)
              (consp (cdr status)) (equal (cadr status) :refused))
         (append (fn-nls-text "history-root: refused reason=")
                 (fn-nls-reason-words (if (consp (cddr status)) (caddr status) nil))
                 *fn-nls-lf*))
        ((equal status '(:history-root :uncertain))
         (append (fn-nls-text "history-root: uncertain") *fn-nls-lf*))
        (t nil)))

; KEYSTONE (the rendered line is the status): the status of a refused refresh
; word renders as a refused line with the word's own reason and figures, for
; every word of begin's form.
(defthm fn-hrs-line-of-a-refused-begin-word-unfolds
  (implies (and (symbolp r) (natp ask) (natp room))
           (equal (fn-hrs-line (fn-hroot-refresh-status (list :refused r ask room)))
                  (append (fn-nls-text "history-root: refused reason=")
                          (fn-nls-reason-words r)
                          (fn-nls-field "asked" ask)
                          (fn-nls-field "available" room)
                          *fn-nls-lf*)))
  :hints (("Goal" :in-theory (enable fn-hrs-line fn-hroot-refresh-status))))

; The building status, a never-asked owner and nil render nothing.
(defthm fn-hrs-line-of-building-is-empty
  (and (equal (fn-hrs-line '(:history-root :building)) nil)
       (equal (fn-hrs-line nil) nil)
       (equal (fn-hrs-line (fn-hroot-refresh-status :funded)) nil)))

(defthm fn-hrs-line-is-true-listp
  (true-listp (fn-hrs-line status))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-hrs-line))))

; A refusal is never rendered as nothing: any (:refused R . DETAIL) word.
(defthm fn-hrs-line-of-any-refusal-is-not-empty
  (implies (and (consp w) (equal (car w) :refused) (consp (cdr w)))
           (consp (fn-hrs-line (fn-hroot-refresh-status w))))
  :hints (("Goal" :in-theory (enable fn-hrs-line fn-hroot-refresh-status))))

; Teeth, end to end: the ledger with no reserve refuses the begin and the
; line names the reason and the figures; the same ledger with the reserve
; raised funds it and renders nothing.
(defthm fn-hrs-teeth-exhausted-renders-refused
  (let ((l (fn-mcr-make 5624942530 2815331266 0 2789392384 16777216 0 nil 0 nil)))
    (equal (fn-hrs-line (fn-hroot-refresh-status (fn-hroot-begin-word l 2)))
           (append (fn-nls-text "history-root: refused reason=")
                   (fn-nls-reason-words :history-root-reserve-exhausted)
                   (fn-nls-field "asked" (fn-hroot-begin-ask))
                   (fn-nls-field "available" 0)
                   *fn-nls-lf*)))
  :rule-classes nil)

(defthm fn-hrs-teeth-funded-renders-nothing
  (let ((l (fn-mcr-make (+ 5624942530 (fn-hroot-begin-ask)) 2815331266 0 2789392384 16777216 0 nil
                        (fn-hroot-begin-ask) nil)))
    (equal (fn-hrs-line (fn-hroot-refresh-status (fn-hroot-begin-word l 2))) nil))
  :rule-classes nil)

; KEYSTONE (K-d): noting the last refresh does not change whether the
; history-root roster holds anything, so a refusal never blocks (nor a
; building word unblocks) a history reset.
(defthm fn-history-root-roster-heldp-of-remove-last-refresh
  (implies (alistp roots)
           (equal (fn-history-root-roster-heldp (remove1-assoc-equal :last-refresh roots))
                  (fn-history-root-roster-heldp roots)))
  :hints (("Goal" :in-theory (enable fn-history-root-roster-heldp remove1-assoc-equal))))

(defthm fn-history-root-roster-heldp-of-note
  (implies (alistp roots)
           (equal (fn-history-root-roster-heldp (fn-hroot-table-note roots w))
                  (fn-history-root-roster-heldp roots)))
  :hints (("Goal" :in-theory (enable fn-history-root-roster-heldp fn-hroot-table-note))))

; The line rendered from the carried table is the line of the noted word.
(defthm fn-hrs-line-of-table-note
  (equal (fn-hrs-line (fn-hroot-table-status (fn-hroot-table-note roots w)))
         (fn-hrs-line (fn-hroot-refresh-status w))))

; Teeth for K-d: the heldp before the reserved-key skip (witness only, the
; definition as it stood) reads a noted table as held, so a reset would have
; been blocked forever by the first noted refresh.
(defun fn-history-root-roster-heldp-before-skip (roots)
  (declare (xargs :guard t))
  (if (consp roots)
      (let* ((entry (car roots)) (row (if (consp entry) (cdr entry) nil)))
        (or (not (consp entry))
            (and row (or (not (true-listp row))
                         (not (equal (len row) 3))
                         (not (member-eq (car row) '(:building :live :retired)))
                         (not (null (caddr row)))))
            (fn-history-root-roster-heldp-before-skip (cdr roots))))
    (not (null roots))))

(defthm fn-history-root-roster-heldp-teeth-skip-is-needed
  (and (equal (fn-history-root-roster-heldp-before-skip
               (fn-hroot-table-note nil '(:installed 1 nil))) t)
       (equal (fn-history-root-roster-heldp
               (fn-hroot-table-note nil '(:installed 1 nil))) nil)
       (equal (fn-history-root-roster-heldp
               (fn-hroot-table-note '((7 :building nil ((8 . lease)))) '(:funded))) t))
  :rule-classes nil)
