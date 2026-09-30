; fn: one committed-row step of signed membership evidence (SUB-008).
; A caller supplies the exact accepted persistence row, not a transport ACK.
; A payload's commit id is not the signed statement identity. Preserve both.
; No site roster, adopted chain or admission decision is installed here.
(in-package "ACL2")
(include-book "stx-commit-codec")
(include-book "principal")

(defun fn-stce-entry (group authority statement commit)
  (declare (xargs :guard t))
  (list group authority statement commit))
(defun fn-stce-entryp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)
       (fn-stmt-p (nth 2 x)) (fn-me-commitp (nth 3 x))
       (equal (nth 3 x) (fn-stx-commit-of-statement (nth 2 x)))))
(defun fn-stce-id-collisionp (entry evidence keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (atom evidence) nil
    (or (and (fn-stce-entryp entry) (fn-stce-entryp (car evidence))
             (equal (car entry) (car (car evidence)))
             (equal (fn-stmt-creator (nth 2 (car evidence))) (nth 1 entry))
             (equal (fn-me-commit-actor (nth 3 (car evidence))) (nth 1 entry))
             (fn-prin-verifiedp (nth 2 (car evidence)) keyring)
             (equal (fn-me-commit-id (nth 3 entry))
                    (fn-me-commit-id (nth 3 (car evidence))))
             (not (and (equal (nth 2 entry) (nth 2 (car evidence)))
                       (equal (nth 3 entry) (nth 3 (car evidence))))))
        (fn-stce-id-collisionp entry (cdr evidence) keyring))))

; Exact retransmissions add nothing. Every distinct signed envelope survives,
; including same-id/different-content evidence: no fn-me-merge on this path.
(defun fn-stce-retain (entry evidence)
  (declare (xargs :guard (true-listp evidence)))
  (if (member-equal entry evidence) evidence (cons entry evidence)))

(defun fn-stce-entry-verdict (entry evidence keyring)
  (declare (xargs :guard (and (true-listp evidence) (fn-prin-keyringp keyring))))
  (cond ((not (fn-stce-entryp entry)) :malformed)
        ((not (fn-prin-verifiedp (nth 2 entry) keyring)) :unverified)
        ((not (nth 1 entry)) :ungoverned)
        ((not (equal (fn-stmt-creator (nth 2 entry)) (nth 1 entry))) :unauthorized)
        ((not (equal (fn-me-commit-actor (nth 3 entry)) (nth 1 entry))) :actor-mismatch)
        ((fn-stce-id-collisionp entry evidence keyring) :commit-id-conflict)
        ((member-equal entry evidence) :retransmission)
        (t :evidence)))

(defun fn-stce-slot-conflictp (entry prior keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (and (fn-stce-entryp entry) (fn-stce-entryp prior)
       (equal (car entry) (car prior))
       (equal (fn-stmt-creator (nth 2 prior)) (nth 1 entry))
       (fn-prin-verifiedp (nth 2 prior) keyring)
       (equal (fn-stmt-creator (nth 2 entry)) (fn-stmt-creator (nth 2 prior)))
       (equal (fn-stmt-incarnation (nth 2 entry)) (fn-stmt-incarnation (nth 2 prior)))
       (equal (fn-stmt-sequence (nth 2 entry)) (fn-stmt-sequence (nth 2 prior)))
       (not (equal (nth 2 entry) (nth 2 prior)))))
; Selection and evidence comparisons are separate resumable phases. A scan
; resume compares one retained envelope; no whole-transcript revalidation.
(defun fn-stce-statementsp (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (fn-stmt-p (car xs)) (fn-stce-statementsp (cdr xs)))
    (null xs)))
(defun fn-stce-start (statements groups)
  (declare (xargs :guard t))
  (list :select statements groups groups))
(defun fn-stce-select-cursorp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4) (equal (car x) :select)
       (fn-stce-statementsp (nth 1 x))))
(defun fn-stce-scan-cursorp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 7) (equal (car x) :scan)
       (fn-stce-entryp (nth 1 x)) (true-listp (nth 2 x))
       (fn-stce-select-cursorp (nth 6 x))))
(defun fn-stce-flags-verdict (entry duplicate conflict keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (cond ((not (fn-stce-entryp entry)) :malformed)
        ((not (fn-prin-verifiedp (nth 2 entry) keyring)) :unverified)
        ((not (nth 1 entry)) :ungoverned)
        ((not (equal (fn-stmt-creator (nth 2 entry)) (nth 1 entry))) :unauthorized)
        ((not (equal (fn-me-commit-actor (nth 3 entry)) (nth 1 entry))) :actor-mismatch)
        (conflict (if (equal conflict :equivocation) :equivocation :commit-id-conflict))
        (duplicate :retransmission)
        (t :evidence)))
(defun fn-stce-cursor-shapep (cursor)
  (declare (xargs :guard t))
  (or (null cursor) (fn-stce-select-cursorp cursor) (fn-stce-scan-cursorp cursor)))
(defun fn-stce-select-tagp (cursor)
  (declare (xargs :guard t))
  (and (true-listp cursor) (equal (len cursor) 4) (equal (car cursor) :select)))
(defun fn-stce-scan-tagp (cursor)
  (declare (xargs :guard t))
  (and (true-listp cursor) (equal (len cursor) 7) (equal (car cursor) :scan)
       (fn-stce-entryp (nth 1 cursor))))
(local (defthm fn-stce-scan-cursor-is-scan-tag
  (implies (fn-stce-scan-cursorp cursor) (fn-stce-scan-tagp cursor))
  :hints (("Goal" :in-theory (e/d (fn-stce-scan-cursorp fn-stce-scan-tagp)
                                   (fn-stce-entryp fn-stce-select-cursorp))))))
(local (defthm fn-stce-select-cursor-is-select-tag
  (implies (fn-stce-select-cursorp cursor) (fn-stce-select-tagp cursor))
  :hints (("Goal" :in-theory (e/d (fn-stce-select-cursorp fn-stce-select-tagp)
                                   (fn-stce-statementsp))))))
(local (defthm fn-stce-select-cursor-is-not-scan-tag
  (implies (fn-stce-select-cursorp cursor) (not (fn-stce-scan-tagp cursor)))
  :hints (("Goal" :in-theory (e/d (fn-stce-select-cursorp fn-stce-scan-tagp)
                                   (fn-stce-entryp fn-stce-statementsp))))))
(defun fn-stce-resume (evidence cursor authority keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (cond
   ((fn-stce-scan-tagp cursor)
    (let ((entry (nth 1 cursor)) (tail (nth 2 cursor))
          (duplicate (nth 3 cursor)) (conflict (nth 4 cursor))
          (next (nth 6 cursor)))
      (if (consp tail)
          (mv evidence
              (list :scan entry (cdr tail)
                    (or duplicate (equal entry (car tail)))
                    (cond ((or (equal conflict :equivocation)
                               (fn-stce-slot-conflictp entry (car tail) keyring)) :equivocation)
                          ((or conflict (fn-stce-id-collisionp entry (list (car tail)) keyring)) :commit-id-conflict)
                          (t nil))
                    (nth 5 cursor) next)
              :scanning)
        (mv (if duplicate evidence (cons entry evidence)) next
            (fn-stce-flags-verdict entry duplicate conflict keyring)))))
   ((not (fn-stce-select-tagp cursor)) (mv evidence nil :malformed))
   ((atom (nth 1 cursor)) (mv evidence nil :done))
   ((atom (nth 2 cursor))
    (mv evidence (list :select (cdr (nth 1 cursor)) (nth 3 cursor) (nth 3 cursor))
        :next-statement))
   (t (let* ((s (car (nth 1 cursor)))
             (commit (if (fn-stmt-p s) (fn-stx-commit-of-statement s) nil))
             (group (car (nth 2 cursor)))
             (next (list :select (nth 1 cursor) (cdr (nth 2 cursor)) (nth 3 cursor))))
        (if (not commit) (mv evidence next :not-a-commit)
          (mv evidence
              (list :scan (fn-stce-entry group
                                        authority
                                        s commit)
                    evidence nil nil nil next)
              :scanning))))))

(defthm fn-stce-retain-keeps-existing-evidence
  (implies (member-equal old evidence)
           (member-equal old (fn-stce-retain entry evidence))))
(defthm fn-stce-retain-keeps-new-evidence
  (member-equal entry (fn-stce-retain entry evidence)))
(defthm fn-stce-exact-retransmission-keeps-evidence-by-definition
  (implies (member-equal entry evidence)
           (equal (fn-stce-retain entry evidence) evidence)))
(defthm fn-stce-id-conflict-retains-both
  (implies (and (member-equal old evidence) (not (equal old entry)))
           (and (member-equal old (fn-stce-retain entry evidence))
                (member-equal entry (fn-stce-retain entry evidence)))))
(defthm fn-stce-resume-retains-existing-evidence
  (implies (member-equal old evidence)
           (member-equal old (mv-nth 0 (fn-stce-resume evidence cursor authority keyring))))
  :hints (("Goal" :in-theory (e/d (fn-stce-resume fn-stce-scan-tagp fn-stce-select-tagp)
                                  (fn-stce-scan-cursorp fn-stce-select-cursorp
                                   fn-stce-flags-verdict fn-stce-id-collisionp
                                   fn-stx-commit-of-statement fn-stce-entry)))))
(defthm fn-stce-publish-retains-the-envelope
  (implies (and (fn-stce-scan-cursorp cursor)
                (atom (nth 2 cursor))
                (implies (nth 3 cursor) (member-equal (nth 1 cursor) evidence)))
           (member-equal (nth 1 cursor)
                         (mv-nth 0 (fn-stce-resume evidence cursor authority keyring))))
  :hints (("Goal" :in-theory (e/d (fn-stce-resume)
                                  (fn-stce-scan-tagp fn-stce-select-tagp fn-stce-scan-cursorp fn-stce-select-cursorp
                                   fn-stce-flags-verdict fn-stce-id-collisionp
                                   fn-stx-commit-of-statement fn-stce-entry)))))
(defun fn-stce-cursor-witnessp (cursor evidence)
  (declare (xargs :guard (true-listp evidence)
                  :guard-hints (("Goal" :in-theory (e/d (fn-stce-scan-cursorp)
                      (fn-stce-entryp fn-stce-select-cursorp))))))
  (or (not (fn-stce-scan-cursorp cursor))
      (and (subsetp-equal (nth 2 cursor) evidence)
           (implies (nth 3 cursor) (member-equal (nth 1 cursor) evidence)))))
(local (defthm fn-stce-subset-member
  (implies (and (subsetp-equal tail evidence) (consp tail))
           (member-equal (car tail) evidence))))
(local (defthm fn-stce-subset-cons
 (implies (subsetp-equal a b) (subsetp-equal a (cons x b)))))
(local (defthm fn-stce-subset-reflexive (subsetp-equal x x)))
(defthm fn-stce-resume-preserves-cursor-witness
  (implies (and (fn-stce-cursor-shapep cursor)
                (fn-stce-cursor-witnessp cursor evidence))
           (fn-stce-cursor-witnessp
            (mv-nth 1 (fn-stce-resume evidence cursor authority keyring))
            (mv-nth 0 (fn-stce-resume evidence cursor authority keyring))))
  :hints (("Goal" :in-theory (e/d (fn-stce-resume fn-stce-scan-tagp fn-stce-select-tagp fn-stce-cursor-shapep fn-stce-cursor-witnessp
                                    fn-stce-scan-cursorp fn-stce-select-cursorp)
                                   (fn-stce-entryp fn-stce-statementsp fn-stce-flags-verdict
                                    fn-stce-id-collisionp fn-stce-slot-conflictp fn-stce-entry
                                    fn-stx-commit-of-statement)))))
(defthm fn-stce-publish-conflict-refuses-authority
  (implies (and (fn-stce-scan-cursorp cursor)
                (atom (nth 2 cursor)) (nth 4 cursor)
                (not (equal (nth 4 cursor) :equivocation))
                (fn-prin-verifiedp (nth 2 (nth 1 cursor)) keyring)
                (nth 1 (nth 1 cursor))
                (equal (fn-stmt-creator (nth 2 (nth 1 cursor)))
                       (nth 1 (nth 1 cursor)))
                (equal (fn-me-commit-actor (nth 3 (nth 1 cursor)))
                       (nth 1 (nth 1 cursor))))
           (equal (mv-nth 2 (fn-stce-resume evidence cursor authority keyring))
                  :commit-id-conflict))
  :hints (("Goal" :in-theory (e/d (fn-stce-resume fn-stce-scan-tagp fn-stce-select-tagp fn-stce-flags-verdict
                                    fn-stce-scan-cursorp)
                                   (fn-stce-entryp fn-stce-select-cursorp
                                    fn-stce-id-collisionp fn-stce-slot-conflictp fn-stce-entry
                                    fn-stx-commit-of-statement fn-prin-verifiedp
                                    fn-stmt-creator fn-me-commit-actor)))))
(local (defthm fn-stce-statementsp-cdr
  (implies (fn-stce-statementsp xs) (fn-stce-statementsp (cdr xs)))))
(local (defthm fn-stce-statementsp-car
  (implies (and (fn-stce-statementsp xs) (consp xs)) (fn-stmt-p (car xs)))))
(local (defthm fn-stce-constructed-entryp
  (implies (and (fn-stmt-p s) (fn-stx-commit-of-statement s))
           (fn-stce-entryp (fn-stce-entry group authority s (fn-stx-commit-of-statement s))))
  :hints (("Goal" :in-theory (e/d (fn-stce-entryp fn-stce-entry)
                                   (fn-stx-commit-of-statement fn-stmt-p fn-me-commitp))))))
(defthm fn-stce-start-has-cursor-shape
  (implies (fn-stce-statementsp statements)
           (fn-stce-cursor-shapep (fn-stce-start statements groups)))
  :hints (("Goal" :in-theory (enable fn-stce-start fn-stce-cursor-shapep
                                     fn-stce-select-cursorp))))
(defthm fn-stce-resume-preserves-cursor-shape
  (implies (and (true-listp evidence) (fn-stce-cursor-shapep cursor))
           (fn-stce-cursor-shapep
            (mv-nth 1 (fn-stce-resume evidence cursor authority keyring))))
  :hints (("Goal" :in-theory (e/d (fn-stce-resume fn-stce-scan-tagp fn-stce-select-tagp fn-stce-cursor-shapep
                                    fn-stce-select-cursorp fn-stce-scan-cursorp)
                                   (fn-stce-entryp fn-stce-entry fn-stce-statementsp
                                    fn-stx-commit-of-statement fn-stce-flags-verdict
                                    fn-stce-id-collisionp)))))
(defthm fn-stce-scanned-slot-conflict-is-recorded
  (implies (and (fn-stce-scan-cursorp cursor) (consp (nth 2 cursor))
                (fn-stce-slot-conflictp (nth 1 cursor) (car (nth 2 cursor)) keyring))
           (equal (nth 4 (mv-nth 1 (fn-stce-resume evidence cursor authority keyring)))
                  :equivocation))
  :hints (("Goal" :in-theory (e/d (fn-stce-resume fn-stce-scan-tagp fn-stce-select-tagp)
                                   (fn-stce-scan-cursorp fn-stce-select-cursorp
                                    fn-stce-slot-conflictp fn-stce-id-collisionp
                                    fn-stce-flags-verdict fn-stx-commit-of-statement)))))
(in-theory (disable (:d fn-stce-start) (:d fn-stce-resume)
                    (:d fn-stce-entry-verdict) (:d fn-stce-id-collisionp)
                    (:d fn-stce-retain)))
