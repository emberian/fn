; Incremental NEWNEWS configured-group selection, PRF-1257.
(in-package "ACL2")
(include-book "nntp-newnews")
(local (in-theory (disable (tau-system))))

; Fixed-size state, retaining patterns, article and list tails by reference.
; Group and membership offsets count entries actually inspected. Membership
; offset resets for each configured group. Neither start nor one computes len.
(defun fn-nnw-select-at (n x)
  (declare (xargs :guard (natp n)))
  (if (consp x)
      (if (zp n) (car x) (fn-nnw-select-at (1- n) (cdr x)))
    nil))

(defun fn-nnw-select-state (patterns groups article tail group phase gi mi answer)
  (declare (xargs :guard t))
  (list :nnw-select patterns groups article tail group phase gi mi answer))

(defun fn-nnw-select-statep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 10) (eq (car s) :nnw-select)
       (member-eq (fn-nnw-select-at 6 s) '(:group :member :done))
       (natp (fn-nnw-select-at 7 s)) (natp (fn-nnw-select-at 8 s))
       (booleanp (fn-nnw-select-at 9 s))))

(defun fn-nnw-select-start (patterns configured-groups article)
  (declare (xargs :guard t))
  (fn-nnw-select-state patterns configured-groups article nil nil :group 0 0 nil))

(defun fn-nnw-select-valid-numberp (number article)
  (declare (xargs :guard t))
  (and (posp number) (<= number *fn-nntp-max-article-number*)
       (ec-call (fn-nntp-article-idp article))))

(defun fn-nnw-select-availablep (group memberships article)
  (declare (xargs :guard t))
  (fn-nnw-select-valid-numberp
   (ec-call (fn-nntp-membership-number group memberships)) article))

; Logical residuals only: the served controller calls start/one, never these
; scans. The wildcard matcher retains its existing work/allocation debt here;
; an entry visit does not assert a byte or allocation tariff.
(defun fn-nnw-select-groups-value (patterns groups article)
  (declare (xargs :guard t))
  (if (consp groups)
      (or (and (fn-nnw-select-availablep (car groups)
                                        (fn-article-memberships article) article)
               (ec-call (fn-nntp-group-matches-parsed-wildmatp patterns (car groups))))
          (fn-nnw-select-groups-value patterns (cdr groups) article))
    nil))

(defun fn-nnw-select-value (s)
  (declare (xargs :guard t))
  (let ((patterns (fn-nnw-select-at 1 s)) (groups (fn-nnw-select-at 2 s))
        (article (fn-nnw-select-at 3 s)) (tail (fn-nnw-select-at 4 s))
        (group (fn-nnw-select-at 5 s)) (phase (fn-nnw-select-at 6 s)))
    (cond ((eq phase :done) (if (fn-nnw-select-at 9 s) t nil))
          ((eq phase :member)
           (or (and (fn-nnw-select-availablep group tail article)
                    (ec-call (fn-nntp-group-matches-parsed-wildmatp patterns group)))
               (fn-nnw-select-groups-value patterns groups article)))
          ((eq phase :group) (fn-nnw-select-groups-value patterns groups article))
          (t nil))))

(defun fn-nnw-select-remaining (s)
  (declare (xargs :guard t))
  (let ((phase (fn-nnw-select-at 6 s)))
    (if (member-eq phase '(:group :member))
        (+ (* (+ 2 (len (fn-article-memberships (fn-nnw-select-at 3 s))))
              (len (fn-nnw-select-at 2 s)))
           (if (eq phase :member) (+ 1 (len (fn-nnw-select-at 4 s))) 0))
      0)))

(defun fn-nnw-select-one (s)
  (declare (xargs :guard t))
  (let ((patterns (fn-nnw-select-at 1 s)) (groups (fn-nnw-select-at 2 s))
        (article (fn-nnw-select-at 3 s)) (tail (fn-nnw-select-at 4 s))
        (group (fn-nnw-select-at 5 s)) (phase (fn-nnw-select-at 6 s))
        (gi (nfix (fn-nnw-select-at 7 s))) (mi (nfix (fn-nnw-select-at 8 s))))
    (cond
     ((eq phase :done) (mv t (if (fn-nnw-select-at 9 s) t nil) s))
     ((eq phase :group)
      (if (consp groups)
          (mv nil nil (fn-nnw-select-state patterns (cdr groups) article
                       (fn-article-memberships article) (car groups) :member
                       (+ 1 gi) 0 nil))
        (mv t nil (fn-nnw-select-state patterns groups article nil group :done gi mi nil))))
     ((eq phase :member)
      (if (consp tail)
          (if (equal group (fn-ag-car (car tail)))
              (if (and (fn-nnw-select-valid-numberp (fn-ag-cdr (car tail)) article)
                       (ec-call (fn-nntp-group-matches-parsed-wildmatp patterns group)))
                  (mv t t (fn-nnw-select-state patterns groups article (cdr tail) group
                           :done gi (+ 1 mi) t))
                (mv nil nil (fn-nnw-select-state patterns groups article (cdr tail) group
                             :group gi (+ 1 mi) nil)))
            (mv nil nil (fn-nnw-select-state patterns groups article (cdr tail) group
                         :member gi (+ 1 mi) nil)))
        (mv nil nil (fn-nnw-select-state patterns groups article nil group :group gi mi nil))))
     (t (mv t nil (fn-nnw-select-state patterns groups article tail group :done gi mi nil))))))

(local (in-theory (enable fn-nntp-newnews-candidatep
                          fn-nntp-filter-groups-by-wildmat
                          fn-nntp-membership-number fn-ag-car fn-ag-cdr)))
(local (in-theory (disable fn-nntp-group-matches-parsed-wildmatp fn-nntp-article-idp
                           fn-article-memberships fn-nntp-filter-groups-by-wildmat-loop)))

(defthm fn-nnw-select-groups-value-is-candidate
  (equal (fn-nnw-select-groups-value patterns groups article)
         (fn-nntp-newnews-candidatep
          (fn-nntp-filter-groups-by-wildmat patterns groups) article))
  :hints (("Goal" :induct (fn-nnw-select-groups-value patterns groups article)
           :in-theory (enable fn-nntp-article-number))))

(defthm fn-nnw-select-start-value
  (equal (fn-nnw-select-value (fn-nnw-select-start patterns groups article))
         (fn-nntp-newnews-candidatep
          (fn-nntp-filter-groups-by-wildmat patterns groups) article)))

(local (in-theory (disable fn-nnw-select-groups-value
                          fn-nnw-select-groups-value-is-candidate
                          fn-nnw-select-valid-numberp)))

(defthm fn-nnw-select-one-preserves-value
  (equal (fn-nnw-select-value (mv-nth 2 (fn-nnw-select-one s)))
         (fn-nnw-select-value s))
  :hints (("Goal" :in-theory (enable fn-nnw-select-groups-value
                                     fn-nntp-membership-number fn-ag-car fn-ag-cdr
                                     fn-nnw-select-valid-numberp))))

(defthm fn-nnw-select-one-decided-value
  (implies (mv-nth 0 (fn-nnw-select-one s))
           (equal (mv-nth 1 (fn-nnw-select-one s)) (fn-nnw-select-value s)))
  :hints (("Goal" :use fn-nnw-select-one-preserves-value
           :in-theory (disable fn-nnw-select-one-preserves-value))))

(defthm fn-nnw-select-start-statep
  (fn-nnw-select-statep (fn-nnw-select-start patterns groups article)))

(defthm fn-nnw-select-one-preserves-statep
  (implies (fn-nnw-select-statep s)
           (fn-nnw-select-statep (mv-nth 2 (fn-nnw-select-one s)))))

(defthm fn-nnw-select-one-progress
  (implies (posp (fn-nnw-select-remaining s))
           (< (fn-nnw-select-remaining (mv-nth 2 (fn-nnw-select-one s)))
              (fn-nnw-select-remaining s)))
  :hints (("Goal" :in-theory (enable fn-nnw-select-remaining))))

(defthm fn-nnw-select-one-group-visits-at-most-one
  (implies (fn-nnw-select-statep s)
           (let ((before (fn-nnw-select-at 7 s))
                 (after (fn-nnw-select-at 7 (mv-nth 2 (fn-nnw-select-one s)))))
             (and (<= before after) (<= after (+ 1 before))))))

(defthm fn-nnw-select-one-member-visits-at-most-one
  (implies (fn-nnw-select-statep s)
           (let ((next (mv-nth 2 (fn-nnw-select-one s))))
             (if (< (fn-nnw-select-at 7 s) (fn-nnw-select-at 7 next))
                 (equal (fn-nnw-select-at 8 next) 0)
               (and (equal (fn-nnw-select-at 7 next) (fn-nnw-select-at 7 s))
                    (<= (fn-nnw-select-at 8 s) (fn-nnw-select-at 8 next))
                    (<= (fn-nnw-select-at 8 next) (+ 1 (fn-nnw-select-at 8 s))))))))

(defun fn-nnw-select-entry-visits (s)
  (declare (xargs :guard t))
  (cond ((eq (fn-nnw-select-at 6 s) :group)
         (if (consp (fn-nnw-select-at 2 s)) 1 0))
        ((eq (fn-nnw-select-at 6 s) :member)
         (if (consp (fn-nnw-select-at 4 s)) 1 0))
        (t 0)))

(defthm fn-nnw-select-one-entry-charge
  (implies (fn-nnw-select-statep s)
           (let* ((next (mv-nth 2 (fn-nnw-select-one s)))
                  (groups (- (fn-nnw-select-at 7 next) (fn-nnw-select-at 7 s)))
                  (members (if (equal groups 0)
                               (- (fn-nnw-select-at 8 next) (fn-nnw-select-at 8 s))
                             0)))
             (and (equal (+ groups members) (fn-nnw-select-entry-visits s))
                  (<= (+ groups members) 1)))))

(defthm fn-nnw-select-one-decision-is-done
  (implies (mv-nth 0 (fn-nnw-select-one s))
           (equal (fn-nnw-select-at 6 (mv-nth 2 (fn-nnw-select-one s))) :done)))

(local
 (defthm fn-nnw-select-zero-len
   (equal (equal (len x) 0) (not (consp x)))
   :hints (("Goal" :expand ((len x))))))

(defthm fn-nnw-select-zero-remaining-settles
  (implies (and (fn-nnw-select-statep s)
                (equal (fn-nnw-select-remaining s) 0))
           (mv-nth 0 (fn-nnw-select-one s)))
  :hints (("Goal" :in-theory (enable fn-nnw-select-remaining))))

(defthm fn-nnw-select-remaining-natp
  (natp (fn-nnw-select-remaining s))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable fn-nnw-select-remaining))))

; Do not expose recursive model scans to the served step's executable theory.
(in-theory (disable fn-nnw-select-groups-value fn-nnw-select-value fn-nnw-select-remaining))
