; Actual NEWNEWS selector adapter: retain matcher state instead of running a
; whole wildcard match inside the first equal membership's scheduling unit.
(in-package "ACL2")
(include-book "newnews-candidate-selector")
(include-book "wildmat-cursor")
(local (in-theory (disable fn-nnw-select-one fn-nnw-select-start
                           fn-wmc-one fn-wmc-step)))

(defun fn-nnm-entry (selector)
  (declare (xargs :guard t))
  (list :entry selector))
(defun fn-nnm-match (matcher following)
  (declare (xargs :guard t))
  (list :match matcher following))
(defun fn-nnm-matchp (s)
  (declare (xargs :guard t))
  (and (consp s) (eq (car s) :match)))
(defun fn-nnm-start (patterns groups article)
  (declare (xargs :guard t))
  (fn-nnm-entry (fn-nnw-select-start patterns groups article)))

; The first equal membership ends its group's search even for an invalid
; number. Only a valid first equal membership creates a retained matcher.
(defun fn-nnm-needs-matchp (selector)
  (declare (xargs :guard t))
  (let ((tail (fn-nnw-select-at 4 selector)))
    (and (eq (fn-nnw-select-at 6 selector) :member)
         (consp tail)
         (equal (fn-nnw-select-at 5 selector) (fn-ag-car (car tail)))
         (fn-nnw-select-valid-numberp (fn-ag-cdr (car tail))
                                     (fn-nnw-select-at 3 selector)))))
(defun fn-nnm-after-membership (selector matched)
  (declare (xargs :guard t))
  (fn-nnw-select-state
   (fn-nnw-select-at 1 selector) (fn-nnw-select-at 2 selector)
   (fn-nnw-select-at 3 selector) (fn-ag-cdr (fn-nnw-select-at 4 selector))
   (fn-nnw-select-at 5 selector) (if matched :done :group)
   (nfix (fn-nnw-select-at 7 selector))
   (+ 1 (nfix (fn-nnw-select-at 8 selector))) (if matched t nil)))
(defun fn-nnm-done (following)
  (declare (xargs :guard t))
  (fn-nnw-select-state
   (fn-nnw-select-at 1 following) (fn-nnw-select-at 2 following)
   (fn-nnw-select-at 3 following) (fn-nnw-select-at 4 following)
   (fn-nnw-select-at 5 following) :done
   (fn-nnw-select-at 7 following) (fn-nnw-select-at 8 following) t))

; One selector or one matcher microstep. Logical engine demand does not grant
; physical heap credit; the producer's working/custody tariff stays separate.
(defun fn-nnm-one (s)
  (declare (xargs :guard t))
  (if (fn-nnm-matchp s)
      (let ((matcher (fn-nnw-select-at 1 s)) (following (fn-nnw-select-at 2 s)))
        (if (fn-wmc-decidedp matcher)
            (if (fn-wmc-matchedp matcher)
                (mv t t (fn-nnm-entry (fn-nnm-done following)))
              (mv nil nil (fn-nnm-entry following)))
          (mv nil nil (fn-nnm-match
                       (fn-wmc-step matcher 1 (fn-wmc-demand matcher)) following))))
    (let ((selector (fn-nnw-select-at 1 s)))
      (if (fn-nnm-needs-matchp selector)
          (mv nil nil
              (fn-nnm-match
               (fn-wmc-start (fn-nnw-select-at 1 selector) (fn-nnw-select-at 5 selector))
               (fn-nnm-after-membership selector nil)))
        (mv-let (decided matched next) (fn-nnw-select-one selector)
          (mv decided matched (fn-nnm-entry next)))))))

; Disabled logical residual: consumed code never scans groups or matcher
; frames to validate a captured state.
(defun fn-nnm-value (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-nnm-matchp s)
      (or (if (fn-wmc-value (fn-nnw-select-at 1 s)) t nil)
          (fn-nnw-select-value (fn-nnw-select-at 2 s)))
    (fn-nnw-select-value (fn-nnw-select-at 1 s))))
(defun fn-nnm-statep (s)
  (declare (xargs :guard t))
  (if (fn-nnm-matchp s)
      (and (true-listp s) (equal (len s) 3)
           (fn-wmc-shapedp (fn-nnw-select-at 1 s))
           (fn-nnw-select-statep (fn-nnw-select-at 2 s))
           (eq (fn-nnw-select-at 6 (fn-nnw-select-at 2 s)) :group))
    (and (true-listp s) (equal (len s) 2) (eq (car s) :entry)
         (fn-nnw-select-statep (fn-nnw-select-at 1 s)))))
(defun fn-nnm-group-remaining (s)
  (declare (xargs :guard t))
  (fn-nnw-select-remaining (fn-nnw-select-at (if (fn-nnm-matchp s) 2 1) s)))
(defun fn-nnm-work-remaining (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-nnm-matchp s) (+ 1 (fn-wmc-remaining (fn-nnw-select-at 1 s))) 0))
(defun fn-nnm-entry-visits (s)
  (declare (xargs :guard t))
  (if (fn-nnm-matchp s) 0 (fn-nnw-select-entry-visits (fn-nnw-select-at 1 s))))
(defun fn-nnm-work (s)
  (declare (xargs :guard t))
  (if (fn-nnm-matchp s)
      (fn-wmc-consumed-work (fn-nnw-select-at 1 s) 1
                            (fn-wmc-demand (fn-nnw-select-at 1 s))) 0))
(defun fn-nnm-engine-cons (s)
  (declare (xargs :guard t))
  (if (fn-nnm-matchp s)
      (fn-wmc-consumed-cons (fn-nnw-select-at 1 s) 1
                            (fn-wmc-demand (fn-nnw-select-at 1 s))) 0))

(defthm fn-nnm-start-value
  (equal (fn-nnm-value (fn-nnm-start patterns groups article))
         (fn-nntp-newnews-candidatep
          (fn-nntp-filter-groups-by-wildmat patterns groups) article)))
(defthm fn-nnm-start-statep
  (fn-nnm-statep (fn-nnm-start patterns groups article)))
(defthm fn-nnm-after-membership-statep
  (implies (fn-nnw-select-statep selector)
           (fn-nnw-select-statep (fn-nnm-after-membership selector matched)))
  :hints (("Goal" :in-theory (enable fn-nnw-select-statep))))
(defthm fn-nnm-done-statep
  (implies (fn-nnw-select-statep following)
           (fn-nnw-select-statep (fn-nnm-done following)))
  :hints (("Goal" :in-theory (enable fn-nnw-select-statep))))
(defthm fn-nnm-one-statep
  (implies (fn-nnm-statep s)
           (fn-nnm-statep (mv-nth 2 (fn-nnm-one s))))
  :hints (("Goal" :in-theory (e/d (fn-nnm-one fn-nnm-statep fn-nnm-matchp
                                     fn-nnm-match fn-nnm-entry fn-nnm-after-membership)
                                    (fn-nnw-select-one fn-wmc-start fn-wmc-step fn-wmc-shapedp)))))
(defthm fn-nnm-entry-visits-at-most-one
  (<= (fn-nnm-entry-visits s) 1))
(defthm fn-nnm-matcher-does-not-visit-entries
  (implies (fn-nnm-matchp s) (equal (fn-nnm-entry-visits s) 0)))
(defthm fn-nnm-engine-work-at-most-one
  (<= (fn-nnm-work s) 1))
(defthm fn-nnm-engine-cons-at-most-demand
  (<= (fn-nnm-engine-cons s)
      (if (fn-nnm-matchp s) (fn-wmc-demand (fn-nnw-select-at 1 s)) 0)))

(defthm fn-nnm-after-membership-value
  (implies (fn-nnm-needs-matchp selector)
           (equal (fn-nnw-select-value selector)
                  (or (fn-nntp-group-matches-parsed-wildmatp
                       (fn-nnw-select-at 1 selector) (fn-nnw-select-at 5 selector))
                      (fn-nnw-select-value (fn-nnm-after-membership selector nil)))))
  :hints (("Goal" :in-theory
           (e/d (fn-nnw-select-value fn-nnw-select-availablep
                  fn-nntp-membership-number fn-nnm-needs-matchp fn-nnm-after-membership
                  fn-nnw-select-valid-numberp fn-ag-car fn-ag-cdr)
                (fn-nntp-group-matches-parsed-wildmatp fn-nnw-select-groups-value
                 fn-nntp-article-idp)))))
(defthm fn-nnm-done-value
  (equal (fn-nnw-select-value (fn-nnm-done following)) t)
  :hints (("Goal" :in-theory (enable fn-nnw-select-value))))

(defthm fn-nnm-one-preserves-value
  (equal (fn-nnm-value (mv-nth 2 (fn-nnm-one s))) (fn-nnm-value s))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nnm-one fn-nnm-value fn-nnm-matchp fn-nnm-match fn-nnm-entry)
                            (fn-wmc-start fn-wmc-step fn-wmc-value fn-wmc-decidedp
                             fn-wmc-matchedp fn-nnm-after-membership fn-nnm-done
                             fn-nnw-select-one fn-nnw-select-value fn-nnm-needs-matchp)))))

(defthm fn-nnm-one-decided-value
  (implies (mv-nth 0 (fn-nnm-one s))
           (equal (mv-nth 1 (fn-nnm-one s)) (fn-nnm-value s)))
  :hints (("Goal" :in-theory (e/d (fn-nnm-one fn-nnm-value fn-nnm-matchp)
                                      (fn-wmc-step fn-wmc-start fn-wmc-value
                                       fn-nnw-select-one fn-nnw-select-value)))))

(defthm fn-nnm-after-membership-progress
  (implies (and (fn-nnw-select-statep selector)
                (fn-nnm-needs-matchp selector))
           (< (fn-nnw-select-remaining (fn-nnm-after-membership selector nil))
              (fn-nnw-select-remaining selector)))
  :hints (("Goal" :in-theory (enable fn-nnw-select-remaining fn-nnw-select-statep))))
(defthm fn-nnm-done-remaining
  (equal (fn-nnw-select-remaining (fn-nnm-done following)) 0)
  :hints (("Goal" :in-theory (enable fn-nnw-select-remaining))))
(defthm fn-nnm-one-progress
  (implies (and (fn-nnm-statep s)
                (or (posp (fn-nnm-group-remaining s))
                    (posp (fn-nnm-work-remaining s))))
           (let ((next (mv-nth 2 (fn-nnm-one s))))
             (or (< (fn-nnm-group-remaining next) (fn-nnm-group-remaining s))
                 (and (equal (fn-nnm-group-remaining next) (fn-nnm-group-remaining s))
                      (< (fn-nnm-work-remaining next) (fn-nnm-work-remaining s))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nnm-one fn-nnm-statep fn-nnm-group-remaining
                             fn-nnm-work-remaining fn-nnm-match fn-nnm-matchp fn-nnm-entry
                             fn-wmc-consumed-work fn-wmc-demand)
                            (fn-nnw-select-one fn-nnw-select-remaining fn-wmc-step
                             fn-wmc-start fn-wmc-shapedp fn-wmc-remaining
                             fn-nnm-after-membership fn-nnm-done)))))

(in-theory (disable fn-nnm-value fn-nnm-group-remaining fn-nnm-work-remaining
                     fn-nnm-statep))
