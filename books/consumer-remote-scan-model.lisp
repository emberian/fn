; Logical observer only. It never walks a query/article list on a request.
(in-package "ACL2")
(include-book "consumer-remote-scan")

(defun fn-crpsm-query-matches (query text)
 (declare (xargs :guard t :verify-guards nil))
 (and (consp query)
      (or (equal text (fn-record-octets-string (car query)))
          (fn-crpsm-query-matches (cdr query) text))))

(defun fn-crpsm-intersects (query articles)
 (declare (xargs :guard t :verify-guards nil))
 (and (consp articles)
      (or (fn-crpsm-query-matches query (car articles))
          (fn-crpsm-intersects query (cdr articles)))))

(defun fn-crpsm-query-prefix (query remaining text)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal query remaining) t
  (and (consp query) (not (equal text (fn-record-octets-string (car query))))
       (fn-crpsm-query-prefix (cdr query) remaining text))))

(defun fn-crpsm-article-prefix (query full remaining)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal full remaining) t
  (and (consp full) (not (fn-crpsm-query-matches query (car full)))
       (fn-crpsm-article-prefix query (cdr full) remaining))))

(defun fn-crpsm-invariant (s)
 (declare (xargs :guard t :verify-guards nil))
 (let ((query (fn-cp-nth 4 s)) (articles (fn-cp-nth 10 s)))
  (and (eq (fn-cp-nth 0 s) :remote-scan)
       (implies (eq (fn-cp-nth 8 s) :match)
   (and (fn-crpsm-article-prefix query
            (fn-record-groups (fn-crps-row-article (fn-cp-nth 9 s))) articles)
        (fn-crpsm-query-prefix query (fn-cp-nth 11 s) (car articles)))))))

(local
 (defthm fn-crpsm-fresh-suffixes
  (and (fn-crpsm-query-prefix query query text)
       (fn-crpsm-article-prefix query full full))
  :hints (("Goal" :in-theory (enable fn-crpsm-query-prefix fn-crpsm-article-prefix)))))

(local
 (defthm fn-crpsm-query-prefix-advance
  (implies (and (fn-crpsm-query-prefix query remaining text)
                (consp remaining)
                (not (equal text (fn-record-octets-string (car remaining)))))
           (fn-crpsm-query-prefix query (cdr remaining) text))
  :hints (("Goal" :induct (fn-crpsm-query-prefix query remaining text)
           :in-theory (enable fn-crpsm-query-prefix)))))

(local
 (defthm fn-crpsm-exhausted-query-does-not-match
  (implies (fn-crpsm-query-prefix query nil text) (not (fn-crpsm-query-matches query text)))
  :hints (("Goal" :induct (fn-crpsm-query-prefix query nil text)
           :in-theory (enable fn-crpsm-query-prefix fn-crpsm-query-matches)))))

(local
 (defthm fn-crpsm-article-prefix-advance
  (implies (and (fn-crpsm-article-prefix query full remaining) (consp remaining)
                (not (fn-crpsm-query-matches query (car remaining))))
           (fn-crpsm-article-prefix query full (cdr remaining)))
  :hints (("Goal" :induct (fn-crpsm-article-prefix query full remaining)
           :in-theory (enable fn-crpsm-article-prefix)))))

(local
 (defthm fn-crpsm-match-in-remaining-is-in-query
  (implies (and (fn-crpsm-query-prefix query remaining text) (consp remaining)
                (equal text (fn-record-octets-string (car remaining))))
           (fn-crpsm-query-matches query text))
  :hints (("Goal" :induct (fn-crpsm-query-prefix query remaining text)
           :in-theory (enable fn-crpsm-query-prefix fn-crpsm-query-matches)))))

(local
 (defthm fn-crpsm-match-in-remaining-is-in-article
  (implies (and (fn-crpsm-article-prefix query full remaining) (consp remaining)
                (fn-crpsm-query-matches query (car remaining)))
           (fn-crpsm-intersects query full))
  :hints (("Goal" :induct (fn-crpsm-article-prefix query full remaining)
           :in-theory (enable fn-crpsm-article-prefix fn-crpsm-intersects)))))

(local
 (defthm fn-crpsm-exhausted-article-does-not-match
  (implies (fn-crpsm-article-prefix query full nil) (not (fn-crpsm-intersects query full)))
  :hints (("Goal" :induct (fn-crpsm-article-prefix query full nil)
           :in-theory (enable fn-crpsm-article-prefix fn-crpsm-intersects)))))

(defthm fn-crps-begin-establishes-no-skipped-match
 (implies (eq (fn-cp-nth 0 (fn-crps-begin plan key scan-limit)) :yield)
          (fn-crpsm-invariant (fn-cp-nth 1 (fn-crps-begin plan key scan-limit))))
 :hints (("Goal" :in-theory (enable fn-crps-begin fn-crps-state fn-crpsm-invariant fn-cp-nth))))

(defthm fn-crps-tick-preserves-no-skipped-match
 (implies (and (fn-crpsm-invariant s) (eq (fn-cp-nth 0 (fn-crps-tick s key row)) :yield))
          (fn-crpsm-invariant (fn-cp-nth 1 (fn-crps-tick s key row))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-crps-tick fn-crps-state fn-crps-page fn-crpsm-invariant fn-cp-nth)
                           (fn-crps-row-article fn-crpsm-article-prefix fn-crpsm-query-prefix
                            fn-crpsm-query-matches fn-crpsm-intersects fn-crs-namep fn-record-octets-string
                            fn-record-groups fn-record-sequence fn-cp-scope-cursor)))))

(local
 (defthm fn-crpsm-cursor-progress-update
  (implies (natp n) (equal (fn-cp-nth n (update-nth n position cursor)) position))
  :hints (("Goal" :induct (update-nth n position cursor)
            :in-theory (enable fn-cp-nth update-nth)))))

(defthm fn-crps-poll-selects-one-actual-matching-event
 (implies (and (fn-crpsm-invariant s)
                (eq (fn-cp-nth 0 (fn-crps-tick s key row)) :poll)
                (fn-cp-nth 2 (fn-crps-tick s key row)))
  (let ((answer (fn-crps-tick s key row)))
   (and (equal key (fn-cp-nth 1 s))
        (equal (fn-cp-nth 2 answer) (fn-cp-nth 9 s))
        (fn-crpsm-intersects (fn-cp-nth 4 s)
           (fn-record-groups (fn-crps-row-article (fn-cp-nth 2 answer))))
        (equal (fn-cp-nth 9 (fn-cp-nth 1 answer)) (1+ (nfix (fn-cp-nth 5 s)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-crps-tick fn-crps-state fn-crps-page fn-crpsm-invariant fn-cp-nth)
                           (fn-crps-row-article fn-crpsm-article-prefix fn-crpsm-query-prefix
                            fn-crpsm-query-matches fn-crpsm-intersects fn-crs-namep fn-record-octets-string
                            fn-record-groups fn-record-sequence fn-cp-scope-cursor)))))

(defthm fn-crps-tick-advances-a-matched-row-only-after-full-exclusion
 (implies (and (fn-crpsm-invariant s) (eq (fn-cp-nth 8 s) :match)
                (eq (fn-cp-nth 0 (fn-crps-tick s key row)) :yield)
                (equal (fn-cp-nth 5 (fn-cp-nth 1 (fn-crps-tick s key row)))
                       (1+ (nfix (fn-cp-nth 5 s)))))
          (not (fn-crpsm-intersects (fn-cp-nth 4 s)
                  (fn-record-groups (fn-crps-row-article (fn-cp-nth 9 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-crps-tick fn-crps-state fn-crps-page fn-crpsm-invariant fn-cp-nth)
                           (fn-crps-row-article fn-crpsm-article-prefix fn-crpsm-query-prefix
                            fn-crpsm-query-matches fn-crpsm-intersects fn-crs-namep fn-record-octets-string
                            fn-record-groups fn-record-sequence fn-cp-scope-cursor)))))

(in-theory (disable fn-crpsm-query-matches fn-crpsm-intersects fn-crpsm-query-prefix
                    fn-crpsm-article-prefix fn-crpsm-invariant))
