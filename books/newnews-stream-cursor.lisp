; NEWNEWS retains a string renderer instead of materializing a Message-ID
; line. The factory retains configured groups and each candidate selects one
; group or membership per step. Matcher and heap tariffs remain separately owed.
(in-package "ACL2")
(include-book "newnews-metadata-cursor")
(include-book "string-line-cursor")
(include-book "newnews-candidate-selector")

(local (in-theory (disable fn-nnw-select-one fn-nnw-select-start)))

(defun fn-nnw-stream-renderp (progress)
  (declare (xargs :guard t))
  (and (consp progress) (eq (car progress) :render)))

(defun fn-nnw-stream-outputp (progress)
  (declare (xargs :guard t))
  (or (fn-nnw-stream-renderp progress) (equal progress '(:terminator))))

(defun fn-nnw-stream-render (line following)
  (declare (xargs :guard t))
  (list :render line following))

(defun fn-nnw-stream-selectp (progress)
  (declare (xargs :guard t))
  (and (consp progress) (eq (car progress) :select)))

(defun fn-nnw-stream-select (selector current)
  (declare (xargs :guard t))
  (list :select selector current))

(defun fn-nnw-stream-tail (progress)
  (declare (xargs :guard t))
  (if (fn-nnw-stream-renderp progress)
      (fn-nnw-stream-tail (fn-cur-at 2 progress))
    (if (fn-nnw-stream-selectp progress)
        (fn-nnw-tail (fn-cur-at 2 progress))
      (fn-nnw-tail progress))))

; Captured configured groups and parsed patterns remain shared references.
; The effective list is a disabled reference projection, never scan execution.
(defun fn-nnw-group-source (patterns groups)
  (declare (xargs :guard t))
  (list :configured patterns groups))

(defun fn-nnw-group-sourcep (source)
  (declare (xargs :guard t))
  (and (consp source) (eq (car source) :configured)))

(defun fn-nnw-group-source-effective (source)
  (declare (xargs :guard t))
  (fn-nntp-filter-groups-by-wildmat (fn-cur-at 1 source) (fn-cur-at 2 source)))

; The tag distinguishes configured references from the legacy filtered list,
; including on total malformed inputs; no list-shape validation runs per step.
(defun fn-nnw-configuredp (progress)
  (declare (xargs :guard t))
  (and (consp progress) (eq (car progress) :newnews-configured)))

(defun fn-nnw-configured-cursorp (progress)
  (declare (xargs :guard t))
  (and (true-listp progress) (equal (len progress) 6) (fn-nnw-configuredp progress)))

(defun fn-nnw-stream-scan-cursor (groups threshold tail horizon configuredp)
  (declare (xargs :guard t))
  (list (if configuredp :newnews-configured :newnews) groups threshold tail nil horizon))

(defun fn-nnw-stream-following (progress)
  (declare (xargs :guard t))
  (let* ((tail (fn-nnw-tail progress))
         (stamp (fn-article-stamp (fn-ag-car tail))))
    (and (consp (fn-ag-cdr tail))
         (fn-nnw-stream-scan-cursor (fn-nnw-groups progress) (fn-nnw-threshold progress)
                                   (fn-ag-cdr tail)
                                   (if (natp stamp) stamp (fn-nnw-horizon progress))
                                   (fn-nnw-configuredp progress)))))

(defun fn-nnw-stream-eligiblep (progress fn-arena fn-cat)
  (declare (xargs :guard t :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let ((article (fn-ag-car (fn-nnw-tail progress))))
    (and (not (fn-scol-tombstonep article fn-arena fn-cat))
         (fn-nntp-newnews-newp (fn-nnw-threshold progress)
                              (fn-article-stamp article) (fn-nnw-horizon progress)))))

(defun fn-nnw-stream-selected (progress matched fn-arena fn-cat)
  (declare (xargs :guard t :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let ((following (fn-nnw-stream-following progress)))
    (mv nil
        (if (and matched (fn-nnw-stream-eligiblep progress fn-arena fn-cat))
            (fn-nnw-stream-render
             (fn-sl-start (fn-article-msgid (fn-ag-car (fn-nnw-tail progress)))) following)
          (or following '(:terminator))))))

(defun fn-nnw-stream-one (progress bytes fn-arena fn-cat)
  (declare (xargs :guard (natp bytes) :stobjs (fn-arena fn-cat)
                  :verify-guards nil))
  (cond
   ((fn-nnw-stream-renderp progress)
    (mv-let (octets line)
      (fn-sl-step (fn-cur-at 1 progress) bytes)
      (mv octets
          (if line
              (fn-nnw-stream-render line (fn-cur-at 2 progress))
            (or (fn-cur-at 2 progress) '(:terminator))))))
   ((equal progress '(:terminator)) (mv '(46 13 10) nil))
   ((fn-nnw-stream-selectp progress)
    (mv-let (decided matched selector)
      (fn-nnw-select-one (fn-cur-at 1 progress))
      (if decided
          (fn-nnw-stream-selected (fn-cur-at 2 progress) matched fn-arena fn-cat)
        (mv nil (fn-nnw-stream-select selector (fn-cur-at 2 progress))))))
   ((not (consp (fn-nnw-tail progress))) (mv '(46 13 10) nil))
   ((fn-nnw-configuredp progress)
    (if (fn-nnw-stream-eligiblep progress fn-arena fn-cat)
        (mv nil
            (fn-nnw-stream-select
             (fn-nnw-select-start
              (fn-cur-at 1 (fn-nnw-groups progress))
              (fn-cur-at 2 (fn-nnw-groups progress))
              (fn-ag-car (fn-nnw-tail progress))) progress))
      (fn-nnw-stream-selected progress nil fn-arena fn-cat)))
   (t (fn-nnw-stream-selected
       progress
       (fn-nntp-newnews-candidatep (fn-nnw-groups progress)
                                  (fn-ag-car (fn-nnw-tail progress)))
       fn-arena fn-cat))))

(defthm fn-nnw-stream-one-visits-at-most-one
  (<= (- (len (fn-nnw-stream-tail progress))
         (len (fn-nnw-stream-tail
               (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat))))) 1)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nnw-stream-one fn-nnw-stream-tail
                                     fn-nnw-stream-renderp fn-nnw-stream-render
                                     fn-nnw-tail fn-nnw-cursor fn-nnw-at
                                     fn-nnw-stream-following fn-nnw-stream-selected
                                     fn-nnw-stream-selectp fn-nnw-stream-select))))

(defthm fn-nnw-stream-output-does-not-visit
  (implies (fn-nnw-stream-outputp progress)
           (equal (- (len (fn-nnw-stream-tail progress))
                     (len (fn-nnw-stream-tail
                           (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat))))) 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nnw-stream-one fn-nnw-stream-tail
                                     fn-nnw-stream-outputp fn-nnw-stream-renderp
                                     fn-nnw-stream-render fn-nnw-tail fn-nnw-at))))

; The legacy filtered-group normal phase consumes one article. Configured
; selection instead retains that article while advancing the selector.
(defthm fn-nnw-stream-candidate-progresses
  (implies (and (not (fn-nnw-stream-outputp progress))
                (not (fn-nnw-stream-selectp progress))
                (not (fn-nnw-configuredp progress))
                (consp (fn-nnw-tail progress)))
           (equal (len (fn-nnw-stream-tail
                        (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat))))
                  (1- (len (fn-nnw-tail progress)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nnw-stream-one fn-nnw-stream-tail
                                     fn-nnw-stream-outputp fn-nnw-stream-renderp
                                     fn-nnw-stream-render fn-nnw-tail fn-nnw-cursor
                                     fn-nnw-at))))

; Within a configured candidate, a positive selector remainder shrinks or
; selection ends. Article-tail length is intentionally unchanged meanwhile.
(defthm fn-nnw-stream-select-progresses
  (implies (and (fn-nnw-stream-selectp progress)
                (posp (fn-nnw-select-remaining (fn-cur-at 1 progress))))
           (< (let ((next (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat))))
                (if (fn-nnw-stream-selectp next)
                    (fn-nnw-select-remaining (fn-cur-at 1 next)) 0))
              (fn-nnw-select-remaining (fn-cur-at 1 progress))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nnw-select-one-progress (s (fn-cur-at 1 progress))))
           :in-theory (e/d (fn-nnw-stream-one fn-nnw-stream-selectp fn-nnw-stream-select
                             fn-nnw-stream-outputp fn-nnw-stream-renderp fn-nnw-stream-render
                             fn-nnw-stream-selected fn-nnw-stream-following
                             fn-nnw-stream-scan-cursor fn-cur-at)
                            (fn-nnw-select-one fn-nnw-select-remaining
                             fn-nnw-stream-eligiblep fn-sl-step)))))

(def-cursor/output fn-nnw-stream (fn-arena fn-cat)
  :stobjs (fn-arena fn-cat)
  :call (fn-nnw-stream-one progress bytes fn-arena fn-cat)
  :output-phase (fn-nnw-stream-outputp progress)
  :output-proof fn-nnw-stream-output-does-not-visit
  :visit-proof fn-nnw-stream-one-visits-at-most-one
  :visit-metric (len (fn-nnw-stream-tail progress)))

(defun fn-nnw-stream-normal-owes (progress fn-arena fn-cat)
  (declare (xargs :guard t :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if progress
      (fn-nnw-meta-owes
       (fn-nnw-cursor (if (fn-nnw-configuredp progress)
                          (fn-nnw-group-source-effective (fn-nnw-groups progress))
                        (fn-nnw-groups progress))
                      (fn-nnw-threshold progress) (fn-nnw-tail progress) nil
                      (fn-nnw-horizon progress)) fn-arena fn-cat)
    nil))

(defun fn-nnw-stream-owes (progress fn-arena fn-cat)
  (declare (xargs :guard t :stobjs (fn-arena fn-cat) :verify-guards nil))
  (cond
   ((fn-nnw-stream-renderp progress)
    (append (fn-sl-remaining (fn-cur-at 1 progress))
            (if (fn-cur-at 2 progress)
                (fn-nnw-stream-owes (fn-cur-at 2 progress) fn-arena fn-cat)
              '(46 13 10))))
   ((equal progress '(:terminator)) '(46 13 10))
   ((fn-nnw-stream-selectp progress)
    (let* ((current (fn-cur-at 2 progress))
           (following (fn-nnw-stream-following current)))
      (append
       (if (and (fn-nnw-select-value (fn-cur-at 1 progress))
                (fn-nnw-stream-eligiblep current fn-arena fn-cat))
           (fn-sl-remaining (fn-sl-start (fn-article-msgid (fn-ag-car (fn-nnw-tail current)))))
         nil)
       (if following
           (fn-nnw-stream-normal-owes following fn-arena fn-cat)
         '(46 13 10)))))
   (t (fn-nnw-stream-normal-owes progress fn-arena fn-cat))))

(defun fn-nnw-stream-remaining (cur fn-arena fn-cat)
  (declare (xargs :guard t :stobjs (fn-arena fn-cat) :verify-guards nil))
  (append (fn-cur-pending cur)
          (fn-nnw-stream-owes (fn-cur-progress cur) fn-arena fn-cat)))

(defun fn-nnw-stream-progress-okp (progress)
  (declare (xargs :guard t))
  (cond ((fn-nnw-stream-renderp progress)
         (and (fn-sl-okp (fn-cur-at 1 progress))
              (fn-nnw-stream-progress-okp (fn-cur-at 2 progress))))
        ((fn-nnw-stream-selectp progress)
         (and (fn-nnw-select-statep (fn-cur-at 1 progress))
              (or (fn-nnw-cursorp (fn-cur-at 2 progress))
                  (fn-nnw-configured-cursorp (fn-cur-at 2 progress)))))
        (t (or (not progress) (equal progress '(:terminator))
               (fn-nnw-cursorp progress) (fn-nnw-configured-cursorp progress)))))

(defun fn-nnw-stream-okp (cur)
  (declare (xargs :guard t))
  (and (true-listp (fn-cur-pending cur))
       (fn-nnw-stream-progress-okp (fn-cur-progress cur))))

(defthm fn-nnw-stream-one-keeps-progress-okp
  (implies (fn-nnw-stream-progress-okp progress)
           (fn-nnw-stream-progress-okp
            (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-nnw-stream-one fn-nnw-stream-progress-okp
                                    fn-nnw-stream-renderp fn-nnw-stream-render
                                    fn-nnw-stream-selected fn-nnw-stream-following
                                    fn-nnw-stream-selectp fn-nnw-stream-select fn-nnw-cursorp)
                                   (fn-sl-step fn-sl-start fn-sl-okp)))))

(local
 (defthm fn-nnw-stream-normal-row-decomposition
   (implies (consp (fn-nnw-tail progress))
            (equal (fn-nnw-stream-normal-owes progress fn-arena fn-cat)
                   (append
                    (if (and (fn-nntp-newnews-candidatep
                              (if (fn-nnw-configuredp progress)
                                  (fn-nnw-group-source-effective (fn-nnw-groups progress))
                                (fn-nnw-groups progress))
                              (fn-ag-car (fn-nnw-tail progress)))
                             (fn-nnw-stream-eligiblep progress fn-arena fn-cat))
                        (fn-sl-remaining
                         (fn-sl-start (fn-article-msgid (fn-ag-car (fn-nnw-tail progress)))))
                      nil)
                    (if (fn-nnw-stream-following progress)
                        (fn-nnw-stream-normal-owes (fn-nnw-stream-following progress)
                                                  fn-arena fn-cat)
                      '(46 13 10)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-nnw-stream-normal-owes fn-nnw-stream-following
                             fn-nnw-stream-eligiblep fn-nnw-meta-owes fn-nnw-cursor
                             fn-nnw-at fn-nnw-tail fn-nnw-groups fn-nnw-threshold
                             fn-nnw-horizon fn-ag-car fn-ag-cdr fn-nntp-stuff-lines)
                            (fn-nnw-group-source-effective fn-sl-start fn-sl-remaining
                             fn-nntp-newnews-candidatep fn-nntp-newnews-newp
                             fn-scol-tombstonep fn-nntp-string-octets fn-article-msgid
                             fn-article-stamp))
            :expand ((fn-nntp-newnews-scan-cat
                      (fn-nnw-group-source-effective (fn-nnw-at 1 progress))
                      (fn-nnw-at 2 progress) (fn-nnw-at 3 progress)
                      (fn-nnw-at 5 progress) fn-arena fn-cat)
                     (fn-nntp-newnews-scan-cat
                      (fn-nnw-at 1 progress) (fn-nnw-at 2 progress)
                      (fn-nnw-at 3 progress) (fn-nnw-at 5 progress) fn-arena fn-cat))))))

(local
 (defthm fn-nnw-stream-owes-of-following
   (equal (fn-nnw-stream-owes (fn-nnw-stream-following progress) fn-arena fn-cat)
          (fn-nnw-stream-normal-owes (fn-nnw-stream-following progress) fn-arena fn-cat))
   :hints (("Goal" :in-theory (e/d (fn-nnw-stream-following fn-nnw-stream-owes
                                     fn-nnw-stream-renderp fn-nnw-stream-selectp
                                     fn-nnw-cursor fn-nnw-at)
                                    (fn-nnw-stream-normal-owes))))))

(local
 (defthm fn-nnw-stream-normal-empty
   (implies (not (consp (fn-nnw-tail progress)))
            (equal (fn-nnw-stream-normal-owes progress fn-arena fn-cat)
                   (if progress '(46 13 10) nil)))
   :hints (("Goal" :in-theory (e/d (fn-nnw-stream-normal-owes fn-nnw-meta-owes
                                     fn-nnw-cursor fn-nnw-at fn-nnw-tail)
                                    (fn-nnw-group-source-effective))
            :expand ((fn-nntp-newnews-scan-cat
                      (fn-nnw-group-source-effective (fn-nnw-at 1 progress))
                      (fn-nnw-at 2 progress) (fn-nnw-at 3 progress)
                      (fn-nnw-at 5 progress) fn-arena fn-cat)
                     (fn-nntp-newnews-scan-cat
                      (fn-nnw-at 1 progress) (fn-nnw-at 2 progress)
                      (fn-nnw-at 3 progress) (fn-nnw-at 5 progress) fn-arena fn-cat))))))

(defthm fn-nnw-stream-one-residual
  (implies progress
           (equal (append (car (fn-nnw-stream-one progress bytes fn-arena fn-cat))
                          (fn-nnw-stream-owes
                           (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat))
                           fn-arena fn-cat))
                  (fn-nnw-stream-owes progress fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nnw-stream-normal-row-decomposition))
           :in-theory (e/d (fn-nnw-stream-one fn-nnw-stream-owes
                            fn-nnw-stream-selectp fn-nnw-stream-select
                            fn-nnw-stream-renderp fn-nnw-stream-render fn-nnw-stream-selected
                            fn-nnw-group-sourcep fn-nnw-group-source-effective fn-nnw-groups
                            fn-nnw-cursor
                            fn-nnw-at fn-nnw-tail fn-nnw-threshold fn-nnw-horizon)
                           (fn-sl-step fn-sl-start fn-sl-remaining fn-sl-okp
                            fn-nnw-select-one fn-nnw-select-value fn-nnw-select-start
                            fn-nnw-stream-normal-owes fn-nnw-stream-following fn-nnw-stream-eligiblep
                            fn-nntp-newnews-candidatep fn-nntp-newnews-newp
                            fn-scol-tombstonep fn-nntp-string-octets fn-article-msgid
                            fn-article-stamp)))))

(local
 (defthm fn-nnw-stream-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-nnw-stream-split-residual-onto
   (equal (append (mv-nth 0 (fn-cur-split xs n))
                  (mv-nth 1 (fn-cur-split xs n)) suffix)
          (append xs suffix))
   :hints (("Goal" :in-theory (disable fn-cur-split fn-nnw-stream-assoc)
            :use ((:instance fn-nnw-stream-assoc
                             (a (mv-nth 0 (fn-cur-split xs n)))
                             (b (mv-nth 1 (fn-cur-split xs n))) (c suffix)))))))

(local
 (defthm fn-nnw-stream-split-residual-append
   (equal (append (car (fn-cur-split xs n))
                  (mv-nth 1 (fn-cur-split xs n)) suffix)
          (append xs suffix))
   :hints (("Goal" :use fn-nnw-stream-split-residual-onto
            :in-theory (disable fn-cur-split fn-nnw-stream-split-residual-onto)))))

(defthm fn-nnw-stream-step-residual
  (equal (append (car (fn-nnw-stream-step cur visits bytes fn-arena fn-cat))
                 (fn-nnw-stream-remaining
                  (mv-nth 1 (fn-nnw-stream-step cur visits bytes fn-arena fn-cat))
                  fn-arena fn-cat))
         (fn-nnw-stream-remaining cur fn-arena fn-cat))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nnw-stream-step fn-nnw-stream-remaining)
                           (fn-cur-split fn-cur-split-residual fn-nnw-stream-one fn-nnw-stream-owes))
           :use ((:instance fn-nnw-stream-one-residual (progress (fn-cur-progress cur)))
                 (:instance fn-cur-split-residual (xs (fn-cur-pending cur)) (n bytes))
                 (:instance fn-cur-split-residual
                            (xs (mv-nth 0 (fn-nnw-stream-one (fn-cur-progress cur) bytes fn-arena fn-cat)))
                            (n bytes))))))

(defthm fn-nnw-stream-step-residual-append
  (equal (append (car (fn-nnw-stream-step cur visits bytes fn-arena fn-cat))
                 (fn-nnw-stream-remaining
                  (mv-nth 1 (fn-nnw-stream-step cur visits bytes fn-arena fn-cat)) fn-arena fn-cat)
                 suffix)
         (append (fn-nnw-stream-remaining cur fn-arena fn-cat) suffix))
  :hints (("Goal" :in-theory (disable fn-nnw-stream-step fn-nnw-stream-remaining
                                     fn-nnw-stream-assoc)
           :use (fn-nnw-stream-step-residual
                 (:instance fn-nnw-stream-assoc
                            (a (car (fn-nnw-stream-step cur visits bytes fn-arena fn-cat)))
                            (b (fn-nnw-stream-remaining
                                (mv-nth 1 (fn-nnw-stream-step cur visits bytes fn-arena fn-cat))
                                fn-arena fn-cat)) (c suffix))))))

(defthm fn-nnw-stream-remaining-of-not-live
  (implies (not (fn-nnw-meta-livep cur))
           (equal (fn-nnw-stream-remaining cur fn-arena fn-cat) nil))
  :hints (("Goal" :in-theory (enable fn-nnw-meta-livep fn-nnw-stream-remaining
                                     fn-nnw-stream-owes fn-nnw-meta-owes))))

(defthm fn-nnw-stream-step-terminal-residual
  (implies (not (fn-nnw-meta-livep
                 (mv-nth 1 (fn-nnw-stream-step cur visits bytes fn-arena fn-cat))))
           (equal (append (car (fn-nnw-stream-step cur visits bytes fn-arena fn-cat)) suffix)
                  (append (fn-nnw-stream-remaining cur fn-arena fn-cat) suffix)))
  :hints (("Goal" :in-theory (disable fn-nnw-stream-step fn-nnw-stream-remaining
                                     fn-nnw-meta-livep fn-nnw-stream-step-residual-append)
           :use fn-nnw-stream-step-residual-append)))

(defthm fn-nnw-stream-one-output-list
  (true-listp (car (fn-nnw-stream-one progress bytes fn-arena fn-cat)))
  :hints (("Goal" :in-theory (enable fn-nnw-stream-one fn-sl-step fn-sl-loop))))

(defthm fn-nnw-stream-step-keeps-pending-true-listp
  (implies (true-listp (fn-cur-pending cur))
           (true-listp
            (fn-cur-pending (mv-nth 1 (fn-nnw-stream-step cur visits bytes fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (e/d (fn-nnw-stream-step) (fn-nnw-stream-one)))))

(defthm fn-nnw-stream-fresh-remaining
  (implies (and (not (fn-nnw-stream-outputp (fn-cur-progress cur)))
                (not (fn-nnw-stream-selectp (fn-cur-progress cur)))
                (not (fn-nnw-configuredp (fn-cur-progress cur))))
           (equal (fn-nnw-stream-remaining cur fn-arena fn-cat)
                  (fn-nnw-meta-remaining cur fn-arena fn-cat)))
  :hints (("Goal" :in-theory (enable fn-nnw-stream-remaining fn-nnw-stream-owes
                                     fn-nnw-stream-outputp fn-nnw-stream-selectp
                                     fn-nnw-meta-remaining fn-nnw-meta-owes
                                     fn-nnw-stream-normal-owes fn-nnw-group-source-effective
                                     fn-nnw-group-sourcep))))

(defthm fn-nnw-stream-configured-remaining
  (equal
   (fn-nnw-stream-remaining
    (list context
          (list :newnews-configured (list :configured patterns groups)
                threshold tail nil horizon)
          pending dependency) fn-arena fn-cat)
   (fn-nnw-meta-remaining
    (list context
          (list :newnews (fn-nntp-filter-groups-by-wildmat patterns groups)
                threshold tail nil horizon)
          pending dependency) fn-arena fn-cat))
  :hints (("Goal"
           :in-theory
           (e/d (fn-nnw-stream-remaining fn-nnw-stream-owes fn-nnw-stream-normal-owes
                 fn-nnw-stream-renderp fn-nnw-stream-selectp fn-nnw-configuredp
                 fn-nnw-stream-scan-cursor fn-nnw-group-source fn-nnw-group-source-effective
                 fn-cur-at fn-cur-make fn-cur-progress fn-cur-pending
                 fn-nnw-meta-remaining fn-nnw-cursor fn-nnw-at fn-nnw-tail
                 fn-nnw-groups fn-nnw-threshold fn-nnw-horizon)
                (fn-nnw-meta-owes fn-nnw-stream-fresh-remaining
                 fn-nntp-filter-groups-by-wildmat)))))

(defthm fn-nnw-stream-initial-status-first
  (implies (fn-nnw-meta-initialp cur)
           (let ((octets (fn-nnw-stream-remaining cur fn-arena fn-cat)))
             (not (and (consp octets) (equal (car octets) 50)
                       (consp (cdr octets)) (equal (car (cdr octets)) 49)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-nnw-meta-initialp fn-nnw-stream-remaining)
                                  (fn-nnw-stream-owes fn-nnw-stream-fresh-remaining)))))

(verify-guards fn-nnw-stream-eligiblep)
(verify-guards fn-nnw-stream-selected)
(verify-guards fn-nnw-stream-one)
(verify-guards fn-nnw-stream-step)

(in-theory (disable fn-nnw-stream-one fn-nnw-stream-step fn-nnw-stream-owes
                    fn-nnw-stream-remaining fn-nnw-stream-okp))

; Incremental factory: validation is the original NEWNEWS decision, but the
; configured-group selector is retained rather than materialized. Its actual
; stream consumer and refinement are assembled with the selector primitive.
(defun fn-nntp-newnews-response-stream (session archive env args fn-arena fn-cat)
  ; fn-nntp-newnews-response, its scan reading the catalog's tombstone
  ; column.  The parse is the reference's, form for form.
  (declare (ignore fn-arena fn-cat)
           (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if (not (and (consp args) (consp (cdr args)) (consp (cdr (cdr args)))
                (or (null (cdr (cdr (cdr args))))
                    (and (consp (cdr (cdr (cdr args))))
                         (null (cdr (cdr (cdr (cdr args)))))
                         (fn-nntp-keywordp (car (cdr (cdr (cdr args))))
                                           "GMT")))))
      (fn-nntp-single session (fn-proto-text * :syntax))
    (let ((date (fn-nntp-newgroups-date-parse
                 (car (cdr args))
                 (fn-nntp-observed-year (fn-nntp-env-observation env))))
          (time (fn-nntp-newgroups-time-parse (car (cdr (cdr args)))))
          (patterns (fn-wildmat-parse (car args))))
      (if (and (not (fn-nntp-parse-okp date))
               (equal (car (cdr date)) :no-century))
          (fn-nntp-single
           session (fn-proto-text * :no-century))
        (if (or (not (fn-nntp-parse-okp date))
                (not (fn-nntp-parse-okp time))
                (not (fn-wildmat-result-okp patterns)))
            (fn-nntp-single session (fn-proto-text * :syntax))
          (fn-nntp-make-result
           session
           (list
            (fn-nnw-meta-effect
             (fn-cur-make
              (list archive env args)
              (fn-nnw-stream-scan-cursor
               (fn-nnw-group-source
                (fn-wildmat-result-value patterns) (fn-state-groups archive))
               (fn-nntp-civil-dtn-ms
                (fn-nntp-parse-1 date) (fn-nntp-parse-2 date)
                (fn-nntp-parse-3 date) (fn-nntp-parse-1 time)
                (fn-nntp-parse-2 time) (fn-nntp-parse-3 time))
               (fn-state-articles archive) (fn-nntp-newnews-reader-horizon env) t)
              (fn-nntp-crlf (fn-nntp-string-octets (fn-proto-text "NEWNEWS" :listed)))
              nil)))))))))

(verify-guards fn-nntp-newnews-response-stream)


(defthm fn-nntp-newnews-response-stream-keeps-session
  (equal (car (fn-nntp-newnews-response-stream session archive env args fn-arena fn-cat))
         session)
  :hints (("Goal" :in-theory (enable fn-nntp-newnews-response-stream
                                     fn-nntp-make-result fn-nntp-single))))

(in-theory (disable fn-nnw-group-source-effective fn-nntp-newnews-response-stream))
