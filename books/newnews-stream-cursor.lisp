; NEWNEWS retains a string renderer instead of materializing a Message-ID
; line. Selection still uses the earlier captured groups; that initialization
; and membership work are separately owed, not covered by emission bytes.
(in-package "ACL2")
(include-book "newnews-metadata-cursor")
(include-book "string-line-cursor")

(defun fn-nnw-stream-renderp (progress)
  (declare (xargs :guard t))
  (and (consp progress) (eq (car progress) :render)))

(defun fn-nnw-stream-outputp (progress)
  (declare (xargs :guard t))
  (or (fn-nnw-stream-renderp progress) (equal progress '(:terminator))))

(defun fn-nnw-stream-render (line following)
  (declare (xargs :guard t))
  (list :render line following))

(defun fn-nnw-stream-tail (progress)
  (declare (xargs :guard t))
  (if (fn-nnw-stream-renderp progress)
      (fn-nnw-stream-tail (fn-cur-at 2 progress))
    (fn-nnw-tail progress)))

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
   ((equal progress '(:terminator))
    (mv '(46 13 10) nil))
   (t
    (let ((tail (fn-nnw-tail progress)))
      (if (not (consp tail))
          (mv '(46 13 10) nil)
        (let* ((article (car tail))
               (stamp (fn-article-stamp article))
               (horizon (fn-nnw-horizon progress))
               (following (and (consp (cdr tail))
                               (fn-nnw-cursor
                                (fn-nnw-groups progress) (fn-nnw-threshold progress)
                                (cdr tail) nil (if (natp stamp) stamp horizon))))
               (matched (and (fn-nntp-newnews-candidatep (fn-nnw-groups progress) article)
                             (not (fn-scol-tombstonep article fn-arena fn-cat))
                             (fn-nntp-newnews-newp (fn-nnw-threshold progress) stamp horizon))))
          (mv nil
              (if matched
                  (fn-nnw-stream-render (fn-sl-start (fn-article-msgid article)) following)
                (or following '(:terminator))))))))))

(defthm fn-nnw-stream-one-visits-at-most-one
  (<= (- (len (fn-nnw-stream-tail progress))
         (len (fn-nnw-stream-tail
               (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat))))) 1)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nnw-stream-one fn-nnw-stream-tail
                                     fn-nnw-stream-renderp fn-nnw-stream-render
                                     fn-nnw-tail fn-nnw-cursor fn-nnw-at))))

(def-cursor/output fn-nnw-stream (fn-arena fn-cat)
  :stobjs (fn-arena fn-cat)
  :call (fn-nnw-stream-one progress bytes fn-arena fn-cat)
  :output-phase (fn-nnw-stream-outputp progress)
  :visit-proof fn-nnw-stream-one-visits-at-most-one
  :visit-metric (len (fn-nnw-stream-tail progress)))

(defun fn-nnw-stream-owes (progress fn-arena fn-cat)
  (declare (xargs :guard t :stobjs (fn-arena fn-cat) :verify-guards nil))
  (cond
   ((fn-nnw-stream-renderp progress)
    (append (fn-sl-remaining (fn-cur-at 1 progress))
            (if (fn-cur-at 2 progress)
                (fn-nnw-stream-owes (fn-cur-at 2 progress) fn-arena fn-cat)
              '(46 13 10))))
   ((equal progress '(:terminator)) '(46 13 10))
   (t (fn-nnw-meta-owes progress fn-arena fn-cat))))

(defun fn-nnw-stream-remaining (cur fn-arena fn-cat)
  (declare (xargs :guard t :stobjs (fn-arena fn-cat) :verify-guards nil))
  (append (fn-cur-pending cur)
          (fn-nnw-stream-owes (fn-cur-progress cur) fn-arena fn-cat)))

(defun fn-nnw-stream-progress-okp (progress)
  (declare (xargs :guard t))
  (if (fn-nnw-stream-renderp progress)
      (and (fn-sl-okp (fn-cur-at 1 progress))
           (fn-nnw-stream-progress-okp (fn-cur-at 2 progress)))
    t))

(defun fn-nnw-stream-okp (cur)
  (declare (xargs :guard t))
  (and (true-listp (fn-cur-pending cur))
       (fn-nnw-stream-progress-okp (fn-cur-progress cur))))

(defthm fn-nnw-stream-one-keeps-progress-okp
  (implies (fn-nnw-stream-progress-okp progress)
           (fn-nnw-stream-progress-okp
            (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-nnw-stream-one fn-nnw-stream-progress-okp
                                    fn-nnw-stream-renderp fn-nnw-stream-render)
                                   (fn-sl-step fn-sl-start fn-sl-okp)))))

(defthm fn-nnw-stream-one-residual
  (implies progress
           (equal (append (car (fn-nnw-stream-one progress bytes fn-arena fn-cat))
                          (fn-nnw-stream-owes
                           (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat))
                           fn-arena fn-cat))
                  (fn-nnw-stream-owes progress fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nnw-stream-one fn-nnw-stream-owes
                            fn-nnw-stream-progress-okp fn-nnw-stream-renderp
                            fn-nnw-stream-render fn-nnw-meta-owes fn-nnw-cursor
                            fn-nnw-at fn-nnw-tail fn-nnw-groups fn-nnw-threshold
                            fn-nnw-horizon fn-nntp-stuff-lines)
                           (fn-sl-step fn-sl-start fn-sl-remaining fn-sl-okp
                            fn-nntp-newnews-candidatep fn-nntp-newnews-newp
                            fn-scol-tombstonep fn-nntp-string-octets fn-article-msgid
                            fn-article-stamp))
           :expand ((fn-nntp-newnews-scan-cat
                     (fn-nnw-at 1 progress) (fn-nnw-at 2 progress)
                     (fn-nnw-at 3 progress) (fn-nnw-at 5 progress) fn-arena fn-cat)))))

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
  (implies (not (fn-nnw-stream-outputp (fn-cur-progress cur)))
           (equal (fn-nnw-stream-remaining cur fn-arena fn-cat)
                  (fn-nnw-meta-remaining cur fn-arena fn-cat)))
  :hints (("Goal" :in-theory (enable fn-nnw-stream-remaining fn-nnw-stream-owes
                                     fn-nnw-stream-outputp fn-nnw-meta-remaining))))

(verify-guards fn-nnw-stream-one)
(verify-guards fn-nnw-stream-step)

(in-theory (disable fn-nnw-stream-one fn-nnw-stream-step fn-nnw-stream-owes
                    fn-nnw-stream-remaining fn-nnw-stream-okp))
