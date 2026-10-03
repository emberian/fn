; Option 2': raw retained identity and available discovery are two views
; of the same root. Capture this projection during view preparation.
(in-package "ACL2")
(include-book "served-columns")

(defun fn-scat-article-availablep (article fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (let ((facts (fn-scol-facts article fn-cat)))
    (and (fn-hnov-p (fn-hf-nov facts))
         (not (fn-hnov-tomb (fn-hf-nov facts))))))

(defun fn-scat-available-articles-loop (articles acc fn-cat)
  (declare (xargs :stobjs fn-cat :guard (true-listp acc)))
  (if (consp articles)
      (fn-scat-available-articles-loop
        (cdr articles)
        (if (fn-scat-article-availablep (car articles) fn-cat)
            (cons (car articles) acc) acc) fn-cat)
    (revappend acc nil)))

(defun fn-scat-available-articles (articles fn-cat)
  (declare (xargs :stobjs fn-cat :guard t :verify-guards nil))
  (mbe :logic
       (if (consp articles)
           (if (fn-scat-article-availablep (car articles) fn-cat)
               (cons (car articles) (fn-scat-available-articles (cdr articles) fn-cat))
             (fn-scat-available-articles (cdr articles) fn-cat))
         nil)
       :exec (fn-scat-available-articles-loop articles nil fn-cat)))

(local (defthm fn-scat-available-articles-loop-is-revappend
  (equal (fn-scat-available-articles-loop articles acc fn-cat)
         (revappend acc (fn-scat-available-articles articles fn-cat)))
  :hints (("Goal" :induct (fn-scat-available-articles-loop articles acc fn-cat)
           :in-theory (disable fn-scat-article-availablep)))))

(verify-guards fn-scat-available-articles
  :hints (("Goal" :use ((:instance fn-scat-available-articles-loop-is-revappend
                                  (acc nil))))))

; Logical bytes reference. It is not evaluated per served command.
(defun fn-nntp-available-articles (articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (if (fn-nntp-article-tombstonep (car articles) fn-arena)
          (fn-nntp-available-articles (cdr articles) fn-arena)
        (cons (car articles) (fn-nntp-available-articles (cdr articles) fn-arena)))
    nil))

(defun fn-scat-available-archive (archive fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (fn-make-state (fn-state-groups archive) (fn-state-nexts archive)
                 (fn-scat-available-articles (fn-state-articles archive) fn-cat)
                 (fn-state-next-txid archive) (fn-state-pending archive)
                 (fn-state-fenced archive)))

(defun fn-nntp-available-archive (archive fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-make-state (fn-state-groups archive) (fn-state-nexts archive)
                 (fn-nntp-available-articles (fn-state-articles archive) fn-arena)
                 (fn-state-next-txid archive) (fn-state-pending archive)
                 (fn-state-fenced archive)))

; Proof-only relation: completeness is carried at view preparation. It is
; never used as a recognizer on a served path.
(defun-nx fn-scat-available-facts-completep (articles fn-arena fn-cat)
  (if (consp articles)
      (let ((facts (fn-scol-facts (car articles) fn-cat)))
        (and (fn-hnov-p (fn-hf-nov facts))
             (equal facts (fn-held-facts-of
                           (fn-nntp-article-bytes (car articles) fn-arena)))
             (fn-scat-available-facts-completep (cdr articles) fn-arena fn-cat)))
    t))

(defun-nx fn-scat-availability-completep (archive fn-arena fn-cat)
  (fn-scat-available-facts-completep (fn-state-articles archive) fn-arena fn-cat))

(defthm fn-hnov-tomb-of-hnov-of
  (equal (fn-hnov-tomb (fn-hnov-of bytes)) (fn-rcl-tombstonep bytes))
  :hints (("Goal" :in-theory
           (e/d (fn-hnov-of fn-hnov-of-parsed)
                (fn-article-parse fn-hnov-parsed-okp fn-hnov-field fn-rcl-tombstonep)))))

(defthm fn-scat-available-articles-is-reference
  (implies (fn-scat-available-facts-completep articles fn-arena fn-cat)
           (equal (fn-scat-available-articles articles fn-cat)
                  (fn-nntp-available-articles articles fn-arena)))
  :hints (("Goal" :induct (fn-scat-available-facts-completep articles fn-arena fn-cat)
           :in-theory (e/d (fn-nntp-article-tombstonep)
                           (fn-scol-facts fn-held-facts-of fn-hf-nov fn-hnov-p
                            fn-nntp-article-bytes fn-rcl-tombstonep)))))

(defthm fn-scat-available-archive-is-reference
  (implies (fn-scat-availability-completep archive fn-arena fn-cat)
           (equal (fn-scat-available-archive archive fn-cat)
                  (fn-nntp-available-archive archive fn-arena)))
  :hints (("Goal" :in-theory
           (e/d (fn-scat-availability-completep fn-scat-available-archive
                 fn-nntp-available-archive)
                (fn-scat-available-articles fn-nntp-available-articles
                 fn-scat-available-facts-completep)))))

(defthm fn-scat-available-archive-keeps-state-fields
  (let ((available (fn-scat-available-archive archive fn-cat)))
    (and (equal (fn-state-groups available) (fn-state-groups archive))
         (equal (fn-state-nexts available) (fn-state-nexts archive))
         (equal (fn-state-next-txid available) (fn-state-next-txid archive))
         (equal (fn-state-pending available) (fn-state-pending archive))
         (equal (fn-state-fenced available) (fn-state-fenced archive)))))

(local (defthm fn-ava-msgid-member-subset
  (implies (member-equal m (fn-article-msgids (fn-scat-available-articles a fn-cat)))
           (member-equal m (fn-article-msgids a)))
  :hints (("Goal" :induct (fn-scat-available-articles a fn-cat)
           :in-theory (e/d (fn-article-msgids) (fn-scat-article-availablep))))))

(local (defthm fn-ava-acceptedp-subset
  (implies (fn-acceptedp m (fn-scat-available-articles a fn-cat))
           (fn-acceptedp m a))
  :hints (("Goal" :induct (fn-scat-available-articles a fn-cat)
           :in-theory (e/d (fn-acceptedp) (fn-scat-article-availablep))))))

(local (defthm fn-ava-article-listp
  (implies (fn-article-listp groups a)
           (fn-article-listp groups (fn-scat-available-articles a fn-cat)))
  :hints (("Goal" :induct (fn-scat-available-articles a fn-cat)
           :in-theory (e/d (fn-article-listp) (fn-scat-article-availablep fn-articlep))))))

(local (defthm fn-ava-pair-member-append
  (equal (fn-pair-memberp p (append a b))
         (or (fn-pair-memberp p a) (fn-pair-memberp p b)))
  :hints (("Goal" :induct (append a b)
           :in-theory (enable fn-pair-memberp)))))

(local (defthm fn-ava-membership-subset
  (implies (fn-pair-memberp p
              (fn-all-article-memberships (fn-scat-available-articles a fn-cat)))
           (fn-pair-memberp p (fn-all-article-memberships a)))
  :hints (("Goal" :induct (fn-scat-available-articles a fn-cat)
           :in-theory (e/d (fn-all-article-memberships)
                           (fn-scat-article-availablep fn-pair-memberp))))))

(local (defthm fn-ava-conflicts-subset
  (implies (fn-memberships-conflictsp m (fn-scat-available-articles a fn-cat))
           (fn-memberships-conflictsp m a))
  :hints (("Goal" :induct (fn-memberships-conflictsp m a)
           :in-theory (e/d (fn-memberships-conflictsp)
                           (fn-scat-available-articles fn-pair-memberp
                            fn-all-article-memberships))))))

(local (defthm fn-ava-freshp
  (implies (fn-articles-freshp a)
           (fn-articles-freshp (fn-scat-available-articles a fn-cat)))
  :hints (("Goal" :induct (fn-scat-available-articles a fn-cat)
           :in-theory (e/d (fn-articles-freshp)
                           (fn-scat-article-availablep fn-memberships-conflictsp))))))

(local (defthm fn-ava-below-nextsp
  (implies (fn-articles-below-nextsp a nexts)
           (fn-articles-below-nextsp (fn-scat-available-articles a fn-cat) nexts))
  :hints (("Goal" :induct (fn-scat-available-articles a fn-cat)
           :in-theory (e/d (fn-articles-below-nextsp)
                           (fn-scat-article-availablep fn-memberships-below-nextsp))))))

(defthm fn-scat-available-archive-keeps-statep
  (implies (fn-statep archive)
           (fn-statep (fn-scat-available-archive archive fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-statep fn-state-internals fn-scat-available-archive)
                (fn-scat-available-articles fn-article-listp fn-articles-freshp
                 fn-articles-below-nextsp fn-acceptedp fn-pendingp fn-nexts-for-p
                 fn-string-listp fn-no-duplicatesp)))))

(in-theory (disable fn-scat-article-availablep fn-scat-available-articles
                    fn-scat-available-archive fn-nntp-available-articles
                    fn-nntp-available-archive fn-scat-availability-completep
                    fn-scat-available-facts-completep))
