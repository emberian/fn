; served-catalog-join-entry.lisp -- the JOIN at the opens (lane sca-join-3,
; 2026-09-27; E for fn-scj-joinp, PRF-302).
;
; The catalog the host loads at an open (books/served-catalog-owner.lisp
; fn-sca-load-held-rows, under the recovered view's index) shows at its
; count exactly the view's visible list, every withdrawal mark is below the
; count, and every row's sequence is below the view's version: the join
; fn-scj-joinp (books/served-catalog-join.lisp).
;
; The catalog side (fn-scj-load-invp): a loaded row is committed visible
; when the index names its Message-ID and withdrawn at its own index
; otherwise, so the view at the count is the rows read as articles, newest
; first, filtered by the index (fn-scj-shown).  The row relation
; (fn-scj-acc-rowsp, books/served-catalog-join-number.lisp; E by
; fn-scj-acc-rowsp-of-cpr-loop) makes those articles the acceptance's; the
; view's visible list is a filter of the same articles
; (fn-ocl-view-historyp) with distinct Message-IDs, and its index is built
; from it (fn-scar-view-indexedp), so the filter by the index IS the visible
; list (fn-scj-shown-of-build-of-filter).

(in-package "ACL2")

(include-book "served-catalog-join-open")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-ctl-visible-articles)
                          (:definition fn-ctl-visible-filter)
                          (:rewrite fn-cpr-config-firstp-has-config)
                          (:rewrite fn-gidx-refresh-is-build)
                          (:rewrite fn-stxa-is-no-other-wire-event))))

(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; The catalog side of the load.

; The row the loader commits for R (its dispatch, by shape).
(defun fn-scj-load-h (r)
  (declare (xargs :guard t))
  (cond ((fn-cat-rowp r) r)
        ((fn-sca-composite-shapep r) (fn-hstxa-held r))
        (t nil)))

(defthm fn-scj-load-held-row-is
  (equal (fn-sca-load-held-row r idx c)
         (let ((h (fn-scj-load-h r)))
           (if h
               (if (fn-midx-lookup (fn-record-msgid h) idx)
                   (fn-cat-commit h c)
                 (fn-cat-commit (fn-held-with-withdrawn h (cons (len c) 0)) c))
             c)))
  :hints (("Goal" :in-theory (e/d (fn-sca-load-held-row) (fn-cat-commit-is-append fn-cat-rowp
                                                           fn-sca-composite-shapep fn-midx-lookup)))))

; The unwithdrawn rows below I, newest first, as articles.
(defun fn-scj-vis-below (i c)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp i)
      nil
    (if (fn-held-withdrawn (nth (1- i) c))
        (fn-scj-vis-below (1- i) c)
      (cons (fn-scj-row-art (nth (1- i) c)) (fn-scj-vis-below (1- i) c)))))

(defthm fn-scj-same-identity-vis-below
  (implies (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
           (equal (fn-scj-vis-below i c) (fn-scj-vis-below i d)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-scj-vis-below i c)
           :in-theory (e/d (fn-scj-vis-below fn-scj-row-identity fn-scj-row-art)
                           (fn-scj-catalog-identity)))
          ("Subgoal *1/3" :use ((:instance fn-scj-same-identity-nth (k (1- i)))))
          ("Subgoal *1/2" :use ((:instance fn-scj-same-identity-nth (k (1- i)))))))

(defthm fn-scj-vis-below-of-available-load
  (equal (fn-scj-vis-below i (fn-sca-load-held-rows rows idx fn-arena fn-cat))
         (fn-scj-vis-below i (fn-sca-load-held-rows-from rows idx nil)))
  :hints (("Goal" :in-theory (disable fn-scj-vis-below fn-sca-load-held-rows
                 fn-sca-load-held-rows-from fn-scj-catalog-identity
                 fn-scj-load-held-rows-keeps-raw-identity)
           :use ((:instance fn-scj-load-held-rows-keeps-raw-identity)
                 (:instance fn-scj-same-identity-vis-below
                  (c (fn-sca-load-held-rows rows idx fn-arena fn-cat))
                  (d (fn-sca-load-held-rows-from rows idx nil)))))))

(defthm fn-scj-view-below-is-vis-below
  (implies (and (fn-scj-marks-below c (len c)) (natp i) (<= i (len c)))
           (equal (fn-cat-view-below i (len c) fn-arena c) (fn-scj-vis-below i c)))
  :hints (("Goal" :induct (fn-scj-vis-below i c)
           :in-theory (e/d (fn-cat-row-article fn-scj-row-art) (fn-cat-visible-at-is-visiblep)))
          ("Subgoal *1/3" :use ((:instance fn-scj-visible-at-count-when-marks-below
                                           (fn-cat c) (seq (+ -1 i)))))
          ("Subgoal *1/2" :use ((:instance fn-scj-visible-at-count-when-marks-below
                                           (fn-cat c) (seq (+ -1 i)))))))

(local (defthm fn-scj-nth-of-append-below
  (implies (and (natp n) (< n (len a)))
           (equal (nth n (append a b)) (nth n a)))))

(defthm fn-scj-vis-below-of-append
  (implies (<= (nfix i) (len c))
           (equal (fn-scj-vis-below i (append c d)) (fn-scj-vis-below i c)))
  :hints (("Goal" :induct (fn-scj-vis-below i c) :in-theory (disable fn-scj-row-art))))

(local (defthm fn-scj-nth-len-of-append
  (equal (nth (len c) (append c (list r))) r)))

(defthm fn-scj-vis-below-of-snoc
  (equal (fn-scj-vis-below (+ 1 (len c)) (append c (list r)))
         (if (fn-held-withdrawn r)
             (fn-scj-vis-below (len c) c)
           (cons (fn-scj-row-art r) (fn-scj-vis-below (len c) c))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-scj-vis-below (+ 1 (len c)) (append c (list r))))
           :in-theory (disable fn-scj-row-art fn-scj-vis-below-of-append fn-scj-vis-below)
           :use ((:instance fn-scj-vis-below-of-append (i (len c)) (d (list r)))
                 (:instance fn-scj-nth-len-of-append)))))

; The articles ARTS whose Message-ID the index IDX names, in order.
(defun fn-scj-shown (arts idx)
  (declare (xargs :guard t))
  (if (consp arts)
      (if (fn-midx-lookup (fn-article-msgid (car arts)) idx)
          (cons (car arts) (fn-scj-shown (cdr arts) idx))
        (fn-scj-shown (cdr arts) idx))
    nil))

; The load's invariant: marks below the count, and the unwithdrawn rows are
; the rows' articles the index names.
(defun-nx fn-scj-load-invp (c idx)
  (and (fn-scj-marks-below c (len c))
       (equal (fn-scj-vis-below (len c) c) (fn-scj-shown (fn-scj-rows-arts c) idx))))

(defthm fn-scj-load-invp-of-available-load
  (equal (fn-scj-load-invp (fn-sca-load-held-rows rows idx fn-arena fn-cat) idx)
         (fn-scj-load-invp (fn-sca-load-held-rows-from rows idx nil) idx))
  :hints (("Goal" :in-theory (e/d (fn-scj-load-invp fn-scj-rows-arts)
               (fn-sca-load-held-rows fn-sca-load-held-rows-from)))))

; Every row the loader commits is unwithdrawn in the store (the intern and
; the POST's row write no withdrawal: fn-intern-row-at).
(defun fn-scj-rows-clearp (rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (and (let ((h (fn-scj-load-h (car rows))))
             (or (not h) (null (fn-held-withdrawn h))))
           (fn-scj-rows-clearp (cdr rows)))
    t))

(defthm fn-scj-row-art-msgid
  (equal (fn-article-msgid (fn-scj-row-art h)) (fn-record-msgid h))
  :hints (("Goal" :in-theory (enable fn-scj-row-art))))

(defthm fn-scj-row-art-of-with-withdrawn
  (equal (fn-scj-row-art (fn-held-with-withdrawn h w)) (fn-scj-row-art h))
  :hints (("Goal" :in-theory (enable fn-scj-row-art))))

(defthm fn-scj-load-invp-of-load-held-row
  (implies (and (fn-scj-load-invp c idx)
                (let ((h (fn-scj-load-h r))) (or (not h) (null (fn-held-withdrawn h)))))
           (fn-scj-load-invp (fn-sca-load-held-row r idx c) idx))
  :hints (("Goal" :in-theory (e/d (fn-scj-load-invp fn-cat-commit-is-append)
                                  (fn-scj-load-h fn-scj-row-art fn-cat-assign fn-midx-lookup
                                   fn-scj-rows-arts fn-scj-vis-below fn-sca-load-held-row))
           :expand ((:free (x b) (fn-scj-marks-below (list x) b)) (:free (b) (fn-scj-marks-below nil b)))
           :use ((:instance fn-scj-vis-below-of-snoc (r (fn-cat-assign (fn-scj-load-h r) c)))
                 (:instance fn-scj-vis-below-of-snoc
                            (r (fn-cat-assign (fn-held-with-withdrawn (fn-scj-load-h r) (cons (len c) 0)) c)))))))

(defthm fn-scj-load-invp-of-load-held-rows-from
  (implies (and (fn-scj-load-invp c idx) (fn-scj-rows-clearp rows))
           (fn-scj-load-invp (fn-sca-load-held-rows-from rows idx c) idx))
  :hints (("Goal" :induct (fn-sca-load-held-rows-from rows idx c)
           :in-theory (disable fn-scj-load-invp fn-sca-load-held-row fn-scj-load-h fn-scj-load-held-row-is))))

(defthm fn-scj-load-invp-of-nil
  (fn-scj-load-invp nil idx)
  :hints (("Goal" :in-theory (enable fn-scj-load-invp))))

; -----------------------------------------------------------------------------
; The view side: the filter by an index built from a filter is that filter.

(defun fn-scj-has-shown (xs vis)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (fn-ctl-has-msgid-p (fn-article-msgid (car xs)) vis)
          (cons (car xs) (fn-scj-has-shown (cdr xs) vis))
        (fn-scj-has-shown (cdr xs) vis))
    nil))

(defthm fn-scj-shown-of-build
  (implies (and (fn-midx-string-article-listp xs) (fn-midx-string-article-listp vis))
           (equal (fn-scj-shown xs (fn-midx-build vis)) (fn-scj-has-shown xs vis)))
  :hints (("Goal" :induct (fn-scj-has-shown xs vis)
           :in-theory (e/d (fn-midx-string-article-listp) (fn-midx-build fn-midx-lookup fn-ctl-has-msgid-p)))))

(defun fn-scj-consesp (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (consp (car xs)) (fn-scj-consesp (cdr xs))) t))

(defthm fn-scj-has-shown-of-cons-other
  (implies (and (not (member-equal (fn-article-msgid x) (fn-article-msgids ys))))
           (equal (fn-scj-has-shown ys (cons x v)) (fn-scj-has-shown ys v)))
  :hints (("Goal" :induct (fn-scj-has-shown ys v))))

(defthm fn-scj-has-msgid-of-visible-filter
  (implies (fn-ctl-has-msgid-p m (fn-ctl-visible-filter xs ws arts vs))
           (member-equal m (fn-article-msgids xs)))
  :hints (("Goal" :induct (fn-ctl-visible-filter xs ws arts vs)
           :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-scj-has-shown-of-visible-filter
  (implies (and (no-duplicatesp-equal (fn-article-msgids xs)) (fn-scj-consesp xs))
           (equal (fn-scj-has-shown xs (fn-ctl-visible-filter xs ws arts vs))
                  (fn-ctl-visible-filter xs ws arts vs)))
  :hints (("Goal" :induct (fn-ctl-visible-filter xs ws arts vs)
           :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-scj-string-articles-of-visible-filter
  (implies (fn-midx-string-article-listp xs)
           (fn-midx-string-article-listp (fn-ctl-visible-filter xs ws arts vs)))
  :hints (("Goal" :induct (fn-ctl-visible-filter xs ws arts vs)
           :in-theory (e/d (fn-midx-string-article-listp) (fn-ctl-withdrawn-by-p)))))

(defthm fn-scj-consesp-of-article-listp
  (implies (fn-article-listp g xs) (fn-scj-consesp xs))
  :hints (("Goal" :in-theory (enable fn-article-listp fn-articlep))))

; KEYSTONE (view side).  The articles XS (an acceptance's: distinct string
; Message-IDs) filtered by the index built from their visible filter are
; that visible filter.
(defthm fn-scj-shown-of-build-of-filter
  (implies (fn-article-listp g xs)
           (equal (fn-scj-shown xs (fn-midx-build (fn-ctl-visible-filter xs ws arts vs)))
                  (fn-ctl-visible-filter xs ws arts vs)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-midx-build fn-ctl-visible-filter fn-article-listp))))

(defthm fn-scj-shown-of-index-of-visible
  (implies (and (equal idx (fn-midx-build vis))
                (equal vis (fn-ctl-visible-filter xs ws xs vs))
                (fn-article-listp g xs))
           (equal (fn-scj-shown xs idx) vis))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-midx-build fn-ctl-visible-filter fn-article-listp))))

; -----------------------------------------------------------------------------
; The sequences: every loaded row's sequence below the view's version.

(defun fn-scj-rows-seqs-below (rows v)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (and (let ((h (fn-scj-load-h (car rows))))
             (or (not h) (< (nfix (fn-record-sequence h)) (nfix v))))
           (fn-scj-rows-seqs-below (cdr rows) v))
    t))

(defthm fn-scj-seqs-below-of-load-held-rows-from
  (implies (and (fn-scj-seqs-below c v) (fn-scj-rows-seqs-below rows v))
           (fn-scj-seqs-below (fn-sca-load-held-rows-from rows idx c) v))
  :hints (("Goal" :induct (fn-sca-load-held-rows-from rows idx c)
           :in-theory (e/d (fn-scj-load-held-row-is)
                           (fn-sca-load-held-row fn-scj-load-h fn-cat-commit-is-append fn-midx-lookup)))))

(defthm fn-scj-seqs-below-of-nil
  (fn-scj-seqs-below nil v)
  :hints (("Goal" :in-theory (enable fn-scj-seqs-below))))

; -----------------------------------------------------------------------------
; The join of the load.

; KEYSTONE (E for the join, over any related acceptance).  The catalog the
; host loads from ROWS under a view's index is joined to that view when the
; loaded catalog is related to an acceptance (the row relation) whose
; articles the view filters (its visible list) and indexes (its index is
; built from the visible list), the rows carry no withdrawal and every row's
; sequence is below the view's version.
(defthm fn-scj-joinp-of-load
  (let ((c (fn-sca-load-held-rows rows (fn-own-view-index view) fn-arena fn-cat)))
    (implies (and (fn-scj-acc-rowsp acc c)
                  (fn-article-listp g (fn-state-articles acc))
                  (equal (fn-state-articles (fn-own-view-archive view))
                         (fn-ctl-visible-articles (fn-state-articles acc) ws vs))
                  (equal (fn-own-view-index view)
                         (fn-midx-build (fn-state-articles (fn-own-view-archive view))))
                  (fn-scj-rows-clearp rows)
                  (fn-scj-rows-seqs-below rows (fn-own-view-version view)))
             (fn-scj-joinp view fn-arena c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scj-joinp fn-cat-view-articles fn-ctl-visible-articles)
                           (fn-scj-acc-rowsp fn-scj-load-invp fn-sca-load-held-rows-from
                            fn-midx-build fn-ctl-visible-filter fn-article-listp
                            fn-scj-rows-arts fn-cat-view-below fn-scj-vis-below
                            fn-scj-load-held-rows-keeps-raw-identity))
           :use ((:instance fn-scj-load-invp-of-load-held-rows-from (c nil) (idx (fn-own-view-index view)))
                 (:instance fn-scj-seqs-below-of-load-held-rows-from (c nil) (idx (fn-own-view-index view))
                            (v (fn-own-view-version view)))
                 (:instance fn-scj-view-below-is-vis-below
                            (c (fn-sca-load-held-rows rows (fn-own-view-index view) fn-arena fn-cat))
                            (i (len (fn-sca-load-held-rows rows (fn-own-view-index view) fn-arena fn-cat))))
                 (:instance fn-scj-acc-rowsp (c (fn-sca-load-held-rows-from rows (fn-own-view-index view) nil)))
                 (:instance fn-scj-load-invp (c (fn-sca-load-held-rows-from rows (fn-own-view-index view) nil))
                            (idx (fn-own-view-index view)))
                 (:instance fn-scj-shown-of-index-of-visible (xs (fn-state-articles acc))
                            (idx (fn-own-view-index view))
                            (vis (fn-state-articles (fn-own-view-archive view))))))))

; -----------------------------------------------------------------------------
; The rows' sequences are their positions (the replay checks each event's),
; and a loaded row's sequence is its event's (a composite's held row by the
; intern's binding, fn-row-composite-okp).

(defun fn-scj-seqs-from (events k)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (and (fn-store-event-p (car events))
           (equal (fn-store-event-sequence (car events)) k)
           (fn-scj-seqs-from (cdr events) (+ 1 (nfix k))))
    t))

(local (defun-nx fn-scj-seq-loop-ind (cn configs events config-sequence event-sequence)
  (declare (xargs :measure (+ (len configs) (len events)) :verify-guards nil))
  (if (not (fn-cnode-statep cn))
      nil
    (if (fn-cpr-config-firstp configs events)
        (let* ((record (car configs))
               (txid (fn-cfg-record-txid record))
               (node (fn-cnode-node cn)))
          (cond ((not (fn-cfg-recordp record)) nil)
                ((not (equal (fn-cfg-record-sequence record) config-sequence)) nil)
                ((not (fn-replay-advance-okp node txid)) nil)
                (t (let ((at (fn-cnode-make (fn-replay-advance-txid node txid) (fn-cnode-config cn))))
                     (if (not (fn-cnode-statep at))
                         nil
                       (if (not (fn-cnode-record-acceptablep at record (fn-cnode-line-ceiling)))
                           nil
                         (fn-scj-seq-loop-ind (fn-cnode-apply-config at record (fn-cnode-line-ceiling))
                                              (cdr configs) events
                                              (+ 1 (nfix config-sequence)) event-sequence)))))))
      (if (consp events)
          (let ((event (car events)))
            (cond ((not (fn-store-event-p event)) nil)
                  ((not (equal (fn-store-event-sequence event) event-sequence)) nil)
                  (t (let ((next (fn-cpr-apply-event cn event)))
                       (if (not (fn-cnode-statep next))
                           nil
                         (fn-scj-seq-loop-ind next configs (cdr events) config-sequence
                                              (+ 1 (nfix event-sequence))))))))
        nil)))))

(defthm fn-scj-seqs-from-of-cpr-loop
  (implies (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok)
           (fn-scj-seqs-from events es))
  :hints (("Goal" :induct (fn-scj-seq-loop-ind cn configs events cs es)
           :expand ((:free (cs es) (fn-cpr-loop cn configs events cs es)))
           :in-theory (e/d () (fn-cpr-loop fn-cnode-statep fn-cnode-apply-config fn-cnode-record-acceptablep
                               fn-cpr-apply-event fn-store-event-p fn-store-event-sequence
                               fn-cfg-recordp fn-replay-advance-txid fn-node-statep fn-replay-advance-okp)))))

(defthm fn-scj-seqs-from-of-cpr-replay
  (implies (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
           (fn-scj-seqs-from events 0))
  :hints (("Goal" :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop))
           :use ((:instance fn-scj-seqs-from-of-cpr-loop (cn (fn-cnode-initial (fn-cfg-initial)))
                            (cs 0) (es 0))))))

(local (defthm fn-scj-sequence-of-held-wire
  (equal (fn-record-sequence (fn-held-wire h p)) (fn-record-sequence h))
  :hints (("Goal" :in-theory (enable fn-held-wire fn-record-internals)))))

(local (defthm fn-scj-held-shape-is-no-other-event
   (implies (fn-held-shapep x)
            (and (not (fn-store-retention-event-p x))
                 (not (fn-stxe-p x)) (not (fn-stxk-p x))
                 (not (fn-hstxa-p x))
                 (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x))))
   :hints (("Goal" :use ((:instance fn-hstxa-p-forward-shape))
            :in-theory (e/d (fn-store-retention-event-p
                             fn-stxe-p fn-stxe-shapep fn-stxk-p fn-stxk-shapep
                             fn-cpe-eventp fn-held-shapep
                             fn-th-topic-eventp fn-th-local-admin-eventp)
                            (fn-hstxa-p))))))

(local (defthm fn-scj-store-event-rowp-is-held
   (implies (and (fn-store-event-p x) (fn-cat-rowp x))
            (fn-held-p x))
   :hints (("Goal" :in-theory (e/d (fn-store-event-p fn-cat-rowp)
                                   (fn-held-p fn-store-retention-event-p fn-stxe-p fn-stxk-p
                                    fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp))))))

(local (defthm fn-scj-held-is-not-tagged (implies (and (fn-held-p x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-held-p fn-held-shapep fn-record-sequence fn-held-internals fn-record-internals fn-record-uint64p fn-held-accessors-are-the-wire-accessors)))))
(local (defthm fn-scj-ret-is-not-tagged (implies (and (fn-store-retention-event-p x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-store-retention-event-p)))))
(local (defthm fn-scj-stxe-is-not-tagged (implies (and (fn-stxe-p x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-stxe-p fn-stxe-shapep fn-stxe-sequence fn-record-uint32p)))))
(local (defthm fn-scj-stxk-is-not-tagged (implies (and (fn-stxk-p x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-stxk-p fn-stxk-shapep fn-stxk-sequence fn-record-uint32p)))))
(local (defthm fn-scj-cpe-is-not-tagged (implies (and (fn-cpe-eventp x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-cpe-eventp)))))
(local (defthm fn-scj-topic-is-not-tagged (implies (and (fn-th-topic-eventp x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-th-topic-eventp fn-th-local-admin-eventp)))))

(local (defthm fn-scj-tagged-store-event-is-composite
   (implies (and (fn-store-event-p x) (consp x) (equal (car x) :hstxa))
            (and (fn-hstxa-p x) (not (fn-held-p x)) (not (fn-store-retention-event-p x))
                 (not (fn-stxe-p x)) (not (fn-stxk-p x))))
   :hints (("Goal" :in-theory (union-theories '(fn-store-event-p fn-scj-held-is-not-tagged
                                                fn-scj-ret-is-not-tagged fn-scj-stxe-is-not-tagged
                                                fn-scj-stxk-is-not-tagged fn-scj-cpe-is-not-tagged
                                                fn-scj-topic-is-not-tagged)
                                              (theory 'minimal-theory))))))

(local (defthm fn-scj-composite-record-sequence
   (implies (fn-replay-composite-record stxa)
            (equal (fn-record-sequence (fn-replay-composite-record stxa))
                   (fn-stxa-sequence stxa)))
   :hints (("Goal" :in-theory (enable fn-replay-composite-record fn-stxa-bindsp)))))

(local (defthm fn-scj-seq-when-row-wire-equal
   (implies (and (fn-held-p h) (equal (fn-row-wire-of h fn-arena) x))
            (equal (fn-record-sequence h) (fn-record-sequence x)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-row-wire-of) (fn-held-wire fn-held-p fn-row-bytes))))))

; A loaded row's sequence is its event's.
(defthm fn-scj-load-h-sequence
  (implies (and (fn-store-event-p r)
                (fn-row-composite-okp r fn-arena)
                (fn-scj-load-h r))
           (equal (fn-record-sequence (fn-scj-load-h r)) (fn-store-event-sequence r)))
  :rule-classes nil
  :hints (("Goal" :cases ((fn-cat-rowp r))
           :in-theory (e/d (fn-scj-load-h fn-sca-composite-shapep fn-store-event-sequence
                            fn-row-composite-okp)
                           (fn-held-p fn-cat-rowp fn-store-event-p fn-hstxa-p fn-stxa-p fn-row-wire-of
                            fn-replay-composite-record fn-held-wire fn-record-p
                            fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-cpe-eventp
                            fn-th-topic-eventp fn-row-bytes))
           :use ((:instance fn-hstxa-p-fields (x r))
                             (:instance fn-scj-seq-when-row-wire-equal (h (fn-hstxa-held r))
                                        (x (fn-replay-composite-record (fn-hstxa-stxa r))))
                 (:instance fn-scj-composite-record-sequence (stxa (fn-hstxa-stxa r)))))))

(defthm fn-scj-rows-seqs-below-of-seqs-from
  (implies (and (fn-scj-seqs-from rows k) (natp k)
                (fn-rows-composites-okp rows fn-arena)
                (<= (+ k (len rows)) (nfix v)))
           (fn-scj-rows-seqs-below rows v))
  :hints (("Goal" :induct (fn-scj-seqs-from rows k)
           :in-theory (e/d (fn-rows-composites-okp)
                           (fn-scj-load-h fn-store-event-p fn-store-event-sequence fn-row-composite-okp)))
          ("Subgoal *1/2" :use ((:instance fn-scj-load-h-sequence (r (car rows)))))
          ("Subgoal *1/1" :use ((:instance fn-scj-load-h-sequence (r (car rows)))))))

; -----------------------------------------------------------------------------
; E for the join at an owner.

; The view is current: it names the whole durable history at the store's
; frontier (what fn-own-refresh makes of an idle store; fn-own-start).
(defun-nx fn-scj-view-currentp (o)
  (let ((files (fn-sn-files (fn-own-store o))))
    (and (equal (fn-own-view-version (fn-own-view o)) (len (fn-sf-records files)))
         (equal (fn-own-view-frontier (fn-own-view o)) (fn-sf-frontier files)))))

; The current view of a related owner at an idle store filters the store's
; acceptance, whose node is a node state.
(defthm fn-scj-current-view-filters-the-acceptance
  (let* ((o (fn-ocfg-owner oc))
         (st (fn-own-store o))
         (view (fn-own-view o))
         (acc (fn-node-acceptance (fn-sn-node st))))
    (implies (and (fn-ocl-relation oc)
                  (fn-own-store-idlep st)
                  (fn-scj-view-currentp o))
             (and (equal (fn-state-articles (fn-own-view-archive view))
                         (fn-ctl-visible-articles (fn-state-articles acc)
                                                  (fn-own-view-withdrawals view)
                                                  (fn-own-view-verdicts view)))
                  (fn-node-statep (fn-sn-node st)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-ocl-relation fn-ocl-view-historyp fn-cst-relation fn-own-store-idlep
                         fn-scj-view-currentp fn-ctl-visible-state fn-ctl-visible-state-of-fields)
                       (theory 'minimal-theory))
           :use ((:instance fn-ocl-cst-events-are-proper (st (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-own-take-of-len
                            (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))))))

; KEYSTONE (E for the join at the owner).  The catalog the host loads from
; the rows of an owner in the live relation, at an idle store, under a
; current view's index, is joined to that view, when the rows carry no
; withdrawal and their sequences are below the view's version.
(defthm fn-scj-joinp-at-idle-related-owner
  (let* ((o (fn-ocfg-owner oc))
         (st (fn-own-store o))
         (view (fn-own-view o))
         (rows (fn-sf-records (fn-sn-files st))))
    (implies (and (fn-ocl-relation oc)
                  (fn-own-store-idlep st)
                  (fn-scar-view-indexedp o)
                  (fn-scj-view-currentp o)
                  (fn-scj-rows-clearp rows)
                  (fn-scj-rows-seqs-below rows (fn-own-view-version view)))
             (fn-scj-joinp view fn-arena
                           (fn-sca-load-held-rows rows (fn-own-view-index view) fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scar-view-indexedp fn-midx-correspondencep)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-current-view-filters-the-acceptance)
                 (:instance fn-scj-acc-rowsp-at-idle-related-owner
                            (view-index (fn-own-view-index (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-own-node-statep-acceptance-articles
                            (node (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-scj-joinp-of-load
                            (view (fn-own-view (fn-ocfg-owner oc)))
                            (rows (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                            (acc (fn-node-acceptance (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
                            (g (fn-state-groups (fn-node-acceptance (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))))
                            (ws (fn-own-view-withdrawals (fn-own-view (fn-ocfg-owner oc))))
                            (vs (fn-own-view-verdicts (fn-own-view (fn-ocfg-owner oc)))))))))

(defthm fn-ocl-relation-carries-cst
  (implies (fn-ocl-relation oc) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-ocl-relation))))

; The rows of a related store are positioned (the replay's sequence check),
; so under the intern's binding of composites every loaded row's sequence is
; below the history's length.
(defthm fn-scj-rows-seqs-below-at-related-store
  (let ((rows (fn-sf-records (fn-sn-files st))))
    (implies (and (fn-cst-relation st)
                  (fn-rows-composites-okp rows fn-arena))
             (fn-scj-rows-seqs-below rows (len rows))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cst-relation fn-cst-recoverablep fn-cst-replay-node)
                           (fn-cpr-replay fn-sn-statep fn-sn-observed-historyp fn-cst-final-configurationp
                            fn-node-statep fn-replay-advance-txid fn-replay-advance-okp fn-cnode-statep
                            fn-scj-rows-seqs-below fn-scj-seqs-from fn-rows-composites-okp
                            fn-cst-pending-linkp fn-cst-deferred-linkp))
           :use ((:instance fn-scj-seqs-from-of-cpr-replay
                            (configs (fn-sn-config-history st))
                            (events (fn-sf-records (fn-sn-files st))))
                 (:instance fn-scj-rows-seqs-below-of-seqs-from
                            (rows (fn-sf-records (fn-sn-files st))) (k 0)
                            (v (len (fn-sf-records (fn-sn-files st)))))))))

; KEYSTONE (E for the join at the owner, the sequences discharged).
(defthm fn-scj-joinp-at-idle-current-owner
  (let* ((o (fn-ocfg-owner oc))
         (st (fn-own-store o))
         (view (fn-own-view o))
         (rows (fn-sf-records (fn-sn-files st))))
    (implies (and (fn-ocl-relation oc)
                  (fn-own-store-idlep st)
                  (fn-scar-view-indexedp o)
                  (fn-scj-view-currentp o)
                  (fn-scj-rows-clearp rows)
                  (fn-rows-composites-okp rows fn-arena))
             (fn-scj-joinp view fn-arena
                           (fn-sca-load-held-rows rows (fn-own-view-index view) fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-view-currentp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-joinp-at-idle-related-owner)
                 (:instance fn-ocl-relation-carries-cst)
                 (:instance fn-scj-rows-seqs-below-at-related-store
                            (st (fn-own-store (fn-ocfg-owner oc))))))))

; -----------------------------------------------------------------------------
; The opens: the owner the host installs has a current, indexed view.

(defthm fn-scj-own-start-view-current
  (implies (fn-own-store-idlep store)
           (fn-scj-view-currentp (fn-own-start store max-conns)))
  :hints (("Goal" :in-theory (e/d (fn-own-start fn-own-refresh fn-scj-view-currentp)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-own-prefix-archive fn-ctl-visible-state fn-midx-build fn-gidx-build
                                   fn-ctl-subseq-diff fn-ctl-visible-state-of)))))

(defthm fn-scj-own-start-store
  (equal (fn-own-store (fn-own-start store max-conns)) store)
  :hints (("Goal" :in-theory (e/d (fn-own-start fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-own-prefix-archive fn-ctl-visible-state fn-midx-build fn-gidx-build
                                   fn-ctl-subseq-diff fn-ctl-visible-state-of)))))

(defthm fn-scj-configure-keeps-store-and-view
  (and (equal (fn-own-store (fn-own-configure o config)) (fn-own-store o))
       (equal (fn-own-view (fn-own-configure o config)) (fn-own-view o)))
  :hints (("Goal" :in-theory (enable fn-own-configure))))

(defthm fn-scj-ock-install-owner
  (implies (not (equal (fn-ock-install replayed opened max-conns) :fault))
           (let ((o (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))
             (and (equal (fn-own-store o) (fn-own-store (fn-own-start (fn-sn-open-state opened) max-conns)))
                  (equal (fn-own-view o) (fn-own-view (fn-own-start (fn-sn-open-state opened) max-conns))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ock-install) (fn-own-start fn-own-configure)))))

(defthm fn-scj-view-indexedp-by-view
  (implies (equal (fn-own-view o) (fn-own-view p))
           (equal (fn-scar-view-indexedp o) (fn-scar-view-indexedp p)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-scar-view-indexedp))))

(defthm fn-scj-installed-view-current-and-indexed
  (let ((o (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))
    (implies (and (not (equal (fn-ock-install replayed opened max-conns) :fault))
                  (fn-own-store-idlep (fn-own-store o)))
             (and (fn-scj-view-currentp o)
                  (fn-scar-view-indexedp o))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scj-view-currentp)
                                  (fn-own-start fn-ock-install fn-own-store-idlep fn-scar-view-indexedp
                                   fn-midx-correspondencep))
           :use ((:instance fn-scj-view-indexedp-by-view
                            (o (fn-ocfg-owner (fn-ock-install replayed opened max-conns)))
                            (p (fn-own-start (fn-sn-open-state opened) max-conns)))
                 (:instance fn-scj-ock-install-owner)
                 (:instance fn-scj-own-start-store (store (fn-sn-open-state opened)))
                 (:instance fn-scj-own-start-view-current (store (fn-sn-open-state opened)))
                 (:instance fn-oix-own-start-is-view-indexed (store (fn-sn-open-state opened)))))))

; -----------------------------------------------------------------------------
; The open's intern writes no withdrawal.

(local (defthm fn-scj-withdrawn-of-row-at
  (equal (fn-held-withdrawn (fn-intern-row-at w keyring generation h)) nil)
  :hints (("Goal" :in-theory (enable fn-intern-row-at fn-held-internals)))))

(local (defthm fn-scj-cat-rowp-not-tagged
  (implies (fn-cat-rowp x) (not (equal (car x) :hstxa)))
  :hints (("Goal" :in-theory (enable fn-cat-rowp fn-held-shapep fn-held-internals fn-record-internals
                                     fn-record-uint64p)))))

(local (defthm fn-scj-tagged-is-not-cat-rowp
  (not (fn-cat-rowp (cons :hstxa y)))
  :hints (("Goal" :use ((:instance fn-scj-cat-rowp-not-tagged (x (cons :hstxa y))))))))

(local (defthm fn-scj-cat-rowp-is-no-other-wire-event
   (implies (fn-cat-rowp x)
            (and (not (fn-store-retention-event-p x))
                 (not (fn-stxe-p x)) (not (fn-stxk-p x))
                 (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x))))
   :hints (("Goal" :in-theory (e/d (fn-cat-rowp) (fn-held-shapep))
            :use ((:instance fn-scj-held-shape-is-no-other-event))))))

(defthm fn-scj-intern-event-row-clear
  (let ((r (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
    (implies (and (not (equal r :bad)) (natp generation))
             (let ((h (fn-scj-load-h r)))
               (or (not h) (null (fn-held-withdrawn h))))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-scj-load-h fn-sca-composite-shapep fn-wire-event-p
                                   fn-hstxa-make fn-hstxa-held)
                                  (fn-intern-row-at fn-cat-intern-list fn-record-p fn-stxa-p fn-held-p
                                   fn-replay-composite-record fn-cat-rowp fn-held-p-of-intern-list
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-cpe-eventp
                                   fn-th-topic-eventp))
           :use ((:instance fn-held-p-of-intern-list)
                 (:instance fn-held-p-of-intern-list (w (fn-replay-composite-record w)))
                 (:instance fn-held-p-implies-cat-rowp (x (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena))))
                 (:instance fn-held-p-implies-cat-rowp
                            (x (mv-nth 0 (fn-cat-intern-list (fn-replay-composite-record w) keyring generation fn-arena))))
                 (:instance fn-scj-withdrawn-of-row-at (h (fn-arena-count fn-arena)))
                 (:instance fn-scj-withdrawn-of-row-at (w (fn-replay-composite-record w)) (h (fn-arena-count fn-arena)))
                 (:instance fn-cat-intern-list-is-row-at-count)
                 (:instance fn-cat-intern-list-is-row-at-count (w (fn-replay-composite-record w)))))))

(defthm fn-scj-intern-events-rows-clear
  (let ((rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))))
    (implies (and (not (equal rows :bad)) (natp generation))
             (fn-scj-rows-clearp rows)))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (union-theories '(fn-intern-events fn-scj-rows-clearp mv-nth car-cons cdr-cons
                                        (:executable-counterpart zp) (:executable-counterpart equal)
                                        (:executable-counterpart fn-scj-rows-clearp)
                                        (:induction fn-intern-events))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/4" :use ((:instance fn-scj-intern-event-row-clear (w (car ws)))))
          ("Subgoal *1/3" :use ((:instance fn-scj-intern-event-row-clear (w (car ws)))))
          ("Subgoal *1/2" :use ((:instance fn-scj-intern-event-row-clear (w (car ws)))))))

; -----------------------------------------------------------------------------
; E for the join at the host's entries.

(defthm fn-scj-cat-ocl-relation-gives-ocl-relation
  (implies (fn-cat-ocl-relation oc fn-arena fn-cat) (fn-ocl-relation oc))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cat-ocl-relation))))

; KEYSTONE (E for the join at recovery and the checkpoint open).  The owner
; host/owner-host.lisp fn-owner-install-extended installs from the capture of
; any prefix of rows extended over any suffix and the catalog it loads from
; those rows under the installed view's index (fn-sca-load-held-rows) are
; joined, under fn-sca-ocl-relation-at-recover's two row hypotheses and the
; rows' carrying no withdrawal (what the open's intern and the POST's row
; write: fn-scj-intern-events-rows-clear).
(defthm fn-scj-joinp-at-recover
  (let* ((oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
              configs frontier max-conns))
         (o (fn-ocfg-owner oc))
         (rows (fn-sf-records (fn-sn-files (fn-own-store o)))))
    (implies (and (not (equal oc :fault))
                  (fn-arena-p fn-arena)
                  (fn-rows-handles-inp (append prefix suffix) fn-arena)
                  (fn-rows-composites-okp (append prefix suffix) fn-arena)
                  (fn-scj-rows-clearp (append prefix suffix)))
             (fn-scj-joinp (fn-own-view o) fn-arena
                           (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view o))
                                                  fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ock-recover-extended) (theory 'minimal-theory))
           :use ((:instance fn-sca-ocl-relation-at-recover
                            (view-index (fn-own-view-index
                                         (fn-own-view (fn-ocfg-owner
                                                       (fn-ock-recover-extended
                                                        (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                                        configs frontier max-conns))))))
                 (:instance fn-scj-cat-ocl-relation-gives-ocl-relation
                            (oc (fn-ock-recover-extended
                                 (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                 configs frontier max-conns))
                            (fn-cat (fn-sca-load-held-rows
                                     (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner
                                      (fn-ock-recover-extended
                                       (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                       configs frontier max-conns)))))
                                     (fn-own-view-index
                                      (fn-own-view (fn-ocfg-owner
                                                    (fn-ock-recover-extended
                                                     (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                                     configs frontier max-conns))))
                                     fn-arena fn-cat)))
                 (:instance fn-scj-installed-view-current-and-indexed
                            (replayed (fn-sco-cpr-finish
                                       (fn-sco-cpr (fn-sco-extend (fn-sco-capture configs prefix) configs suffix))
                                       configs))
                            (opened (fn-sco-finalize
                                     (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                     configs frontier)))
                 (:instance fn-scj-joinp-at-idle-current-owner
                            (oc (fn-ock-recover-extended
                                 (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                 configs frontier max-conns)))))))

(local (defthm fn-scj-arena-p-of-clear
   (fn-arena-p (fn-arena-clear fn-arena))
   :hints (("Goal" :in-theory (enable fn-arena-clear)))))

; KEYSTONE (E for the join at the full open).  The rows the open interns
; from the decoded journal WS into the cleared arena, and the catalog the
; host loads from them under the installed view's index, are joined.
(defthm fn-scj-joinp-at-full-open
  (let* ((arena0 (fn-arena-clear fn-arena))
         (rows (mv-nth 0 (fn-intern-events ws nil 0 arena0)))
         (arena (mv-nth 1 (fn-intern-events ws nil 0 arena0)))
         (oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs nil) configs rows)
              configs frontier max-conns))
         (o (fn-ocfg-owner oc)))
    (implies (and (true-listp ws)
                  (not (equal rows :bad))
                  (not (equal oc :fault)))
             (fn-scj-joinp (fn-own-view o) arena
                           (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                                  (fn-own-view-index (fn-own-view o))
                                                  arena fn-cat))))
  :hints (("Goal" :use ((:instance fn-scj-joinp-at-recover
                                   (prefix nil)
                                   (suffix (mv-nth 0 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena))))
                                   (fn-arena (mv-nth 1 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena)))))
                        (:instance fn-scj-intern-events-rows-clear
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-sca-intern-events-accepts-wire-events
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-arena-p
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-handles-in
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-sca-intern-events-composites-okp
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(binary-append fn-scj-arena-p-of-clear
                                        (:executable-counterpart natp)
                                        (:executable-counterpart consp))))))
