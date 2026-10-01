; fn: a restricted reader's view, prepared once per pin and read by every
; command (PKT-643).
;
; A read-restricted session (PRF-222, books/group-access.lisp) is served the
; view fn-gac-view-entry TEXT ARCHIVE CONTROL: the store with every group its
; rule TEXT does not admit absent, and that store's trie, buckets and
; withdrawn list.  Built per command it is a walk of the whole archive (the
; cut, a trie and a bucket build) for every command of such a session.
;
; The access cache holds, per read text, ONE entry: the text, the archive
; and control pin it was built for, and the view.  Its invariant
; (fn-gacc-okp) is that every entry's view IS fn-gac-view-entry of its own
; key, so an entry found under the key a command needs is the view that
; command would build (KEYSTONE fn-gacc-view-is-the-view-entry).  The host
; prepares the connection's entry before a read (fn-gacc-prepare, from
; host/owner-host.lisp): the entry already keyed to the connection's pin is
; kept; one keyed to the pin before an acceptance is extended by the one
; article (fn-gacc-extend: the cut of one article, one trie path copy and its
; bucket entries); anything else is built once (a restart, a withdrawal, a
; new rule).  KEYSTONE fn-gacc-prepare-keeps-okp: preparing keeps the
; invariant; with fn-gacc-okp-of-nil the cache the host starts with, every
; cache the host holds satisfies it.  The served delegate
; (books/served-catalog-chain.lisp fn-scr-auth-delegate) reads the entry
; (fn-gacc-view) and builds the view per command only when none is keyed to
; its pin.
;
; The keys are compared with EQUAL, which is EQ first: the connection's
; pinned archive and control are the very objects the entry was built from,
; so a hit costs a few pointer comparisons.

(in-package "ACL2")
(include-book "def-loop")
(include-book "group-access")
(include-book "owner")

; -----------------------------------------------------------------------------
; Entries

(defun fn-gacc-entry (text archive control view)
  (declare (xargs :guard t))
  (list* text archive control view))

(defun fn-gacc-text (e) (declare (xargs :guard t)) (fn-ag-car e))
(defun fn-gacc-archive (e) (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr e)))
(defun fn-gacc-control (e) (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr e))))
(defun fn-gacc-entry-view (e) (declare (xargs :guard t)) (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr e))))

(defthm fn-gacc-entry-fields
  (and (equal (fn-gacc-text (fn-gacc-entry text archive control view)) text)
       (equal (fn-gacc-archive (fn-gacc-entry text archive control view)) archive)
       (equal (fn-gacc-control (fn-gacc-entry text archive control view)) control)
       (equal (fn-gacc-entry-view (fn-gacc-entry text archive control view)) view)
       (consp (fn-gacc-entry text archive control view)))
  :hints (("Goal" :in-theory (enable fn-ag-car fn-ag-cdr))))

; An entry is sound when its view is the view of its key.
(defun fn-gacc-entry-okp (e)
  (declare (xargs :guard t))
  (and (consp e) (consp (cdr e)) (consp (cddr e))
       (equal (fn-gacc-entry-view e)
              (fn-gac-view-entry (fn-gacc-text e) (fn-gacc-archive e)
                                 (fn-gacc-control e)))))

(defun fn-gacc-okp (cache)
  (declare (xargs :guard t))
  (if (consp cache)
      (and (fn-gacc-entry-okp (car cache))
           (fn-gacc-okp (cdr cache)))
    t))

(defthm fn-gacc-okp-of-nil
  (fn-gacc-okp nil))

; The entry for TEXT, or nil.
(defun fn-gacc-find (text cache)
  (declare (xargs :guard t))
  (if (consp cache)
      (if (and (consp (car cache)) (equal (fn-gacc-text (car cache)) text))
          (car cache)
        (fn-gacc-find text (cdr cache)))
    nil))

(defthm fn-gacc-find-okp
  (implies (and (fn-gacc-okp cache) (fn-gacc-find text cache))
           (fn-gacc-entry-okp (fn-gacc-find text cache))))

(defthm fn-gacc-find-text
  (implies (fn-gacc-find text cache)
           (equal (fn-gacc-text (fn-gacc-find text cache)) text)))

; The view the cache holds for TEXT at exactly this ARCHIVE and CONTROL, or
; nil.
(defun fn-gacc-view (text archive control cache)
  (declare (xargs :guard t))
  (let ((e (fn-gacc-find text cache)))
    (if (and e
             (equal (fn-gacc-archive e) archive)
             (equal (fn-gacc-control e) control))
        (fn-gacc-entry-view e)
      nil)))

(defthm fn-gacc-find-view
  (implies (and (fn-gacc-okp cache) (fn-gacc-find text cache))
           (equal (fn-gacc-entry-view (fn-gacc-find text cache))
                  (fn-gac-view-entry text (fn-gacc-archive (fn-gacc-find text cache))
                                     (fn-gacc-control (fn-gacc-find text cache)))))
  :hints (("Goal" :in-theory (disable fn-gac-view-entry fn-gacc-text fn-gacc-archive
                                      fn-gacc-control fn-gacc-entry-view))))

;; KEYSTONE.  A view the cache answers is the view of the command's key.
(defthm fn-gacc-view-is-the-view-entry
  (implies (and (fn-gacc-okp cache)
                (fn-gacc-view text archive control cache))
           (equal (fn-gacc-view text archive control cache)
                  (fn-gac-view-entry text archive control)))
  :hints (("Goal" :in-theory (e/d (fn-gacc-view)
                                  (fn-gacc-find fn-gac-view-entry fn-gacc-okp
                                   fn-gacc-archive fn-gacc-control
                                   fn-gacc-entry-view)))))

; -----------------------------------------------------------------------------
; Acceptances: the view extended by the articles accepted since its key

; One article A over the restricted articles, trie and buckets: A's cut is
; consed on, one trie path copy and its bucket entries put, when TEXT reads
; a group of A; else nothing changes.
(defun fn-gacc-step (text a rarts trie buckets)
  (declare (xargs :guard t))
  (if (consp (fn-gac-filter-groups text (fn-article-groups a)))
      (let ((ra (fn-gac-restrict-article text a)))
        (mv (cons ra rarts)
            (fn-midx-extend ra trie)
            (fn-gidx-put-all (fn-index-article-entries ra) buckets)))
    (mv rarts trie buckets)))

; The articles of NEW before its tail OLD, oldest first (onto ACC); FOUND
; when OLD is a tail of NEW.  A loop: its work is the new articles' count
; (each comparison is EQ first, and a longer tail differs in its first
; article).
(defun fn-gacc-prefix (new old acc)
  (declare (xargs :guard t :measure (acl2-count new)))
  (cond ((equal new old) (mv t acc))
        ((atom new) (mv nil acc))
        (t (fn-gacc-prefix (cdr new) old (cons (car new) acc)))))

; The steps of AS, oldest first.  A loop.
(defun fn-gacc-grow (text as rarts trie buckets)
  (declare (xargs :guard t))
  (if (consp as)
      (mv-let (r tr bu) (fn-gacc-step text (car as) rarts trie buckets)
        (fn-gacc-grow text (cdr as) r tr bu))
    (mv rarts trie buckets)))

; The view of TEXT over ARCHIVE from VIEW, the view of TEXT over an archive
; whose articles are the tail OLD-ARTS of ARCHIVE's (same control cut): the
; groups and their next numbers are cut again (configuration-sized); the
; articles, trie and buckets grow by the articles before the tail.
(defun fn-gacc-extend-view (text archive prefix view)
  (declare (xargs :guard t))
  (let* ((rs (fn-ag-car view))
         (rindex (fn-ag-cdr view)))
    (mv-let (rarts trie buckets)
      (fn-gacc-grow text prefix (fn-state-articles rs) (fn-gidx-pin-trie rindex)
                    (fn-gidx-pin-buckets rindex))
      (cons (fn-make-state (fn-gac-filter-groups text (fn-state-groups archive))
                           (fn-gac-filter-pairs text (fn-state-nexts archive))
                           rarts
                           (fn-state-next-txid archive)
                           nil nil)
            (fn-gidx-pin-with-control trie buckets (fn-gidx-pin-control rindex))))))

; The two controls cut to the same restricted control.
(defun fn-gacc-same-cut-p (c1 c2)
  (declare (xargs :guard t))
  (and (equal (fn-ctl-pin-withdrawn c1) (fn-ctl-pin-withdrawn c2))
       (equal (fn-ctl-pin-ws c1) (fn-ctl-pin-ws c2))))

; The entry for TEXT at ARCHIVE and CONTROL, from OLD (the cache's entry for
; TEXT, or nil): OLD itself when keyed to them; OLD grown by the articles
; accepted since, when OLD's articles are a tail of ARCHIVE's under the same
; control cut; else built (a restart, a withdrawal, a new rule).
(defun fn-gacc-refresh (text archive control old)
  (declare (xargs :guard t))
  (if (and (consp old) (equal (fn-gacc-text old) text))
      (if (and (equal (fn-gacc-archive old) archive)
               (equal (fn-gacc-control old) control))
          old
        (mv-let (found prefix)
          (if (fn-gacc-same-cut-p control (fn-gacc-control old))
              (fn-gacc-prefix (fn-state-articles archive)
                              (fn-state-articles (fn-gacc-archive old)) nil)
            (mv nil nil))
          (if found
              (fn-gacc-entry text archive control
                             (fn-gacc-extend-view text archive prefix
                                                  (fn-gacc-entry-view old)))
            (fn-gacc-entry text archive control
                           (fn-gac-view-entry text archive control)))))
    (fn-gacc-entry text archive control (fn-gac-view-entry text archive control))))

; The cache with TEXT's entry replaced by (or, absent one, extended with) E.
; Executes by a loop (one frame per step would be one per rule, operator
; data: D27); the :logic is the recursion.
(def-loop fn-gacc-put (text e cache)
  :shape :map
  :over cache
  :stop (and (consp (car cache)) (equal (fn-gacc-text (car cache)) text))
  :stop-value (cons e (cdr cache))
  :body (car cache)
  :tail (list e))

; Prepare the entry a restricted connection's commands will read.
(defun fn-gacc-prepare (text archive control cache)
  (declare (xargs :guard t))
  (fn-gacc-put text (fn-gacc-refresh text archive control (fn-gacc-find text cache))
               cache))
;; -----------------------------------------------------------------------------
;; The refresh is the view of its key

(defthm fn-gacc-restrict-articles-of-consp
  (implies (consp arts)
           (equal (fn-gac-restrict-articles text arts)
                  (if (consp (fn-gac-filter-groups text (fn-article-groups (car arts))))
                      (cons (fn-gac-restrict-article text (car arts))
                            (fn-gac-restrict-articles text (cdr arts)))
                    (fn-gac-restrict-articles text (cdr arts)))))
  :hints (("Goal" :in-theory (enable fn-gac-restrict-articles))))

;; The loops against the builds: one step conses the cut and extends the
;; trie and buckets exactly as the builds of the longer list do (fn-midx-build
;; of a cons is the extend; fn-gidx-build-of-cons); the steps over the
;; articles before a tail build the whole list.
(defthm fn-gacc-step-builds
  (equal (fn-gacc-step text a (fn-gac-restrict-articles text ys)
                       (fn-midx-build (fn-gac-restrict-articles text ys))
                       (fn-gidx-build (fn-gac-restrict-articles text ys)))
         (let ((r (fn-gac-restrict-articles text (cons a ys))))
           (mv r (fn-midx-build r) (fn-gidx-build r))))
  :hints (("Goal" :in-theory (e/d (fn-gacc-step fn-midx-build)
                                  (fn-gac-restrict-articles fn-gac-restrict-article
                                   fn-gac-filter-groups fn-midx-extend fn-gidx-build
                                   fn-gidx-put-all fn-index-article-entries))
           :expand ((fn-midx-build (cons (fn-gac-restrict-article text a)
                                         (fn-gac-restrict-articles text ys)))))))

(local
 (defun fn-gacc-grow-ind (as ys)
   (if (consp as) (fn-gacc-grow-ind (cdr as) (cons (car as) ys)) (list as ys))))

(defthm fn-gacc-grow-builds
  (equal (fn-gacc-grow text as (fn-gac-restrict-articles text ys)
                       (fn-midx-build (fn-gac-restrict-articles text ys))
                       (fn-gidx-build (fn-gac-restrict-articles text ys)))
         (let ((r (fn-gac-restrict-articles text (revappend as ys))))
           (mv r (fn-midx-build r) (fn-gidx-build r))))
  :hints (("Goal" :induct (fn-gacc-grow-ind as ys)
           :in-theory (e/d (fn-gacc-grow)
                           (fn-gacc-step fn-gac-restrict-articles fn-midx-build fn-gidx-build)))))

(defthm fn-gacc-prefix-revappend
  (implies (mv-nth 0 (fn-gacc-prefix new old acc))
           (equal (revappend (mv-nth 1 (fn-gacc-prefix new old acc)) old)
                  (revappend acc new))))

;; The grown view IS the view of the new key: the articles accepted since the
;; entry's key (a tail of the new articles) are cut, path-copied and put, and
;; the restricted control reused (the same withdrawn list and records).
(defthm fn-gacc-extend-view-is-the-view-entry
  (implies (and (mv-nth 0 (fn-gacc-prefix (fn-state-articles archive) (fn-state-articles old) nil))
                (fn-gacc-same-cut-p control octl))
           (equal (fn-gacc-extend-view
                   text archive
                   (mv-nth 1 (fn-gacc-prefix (fn-state-articles archive) (fn-state-articles old) nil))
                   (fn-gac-view-entry text old octl))
                  (fn-gac-view-entry text archive control)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-gacc-extend-view fn-gac-view-entry fn-gac-restrict-index
                                   fn-gac-restrict-state fn-gacc-same-cut-p)
                                  (fn-gac-restrict-articles fn-gac-restrict-article
                                   fn-gac-filter-groups fn-gac-filter-pairs fn-midx-build
                                   fn-gidx-build fn-gacc-grow fn-gacc-prefix fn-gacc-prefix-revappend))
           :use ((:instance fn-gacc-prefix-revappend (new (fn-state-articles archive))
                            (old (fn-state-articles old)) (acc nil))
                 (:instance fn-gacc-grow-builds
                            (as (mv-nth 1 (fn-gacc-prefix (fn-state-articles archive)
                                                          (fn-state-articles old) nil)))
                            (ys (fn-state-articles old)))))))

(defthm fn-gacc-refresh-fields
  (and (equal (fn-gacc-text (fn-gacc-refresh text archive control old)) text)
       (equal (fn-gacc-archive (fn-gacc-refresh text archive control old)) archive)
       (equal (fn-gacc-control (fn-gacc-refresh text archive control old)) control)
       (consp (fn-gacc-refresh text archive control old)))
  :hints (("Goal" :in-theory (disable fn-gacc-extend-view fn-gac-view-entry fn-gacc-prefix))))

(defthm fn-gacc-refresh-okp
  (implies (or (null old) (fn-gacc-entry-okp old))
           (fn-gacc-entry-okp (fn-gacc-refresh text archive control old)))
  :hints (("Goal" :in-theory (e/d (fn-gacc-entry-okp)
                                  (fn-gacc-extend-view fn-gac-view-entry fn-gacc-prefix
                                   fn-gacc-same-cut-p))
           :use ((:instance fn-gacc-extend-view-is-the-view-entry
                            (old (fn-gacc-archive old)) (octl (fn-gacc-control old)))))))

(defthm fn-gacc-refresh-view
  (implies (or (null old) (fn-gacc-entry-okp old))
           (equal (fn-gacc-entry-view (fn-gacc-refresh text archive control old))
                  (fn-gac-view-entry text archive control)))
  :hints (("Goal" :in-theory (e/d (fn-gacc-entry-okp)
                                  (fn-gacc-refresh fn-gac-view-entry fn-gacc-text fn-gacc-archive
                                   fn-gacc-control fn-gacc-entry-view fn-gacc-refresh-okp))
           :use ((:instance fn-gacc-refresh-okp)))))

(defthm fn-gacc-okp-of-put
  (implies (and (fn-gacc-okp cache) (fn-gacc-entry-okp e))
           (fn-gacc-okp (fn-gacc-put text e cache)))
  :hints (("Goal" :in-theory (disable fn-gacc-entry-okp))))

(defthm fn-gacc-find-of-put
  (implies (and (consp e) (equal (fn-gacc-text e) text))
           (equal (fn-gacc-find text (fn-gacc-put text e cache)) e)))

;; KEYSTONE.  Preparing keeps the invariant: every cache the host holds
;; (nil at start, fn-gacc-okp-of-nil; then prepared) satisfies it.
(defthm fn-gacc-prepare-keeps-okp
  (implies (fn-gacc-okp cache)
           (fn-gacc-okp (fn-gacc-prepare text archive control cache)))
  :hints (("Goal" :in-theory (disable fn-gacc-refresh fn-gacc-put fn-gacc-entry-okp fn-gacc-okp
                                      fn-gacc-find)
           :use ((:instance fn-gacc-refresh-okp (old (fn-gacc-find text cache)))
                 (:instance fn-gacc-find-okp)))))

;; KEYSTONE.  The prepared key is answered from the cache: a restricted
;; command at the pin the host prepared builds nothing.
(defthm fn-gacc-view-of-prepare
  (implies (fn-gacc-okp cache)
           (equal (fn-gacc-view text archive control (fn-gacc-prepare text archive control cache))
                  (fn-gac-view-entry text archive control)))
  :hints (("Goal" :in-theory (e/d (fn-gacc-view fn-gacc-prepare)
                                  (fn-gacc-refresh fn-gacc-put fn-gacc-okp fn-gacc-entry-okp
                                   fn-gac-view-entry fn-gacc-text fn-gacc-archive fn-gacc-control
                                   fn-gacc-entry-view fn-gacc-find))
           :use ((:instance fn-gacc-find-okp)))))

(in-theory (disable fn-gacc-entry fn-gacc-text fn-gacc-archive fn-gacc-control
                    fn-gacc-entry-view fn-gacc-okp fn-gacc-find fn-gacc-view
                    fn-gacc-extend-view fn-gacc-refresh fn-gacc-put fn-gacc-put-loop fn-gacc-prepare
                    fn-gacc-step fn-gacc-prefix fn-gacc-grow))
