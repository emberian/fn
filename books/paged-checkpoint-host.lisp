; fn: the decisions the host takes around the paged checkpoint (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM-20261006.md section 3.3).  Model
; level over books/paged-checkpoint.lisp and books/catalog-pages.lisp: the
; host asks these functions and does what they answer.
;
;   fn-pck-publish-plan        which pages a publication writes, or its named
;                              refusal when the root exceeds K pages
;   fn-pck-open-selection      which open runs, over the page store's open
;   fn-pck-compact-floor/-log  the compaction rule: drop only below the S of
;                              both root slots
;   fn-pck-catalog-open        the catalog root is adopted only when its S is
;                              the events root's S, else rebuilt from records
;
;   fn-pck-publish-plan-commits-the-delta     a commit plan is fn-pck-dirty and
;                              applies to the new image, within the dirty bound
;   fn-pck-publish-plan-refuses-only-an-over-k-root
;   fn-pck-open-selection-bounds-the-suffix   a checkpoint open has S <= count
;                              and suffix <= K
;   fn-pck-compact-keeps-both-slots           the compacted log still retains
;                              both slots' S and holds the same records
;   fn-pck-crash-after-compaction             the crash keystone with the log
;                              compacted at the floor
;   fn-pck-catalog-open-is-rebuild            the S-match gate makes adopt
;                              equal rebuild
;
; Scope, named.  (1) The log is the model (START . TAIL) of
; books/paged-checkpoint.lisp.  (2) A root slot that holds no checkpoint has
; S = 0, so the floor is 0 until two checkpoints exist: nothing is dropped
; while the older slot is empty.  (3) fn-pck-compact-keeps-both-slots covers
; compaction against the two slots' S; a media fault in the NEWER slot falls
; back to the older slot, whose S the floor kept (the crash keystone covers a
; torn commit, not a corrupt slot).  (4) fn-pck-catalog-open-is-rebuild is
; generic over the catalog builder (a constrained function): its premise, that
; a catalog root tagged S holds the catalog of the first S records, is
; PCK-ADOPT-TAG / PCK-ADOPT-LOAD.

(in-package "ACL2")
(include-book "paged-checkpoint")
(include-book "catalog-pages")
(include-book "catalog-availability-owner-load")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; 1. Publication

(defun fn-pck-publish-plan (configs prefix delta)
  ; (:commit DIRTY) or (:refused :checkpoint-root-over-k); a refusal writes
  ; nothing and the log is kept whole.
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-pck-root-fitsp configs (append prefix delta))
      (list :commit (fn-pck-dirty configs prefix delta))
    (list :refused :checkpoint-root-over-k)))

(defthm fn-pck-publish-plan-commits-the-delta
  (implies (and (true-listp prefix) (true-listp delta)
                (fn-pck-sccb-listp (append prefix delta))
                (equal (car (fn-pck-publish-plan configs prefix delta)) :commit))
           (and (equal (cadr (fn-pck-publish-plan configs prefix delta))
                       (fn-pck-dirty configs prefix delta))
                (fn-pck-root-fitsp configs (append prefix delta))
                (equal (pgs-apply-dirty (fn-pck-pages configs prefix)
                                        (cadr (fn-pck-publish-plan configs prefix delta)))
                       (fn-pck-pages configs (append prefix delta)))
                (<= (len (cadr (fn-pck-publish-plan configs prefix delta)))
                    (+ *fn-pck-root-pages* (fn-pck-delta-page-bound delta)))))
  :hints (("Goal" :in-theory (disable fn-pck-dirty fn-pck-pages fn-pck-root-fitsp
                                      fn-pck-delta-page-bound)
           :use (fn-pck-dirty-is-the-delta fn-pck-dirty-bound))))

(defthm fn-pck-publish-plan-refuses-only-an-over-k-root
  (implies (equal (car (fn-pck-publish-plan configs prefix delta)) :refused)
           (and (equal (fn-pck-publish-plan configs prefix delta)
                       '(:refused :checkpoint-root-over-k))
                (not (fn-pck-root-fitsp configs (append prefix delta))))))

; -----------------------------------------------------------------------------
; 2. Open

(defun fn-pck-open-selection (filep disk r mode count k)
  ; Which open runs.  PRESENT: the page file exists.  COUNT: the records the
  ; log holds.  The reasons are fn-sco-select's.
  (declare (xargs :guard t :verify-guards nil))
  (if (not filep)
      (fn-sco-select :absent 0 count k)
    (let ((o (pgs-open disk r mode)))
      (if (equal (car o) :ok)
          (fn-sco-select :ok
                         (len (fn-sco-records (fn-pck-capture-of-pages (second (pgs-view o)))))
                         count k)
        (fn-sco-select :corrupt 0 count k)))))

(defthm fn-pck-open-selection-bounds-the-suffix
  (implies (equal (car (fn-pck-open-selection filep disk r mode count k)) :checkpoint)
           (and (not (equal filep nil)) (equal (car (pgs-open disk r mode)) :ok) (natp count)
                (equal (cadr (fn-pck-open-selection filep disk r mode count k))
                       (len (fn-sco-records (fn-pck-capture-of-pages (second (pgs-view (pgs-open disk r mode)))))))
                (<= (cadr (fn-pck-open-selection filep disk r mode count k)) count)
                (<= (- count (cadr (fn-pck-open-selection filep disk r mode count k))) k)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-pck-capture-of-pages pgs-open pgs-view fn-sco-records)
           :expand ((fn-pck-open-selection filep disk r mode count k))
           :do-not-induct t)))

; -----------------------------------------------------------------------------
; 3. Compaction

(defun fn-pck-slot-s (s)
  ; The S of a root slot: 0 for a slot that holds no checkpoint.
  (declare (xargs :guard t))
  (if (natp s) s 0))

(defun fn-pck-compact-floor (sa sb)
  ; Segments are dropped only below the S of BOTH root slots.
  (declare (xargs :guard t))
  (min (fn-pck-slot-s sa) (fn-pck-slot-s sb)))

(defun fn-pck-compact-log (log floor)
  ; LOG = (START . TAIL) after dropping every record below FLOOR; a log that
  ; starts past FLOOR, or holds fewer records than reach FLOOR, is unchanged.
  (declare (xargs :guard t))
  (if (and (consp log) (natp (car log)) (natp floor) (true-listp (cdr log))
           (<= (car log) floor)
           (<= (- floor (car log)) (len (cdr log))))
      (cons floor (nthcdr (- floor (car log)) (cdr log)))
    log))

(defthm fn-pck-compact-keeps-both-slots
  (implies (and (true-listp all) (consp log) (natp (car log)) (true-listp (cdr log))
                (equal (nthcdr (car log) all) (cdr log))
                (<= (car log) (fn-pck-compact-floor sa sb))
                (<= (fn-pck-compact-floor sa sb) (len all)))
           (let ((log2 (fn-pck-compact-log log (fn-pck-compact-floor sa sb))))
             (and (equal (car log2) (fn-pck-compact-floor sa sb))
                  (equal (nthcdr (car log2) all) (cdr log2))
                  (implies (natp sa) (fn-pck-log-retains log2 sa))
                  (implies (natp sb) (fn-pck-log-retains log2 sb)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pck-compact-floor fn-pck-slot-s fn-pck-log-retains)
                                  (nthcdr))
           :use ((:instance pck-nthcdr-nthcdr
                            (a (- (min (fn-pck-slot-s sa) (fn-pck-slot-s sb)) (car log)))
                            (b (car log)) (x all))
                 ))))

(local (defthm fn-pck-floor-le-len2
  (<= (fn-pck-compact-floor older (len prefix)) (len (append prefix rest)))
  :hints (("Goal" :in-theory (enable fn-pck-compact-floor fn-pck-slot-s)))))

(defthm fn-pck-crash-after-compaction
  ; The crash keystone with the log compacted at the floor of the two slots:
  ; the older slot (S = OLDER) and the pre-commit slot (S = len PREFIX).
  (let* ((p (pgs-plan-commit disk r mode (fn-pck-dirty configs prefix delta) alloc))
         (floor (fn-pck-compact-floor older (len prefix)))
         (log2 (fn-pck-compact-log log floor)))
    (implies (and (true-listp prefix) (true-listp delta) (true-listp suffix)
                  (fn-pck-recordsp configs (append prefix delta))
                  (fn-pck-recordsp configs prefix)
                  (fn-pck-root-fitsp configs (append prefix delta))
                  (fn-pck-root-fitsp configs prefix)
                  (fn-pck-disk-holds disk r mode configs prefix)
                  (pgs-alloc-inv alloc disk)
                  (pgs-writes-faithful (second p) (pgs-pages disk))
                  (or (equal sv (pgs-slot (third p) (pgs-root-slots r disk)))
                      (equal sv (fourth p))
                      (not (pgs-rec-valid sv)))
                  (consp log) (natp (car log)) (true-listp (cdr log))
                  (equal (nthcdr (car log) (append prefix delta suffix)) (cdr log))
                  (<= (car log) floor))
             (equal (fn-pck-recover (pgs-crash disk r (second p) keep (third p) sv)
                                    r mode log2 configs frontier max-conns)
                    (fn-ock-recover-full configs frontier (append prefix delta suffix) max-conns))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '((:type-prescription len) natp-compound-recognizer
                                        fn-pck-log-retains (:executable-counterpart consp)))
           :use ((:instance pck-true-listp-append (a prefix) (b (append delta suffix)))
                 (:instance pck-true-listp-append (a delta) (b suffix))
                 (:instance fn-pck-compact-keeps-both-slots
                            (all (append prefix delta suffix)) (sa older) (sb (len prefix)))
                 (:instance fn-pck-floor-le-len2 (rest (append delta suffix)))
                 (:instance fn-pck-crash-recovers-from-old-or-new
                            (log (fn-pck-compact-log log (fn-pck-compact-floor older (len prefix)))))))))

; -----------------------------------------------------------------------------
; 4. The catalog root

(local (defthm take-of-len-free-local
  (implies (and (true-listp x) (equal n (len x))) (equal (take n x) x))))

(defun fn-pck-catalog-verdict (cat-s events-s)
  ; :adopt only when the catalog root's S header is the events root's S.
  (declare (xargs :guard t))
  (if (and (natp cat-s) (equal cat-s events-s)) :adopt :rebuild))

(defthm fn-pck-catalog-verdict-gate
  (equal (equal (fn-pck-catalog-verdict cat-s events-s) :adopt)
         (and (natp cat-s) (equal cat-s events-s))))

(local (defthm fn-pck-decode-of-pages
  (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h))
           (equal (fn-pck-held-of-crow-rows (fn-crow-of-pages (fn-pck-cat-pages h))) h))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-pck-adopt-is-the-catalog))))

(defun-nx fn-pck-catalog-open (cat-s cat-pages recs idx)
  ; CAT-PAGES: the catalog root's pages, written at checkpoint S = CAT-S.
  ; Adopted (decoded) only when CAT-S is the events root's S; else the
  ; catalog is the load of the records, as today.
  (declare (xargs :guard t :verify-guards nil))
  (if (eq (fn-pck-catalog-verdict cat-s (len recs)) :adopt)
      (fn-pck-held-of-crow-rows (fn-crow-of-pages cat-pages))
    (fn-sca-load-held-rows-from recs idx nil)))

(defthm fn-pck-catalog-open-is-the-load
  ; PCK-ADOPT-LOAD is the premise: the catalog H the root was written from is
  ; the load of the first CAT-S records.  The gate then makes adoption equal
  ; the rebuild; without the gate (CAT-S < S) it would return the catalog of
  ; the shorter prefix.
  (implies (and (true-listp recs) (natp cat-s) (<= cat-s (len recs))
                (fn-cat-rowsp h) (fn-pck-carriedp h)
                (equal h (fn-sca-load-held-rows-from (take cat-s recs) idx nil)))
           (equal (fn-pck-catalog-open cat-s (fn-pck-cat-pages h) recs idx)
                  (fn-sca-load-held-rows-from recs idx nil)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '((:definition fn-pck-catalog-open) (:definition fn-pck-catalog-verdict)
                                        (:executable-counterpart equal) (:executable-counterpart natp)))
           :use (fn-pck-decode-of-pages (:instance take-of-len-free-local (n cat-s) (x recs))))))
