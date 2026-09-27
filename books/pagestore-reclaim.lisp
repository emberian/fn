; fn: reclamation for the page store (lane arena-store, 2026-09-27).
;
; Over the model of books/pagestore.lisp and its keystones:
;   pgs-keeps-after-commit   a commit keeps nothing new but what it just
;                            allocated: every address a valid record of any
;                            root keeps afterwards was kept before, or is
;                            one of the commit's fresh addresses.
;   pgs-alloc-inv-after-commit
;                            the allocator invariant (the free list avoids
;                            every kept address; everything kept is below the
;                            high-water mark) survives the commit, with the
;                            allocator state the plan returns.
;   pgs-reclaim-never-frees-live
;                            reclamation adds to the free list only addresses
;                            no valid record of any root keeps.  A cycle
;                            snapshots the free list and high-water mark
;                            (FREE0, HWM0) and marks MARKS; commits run
;                            meanwhile (`pgs-cycle-inv-after-commit'); the
;                            sweep frees the addresses below HWM0 in neither
;                            MARKS nor FREE0.  The work is bounded per step:
;                            the sweep is a cursor over [0, HWM0)
;                            (`pgs-sweep-split'), the marks a union over the
;                            records' tables.
(in-package "ACL2")
(include-book "pagestore-keystones")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Subsets.

(defun pgs-subset (xs ys)
  (if (atom xs) t (and (member-equal (car xs) ys) (pgs-subset (cdr xs) ys))))

(defthm pgs-subset-member
  (implies (and (pgs-subset xs ys) (member-equal a xs)) (member-equal a ys)))

(defthm pgs-subset-append-left
  (equal (pgs-subset (append a b) ys) (and (pgs-subset a ys) (pgs-subset b ys))))

(defthm pgs-subset-append-right-1
  (implies (pgs-subset xs a) (pgs-subset xs (append a b))))

(defthm pgs-subset-append-right-2
  (implies (pgs-subset xs b) (pgs-subset xs (append a b))))

(defthm pgs-subset-cons-right
  (implies (pgs-subset xs ys) (pgs-subset xs (cons y ys))))

(defthm pgs-subset-refl
  (pgs-subset xs xs)
  :hints (("Goal" :induct (len xs))))

(defthm pgs-subset-trans
  (implies (and (pgs-subset xs ys) (pgs-subset ys zs)) (pgs-subset xs zs)))

(defthm pgs-avoids-of-subset
  ; What avoids a set avoids its subsets.
  (implies (and (pgs-subset xs ys) (pgs-avoids ys w)) (pgs-avoids xs w)))

(defthm pgs-all-below-of-subset
  (implies (and (pgs-subset xs ys) (pgs-all-below ys b)) (pgs-all-below xs b))
  :hints (("Goal" :induct (len xs))
          ("Subgoal *1/2" :use ((:instance pgs-all-below-member (s ys) (x (car xs)))))))

; -----------------------------------------------------------------------------
; The addresses a table names after the planner: the old ones and the fresh.

(defthm pgs-physes-of-update-nth
  (implies (< (nfix i) (len p))
           (pgs-subset (pgs-ptab-physes (update-nth i e p)) (cons (first e) (pgs-ptab-physes p))))
  :hints (("Goal" :induct (update-nth i e p) :in-theory (enable update-nth))))

(defthm pgs-physes-of-append
  (equal (pgs-ptab-physes (append a b)) (append (pgs-ptab-physes a) (pgs-ptab-physes b))))

(defthm pgs-physes-of-update-entry
  (pgs-subset (pgs-ptab-physes (pgs-update-entry i e p)) (cons (first e) (pgs-ptab-physes p)))
  :hints (("Goal" :in-theory (enable pgs-update-entry)
                  :cases ((< (nfix i) (len p))))))

(defthm pgs-subset-cdr
  (pgs-subset (cdr xs) xs)
  :hints (("Goal" :cases ((consp xs)))))

(defthm pgs-subset-append-mono
  (implies (pgs-subset a b) (pgs-subset (append a c) (append b c))))

(defthm pgs-subset-shift
  (implies (consp f)
           (pgs-subset (append (cons (car f) p) (cdr f)) (append p f)))
  :hints (("Goal" :use ((:instance pgs-subset-trans (xs (cdr f)) (ys f) (zs (append p f)))))))

(defthm pgs-physes-of-plan-ptab
  (implies (and (nat-listp fresh) (<= (len lpages) (len fresh)))
           (pgs-subset (pgs-ptab-physes (pgs-plan-ptab p lpages fresh digests txid))
                       (append (pgs-ptab-physes p) fresh)))
  :hints (("Goal" :induct (pgs-plan-ptab p lpages fresh digests txid)
                  :in-theory (disable pgs-update-entry pgs-subset-trans))
          ("Subgoal *1/2" :use ((:instance pgs-physes-of-update-entry
                                           (i (car lpages)) (p p)
                                           (e (list (nfix (car fresh)) (nfix txid) (nfix (car digests)))))
                                (:instance pgs-subset-append-mono
                                           (a (pgs-ptab-physes (pgs-update-entry (car lpages)
                                                                                 (list (nfix (car fresh)) (nfix txid) (nfix (car digests)))
                                                                                 p)))
                                           (b (cons (car fresh) (pgs-ptab-physes p)))
                                           (c (cdr fresh)))
                                (:instance pgs-subset-shift (f fresh) (p (pgs-ptab-physes p)))
                                (:instance pgs-subset-trans
                                           (xs (pgs-ptab-physes (pgs-plan-ptab (pgs-update-entry (car lpages)
                                                                                                 (list (nfix (car fresh)) (nfix txid) (nfix (car digests)))
                                                                                                 p)
                                                                               (cdr lpages) (cdr fresh) (cdr digests) txid)))
                                           (ys (append (pgs-ptab-physes (pgs-update-entry (car lpages)
                                                                                          (list (nfix (car fresh)) (nfix txid) (nfix (car digests)))
                                                                                          p))
                                                       (cdr fresh)))
                                           (zs (append (cons (car fresh) (pgs-ptab-physes p)) (cdr fresh))))
                                (:instance pgs-subset-trans
                                           (xs (pgs-ptab-physes (pgs-plan-ptab (pgs-update-entry (car lpages)
                                                                                                 (list (nfix (car fresh)) (nfix txid) (nfix (car digests)))
                                                                                                 p)
                                                                               (cdr lpages) (cdr fresh) (cdr digests) txid)))
                                           (ys (append (cons (car fresh) (pgs-ptab-physes p)) (cdr fresh)))
                                           (zs (append (pgs-ptab-physes p) fresh)))))))

; -----------------------------------------------------------------------------
; A record's kept set reads only what it keeps.

(defthm pgs-rec-keeps-in-of-apply-pages
  (implies (pgs-avoids (pgs-rec-keeps-in rec pages) (pgs-write-addrs writes))
           (equal (pgs-rec-keeps-in rec (pgs-apply-pages writes keep pages))
                  (pgs-rec-keeps-in rec pages)))
  :hints (("Goal" :in-theory (e/d (pgs-rec-keeps-in) (pgs-apply-pages pgs-contents pgs-ptab-p
                                                     pgs-rec-dir-addr pgs-rec-keeps-avoids-addr
                                                     pgs-rec-keeps-avoids-dir))
                  :cases ((pgs-ptab-p (pgs-lookup (pgs-rec-dir-addr rec) pages)))
                  :use ((:instance pgs-rec-keeps-avoids-addr
                                   (dir (pgs-lookup (pgs-rec-dir-addr rec) pages))
                                   (tables (if (pgs-ptab-p (pgs-lookup (pgs-rec-dir-addr rec) pages))
                                               (pgs-contents (pgs-lookup (pgs-rec-dir-addr rec) pages) pages)
                                             nil))
                                   (w (pgs-write-addrs writes)))
                        (:instance pgs-rec-keeps-avoids-dir
                                   (dir (pgs-lookup (pgs-rec-dir-addr rec) pages))
                                   (tables (pgs-contents (pgs-lookup (pgs-rec-dir-addr rec) pages) pages))
                                   (w (pgs-write-addrs writes)))))))

(defthm pgs-slots-keeps-of-apply-pages
  (implies (pgs-avoids (pgs-slots-keeps slots pages) (pgs-write-addrs writes))
           (equal (pgs-slots-keeps slots (pgs-apply-pages writes keep pages))
                  (pgs-slots-keeps slots pages)))
  :hints (("Goal" :in-theory (disable pgs-rec-keeps-in pgs-apply-pages pgs-rec-valid))))

(defthm pgs-roots-keeps-of-apply-pages
  (implies (pgs-avoids (pgs-roots-keeps roots pages seen) (pgs-write-addrs writes))
           (equal (pgs-roots-keeps roots (pgs-apply-pages writes keep pages) seen)
                  (pgs-roots-keeps roots pages seen)))
  :hints (("Goal" :induct (pgs-roots-keeps roots pages seen)
                  :in-theory (disable pgs-slots-keeps pgs-apply-pages))))

(defthm pgs-roots-keeps-seen-mono
  (implies (pgs-subset seen1 seen2)
           (pgs-subset (pgs-roots-keeps roots pages seen2) (pgs-roots-keeps roots pages seen1)))
  :hints (("Goal" :induct (list (pgs-roots-keeps roots pages seen1) (pgs-roots-keeps roots pages seen2))
                  :in-theory (disable pgs-slots-keeps))))

(defthm pgs-slots-keeps-in-roots
  (implies (not (member-equal r seen))
           (pgs-subset (pgs-slots-keeps (cdr (hons-assoc-equal r roots)) pages)
                       (pgs-roots-keeps roots pages seen)))
  :hints (("Goal" :induct (pgs-roots-keeps roots pages seen)
                  :in-theory (disable pgs-slots-keeps))))

; -----------------------------------------------------------------------------
; The new record keeps the old record's addresses and the fresh ones.

(defthm pgs-cur-keeps-cover
  ; The current record keeps its directory and its table.
  (implies (and (pgs-ptab-p (pgs-sd cur pages)) (pgs-ptab-p (pgs-sp cur pages)))
           (and (pgs-subset (pgs-ptab-physes (pgs-sd cur pages)) (pgs-rec-keeps-in cur pages))
                (pgs-subset (pgs-ptab-physes (pgs-sp cur pages)) (pgs-rec-keeps-in cur pages))))
  :hints (("Goal" :in-theory (enable pgs-rec-keeps pgs-rec-keeps-in pgs-sd pgs-sp))))

(defthm pgs-dir-run-pages-posp
  (<= 1 (pgs-dir-run-pages n))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable pgs-dir-run-pages))))

(defun pgs-s-new (cur pages dirty fresh tfresh rs txid)
  ; What a commit step allocates: the data pages, the table pages, and the
  ; whole directory run.
  (append fresh tfresh (pgs-run rs (pgs-dir-run-pages (len (pgs-sp2 cur pages dirty fresh txid))))))

(defthm pgs-set-lemma-new-keeps
  (implies (and (pgs-subset d2 (append d tf)) (pgs-subset p2 (append p f))
                (pgs-subset d k) (pgs-subset p k))
           (pgs-subset (append r (append d2 p2)) (append k (append f tf r))))
  :hints (("Goal" :in-theory (disable pgs-subset-trans)
                  :use ((:instance pgs-subset-trans (xs d2) (ys (append d tf)) (zs (append k (append f tf r))))
                        (:instance pgs-subset-trans (xs p2) (ys (append p f)) (zs (append k (append f tf r))))
                        (:instance pgs-subset-trans (xs d) (ys k) (zs (append k (append f tf r))))
                        (:instance pgs-subset-trans (xs p) (ys k) (zs (append k (append f tf r))))))))

(defthm pgs-s-srec-keeps-is
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (equal (pgs-rec-keeps-in (pgs-srec cur pages dirty fresh tfresh rs txid)
                                    (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages))
                  (append (pgs-run rs (pgs-dir-run-pages (len (pgs-sp2 cur pages dirty fresh txid))))
                          (append (pgs-ptab-physes (pgs-sd2 cur pages dirty fresh tfresh txid))
                                  (pgs-ptab-physes (pgs-sp2 cur pages dirty fresh txid))))))
  :hints (("Goal" :in-theory (union-theories '(pgs-rec-keeps pgs-srec pgs-rec-keeps-in-when-dir
                                               pgs-flatten-of-chunk pgs-ptab-p-true-listp)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-s-lands)
                        (:instance pgs-s-new-shapes)
                        (:instance pgs-s-dir2-contents)
                        (:instance pgs-make-rec-fields
                                   (a rs) (n (len (pgs-sp2 cur pages dirty fresh txid)))
                                   (x (pgs-sd2 cur pages dirty fresh tfresh txid))
                                   (d (pgs-digest (pgs-sd2 cur pages dirty fresh tfresh txid))))))
          (and stable-under-simplificationp
               '(:in-theory (enable natp (:type-prescription len))))))

(defthm pgs-std-is
  (equal (pgs-dirty-lpages (pgs-std cur pages dirty fresh txid)) (pgs-step-tl dirty))
  :hints (("Goal" :in-theory (enable pgs-std pgs-step-tdirty pgs-step-tl))))

(defthm pgs-len-of-dirty-lpages
  (equal (len (pgs-dirty-lpages dirty)) (len dirty)))

(defthm pgs-s-new-keeps
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (pgs-subset (pgs-rec-keeps-in (pgs-srec cur pages dirty fresh tfresh rs txid)
                                         (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid)
                                                          nil pages))
                       (append (pgs-rec-keeps-in cur pages) (pgs-s-new cur pages dirty fresh tfresh rs txid))))
  :hints (("Goal" :in-theory (union-theories '(pgs-s-new pgs-s-srec-keeps-is pgs-ptab-p-of-true-list-fix
                                               pgs-len-of-dirty-lpages pgs-nat-listp-of-touched pgs-step-tl
                                               pgs-len-of-std pgs-dirty-lpages-of-table-dirty)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-cur-keeps-cover)
                        (:instance pgs-sd2-is-plan)
                        (:instance pgs-sp2-is-plan)
                        (:instance pgs-len-of-std)
                        (:instance pgs-dirty-lpages-of-table-dirty
                                   (tl (pgs-step-tl dirty)) (cs (pgs-chunk (pgs-sp2 cur pages dirty fresh txid))))
                        (:instance pgs-physes-of-plan-ptab
                                   (p (true-list-fix (pgs-sd cur pages)))
                                   (lpages (pgs-dirty-lpages (pgs-std cur pages dirty fresh txid)))
                                   (fresh tfresh)
                                   (digests (pgs-dirty-digests (pgs-std cur pages dirty fresh txid))))
                        (:instance pgs-physes-of-plan-ptab
                                   (p (pgs-sp cur pages)) (lpages (pgs-dirty-lpages dirty))
                                   (digests (pgs-dirty-digests dirty)))
                        (:instance pgs-set-lemma-new-keeps
                                   (r (pgs-run rs (pgs-dir-run-pages (len (pgs-sp2 cur pages dirty fresh txid)))))
                                   (d2 (pgs-ptab-physes (pgs-sd2 cur pages dirty fresh tfresh txid)))
                                   (p2 (pgs-ptab-physes (pgs-sp2 cur pages dirty fresh txid)))
                                   (d (pgs-ptab-physes (pgs-sd cur pages)))
                                   (p (pgs-ptab-physes (pgs-sp cur pages)))
                                   (f fresh) (tf tfresh)
                                   (k (pgs-rec-keeps-in cur pages)))
                        (:instance pgs-std-is (cur cur))))))

; -----------------------------------------------------------------------------
; A commit keeps nothing new but what it just allocated.

(defthm pgs-slots-keeps-two
  (implies (or (equal slots (cons a b)) (equal slots (cons b a)))
           (pgs-subset (pgs-slots-keeps slots p)
                       (append (pgs-rec-keeps-in a p) (pgs-rec-keeps-in b p))))
  :hints (("Goal" :in-theory (disable pgs-rec-keeps-in pgs-rec-valid))))

(defthm pgs-keeps-in-cur-in-disk
  (implies (equal (car (pgs-open disk r mode)) :ok)
           (pgs-subset (pgs-rec-keeps-in (pgs-c-cur disk r mode) (pgs-pages disk))
                       (pgs-disk-keeps disk)))
  :hints (("Goal" :in-theory (disable pgs-open pgs-rec-keeps-in pgs-rec-valid pgs-slots-keeps-in-roots
                                      pgs-c-open-facts pgs-roots-keeps)
                  :use ((:instance pgs-c-open-facts)
                        (:instance pgs-slots-keeps-in-roots (roots (pgs-roots disk)) (pages (pgs-pages disk))
                                   (seen nil))))))

(defun pgs-c-new (disk r mode dirty alloc)
  (pgs-s-new (pgs-c-cur disk r mode) (pgs-pages disk) dirty (pgs-c-fresh disk r mode dirty alloc)
             (pgs-c-tfresh disk r mode dirty alloc) (pgs-c-rs disk r mode dirty alloc) (pgs-c-txid disk r)))

(defthm pgs-set-lemma-keeps-after
  (implies (and (pgs-subset s (append kc kr)) (pgs-subset kc k) (pgs-subset kr (append kc n))
                (pgs-subset o k))
           (pgs-subset (append s o) (append k n)))
  :hints (("Goal" :in-theory (disable pgs-subset-trans)
                  :use ((:instance pgs-subset-trans (xs kr) (ys (append kc n)) (zs (append k n)))
                        (:instance pgs-subset-trans (xs s) (ys (append kc kr)) (zs (append k n)))
                        (:instance pgs-subset-trans (xs kc) (ys k) (zs (append k n)))
                        (:instance pgs-subset-trans (xs o) (ys k) (zs (append k n)))))))

(defthm pgs-subset-of-nil
  (pgs-subset nil ys))

(defthm pgs-pages-roots-of-cons
  (and (equal (pgs-pages (cons a b)) a) (equal (pgs-roots (cons a b)) b)))

(defthm pgs-root-slots-of-cons-roots
  (equal (pgs-root-slots r (cons a (pgs-roots disk))) (pgs-root-slots r disk)))

(defthm pgs-keeps-after-commit
  (implies (and (equal (car (pgs-open disk r mode)) :ok)
                (pgs-lpages-ok (pgs-dirty-lpages dirty) (len (fourth (pgs-open disk r mode))) 0)
                (pgs-alloc-inv alloc disk))
           (pgs-subset (pgs-disk-keeps (pgs-commit disk r mode dirty alloc))
                       (append (pgs-disk-keeps disk) (pgs-c-new disk r mode dirty alloc))))
  :hints (("Goal" :in-theory (union-theories '(pgs-commit pgs-crash pgs-set-root-slot pgs-disk-keeps
                                               pgs-pages-roots-of-cons pgs-roots-keeps pgs-c-new pgs-c-cur
                                               pgs-c-writes pgs-c-rec pgs-c-lpages-ok-is pgs-plan-commit-unfold
                                               pgs-root-slots-of-cons-roots pgs-subset-of-nil
                                               car-cons cdr-cons member-equal)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-c-open-facts)
                        (:instance pgs-c-step-hyps)
                        (:instance pgs-c-writes-avoid-keeps)
                        (:instance pgs-set-other-slot (k0 (pgs-c-k0 disk r mode))
                                   (v (pgs-c-rec disk r mode dirty alloc))
                                   (slots (pgs-root-slots r disk)))
                        (:instance pgs-slots-keeps-two
                                   (slots (pgs-set-slot (if (equal (pgs-c-k0 disk r mode) 1) 0 1)
                                                        (pgs-c-rec disk r mode dirty alloc)
                                                        (pgs-root-slots r disk)))
                                   (a (pgs-c-cur disk r mode)) (b (pgs-c-rec disk r mode dirty alloc))
                                   (p (pgs-apply-pages (pgs-c-writes disk r mode dirty alloc) nil (pgs-pages disk))))
                        (:instance pgs-keeps-in-cur-in-disk)
                        (:instance pgs-c-avoids-cur (w (pgs-write-addrs (pgs-c-writes disk r mode dirty alloc))))
                        (:instance pgs-rec-keeps-in-of-apply-pages (rec (pgs-c-cur disk r mode))
                                   (pages (pgs-pages disk)) (writes (pgs-c-writes disk r mode dirty alloc))
                                   (keep nil))
                        (:instance pgs-s-new-keeps
                                   (cur (pgs-c-cur disk r mode)) (pages (pgs-pages disk))
                                   (fresh (pgs-c-fresh disk r mode dirty alloc))
                                   (tfresh (pgs-c-tfresh disk r mode dirty alloc))
                                   (rs (pgs-c-rs disk r mode dirty alloc)) (txid (pgs-c-txid disk r)))
                        (:instance pgs-roots-keeps-seen-mono (roots (pgs-roots disk)) (pages (pgs-pages disk))
                                   (seen1 nil) (seen2 (list r)))
                        (:instance pgs-avoids-of-subset
                                   (xs (pgs-roots-keeps (pgs-roots disk) (pgs-pages disk) (list r)))
                                   (ys (pgs-disk-keeps disk))
                                   (w (pgs-write-addrs (pgs-c-writes disk r mode dirty alloc))))
                        (:instance pgs-roots-keeps-of-apply-pages (roots (pgs-roots disk)) (pages (pgs-pages disk))
                                   (seen (list r)) (writes (pgs-c-writes disk r mode dirty alloc)) (keep nil))
                        (:instance pgs-set-lemma-keeps-after
                                   (s (pgs-slots-keeps (pgs-set-slot (if (equal (pgs-c-k0 disk r mode) 1) 0 1)
                                                                     (pgs-c-rec disk r mode dirty alloc)
                                                                     (pgs-root-slots r disk))
                                                       (pgs-apply-pages (pgs-c-writes disk r mode dirty alloc) nil (pgs-pages disk))))
                                   (kc (pgs-rec-keeps-in (pgs-c-cur disk r mode)
                                                         (pgs-apply-pages (pgs-c-writes disk r mode dirty alloc) nil (pgs-pages disk))))
                                   (kr (pgs-rec-keeps-in (pgs-c-rec disk r mode dirty alloc)
                                                         (pgs-apply-pages (pgs-c-writes disk r mode dirty alloc) nil (pgs-pages disk))))
                                   (k (pgs-disk-keeps disk))
                                   (n (pgs-c-new disk r mode dirty alloc))
                                   (o (pgs-roots-keeps (pgs-roots disk)
                                                       (pgs-apply-pages (pgs-c-writes disk r mode dirty alloc) nil (pgs-pages disk))
                                                       (list r))))))))

; -----------------------------------------------------------------------------
; The allocator's state after a commit.

(defun pgs-from (xs free hwm)
  ; Every element of XS is in FREE or at or above HWM.
  (if (atom xs)
      t
    (and (or (member-equal (car xs) free) (and (natp (car xs)) (<= (nfix hwm) (car xs))))
         (pgs-from (cdr xs) free hwm))))

(defthm pgs-from-append
  (equal (pgs-from (append a b) free hwm) (and (pgs-from a free hwm) (pgs-from b free hwm))))

(defthm pgs-from-weaken
  (implies (and (pgs-from xs f1 h1) (pgs-subset f1 f2) (<= (nfix h2) (nfix h1)))
           (pgs-from xs f2 h2)))

(defthm pgs-take-singles-rest-subset
  (pgs-subset (mv-nth 1 (pgs-take-singles n free hwm)) free)
  :hints (("Goal" :induct (pgs-take-singles n free hwm))))

(defthm pgs-take-singles-h-linear
  (<= (nfix hwm) (mv-nth 2 (pgs-take-singles n free hwm)))
  :rule-classes :linear
  :hints (("Goal" :use pgs-take-singles-simple :in-theory (disable pgs-take-singles-simple))))

(defthm pgs-take-singles-below-h
  (implies (and (pgs-all-below free hwm) (natp hwm))
           (pgs-all-below (car (pgs-take-singles n free hwm)) (mv-nth 2 (pgs-take-singles n free hwm))))
  :hints (("Goal" :induct (pgs-take-singles n free hwm))))

(defthm pgs-take-singles-from-list
  (implies (natp hwm) (pgs-from (car (pgs-take-singles n free hwm)) free hwm))
  :hints (("Goal" :induct (pgs-take-singles n free hwm))
          ("Subgoal *1/3" :use ((:instance pgs-from-weaken
                                           (xs (car (pgs-take-singles (+ -1 n) nil (+ 1 hwm))))
                                           (f1 nil) (h1 (+ 1 hwm)) (f2 free) (h2 hwm))))
          ("Subgoal *1/2" :use ((:instance pgs-from-weaken
                                           (xs (car (pgs-take-singles (+ -1 n) (cdr free) hwm)))
                                           (f1 (cdr free)) (h1 hwm) (f2 free) (h2 hwm))))))

(defthm pgs-from-of-all-in
  (implies (pgs-all-in xs free) (pgs-from xs free hwm)))

(defthm pgs-from-of-run-above
  (implies (and (natp a) (<= (nfix hwm) a)) (pgs-from (pgs-run a m) free hwm))
  :hints (("Goal" :induct (pgs-run a m))))

(defthm pgs-subset-of-remove-all
  (pgs-subset (pgs-remove-all xs free) free))

(defthm pgs-from-of-remove-all
  (implies (pgs-from xs (pgs-remove-all r free) hwm) (pgs-from xs free hwm))
  :hints (("Goal" :use ((:instance pgs-from-weaken (f1 (pgs-remove-all r free)) (f2 free) (h1 hwm) (h2 hwm))))))

(defun pgs-alloc-state-ok (al m free hwm)
  (let ((free2 (third al)) (hwm2 (fourth al))
        (new (append (second al) (pgs-run (first al) (max 1 (nfix m))))))
    (and (nat-listp free2) (no-duplicatesp-equal free2) (natp hwm2) (<= (nfix hwm) hwm2)
         (pgs-subset free2 free) (pgs-all-below free2 hwm2) (pgs-all-below new hwm2)
         (pgs-avoids free2 new) (pgs-from new free hwm))))

(defthm pgs-avoids-subset-rotate
  (implies (consp s)
           (equal (pgs-avoids f (append (cdr s) (list (car s)))) (pgs-avoids f s))))

(defthm pgs-all-below-append
  (equal (pgs-all-below (append a b) x) (and (pgs-all-below a x) (pgs-all-below b x))))

(defthm pgs-from-rotate
  (implies (consp s)
           (equal (pgs-from (append (cdr s) (list (car s))) free hwm) (pgs-from s free hwm))))

(defthm pgs-all-below-rotate
  (implies (consp s)
           (equal (pgs-all-below (append (cdr s) (list (car s))) b) (pgs-all-below s b))))

(defthm pgs-alloc-state-single
  (implies (and (nat-listp free) (no-duplicatesp-equal free) (pgs-all-below free hwm) (natp hwm)
                (<= (nfix m) 1) (natp n))
           (let ((ts (pgs-take-singles (+ 1 n) free hwm)))
             (pgs-alloc-state-ok (list (car (car ts)) (cdr (car ts)) (mv-nth 1 ts) (mv-nth 2 ts)) m free hwm)))
  :hints (("Goal" :in-theory (e/d (pgs-run-one)
                                  (pgs-take-singles pgs-run pgs-avoids pgs-from pgs-all-below
                                   no-duplicatesp-equal nat-listp pgs-subset
                                   pgs-all-below-append pgs-from-append pgs-no-dups-append
                                   pgs-avoids-append-right))
                  :use ((:instance pgs-take-singles-simple (n (+ 1 n)))
                        (:instance pgs-consp-iff-len (y (car (pgs-take-singles (+ 1 n) free hwm))))
                        (:instance pgs-take-singles-avoid-rest (n (+ 1 n)))
                        (:instance pgs-take-singles-rest-subset (n (+ 1 n)))
                        (:instance pgs-take-singles-rest-below (n (+ 1 n)))
                        (:instance pgs-take-singles-below-h (n (+ 1 n)))
                        (:instance pgs-take-singles-from-list (n (+ 1 n)))
                        (:instance pgs-avoids-symmetric (xs (car (pgs-take-singles (+ 1 n) free hwm)))
                                   (ys (mv-nth 1 (pgs-take-singles (+ 1 n) free hwm))))))))

(defthm pgs-alloc-state-found
  (implies (and (nat-listp free) (no-duplicatesp-equal free) (pgs-all-below free hwm) (natp hwm)
                (< 1 (nfix m)) (natp a) (pgs-all-in (pgs-run a m) free))
           (let ((ts (pgs-take-singles n (pgs-remove-all (pgs-run a m) free) hwm)))
             (pgs-alloc-state-ok (list a (car ts) (mv-nth 1 ts) (mv-nth 2 ts)) m free hwm)))
  :hints (("Goal" :in-theory (disable pgs-take-singles pgs-run pgs-remove-all pgs-avoids pgs-from
                                      pgs-all-below no-duplicatesp-equal nat-listp pgs-subset pgs-all-in)
                  :use ((:instance pgs-take-singles-avoid-rest (free (pgs-remove-all (pgs-run a m) free)))
                        (:instance pgs-take-singles-simple (free (pgs-remove-all (pgs-run a m) free)))
                        (:instance pgs-take-singles-rest-below (free (pgs-remove-all (pgs-run a m) free)))
                        (:instance pgs-take-singles-below-h (free (pgs-remove-all (pgs-run a m) free)))
                        (:instance pgs-take-singles-rest-subset (free (pgs-remove-all (pgs-run a m) free)))
                        (:instance pgs-avoids-symmetric
                                   (xs (car (pgs-take-singles n (pgs-remove-all (pgs-run a m) free) hwm)))
                                   (ys (mv-nth 1 (pgs-take-singles n (pgs-remove-all (pgs-run a m) free) hwm))))
                        (:instance pgs-avoids-of-subset
                                   (xs (mv-nth 1 (pgs-take-singles n (pgs-remove-all (pgs-run a m) free) hwm)))
                                   (ys (pgs-remove-all (pgs-run a m) free)) (w (pgs-run a m)))
                        (:instance pgs-remove-all-avoids-removed (xs (pgs-run a m)))
                        (:instance pgs-subset-trans
                                   (xs (mv-nth 1 (pgs-take-singles n (pgs-remove-all (pgs-run a m) free) hwm)))
                                   (ys (pgs-remove-all (pgs-run a m) free)) (zs free))
                        (:instance pgs-subset-of-remove-all (xs (pgs-run a m)))
                        (:instance pgs-remove-all-distinct (xs (pgs-run a m)))
                        (:instance pgs-remove-all-nat-listp (xs (pgs-run a m)))
                        (:instance pgs-remove-all-below (xs (pgs-run a m)) (b hwm))
                        (:instance pgs-all-below-of-all-in (xs (pgs-run a m)) (b hwm))
                        (:instance pgs-all-below-weaken (s (pgs-run a m)) (a hwm)
                                   (b (mv-nth 2 (pgs-take-singles n (pgs-remove-all (pgs-run a m) free) hwm))))
                        (:instance pgs-from-of-all-in (xs (pgs-run a m)))
                        (:instance pgs-take-singles-from-list (free (pgs-remove-all (pgs-run a m) free)))
                        (:instance pgs-from-of-remove-all
                                   (xs (car (pgs-take-singles n (pgs-remove-all (pgs-run a m) free) hwm)))
                                   (r (pgs-run a m)))))))

(defthm pgs-alloc-state-extend
  (implies (and (nat-listp free) (no-duplicatesp-equal free) (pgs-all-below free hwm) (natp hwm)
                (< 1 (nfix m)))
           (let ((ts (pgs-take-singles n free (+ hwm (nfix m)))))
             (pgs-alloc-state-ok (list hwm (car ts) (mv-nth 1 ts) (mv-nth 2 ts)) m free hwm)))
  :hints (("Goal" :in-theory (disable pgs-take-singles pgs-run)
                  :use ((:instance pgs-take-singles-avoid-rest (hwm (+ hwm (nfix m))))
                        (:instance pgs-avoids-symmetric
                                   (xs (car (pgs-take-singles n free (+ hwm (nfix m)))))
                                   (ys (mv-nth 1 (pgs-take-singles n free (+ hwm (nfix m))))))
                        (:instance pgs-avoids-of-subset
                                   (xs (mv-nth 1 (pgs-take-singles n free (+ hwm (nfix m)))))
                                   (ys free) (w (pgs-run hwm m)))
                        (:instance pgs-avoids-of-all-below-above (xs free) (a hwm) (b hwm))
                        (:instance pgs-all-below-of-run (a hwm))
                        (:instance pgs-all-below-weaken (s (pgs-run hwm m)) (a (+ hwm (nfix m)))
                                   (b (mv-nth 2 (pgs-take-singles n free (+ hwm (nfix m))))))
                        (:instance pgs-take-singles-from-list (hwm (+ hwm (nfix m))))
                        (:instance pgs-from-weaken (xs (car (pgs-take-singles n free (+ hwm (nfix m)))))
                                   (f1 free) (h1 (+ hwm (nfix m))) (f2 free) (h2 hwm))))))

(defthm pgs-alloc-state-ok-of-alloc
  (implies (pgs-alloc-inv alloc disk)
           (pgs-alloc-state-ok (pgs-alloc n m alloc) m (pgs-alloc-free alloc) (pgs-alloc-hwm alloc)))
  :hints (("Goal" :in-theory (union-theories '(pgs-alloc-inv pgs-alloc-when-single pgs-alloc-when-found
                                               pgs-alloc-when-extend
                                               pgs-alloc-state-found pgs-alloc-state-extend
                                               pgs-find-free-run-found pgs-alloc-hwm-natp
                                               natp (:compound-recognizer natp-compound-recognizer)
                                               (:type-prescription nfix))
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-alloc-state-single (free (pgs-alloc-free alloc)) (n (nfix n))
                                   (hwm (pgs-alloc-hwm alloc))))
                  :cases ((<= (nfix m) 1)
                          (and (< 1 (nfix m))
                               (natp (pgs-find-free-run (pgs-alloc-free alloc) m (pgs-alloc-free alloc))))
                          (and (< 1 (nfix m))
                               (not (natp (pgs-find-free-run (pgs-alloc-free alloc) m (pgs-alloc-free alloc)))))))))

(defthm pgs-len-of-sp2
  (equal (len (pgs-sp2 cur pages dirty fresh txid))
         (pgs-grown-len (pgs-dirty-lpages dirty) (len (pgs-sp cur pages))))
  :hints (("Goal" :use pgs-sp2-is-plan :in-theory (disable pgs-sp2))))

(defthm pgs-max-dir-run-pages
  (equal (max 1 (nfix (pgs-dir-run-pages x))) (pgs-dir-run-pages x))
  :hints (("Goal" :in-theory (disable pgs-dir-run-pages) :use ((:instance pgs-dir-run-pages-posp (n x))))))

(defthm pgs-nfix-of-len-sum
  (equal (nfix (+ (len a) (len b))) (+ (len a) (len b))))

(defthm pgs-len-second-c-al
  (implies (pgs-alloc-inv alloc disk)
           (equal (len (second (pgs-c-al disk r mode dirty alloc)))
                  (+ (len dirty) (len (pgs-touched (pgs-dirty-lpages dirty) nil)))))
  :hints (("Goal" :in-theory (union-theories '(pgs-c-al pgs-nfix-of-len-sum) (theory 'minimal-theory))
                  :use ((:instance pgs-alloc-fresh
                                   (n (+ (len dirty) (len (pgs-touched (pgs-dirty-lpages dirty) nil))))
                                   (m (pgs-c-m-term)))))))

(defthm pgs-nat-listp-second-c-al
  (implies (pgs-alloc-inv alloc disk)
           (nat-listp (second (pgs-c-al disk r mode dirty alloc))))
  :hints (("Goal" :in-theory (union-theories '(pgs-c-al) (theory 'minimal-theory))
                  :use ((:instance pgs-alloc-fresh
                                   (n (+ (len dirty) (len (pgs-touched (pgs-dirty-lpages dirty) nil))))
                                   (m (pgs-c-m-term)))))))

(defthm pgs-s-new-unfold
  (equal (pgs-s-new cur pages dirty fresh tfresh rs txid)
         (append fresh (append tfresh (pgs-run rs (pgs-dir-run-pages
                                                   (pgs-grown-len (pgs-dirty-lpages dirty)
                                                                  (len (pgs-sp cur pages)))))))))

(defthm pgs-c-new-is-alloc-new
  (implies (pgs-alloc-inv alloc disk)
           (equal (pgs-c-new disk r mode dirty alloc)
                  (append (second (pgs-c-al disk r mode dirty alloc))
                          (pgs-run (first (pgs-c-al disk r mode dirty alloc)) (max 1 (nfix (pgs-c-m-term)))))))
  :hints (("Goal" :in-theory (union-theories '(pgs-c-new pgs-c-fresh pgs-c-tfresh pgs-c-rs
                                               pgs-s-new-unfold pgs-max-dir-run-pages)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-append-take-nthcdr-assoc
                                   (s (second (pgs-c-al disk r mode dirty alloc))) (n (len dirty))
                                   (x (pgs-run (first (pgs-c-al disk r mode dirty alloc)) (pgs-c-m-term))))
                        (:instance pgs-len-second-c-al)
                        (:instance pgs-nat-listp-second-c-al)
                        (:instance pgs-nat-listp-true-listp (x (second (pgs-c-al disk r mode dirty alloc))))))
          (and stable-under-simplificationp
               '(:in-theory (union-theories '(pgs-c-new pgs-c-fresh pgs-c-tfresh pgs-c-rs
                                              pgs-s-new-unfold pgs-max-dir-run-pages nfix
                                              (:type-prescription len))
                                            (theory 'minimal-theory))))))

(defthm pgs-set-lemma-below
  (implies (and (pgs-subset k2 (append k n)) (pgs-all-below k h) (<= h h2) (pgs-all-below n h2))
           (pgs-all-below k2 h2))
  :hints (("Goal" :in-theory (disable pgs-all-below-of-subset)
                  :use ((:instance pgs-all-below-of-subset (xs k2) (ys (append k n)) (b h2))))))

(defthm pgs-set-lemma-avoids
  (implies (and (pgs-subset k2 (append k n)) (pgs-subset f2 f) (pgs-avoids f k) (pgs-avoids f2 n))
           (pgs-avoids f2 k2))
  :hints (("Goal" :in-theory (disable pgs-avoids-of-subset)
                  :use ((:instance pgs-avoids-of-subset (xs f2) (ys f) (w k))
                        (:instance pgs-avoids-symmetric (xs f2) (ys (append k n)))
                        (:instance pgs-avoids-symmetric (xs f2) (ys k2))
                        (:instance pgs-avoids-of-subset (xs k2) (ys (append k n)) (w f2))))))

(defthm pgs-alloc-inv-after-commit
  (implies (and (equal (car (pgs-open disk r mode)) :ok)
                (pgs-lpages-ok (pgs-dirty-lpages dirty) (len (fourth (pgs-open disk r mode))) 0)
                (pgs-alloc-inv alloc disk))
           (pgs-alloc-inv (fifth (pgs-plan-commit disk r mode dirty alloc))
                          (pgs-commit disk r mode dirty alloc)))
  :hints (("Goal" :in-theory (union-theories '(pgs-alloc-inv pgs-alloc-free pgs-alloc-hwm pgs-alloc-state-ok
                                               pgs-plan-commit-unfold pgs-c-lpages-ok-is
                                               pgs-true-list-fix-when-true-listp pgs-nat-listp-true-listp
                                               car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-c-open-facts)
                        (:instance pgs-keeps-after-commit)
                        (:instance pgs-c-new-is-alloc-new)
                        (:instance pgs-alloc-state-ok-of-alloc
                                   (n (+ (len dirty) (len (pgs-touched (pgs-dirty-lpages dirty) nil))))
                                   (m (pgs-c-m-term)))
                        (:instance pgs-c-al)
                        (:instance pgs-set-lemma-below
                                   (k2 (pgs-disk-keeps (pgs-commit disk r mode dirty alloc)))
                                   (k (pgs-disk-keeps disk)) (n (pgs-c-new disk r mode dirty alloc))
                                   (h (pgs-alloc-hwm alloc)) (h2 (fourth (pgs-c-al disk r mode dirty alloc))))
                        (:instance pgs-set-lemma-avoids
                                   (k2 (pgs-disk-keeps (pgs-commit disk r mode dirty alloc)))
                                   (k (pgs-disk-keeps disk)) (n (pgs-c-new disk r mode dirty alloc))
                                   (f (pgs-alloc-free alloc)) (f2 (third (pgs-c-al disk r mode dirty alloc))))))
          (and stable-under-simplificationp
               '(:in-theory (union-theories '(pgs-alloc-inv pgs-alloc-free pgs-alloc-hwm pgs-alloc-state-ok
                                              pgs-plan-commit-unfold pgs-c-lpages-ok-is
                                              pgs-true-list-fix-when-true-listp pgs-nat-listp-true-listp
                                              car-cons cdr-cons nfix natp)
                                            (theory 'minimal-theory))))))

; -----------------------------------------------------------------------------
; Reclamation: a mark-and-sweep cycle that commits may interleave with.
;
; The cycle starts by snapshotting the free list FREE0 and the high-water
; mark HWM0; it marks MARKS (every address the records present at the start
; keep: `pgs-disk-keeps' of that disk, built in bounded steps over their
; tables); commits run meanwhile, allocating only from FREE0 or at or above
; HWM0; the sweep frees the addresses below HWM0 in neither MARKS nor FREE0.
; The cycle invariant says every address kept NOW is marked, was free at
; the start, or is at or above HWM0 -- and it survives every commit.

(defun pgs-cycle-inv (disk marks free0 hwm0 alloc)
  (and (pgs-from (pgs-disk-keeps disk) (append marks free0) hwm0)
       (pgs-subset (pgs-alloc-free alloc) free0)
       (<= (nfix hwm0) (pgs-alloc-hwm alloc))))

(defun pgs-sweep (lo hi marks free0)
  ; The addresses in [LO, HI) in neither MARKS nor FREE0, ascending.
  (declare (xargs :measure (nfix (- (nfix hi) (nfix lo)))))
  (if (and (natp lo) (natp hi) (< lo hi))
      (if (or (member-equal lo marks) (member-equal lo free0))
          (pgs-sweep (+ 1 lo) hi marks free0)
        (cons lo (pgs-sweep (+ 1 lo) hi marks free0)))
    nil))

(defun pgs-reclaim (alloc marks free0 hwm0)
  ; The allocator state after the sweep: the free list grows by the swept
  ; addresses; the high-water mark is unchanged.
  (list (append (pgs-alloc-free alloc) (pgs-sweep 0 hwm0 marks free0))
        (pgs-alloc-hwm alloc)))

; Bounded work per step: the sweep over [LO, HI) is the sweep over [LO, MID)
; followed by the sweep over [MID, HI); the host sweeps a quantum at a time.
(defthm pgs-sweep-split
  (implies (and (natp lo) (natp mid) (natp hi) (<= lo mid) (<= mid hi))
           (equal (pgs-sweep lo hi marks free0)
                  (append (pgs-sweep lo mid marks free0) (pgs-sweep mid hi marks free0))))
  :rule-classes nil
  :hints (("Goal" :induct (pgs-sweep lo mid marks free0))))

(defthm pgs-sweep-member-bounds
  (implies (member-equal x (pgs-sweep lo hi marks free0))
           (and (natp x) (<= (nfix lo) x) (< x (nfix hi))
                (not (member-equal x marks)) (not (member-equal x free0))))
  :rule-classes nil
  :hints (("Goal" :induct (pgs-sweep lo hi marks free0))))

(defthm pgs-sweep-not-member-below
  (implies (and (natp lo) (< x lo)) (not (member-equal x (pgs-sweep lo hi marks free0))))
  :hints (("Goal" :use pgs-sweep-member-bounds)))

(defthm pgs-sweep-facts
  (implies (natp lo)
           (and (nat-listp (pgs-sweep lo hi marks free0))
                (no-duplicatesp-equal (pgs-sweep lo hi marks free0))
                (pgs-all-below (pgs-sweep lo hi marks free0) (nfix hi))))
  :hints (("Goal" :induct (pgs-sweep lo hi marks free0))))

(defthm pgs-sweep-member
  (implies (member-equal x (pgs-sweep lo hi marks free0))
           (and (natp x) (< x (nfix hi))
                (not (member-equal x marks)) (not (member-equal x free0))))
  :rule-classes nil
  :hints (("Goal" :use pgs-sweep-member-bounds)))

(defthm pgs-sweep-avoids-kept
  ; A swept address is kept by no valid record when the cycle invariant holds.
  (implies (pgs-from k (append marks free0) hwm0)
           (pgs-avoids (pgs-sweep 0 hwm0 marks free0) k))
  :hints (("Goal" :induct (len k))
          ("Subgoal *1/1" :use ((:instance pgs-sweep-member (lo 0) (hi hwm0) (x (car k)))))))

(defthm pgs-sweep-avoids-free
  (implies (pgs-subset free free0)
           (pgs-avoids (pgs-sweep 0 hwm0 marks free0) free))
  :hints (("Goal" :induct (len free))
          ("Subgoal *1/1" :use ((:instance pgs-sweep-member (lo 0) (hi hwm0) (x (car free)))))))

(defthm pgs-all-in-of-subset
  (implies (pgs-subset xs ys) (pgs-all-in xs ys)))

(defthm pgs-all-in-append-self
  (pgs-all-in xs (append xs ys))
  :hints (("Goal" :use ((:instance pgs-all-in-of-subset (ys (append xs ys)))))))

(defthm pgs-cycle-inv-start
  ; Marking every address the records present at the start keep establishes
  ; the cycle invariant.
  (implies (pgs-alloc-inv alloc disk)
           (pgs-cycle-inv disk (pgs-disk-keeps disk) (pgs-alloc-free alloc) (pgs-alloc-hwm alloc) alloc))
  :hints (("Goal" :in-theory (disable pgs-disk-keeps pgs-alloc-free pgs-alloc-hwm)
                  :use ((:instance pgs-from-of-all-in (xs (pgs-disk-keeps disk))
                                   (free (append (pgs-disk-keeps disk) (pgs-alloc-free alloc)))
                                   (hwm (pgs-alloc-hwm alloc)))))))

(defthm pgs-from-member
  (implies (and (pgs-from xs free hwm) (member-equal a xs))
           (or (member-equal a free) (and (natp a) (<= (nfix hwm) a))))
  :rule-classes nil)

(defthm pgs-set-lemma-cycle-point
  (implies (and (member-equal a (append k n)) (pgs-from k mf hwm0) (pgs-from n free hwm)
                (pgs-subset free f0) (<= (nfix hwm0) (nfix hwm)) (pgs-subset f0 mf))
           (or (member-equal a mf) (and (natp a) (<= (nfix hwm0) a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable pgs-from pgs-subset-trans pgs-subset)
                  :use ((:instance pgs-from-member (xs k) (free mf) (hwm hwm0))
                        (:instance pgs-from-member (xs n))
                        (:instance pgs-subset-member (xs free) (ys f0))
                        (:instance pgs-subset-member (xs f0) (ys mf))))))

(defthm pgs-set-lemma-cycle
  (implies (and (pgs-subset k2 (append k n)) (pgs-from k mf hwm0) (pgs-from n free hwm)
                (pgs-subset free f0) (<= (nfix hwm0) (nfix hwm)) (pgs-subset f0 mf))
           (pgs-from k2 mf hwm0))
  :hints (("Goal" :induct (pgs-avoids-by-member-ind k2) :in-theory (disable pgs-subset-trans))
          ("Subgoal *1/2" :use ((:instance pgs-set-lemma-cycle-point (a (car k2)))))))

(defthm pgs-alloc-free-hwm-of-list
  (and (implies (true-listp f) (equal (pgs-alloc-free (list f h)) f))
       (equal (pgs-alloc-hwm (list f h)) (nfix h))))

(defthm pgs-nfix-when-natp
  (implies (natp x) (equal (nfix x) x)))

(defthm pgs-nfix-of-alloc-hwm
  (equal (nfix (pgs-alloc-hwm alloc)) (pgs-alloc-hwm alloc)))

(defthm pgs-cycle-inv-after-commit
  ; A commit during the cycle keeps the cycle invariant, with the allocator
  ; state the plan returns.
  (implies (and (equal (car (pgs-open disk r mode)) :ok)
                (pgs-lpages-ok (pgs-dirty-lpages dirty) (len (fourth (pgs-open disk r mode))) 0)
                (pgs-alloc-inv alloc disk)
                (pgs-cycle-inv disk marks free0 hwm0 alloc))
           (pgs-cycle-inv (pgs-commit disk r mode dirty alloc) marks free0 hwm0
                          (fifth (pgs-plan-commit disk r mode dirty alloc))))
  :hints (("Goal" :in-theory (union-theories '(pgs-cycle-inv pgs-alloc-free-hwm-of-list pgs-alloc-state-ok
                                               pgs-c-new-is-alloc-new pgs-max-dir-run-pages pgs-c-al pgs-nfix-of-alloc-hwm pgs-nfix-when-natp
                                               pgs-plan-commit-unfold pgs-c-lpages-ok-is
                                               pgs-true-list-fix-when-true-listp pgs-nat-listp-true-listp
                                               car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-c-open-facts)
                        (:instance pgs-keeps-after-commit)
                        (:instance pgs-alloc-state-ok-of-alloc
                                   (n (+ (len dirty) (len (pgs-touched (pgs-dirty-lpages dirty) nil))))
                                   (m (pgs-c-m-term)))
                        (:instance pgs-set-lemma-cycle
                                   (k2 (pgs-disk-keeps (pgs-commit disk r mode dirty alloc)))
                                   (k (pgs-disk-keeps disk)) (n (pgs-c-new disk r mode dirty alloc))
                                   (mf (append marks free0)) (free (pgs-alloc-free alloc))
                                   (hwm (pgs-alloc-hwm alloc)) (f0 free0))
                        (:instance pgs-subset-append-right-2 (xs free0) (a marks) (b free0))
                        (:instance pgs-subset-refl (xs free0))
                        (:instance pgs-subset-trans (xs (third (pgs-c-al disk r mode dirty alloc)))
                                   (ys (pgs-alloc-free alloc)) (zs free0))))))

; The keystone: reclamation never frees an address a valid record of any
; root keeps.  The allocator invariant (in particular, the free list avoids
; every kept address) holds after the sweep.
(defthm pgs-reclaim-never-frees-live
  (implies (and (pgs-alloc-inv alloc disk)
                (pgs-cycle-inv disk marks free0 hwm0 alloc))
           (pgs-alloc-inv (pgs-reclaim alloc marks free0 hwm0) disk))
  :hints (("Goal" :in-theory (e/d (pgs-alloc-inv pgs-cycle-inv pgs-reclaim)
                                  (pgs-sweep pgs-disk-keeps pgs-alloc-free pgs-alloc-hwm))
                  :use ((:instance pgs-sweep-facts (lo 0) (hi hwm0))
                        (:instance pgs-sweep-avoids-kept (k (pgs-disk-keeps disk)))
                        (:instance pgs-sweep-avoids-free (free (pgs-alloc-free alloc)))
                        (:instance pgs-avoids-symmetric (xs (pgs-sweep 0 hwm0 marks free0))
                                   (ys (pgs-alloc-free alloc)))
                        (:instance pgs-all-below-weaken (s (pgs-sweep 0 hwm0 marks free0))
                                   (a (nfix hwm0)) (b (pgs-alloc-hwm alloc)))
                        (:instance pgs-alloc-free (alloc (pgs-reclaim alloc marks free0 hwm0)))
                        (:instance pgs-alloc-hwm (alloc (pgs-reclaim alloc marks free0 hwm0)))))))

(defthm pgs-reclaim-avoids-every-root
  ; Its meaning, root by root: no address the reclaimed free list holds is
  ; one a valid record in either slot of any root R2 keeps.
  (implies (and (pgs-alloc-inv alloc disk)
                (pgs-cycle-inv disk marks free0 hwm0 alloc))
           (pgs-avoids (pgs-alloc-free (pgs-reclaim alloc marks free0 hwm0))
                       (pgs-slots-keeps (pgs-root-slots r2 disk) (pgs-pages disk))))
  :hints (("Goal" :in-theory (disable pgs-alloc-inv pgs-cycle-inv pgs-reclaim pgs-slots-keeps
                                      pgs-roots-keeps-cover pgs-alloc-free pgs-disk-keeps)
                  :use ((:instance pgs-reclaim-never-frees-live)
                        (:instance pgs-alloc-inv (alloc (pgs-reclaim alloc marks free0 hwm0)))
                        (:instance pgs-disk-keeps)
                        (:instance pgs-avoids-symmetric
                                   (xs (pgs-alloc-free (pgs-reclaim alloc marks free0 hwm0)))
                                   (ys (pgs-disk-keeps disk)))
                        (:instance pgs-avoids-symmetric
                                   (xs (pgs-alloc-free (pgs-reclaim alloc marks free0 hwm0)))
                                   (ys (pgs-slots-keeps (pgs-root-slots r2 disk) (pgs-pages disk))))
                        (:instance pgs-roots-keeps-cover (r r2) (roots (pgs-roots disk)) (pages (pgs-pages disk))
                                   (w (pgs-alloc-free (pgs-reclaim alloc marks free0 hwm0))))))))

; A fork keeps nothing new, so both invariants survive it.
(defthm pgs-roots-keeps-of-cons-binding
  (equal (pgs-roots-keeps (cons (cons r2 slots) roots) pages nil)
         (append (pgs-slots-keeps slots pages) (pgs-roots-keeps roots pages (list r2))))
  :hints (("Goal" :expand ((pgs-roots-keeps (cons (cons r2 slots) roots) pages nil)))))

(defthm pgs-slots-keeps-single
  (pgs-subset (pgs-slots-keeps (cons a nil) p) (pgs-rec-keeps-in a p))
  :hints (("Goal" :in-theory (disable pgs-rec-keeps-in))))

(defthm pgs-fork-is
  (equal (pgs-fork disk r r2 mode)
         (if (and (consp (pgs-open disk r mode)) (eq (car (pgs-open disk r mode)) :ok)
                  (true-listp (pgs-open disk r mode)))
             (cons (pgs-pages disk)
                   (cons (cons r2 (cons (pgs-c-cur disk r mode) nil)) (pgs-roots disk)))
           disk))
  :hints (("Goal" :in-theory (e/d (pgs-c-cur pgs-c-k0) (pgs-open)))))

(defthm pgs-subset-append-nil
  (equal (pgs-subset xs (append ys nil)) (pgs-subset xs ys)))

(in-theory (disable pgs-fork-is))

(defthm pgs-keeps-after-fork
  (pgs-subset (pgs-disk-keeps (pgs-fork disk r r2 mode)) (pgs-disk-keeps disk))
  :hints (("Goal" :in-theory (union-theories '(pgs-disk-keeps pgs-pages-roots-of-cons pgs-fork-is
                                               pgs-roots-keeps-of-cons-binding pgs-subset-refl
                                               pgs-subset-append-nil)
                                             (theory 'minimal-theory))
                  :use (
                        (:instance pgs-slots-keeps-single (a (pgs-c-cur disk r mode)) (p (pgs-pages disk)))
                        (:instance pgs-keeps-in-cur-in-disk)
                        (:instance pgs-roots-keeps-seen-mono (roots (pgs-roots disk)) (pages (pgs-pages disk))
                                   (seen1 nil) (seen2 (list r2)))
                        (:instance pgs-subset-of-nil (ys (list r2)))
                        (:instance pgs-set-lemma-keeps-after
                                   (s (pgs-slots-keeps (cons (pgs-c-cur disk r mode) nil) (pgs-pages disk)))
                                   (kc (pgs-rec-keeps-in (pgs-c-cur disk r mode) (pgs-pages disk)))
                                   (kr nil) (k (pgs-disk-keeps disk)) (n nil)
                                   (o (pgs-roots-keeps (pgs-roots disk) (pgs-pages disk) (list r2))))
                        (:instance pgs-subset-append-right-1 (xs (pgs-slots-keeps (cons (pgs-c-cur disk r mode) nil)
                                                                                  (pgs-pages disk)))
                                   (a (pgs-rec-keeps-in (pgs-c-cur disk r mode) (pgs-pages disk))) (b nil))))
          (and stable-under-simplificationp
               '(:in-theory (union-theories '(pgs-disk-keeps pgs-pages-roots-of-cons append pgs-subset
                                              pgs-roots-keeps-of-cons-binding pgs-subset-refl
                                              car-cons cdr-cons)
                                            (theory 'minimal-theory))))))

(defthm pgs-invariants-after-fork
  (and (implies (pgs-alloc-inv alloc disk) (pgs-alloc-inv alloc (pgs-fork disk r r2 mode)))
       (implies (pgs-cycle-inv disk marks free0 hwm0 alloc)
                (pgs-cycle-inv (pgs-fork disk r r2 mode) marks free0 hwm0 alloc)))
  :hints (("Goal" :in-theory (disable pgs-fork pgs-disk-keeps pgs-alloc-free pgs-alloc-hwm)
                  :use ((:instance pgs-keeps-after-fork)
                        (:instance pgs-all-below-of-subset (xs (pgs-disk-keeps (pgs-fork disk r r2 mode)))
                                   (ys (pgs-disk-keeps disk)) (b (pgs-alloc-hwm alloc)))
                        (:instance pgs-avoids-symmetric (xs (pgs-alloc-free alloc)) (ys (pgs-disk-keeps disk)))
                        (:instance pgs-avoids-symmetric (xs (pgs-alloc-free alloc))
                                   (ys (pgs-disk-keeps (pgs-fork disk r r2 mode))))
                        (:instance pgs-avoids-of-subset (xs (pgs-disk-keeps (pgs-fork disk r r2 mode)))
                                   (ys (pgs-disk-keeps disk)) (w (pgs-alloc-free alloc)))
                        (:instance pgs-set-lemma-cycle (k2 (pgs-disk-keeps (pgs-fork disk r r2 mode)))
                                   (k (pgs-disk-keeps disk)) (n nil) (mf (append marks free0))
                                   (free nil) (hwm hwm0) (f0 nil))))))
