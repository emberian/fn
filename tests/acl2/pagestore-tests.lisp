; fn: witnesses and teeth for the page store's keystones
; (books/pagestore-keystones.lisp, books/pagestore-reclaim.lisp;
; lanes proto-pagestore and arena-store, 2026-09-27).
;
; The digest seam is attached to a toy structural hash for the reachable
; witnesses, then to a constant (every content collides) for the teeth of
; `pgs-writes-faithful'.  A later defattach replaces an earlier one; every
; disk below is built under the attachment it is judged under.
;
; Store D0: root :main, one commit (txid 1).  Its directory at address 0
; names one table page at 1; the table page names "alpha" at 2 and "beta"
; at 3; address 4 holds a stale page no record keeps.  The allocator state
; is FREE (5 4), HWM 6.  The commit of DIRTY = ((1 . "new")) takes the
; directory run at 5, the data page at 4 (the stale one) and the table page
; at 6, and writes the record to slot 1.
(in-package "ACL2")
(include-book "../../books/pagestore-reclaim")
(include-book "std/testing/assert-bang" :dir :system)

(defun pgs-toy-h (x)
  ; A digest that separates every pair of contents the witnesses compare.
  ; Not a hash.
  (declare (xargs :guard t))
  (acl2-count x))

(defattach pgs-digest pgs-toy-h)

(defun pgs-t-tab () (list (list 2 1 (pgs-digest "alpha")) (list 3 1 (pgs-digest "beta"))))
(defun pgs-t-dir () (list (list 1 1 (pgs-digest (pgs-t-tab)))))
(defun pgs-t-rec () (pgs-make-rec 1 0 2 (pgs-digest (pgs-t-dir))))
(defun pgs-t-pages ()
  (list (cons 0 (pgs-t-dir)) (cons 1 (pgs-t-tab)) (cons 2 "alpha") (cons 3 "beta")
        (cons 4 "stale")))
(defun pgs-t-d0 () (cons (pgs-t-pages) (list (cons :main (cons (pgs-t-rec) nil)))))
(defun pgs-t-alloc () (list (list 5 4) 6))
(defun pgs-t-dirty () (list (cons 1 "new")))
(defun pgs-t-plan (mode) (pgs-plan-commit (pgs-t-d0) :main mode (pgs-t-dirty) (pgs-t-alloc)))
(defun pgs-t-image (mode keep sv)
  (let ((p (pgs-t-plan mode)))
    (pgs-crash (pgs-t-d0) :main (second p) keep (third p) sv)))

; The store opens on txid 1, eagerly and lazily; the allocator invariant
; holds; the plan writes the data page at 4, the table page at 6, the
; directory at 5, the record to slot 1.
(assert-event (equal (pgs-view (pgs-open (pgs-t-d0) :main :eager)) '(1 ("alpha" "beta"))))
(assert-event (equal (pgs-view (pgs-open (pgs-t-d0) :main :lazy)) '(1 ("alpha" "beta"))))
(assert-event (pgs-alloc-inv (pgs-t-alloc) (pgs-t-d0)))
(assert-event (equal (pgs-disk-keeps (pgs-t-d0)) '(0 1 2 3)))
(assert-event (let ((p (pgs-t-plan :eager)))
                (and (equal (car p) :plan)
                     (equal (strip-cars (second p)) '(4 6 5))
                     (equal (third p) 1)
                     (equal (pgs-rec-txid (fourth p)) 2)
                     (equal (fifth p) '(nil 7)))))

; -----------------------------------------------------------------------------
; pgs-open-after-commit: reachable witnesses (antecedent and conclusion),
; eager and lazy, and with growth across the dirty set.
(defun pgs-t-k1-hyps (disk mode dirty alloc)
  (and (equal (car (pgs-open disk :main mode)) :ok)
       (pgs-lpages-ok (pgs-dirty-lpages dirty) (len (fourth (pgs-open disk :main mode))) 0)
       (pgs-alloc-inv alloc disk)))
(defun pgs-t-k1-concl (disk mode dirty alloc)
  (equal (pgs-view (pgs-open (pgs-commit disk :main mode dirty alloc) :main mode))
         (list (pgs-next-txid (pgs-root-slots :main disk))
               (pgs-apply-dirty (fourth (pgs-open disk :main mode)) dirty))))

(assert-event (and (pgs-t-k1-hyps (pgs-t-d0) :eager (pgs-t-dirty) (pgs-t-alloc))
                   (pgs-t-k1-concl (pgs-t-d0) :eager (pgs-t-dirty) (pgs-t-alloc))
                   (equal (pgs-view (pgs-open (pgs-commit (pgs-t-d0) :main :eager (pgs-t-dirty) (pgs-t-alloc))
                                              :main :eager))
                          '(2 ("alpha" "new")))))
(assert-event (and (pgs-t-k1-hyps (pgs-t-d0) :lazy (pgs-t-dirty) (pgs-t-alloc))
                   (pgs-t-k1-concl (pgs-t-d0) :lazy (pgs-t-dirty) (pgs-t-alloc))))
; Growth: a page appended at the end.
(defun pgs-t-grow () (list (cons 1 "new") (cons 2 "gamma")))
(assert-event (and (pgs-t-k1-hyps (pgs-t-d0) :eager (pgs-t-grow) (pgs-t-alloc))
                   (pgs-t-k1-concl (pgs-t-d0) :eager (pgs-t-grow) (pgs-t-alloc))
                   (equal (pgs-view (pgs-open (pgs-commit (pgs-t-d0) :main :eager (pgs-t-grow) (pgs-t-alloc))
                                              :main :eager))
                          '(2 ("alpha" "new" "gamma")))))

; Growth across a table-page boundary: a 341-page store (one full table
; page) gains two pages; the commit writes a second table page and a new
; directory entry.
(defun pgs-t-names (i n) (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n)) (cons i (pgs-t-names (+ 1 i) n)) nil))
(defun pgs-t-bigtab (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n))
      (cons (list (+ 10 i) 1 (pgs-digest i)) (pgs-t-bigtab (+ 1 i) n))
    nil))
(defun pgs-t-bigpages (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n)) (cons (cons (+ 10 i) i) (pgs-t-bigpages (+ 1 i) n)) nil))
(defun pgs-t-bigdisk ()
  (let* ((tab (pgs-t-bigtab 0 341))
         (dir (list (list 1 1 (pgs-digest tab)))))
    (cons (append (list (cons 0 dir) (cons 1 tab)) (pgs-t-bigpages 0 341))
          (list (cons :main (cons (pgs-make-rec 1 0 341 (pgs-digest dir)) nil))))))
(defun pgs-t-bigdirty () (list (cons 5 :five) (cons 341 :a) (cons 342 :b)))
(defun pgs-t-bigalloc () (list nil 400))
(defun pgs-t-touched-of (dirty) (pgs-touched (pgs-dirty-lpages dirty) nil))
(assert-event (and (pgs-t-k1-hyps (pgs-t-bigdisk) :eager (pgs-t-bigdirty) (pgs-t-bigalloc))
                   (pgs-t-k1-concl (pgs-t-bigdisk) :eager (pgs-t-bigdirty) (pgs-t-bigalloc))
                   (equal (len (second (pgs-view (pgs-open (pgs-commit (pgs-t-bigdisk) :main :eager
                                                                        (pgs-t-bigdirty) (pgs-t-bigalloc))
                                                           :main :eager))))
                          343)
                   (equal (len (pgs-t-touched-of (pgs-t-bigdirty))) 2)))

; Teeth for pgs-open-after-commit, one per hypothesis; each affirms the
; retained hypotheses, the failure of the omitted one, and the failure of
; the conclusion.
; (1) Without an open: a root with only a torn slot.
(defun pgs-t-dbad () (cons (pgs-t-pages) (list (cons :main (cons :torn nil)))))
(assert-event
 (and (not (equal (car (pgs-open (pgs-t-dbad) :main :eager)) :ok))
      (pgs-alloc-inv (pgs-t-alloc) (pgs-t-dbad))
      (not (pgs-t-k1-concl (pgs-t-dbad) :eager (pgs-t-dirty) (pgs-t-alloc)))))
; (2) Without the dirty pages in order: a gap (logical page 3 of a
; two-page state) is refused by name and the state does not move.
(defun pgs-t-gap () (list (cons 3 "far")))
(assert-event
 (and (equal (car (pgs-open (pgs-t-d0) :main :eager)) :ok)
      (pgs-alloc-inv (pgs-t-alloc) (pgs-t-d0))
      (not (pgs-lpages-ok (pgs-dirty-lpages (pgs-t-gap)) 2 0))
      (equal (pgs-plan-commit (pgs-t-d0) :main :eager (pgs-t-gap) (pgs-t-alloc))
             '(:refused :dirty-out-of-order))
      (not (pgs-t-k1-concl (pgs-t-d0) :eager (pgs-t-gap) (pgs-t-alloc)))))
; (3) Without the allocator invariant: a free list holding "alpha"'s page 2.
; The commit's directory overwrites it; the eager open refuses both slots
; (both name page 2), the lazy open answers the directory as page 0.
(defun pgs-t-badalloc () (list (list 2) 6))
(assert-event
 (and (equal (car (pgs-open (pgs-t-d0) :main :eager)) :ok)
      (pgs-lpages-ok (pgs-dirty-lpages (pgs-t-dirty)) 2 0)
      (not (pgs-alloc-inv (pgs-t-badalloc) (pgs-t-d0)))
      (not (pgs-t-k1-concl (pgs-t-d0) :eager (pgs-t-dirty) (pgs-t-badalloc)))
      (not (pgs-t-k1-concl (pgs-t-d0) :lazy (pgs-t-dirty) (pgs-t-badalloc)))))

; -----------------------------------------------------------------------------
; pgs-open-after-crash: reachable witnesses, each asserting the antecedent.
(defun pgs-t-k2-hyps (mode sv)
  (let ((p (pgs-t-plan mode)))
    (and (pgs-t-k1-hyps (pgs-t-d0) mode (pgs-t-dirty) (pgs-t-alloc))
         (pgs-writes-faithful (second p) (pgs-pages (pgs-t-d0)))
         (or (equal sv (pgs-slot (third p) (pgs-root-slots :main (pgs-t-d0))))
             (equal sv (fourth p))
             (not (pgs-rec-valid sv))))))

(defun pgs-t-k2-concl (mode keep sv)
  (let ((p (pgs-t-plan mode))
        (v (pgs-view (pgs-open (pgs-t-image mode keep sv) :main mode))))
    (and (member-equal v (list (pgs-view (pgs-open (pgs-commit (pgs-t-d0) :main mode (pgs-t-dirty)
                                                                (pgs-t-alloc))
                                                   :main mode))
                               (pgs-view (pgs-open (pgs-t-d0) :main mode))))
         (implies (not (equal sv (fourth p)))
                  (equal v (pgs-view (pgs-open (pgs-t-d0) :main mode)))))))

(defun pgs-t-new-rec (mode) (fourth (pgs-t-plan mode)))

; Every write reached the disk, record new: the committed state.
(assert-event (and (pgs-t-k2-hyps :eager (pgs-t-new-rec :eager))
                   (pgs-t-k2-concl :eager nil (pgs-t-new-rec :eager))
                   (equal (pgs-view (pgs-open (pgs-t-image :eager nil (pgs-t-new-rec :eager)) :main :eager))
                          '(2 ("alpha" "new")))))
; The table page and directory landed, the data page did not (the stale
; page is there), record new: refused :page-damaged by name; the previous
; commit.  The same in lazy mode (the commit's own pages are checked).
(assert-event
 (let ((o (pgs-open (pgs-t-image :eager '(nil t t) (pgs-t-new-rec :eager)) :main :eager)))
   (and (pgs-t-k2-hyps :eager (pgs-t-new-rec :eager))
        (pgs-t-k2-concl :eager '(nil t t) (pgs-t-new-rec :eager))
        (equal (pgs-view o) '(1 ("alpha" "beta")))
        (equal (fifth o) '((:slot 1 :page-damaged 1 4))))))
(assert-event
 (let ((o (pgs-open (pgs-t-image :lazy '(nil t t) (pgs-t-new-rec :lazy)) :main :lazy)))
   (and (pgs-t-k2-hyps :lazy (pgs-t-new-rec :lazy))
        (pgs-t-k2-concl :lazy '(nil t t) (pgs-t-new-rec :lazy))
        (equal (pgs-view o) '(1 ("alpha" "beta")))
        (equal (fifth o) '((:slot 1 :page-damaged 1 4))))))
; The table page did not land: refused :table-damaged (table page 0 at 6).
(assert-event
 (let ((o (pgs-open (pgs-t-image :eager '(t nil t) (pgs-t-new-rec :eager)) :main :eager)))
   (and (pgs-t-k2-hyps :eager (pgs-t-new-rec :eager))
        (pgs-t-k2-concl :eager '(t nil t) (pgs-t-new-rec :eager))
        (equal (pgs-view o) '(1 ("alpha" "beta")))
        (equal (fifth o) '((:slot 1 :table-damaged 0 6))))))
; The directory did not land: refused :dir-damaged (at 5).
(assert-event
 (let ((o (pgs-open (pgs-t-image :eager '(t t nil) (pgs-t-new-rec :eager)) :main :eager)))
   (and (pgs-t-k2-hyps :eager (pgs-t-new-rec :eager))
        (pgs-t-k2-concl :eager '(t t nil) (pgs-t-new-rec :eager))
        (equal (pgs-view o) '(1 ("alpha" "beta")))
        (equal (fifth o) '((:slot 1 :dir-damaged 5))))))
; A torn record: refused :commit-torn by name, previous commit.
(assert-event
 (let ((o (pgs-open (pgs-t-image :eager nil :torn) :main :eager)))
   (and (pgs-t-k2-hyps :eager :torn)
        (pgs-t-k2-concl :eager nil :torn)
        (equal (pgs-view o) '(1 ("alpha" "beta")))
        (equal (fifth o) '((:slot 1 :commit-torn))))))
; The record never written (slot 1 keeps its old value, empty).
(assert-event (and (pgs-t-k2-hyps :eager nil) (pgs-t-k2-concl :eager '(t t t) nil)))

; Every host cut is a model crash point the keystone admits
; (`pgs-cut-crash-point'; the host names each in host/native/proto-pagestore.lisp):
; for each cut, the image it names opens as allowed.  One data page, one
; table page, then the directory: three writes.
(defun pgs-t-cut-ok (cuts mode)
  (if (atom cuts)
      t
    (and (let* ((cp (pgs-cut-crash-point (car cuts) 1 1 3))
                (sv (case (cdr cp)
                      (:old nil)
                      (:torn :torn)
                      (otherwise (pgs-t-new-rec mode)))))
           (and (pgs-t-k2-hyps mode sv) (pgs-t-k2-concl mode (car cp) sv)))
         (pgs-t-cut-ok (cdr cuts) mode))))
(assert-event (and (pgs-t-cut-ok *pgs-snapshot-cuts* :eager)
                   (pgs-t-cut-ok *pgs-snapshot-cuts* :lazy)))

; Teeth for the record hypothesis: a valid record that is neither the old
; nor the new one (a forged txid 99 naming the old directory) is opened, and
; the conclusion fails; every other hypothesis holds.
(defun pgs-t-forged () (pgs-make-rec 99 0 2 (pgs-digest (pgs-t-dir))))
(assert-event
 (let ((p (pgs-t-plan :eager)))
   (and (pgs-t-k1-hyps (pgs-t-d0) :eager (pgs-t-dirty) (pgs-t-alloc))
        (pgs-writes-faithful (second p) (pgs-pages (pgs-t-d0)))
        (not (or (equal (pgs-t-forged) (pgs-slot (third p) (pgs-root-slots :main (pgs-t-d0))))
                 (equal (pgs-t-forged) (fourth p))
                 (not (pgs-rec-valid (pgs-t-forged)))))
        (not (pgs-t-k2-concl :eager nil (pgs-t-forged))))))

; -----------------------------------------------------------------------------
; Fork isolation: :b forked from :main; commits on either leave the other.
(defun pgs-t-df () (pgs-fork (pgs-t-d0) :main :b :eager))
(assert-event (and (equal (car (pgs-open (pgs-t-d0) :main :eager)) :ok)
                   (equal (pgs-view (pgs-open (pgs-t-df) :b :eager))
                          (pgs-view (pgs-open (pgs-t-d0) :main :eager)))
                   (equal (pgs-open (pgs-t-df) :main :eager) (pgs-open (pgs-t-d0) :main :eager))))
(assert-event
 (let* ((p (pgs-plan-commit (pgs-t-df) :main :eager (pgs-t-dirty) (pgs-t-alloc)))
        (d1 (pgs-crash (pgs-t-df) :main (second p) nil (third p) (fourth p))))
   (and (pgs-alloc-inv (pgs-t-alloc) (pgs-t-df))
        (equal (car p) :plan)
        (equal (pgs-view (pgs-open d1 :main :eager)) '(2 ("alpha" "new")))
        (equal (pgs-open d1 :b :eager) (pgs-open (pgs-t-df) :b :eager)))))
(assert-event
 (let* ((p (pgs-plan-commit (pgs-t-df) :b :eager (list (cons 0 "gamma")) (pgs-t-alloc)))
        (d1 (pgs-crash (pgs-t-df) :b (second p) nil (third p) (fourth p))))
   (and (equal (car p) :plan)
        (equal (pgs-view (pgs-open d1 :b :eager)) '(2 ("gamma" "beta")))
        (equal (pgs-open d1 :main :eager) (pgs-open (pgs-t-df) :main :eager)))))
; Teeth (r2 = r): the committing root itself does change.
(assert-event
 (not (equal (pgs-open (pgs-t-image :eager nil (pgs-t-new-rec :eager)) :main :eager)
             (pgs-open (pgs-t-d0) :main :eager))))
; Teeth (no allocator invariant): a free list holding "beta"'s page 3 lets a
; commit on :main overwrite a page :b keeps; :b's open changes.
(assert-event
 (let* ((bad (list (list 3) 6))
        (p (pgs-plan-commit (pgs-t-df) :main :eager (pgs-t-dirty) bad))
        (d1 (pgs-crash (pgs-t-df) :main (second p) nil (third p) (fourth p))))
   (and (not (equal :b :main))
        (not (pgs-alloc-inv bad (pgs-t-df)))
        (not (equal (pgs-open d1 :b :eager) (pgs-open (pgs-t-df) :b :eager))))))

; Fork teeth.  Without an openable source, a fork onto an existing root
; leaves that root's own state, which is not the source's.
(defun pgs-t-d2 ()
  (cons (pgs-t-pages) (list (cons :main (cons :torn nil)) (cons :b (cons (pgs-t-rec) nil)))))
(assert-event
 (and (not (equal (car (pgs-open (pgs-t-d2) :main :eager)) :ok))
      (not (equal :b :main))
      (not (equal (pgs-view (pgs-open (pgs-fork (pgs-t-d2) :main :b :eager) :b :eager))
                  (pgs-view (pgs-open (pgs-t-d2) :main :eager))))))
; With r2 = r, the source's open moves (its record now sits in slot 0).
(defun pgs-t-d3 () (pgs-commit (pgs-t-d0) :main :eager (pgs-t-dirty) (pgs-t-alloc)))
(assert-event
 (and (equal (car (pgs-open (pgs-t-d3) :main :eager)) :ok)
      (not (equal (pgs-open (pgs-fork (pgs-t-d3) :main :main :eager) :main :eager)
                  (pgs-open (pgs-t-d3) :main :eager)))))

; -----------------------------------------------------------------------------
; pgs-alloc-fresh: allocation answers N singles and a run, distinct and
; fresh, in each of its three branches; its teeth: without the invariant
; the answer lands on a kept address.
(defun pgs-t-fresh-ok (n m alloc disk)
  (let* ((al (pgs-alloc n m alloc))
         (new (append (second al) (pgs-run (first al) (max 1 (nfix m))))))
    (and (natp (first al)) (nat-listp (second al)) (equal (len (second al)) (nfix n))
         (no-duplicatesp-equal new) (pgs-avoids new (pgs-disk-keeps disk)))))
; one-page run (the singles' first), a run found in FREE, a run at HWM
(assert-event (and (pgs-alloc-inv (pgs-t-alloc) (pgs-t-d0)) (pgs-t-fresh-ok 3 1 (pgs-t-alloc) (pgs-t-d0))
                   (equal (pgs-alloc 3 1 (pgs-t-alloc)) '(5 (4 6 7) nil 8))))
(assert-event (let ((a (list (list 9 7 8 5) 10)))
                (and (pgs-alloc-inv a (pgs-t-d0)) (pgs-t-fresh-ok 2 2 a (pgs-t-d0))
                     (equal (first (pgs-alloc 2 2 a)) 7))))
(assert-event (let ((a (list (list 9 5) 10)))
                (and (pgs-alloc-inv a (pgs-t-d0)) (pgs-t-fresh-ok 2 3 a (pgs-t-d0))
                     (equal (first (pgs-alloc 2 3 a)) 10))))
(assert-event (and (not (pgs-alloc-inv (pgs-t-badalloc) (pgs-t-d0)))
                   (not (pgs-t-fresh-ok 2 1 (pgs-t-badalloc) (pgs-t-d0)))))

; -----------------------------------------------------------------------------
; Reclamation.  D1 = D0 after the commit (record 2 in slot 1), D2 = D1
; after a second commit (record 3 overwrites record 1 in slot 0): record 1's
; directory (0), table page (1) and "beta"'s page (3) are then garbage,
; and the reclaimed free list holds exactly them.
(defun pgs-t-d1 () (pgs-commit (pgs-t-d0) :main :eager (pgs-t-dirty) (pgs-t-alloc)))
(defun pgs-t-a1 () (fifth (pgs-plan-commit (pgs-t-d0) :main :eager (pgs-t-dirty) (pgs-t-alloc))))
(defun pgs-t-dirty2 () (list (cons 0 "alpha2")))
(defun pgs-t-d2c () (pgs-commit (pgs-t-d1) :main :eager (pgs-t-dirty2) (pgs-t-a1)))
(defun pgs-t-a2 () (fifth (pgs-plan-commit (pgs-t-d1) :main :eager (pgs-t-dirty2) (pgs-t-a1))))
; the invariants carried across both commits (pgs-alloc-inv-after-commit)
(assert-event (and (pgs-alloc-inv (pgs-t-a1) (pgs-t-d1)) (pgs-alloc-inv (pgs-t-a2) (pgs-t-d2c))
                   (equal (pgs-view (pgs-open (pgs-t-d2c) :main :eager)) '(3 ("alpha2" "new")))))
; pgs-keeps-after-commit, reachable: D2's kept set is D1's plus the second
; commit's new addresses.
(assert-event (pgs-subset (pgs-disk-keeps (pgs-t-d2c))
                          (append (pgs-disk-keeps (pgs-t-d1))
                                  (pgs-c-new (pgs-t-d1) :main :eager (pgs-t-dirty2) (pgs-t-a1)))))
; A cycle started at D1 (marks = D1's kept set, FREE0 and HWM0 from A1), the
; second commit made during it; the cycle invariant holds at D2 and the
; sweep frees record 1's pages that no record keeps any more.
(defun pgs-t-marks () (pgs-disk-keeps (pgs-t-d1)))
(assert-event
 (and (pgs-cycle-inv (pgs-t-d1) (pgs-t-marks) (pgs-alloc-free (pgs-t-a1)) (pgs-alloc-hwm (pgs-t-a1)) (pgs-t-a1))
      (pgs-cycle-inv (pgs-t-d2c) (pgs-t-marks) (pgs-alloc-free (pgs-t-a1)) (pgs-alloc-hwm (pgs-t-a1)) (pgs-t-a2))
      (pgs-alloc-inv (pgs-reclaim (pgs-t-a2) (pgs-t-marks) (pgs-alloc-free (pgs-t-a1)) (pgs-alloc-hwm (pgs-t-a1)))
                     (pgs-t-d2c))))
; A cycle started at D2 frees the garbage: record 1's directory 0, its
; table page 1 and "beta" at 3.  "alpha" at 2 is not freed: record 2, still
; valid in slot 1, keeps it.
(assert-event
 (let ((a (pgs-reclaim (pgs-t-a2) (pgs-disk-keeps (pgs-t-d2c)) (pgs-alloc-free (pgs-t-a2))
                       (pgs-alloc-hwm (pgs-t-a2)))))
   (and (pgs-alloc-inv (pgs-t-a2) (pgs-t-d2c))
        (pgs-alloc-inv a (pgs-t-d2c))
        (equal (pgs-sweep 0 (pgs-alloc-hwm (pgs-t-a2)) (pgs-disk-keeps (pgs-t-d2c)) (pgs-alloc-free (pgs-t-a2)))
               '(0 1 3))
        (not (member-equal 2 (pgs-alloc-free a))))))
; The sweep in two quanta is the sweep (pgs-sweep-split).
(assert-event
 (let ((k (pgs-disk-keeps (pgs-t-d2c))) (f (pgs-alloc-free (pgs-t-a2))) (h (pgs-alloc-hwm (pgs-t-a2))))
   (equal (append (pgs-sweep 0 3 k f) (pgs-sweep 3 h k f)) (pgs-sweep 0 h k f))))
; Teeth for pgs-reclaim-never-frees-live: marks missing a kept address (the
; new directory, 7) -- the cycle invariant fails, the sweep frees a page a
; live record keeps, and the invariant after the sweep fails.  (Corrupted
; marking state.)
(assert-event
 (let* ((marks (remove-equal 7 (pgs-disk-keeps (pgs-t-d2c))))
        (f0 (pgs-alloc-free (pgs-t-a2))) (h0 (pgs-alloc-hwm (pgs-t-a2))))
   (and (pgs-alloc-inv (pgs-t-a2) (pgs-t-d2c))
        (member-equal 7 (pgs-disk-keeps (pgs-t-d2c)))
        (not (pgs-cycle-inv (pgs-t-d2c) marks f0 h0 (pgs-t-a2)))
        (member-equal 7 (pgs-sweep 0 h0 marks f0))
        (not (pgs-alloc-inv (pgs-reclaim (pgs-t-a2) marks f0 h0) (pgs-t-d2c))))))
; Teeth for the allocator hypothesis: with a free list already holding a
; kept address, the reclaimed state still violates the invariant.
(assert-event
 (let ((bad (list (list 2) 8)) (k (pgs-disk-keeps (pgs-t-d0))))
   (and (pgs-cycle-inv (pgs-t-d0) k (list 2) 8 bad)
        (not (pgs-alloc-inv bad (pgs-t-d0)))
        (not (pgs-alloc-inv (pgs-reclaim bad k (list 2) 8) (pgs-t-d0))))))

; -----------------------------------------------------------------------------
; Teeth for `pgs-writes-faithful': under a digest where every content
; collides, the stale page at the fresh address verifies as the new page,
; and the crash opens on a state that is neither the new nor the old one.
; Every other hypothesis holds.
(defun pgs-toy-zero (x) (declare (xargs :guard t) (ignore x)) 0)
(defattach pgs-digest pgs-toy-zero)
(assert-event
 (let* ((p (pgs-t-plan :eager))
        (sv (fourth p)))
   (and (pgs-t-k1-hyps (pgs-t-d0) :eager (pgs-t-dirty) (pgs-t-alloc))
        (not (pgs-writes-faithful (second p) (pgs-pages (pgs-t-d0))))
        (equal sv (fourth p))
        (not (pgs-t-k2-concl :eager '(nil t t) sv))
        (equal (pgs-view (pgs-open (pgs-t-image :eager '(nil t t) sv) :main :eager))
               '(2 ("alpha" "stale"))))))
