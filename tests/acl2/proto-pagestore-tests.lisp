; fn: witnesses and teeth for books/proto/pagestore-keystones.lisp
; (lane proto-pagestore, 2026-09-27).
;
; The digest seam is attached to a toy structural hash for the reachable
; witnesses, then to a constant (every content collides) for the teeth of
; `pgs-writes-faithful'.  A later defattach replaces an earlier one; every
; disk below is built under the attachment it is judged under.
;
; Store D0: root :main, one commit (txid 1) whose table at address 0 names
; "alpha" at 1 and "beta" at 2; address 4 holds a stale page no record
; keeps.  The commit of DIRTY = ((1 . "new")) allocates the table run at 3
; and the dirty page at 4 (the stale one), and writes the record to slot 1.
(in-package "ACL2")
(include-book "../../books/proto/pagestore-keystones")
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

(defun pgs-toy-h (x)
  ; A digest that separates every pair of contents the witnesses compare
  ; ("new" 3 / "stale" 5; an empty address 0 / any table).  Not a hash.
  (declare (xargs :guard t))
  (acl2-count x))

(defattach pgs-digest pgs-toy-h)

(defun pgs-t-ptab () (list (list 1 1 (pgs-digest "alpha")) (list 2 1 (pgs-digest "beta"))))
(defun pgs-t-rec () (pgs-make-rec 1 0 2 (pgs-digest (pgs-t-ptab))))
(defun pgs-t-pages ()
  (list (cons 0 (pgs-t-ptab)) (cons 1 "alpha") (cons 2 "beta") (cons 4 "stale")))
(defun pgs-t-d0 () (cons (pgs-t-pages) (list (cons :main (cons (pgs-t-rec) nil)))))
(defun pgs-t-dirty () (list (cons 1 "new")))
(defun pgs-t-plan (mode) (pgs-plan-commit (pgs-t-d0) :main mode (pgs-t-dirty)))
(defun pgs-t-image (mode keep sv)
  (let ((p (pgs-t-plan mode)))
    (pgs-crash (pgs-t-d0) :main (second p) keep (third p) sv)))

; The store opens on txid 1, eagerly and lazily.
(assert-event (equal (pgs-view (pgs-open (pgs-t-d0) :main :eager)) '(1 ("alpha" "beta"))))
(assert-event (equal (pgs-view (pgs-open (pgs-t-d0) :main :lazy)) '(1 ("alpha" "beta"))))
; The plan: the table run at 3, the page at 4 (the stale address), slot 1.
(assert-event (let ((p (pgs-t-plan :eager)))
                (and (equal (car p) :plan)
                     (equal (strip-cars (second p)) '(4 3))
                     (equal (third p) 1)
                     (equal (pgs-rec-txid (fourth p)) 2))))

; -----------------------------------------------------------------------------
; pgs-open-after-commit: reachable witness (antecedent and conclusion).
(assert-event
 (and (equal (car (pgs-t-plan :eager)) :plan)
      (equal (pgs-view (pgs-open (pgs-commit (pgs-t-d0) :main :eager (pgs-t-dirty)) :main :eager))
             (list (pgs-next-txid (pgs-root-slots :main (pgs-t-d0)))
                   (pgs-apply-dirty (fourth (pgs-open (pgs-t-d0) :main :eager)) (pgs-t-dirty))))
      (equal (pgs-view (pgs-open (pgs-commit (pgs-t-d0) :main :eager (pgs-t-dirty)) :main :eager))
             '(2 ("alpha" "new")))))

; Teeth (the one hypothesis): a store with only a torn slot has no plan;
; the "commit" leaves it unopenable, and the conclusion fails.
(defun pgs-t-dbad () (cons (pgs-t-pages) (list (cons :main (cons :torn nil)))))
(assert-event
 (and (not (equal (car (pgs-plan-commit (pgs-t-dbad) :main :eager (pgs-t-dirty))) :plan))
      (not (equal (pgs-view (pgs-open (pgs-commit (pgs-t-dbad) :main :eager (pgs-t-dirty)) :main :eager))
                  (list (pgs-next-txid (pgs-root-slots :main (pgs-t-dbad)))
                        (pgs-apply-dirty (fourth (pgs-open (pgs-t-dbad) :main :eager))
                                         (pgs-t-dirty)))))))

; -----------------------------------------------------------------------------
; pgs-open-after-crash: reachable witnesses, each asserting the antecedent.
(defun pgs-t-k2-hyps (mode sv)
  (let ((p (pgs-t-plan mode)))
    (and (equal (car p) :plan)
         (pgs-writes-faithful (second p) (pgs-pages (pgs-t-d0)))
         (or (equal sv (pgs-slot (third p) (pgs-root-slots :main (pgs-t-d0))))
             (equal sv (fourth p))
             (not (pgs-rec-valid sv))))))

(defun pgs-t-k2-concl (mode keep sv)
  (let ((p (pgs-t-plan mode))
        (v (pgs-view (pgs-open (pgs-t-image mode keep sv) :main mode))))
    (and (member-equal v (list (pgs-view (pgs-open (pgs-commit (pgs-t-d0) :main mode (pgs-t-dirty))
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
; The table landed, the page did not (the stale page is there), record new:
; refused :page-damaged by name, and the previous commit.
(assert-event
 (let ((o (pgs-open (pgs-t-image :eager '(nil t) (pgs-t-new-rec :eager)) :main :eager)))
   (and (pgs-t-k2-hyps :eager (pgs-t-new-rec :eager))
        (pgs-t-k2-concl :eager '(nil t) (pgs-t-new-rec :eager))
        (equal (pgs-view o) '(1 ("alpha" "beta")))
        (equal (fifth o) '((:slot 1 :page-damaged 1 4))))))
; The same in lazy mode (the commit's own pages are checked at open).
(assert-event
 (let ((o (pgs-open (pgs-t-image :lazy '(nil t) (pgs-t-new-rec :lazy)) :main :lazy)))
   (and (pgs-t-k2-hyps :lazy (pgs-t-new-rec :lazy))
        (pgs-t-k2-concl :lazy '(nil t) (pgs-t-new-rec :lazy))
        (equal (pgs-view o) '(1 ("alpha" "beta")))
        (equal (fifth o) '((:slot 1 :page-damaged 1 4))))))
; The page landed, the table did not: refused :ptab-damaged, previous commit.
(assert-event
 (let ((o (pgs-open (pgs-t-image :eager '(t nil) (pgs-t-new-rec :eager)) :main :eager)))
   (and (pgs-t-k2-hyps :eager (pgs-t-new-rec :eager))
        (pgs-t-k2-concl :eager '(t nil) (pgs-t-new-rec :eager))
        (equal (pgs-view o) '(1 ("alpha" "beta")))
        (equal (fifth o) '((:slot 1 :ptab-damaged 3))))))
; A torn record: refused :commit-torn by name, previous commit.
(assert-event
 (let ((o (pgs-open (pgs-t-image :eager nil :torn) :main :eager)))
   (and (pgs-t-k2-hyps :eager :torn)
        (pgs-t-k2-concl :eager nil :torn)
        (equal (pgs-view o) '(1 ("alpha" "beta")))
        (equal (fifth o) '((:slot 1 :commit-torn))))))
; The record never written (slot 1 keeps its old value, empty).
(assert-event (and (pgs-t-k2-hyps :eager nil) (pgs-t-k2-concl :eager '(t t) nil)))

; Every host cut is a model crash point the keystone admits
; (`pgs-cut-crash-point', the table of host/native/proto-pagestore.lisp's
; cuts): for each cut and occurrence, the image it names opens as allowed.
(defun pgs-t-cut-ok (cuts mode)
  (if (atom cuts)
      t
    (and (let* ((cp (pgs-cut-crash-point (car cuts) 1 2))
                (sv (case (cdr cp)
                      (:old nil)
                      (:torn :torn)
                      (otherwise (pgs-t-new-rec mode)))))
           (and (pgs-t-k2-hyps mode sv) (pgs-t-k2-concl mode (car cp) sv)))
         (pgs-t-cut-ok (cdr cuts) mode))))
(assert-event (and (pgs-t-cut-ok *pgs-snapshot-cuts* :eager)
                   (pgs-t-cut-ok *pgs-snapshot-cuts* :lazy)))

; Teeth for the record hypothesis: a valid record that is neither the old
; nor the new one (a forged txid 99 naming the old table) is opened, and the
; conclusion fails; every other hypothesis holds.
(defun pgs-t-forged () (pgs-make-rec 99 0 2 (pgs-digest (pgs-t-ptab))))
(assert-event
 (let ((p (pgs-t-plan :eager)))
   (and (equal (car p) :plan)
        (pgs-writes-faithful (second p) (pgs-pages (pgs-t-d0)))
        (not (or (equal (pgs-t-forged) (pgs-slot (third p) (pgs-root-slots :main (pgs-t-d0))))
                 (equal (pgs-t-forged) (fourth p))
                 (not (pgs-rec-valid (pgs-t-forged)))))
        (not (pgs-t-k2-concl :eager nil (pgs-t-forged))))))

; -----------------------------------------------------------------------------
; Fork isolation: :b forked from :main; commits on either leave the other.
(defun pgs-t-df () (pgs-fork (pgs-t-d0) :main :b :eager))
(assert-event (equal (pgs-view (pgs-open (pgs-t-df) :b :eager))
                     (pgs-view (pgs-open (pgs-t-d0) :main :eager))))
(assert-event (equal (pgs-open (pgs-t-df) :main :eager) (pgs-open (pgs-t-d0) :main :eager)))
(assert-event
 (let* ((p (pgs-plan-commit (pgs-t-df) :main :eager (pgs-t-dirty)))
        (d1 (pgs-crash (pgs-t-df) :main (second p) nil (third p) (fourth p))))
   (and (equal (car p) :plan)
        (equal (pgs-view (pgs-open d1 :main :eager)) '(2 ("alpha" "new")))
        (equal (pgs-open d1 :b :eager) (pgs-open (pgs-t-df) :b :eager)))))
(assert-event
 (let* ((p (pgs-plan-commit (pgs-t-df) :b :eager (list (cons 0 "gamma"))))
        (d1 (pgs-crash (pgs-t-df) :b (second p) nil (third p) (fourth p))))
   (and (equal (car p) :plan)
        (equal (pgs-view (pgs-open d1 :b :eager)) '(2 ("gamma" "beta")))
        (equal (pgs-open d1 :main :eager) (pgs-open (pgs-t-df) :main :eager)))))
; Teeth (r2 /= r): the committing root itself does change.
(assert-event
 (not (equal (pgs-open (pgs-t-image :eager nil (pgs-t-new-rec :eager)) :main :eager)
             (pgs-open (pgs-t-d0) :main :eager))))

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
(defun pgs-t-d3 () (pgs-commit (pgs-t-d0) :main :eager (pgs-t-dirty)))
(assert-event
 (and (equal (car (pgs-open (pgs-t-d3) :main :eager)) :ok)
      (not (equal (pgs-open (pgs-fork (pgs-t-d3) :main :main :eager) :main :eager)
                  (pgs-open (pgs-t-d3) :main :eager)))))

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
   (and (equal (car p) :plan)
        (not (pgs-writes-faithful (second p) (pgs-pages (pgs-t-d0))))
        (equal sv (fourth p))
        (not (pgs-t-k2-concl :eager '(nil t) sv))
        (equal (pgs-view (pgs-open (pgs-t-image :eager '(nil t) sv) :main :eager))
               '(2 ("alpha" "stale"))))))
