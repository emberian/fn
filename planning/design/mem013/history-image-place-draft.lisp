; MEM-013 B' -- UNPROVED DRAFT (lane n-mem13, 2026-10-07).  NOT a book: it lives
; under planning/design/ so no closure, cert or green_check sees it.  When the
; proofs land it becomes books/history-image-place.lisp (includes
; history-pages-import and pagestore-exec) and the old checkpoint build path is
; deleted (docs: planning/design/mem013/README in the lane dump).
;
; The checkpoint build has every record up front.  Pass 1 (fn-his-plan-row)
; sums each row's padded pool length into a host-carried PLAN = (N LENS); the
; layout (starts, NP) is then final; ONE pgs-x-grow-image of exactly NP pages on
; the empty store and the header page; pass 2 (fn-his-place-row) writes each
; row's five cells at their final positions.  No relocation, no resize copy of
; live data, no holes beyond the canonical image's own zero pages.
;
; Reuse: fn-hp-x-blocks / fn-hp-bb-list (the cells' positions), fn-hp-x-blocks-
; ready / fn-hp-x-put-blocks (the guarded writes), fn-hp-hdr2 (the header page),
; pgs-x-grow-image.  fn-hp-x-row is the encode half of fn-hp-x-append-plan
; (history-pages-write-exec.lisp:210), to be factored out of it so the plan
; calls it too.
(in-package "ACL2")

(defun fn-hp-x-row (ev)
  ; (mv VERDICT TL PE): the row's tree length and padded pool entry
  (declare (xargs :verify-guards nil))
  (if (not (fn-sccb-treep ev))
      (mv (list :refused :event) 0 nil)
    (let* ((enc (fn-scc-encode ev)) (tl (len enc)))
      (if (not (unsigned-byte-p 64 tl))
          (mv (list :refused :event) 0 nil)
        (mv nil tl (fn-hp-pad8 enc))))))

; Pass 1.  PLAN = (N LENS): the header answer the host carries, as fn-hp-x-append's.
(defun fn-his-plan-row (ev plan)
  (declare (xargs :verify-guards nil))
  (mv-let (v tl pe) (fn-hp-x-row ev)
    (declare (ignore tl))
    (if v
        (mv v plan)
      (mv nil (list (+ 1 (nfix (car plan)))
                    (fn-hp-x-add (cadr plan) (list 8 8 8 8 (len pe))))))))

(defun fn-his-plan-all (evs plan)
  ; the model of the host's pass-1 loop
  (declare (xargs :verify-guards nil))
  (if (atom evs)
      (mv nil plan)
    (mv-let (v plan2) (fn-his-plan-row (car evs) plan)
      (if v (mv v plan) (fn-his-plan-all (cdr evs) plan2)))))

(defun fn-his-layout (plan)
  ; (mv VERDICT STARTS NP): the final placement, the canonical one
  (declare (xargs :verify-guards nil))
  (let* ((n (car plan)) (lens (cadr plan))
         (starts (adt-starts-l lens 1)) (np (adt-end-l lens 1)))
    (if (and (unsigned-byte-p 64 n) (fn-hp-u64-listp lens) (fn-hp-u64-listp starts)
             (unsigned-byte-p 64 (* 16384 np)))
        (mv nil starts np)
      (mv (list :refused :out-of-range) nil 0))))

; The one grow: exactly 2048*NP words (and NP v/d flags), on an empty store,
; then the header page.  Nothing is copied: the arrays were empty.
(defun fn-his-image-open (plan pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (not (and (equal (pgs-v-length pgs-mem) 0) (equal (pgs-d-length pgs-mem) 0)
                (equal (pgs-w-length pgs-mem) 0)))
      (mv (list :refused :image) nil 0 pgs-mem)
    (mv-let (v starts np) (fn-his-layout plan)
      (if v
          (mv v nil 0 pgs-mem)
        (let* ((pgs-mem (pgs-x-grow-image np pgs-mem))
               (pgs-mem (fn-hp-x-put 0 (fn-hp-hdr2 (car plan) (cadr plan) starts np) pgs-mem)))
          (mv nil starts np pgs-mem))))))

; Pass 2.  (N LENS) is the prefix header answer the host carries, STARTS and NP
; the layout.  Row N's five cells go to their final words.
(defun fn-his-place-row (ev salt n lens starts np pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (mv-let (v tl pe) (fn-hp-x-row ev)
    (if v
        (mv v n lens pgs-mem)
      (let* ((plen (len pe))
             (lens2 (fn-hp-x-add lens (list 8 8 8 8 plen))))
        (if (not (adt-placement-ok starts lens2 np))
            (mv (list :refused :plan-mismatch) n lens pgs-mem)
          (let ((blocks (cdr (fn-hp-x-blocks n lens lens2 starts (fn-hp-mkey ev salt) tl
                                             (fn-hp-pack8 (floor plen 8) pe)))))
            (let ((r (fn-hp-x-blocks-ready blocks pgs-mem)))
              (if (not (eq r :ok))
                  (mv r n lens pgs-mem)
                (let ((pgs-mem (fn-hp-x-put-blocks blocks pgs-mem)))
                  (mv :ok (+ 1 n) lens2 pgs-mem))))))))))

(defun fn-his-place-all (evs salt n lens starts np pgs-mem)
  ; the model of the host's pass-2 loop
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom evs)
      (mv :ok n lens pgs-mem)
    (mv-let (v n2 lens2 pgs-mem) (fn-his-place-row (car evs) salt n lens starts np pgs-mem)
      (if (eq v :ok)
          (fn-his-place-all (cdr evs) salt n2 lens2 starts np pgs-mem)
        (mv v n lens pgs-mem)))))

; Everything after pass 1, given the plan.  A plan the rows do not fill exactly
; is refused by name; nothing is returned as an image.
(defun fn-his-image-build-from-plan (h salt plan pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (mv-let (v starts np pgs-mem) (fn-his-image-open plan pgs-mem)
    (if v
        (mv v 0 '(0 0 0 0 0) nil 0 pgs-mem)
      (mv-let (v n lens pgs-mem) (fn-his-place-all h salt 0 '(0 0 0 0 0) starts np pgs-mem)
        (cond ((not (eq v :ok)) (mv v n lens starts np pgs-mem))
              ((not (equal (list n lens) plan))
               (mv (list :refused :plan-mismatch) n lens starts np pgs-mem))
              (t (mv :ok n lens starts np pgs-mem)))))))

; The function the host's checkpoint build runs (pass 1, then the rest).
; (mv VERDICT N LENS STARTS NP pgs-mem)
(defun fn-his-image-build (h salt pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (mv-let (v plan) (fn-his-plan-all h (list 0 '(0 0 0 0 0)))
    (if v
        (mv v 0 '(0 0 0 0 0) nil 0 pgs-mem)
      (fn-his-image-build-from-plan h salt plan pgs-mem))))

; KEYSTONE (UNPROVED).  On an empty page store, the build of a history the
; image can hold answers :ok and leaves exactly its canonical image: the
; words are fn-hp-iw, the store is exactly NPAGES pages (words 2048*NPAGES,
; v and d NPAGES), every page verified, every page not marked dirty is a zero
; page of the image (so the commit's dirty list names every page the host must
; write), and the answered header is the canonical one.
(defthm fn-his-image-build-is-canonical-image
  (implies (and (fn-hp-okp h salt)
                (equal (pgs-w-length pgs-mem) 0)
                (equal (pgs-v-length pgs-mem) 0)
                (equal (pgs-d-length pgs-mem) 0))
           (let* ((res (fn-his-image-build h salt pgs-mem))
                  (n (mv-nth 1 res)) (lens (mv-nth 2 res)) (starts (mv-nth 3 res))
                  (np (mv-nth 4 res)) (mem2 (mv-nth 5 res)))
             (and (equal (mv-nth 0 res) :ok)
                  (equal (nth *pgs-wi* mem2) (fn-hp-iw h salt))
                  (equal (pgs-w-length mem2) (* 2048 (fn-hp-npages h salt)))
                  (equal (pgs-v-length mem2) (fn-hp-npages h salt))
                  (equal (pgs-d-length mem2) (fn-hp-npages h salt))
                  (equal n (len h))
                  (equal lens (fn-hp-lens h salt))
                  (equal starts (fn-hp-starts h salt))
                  (equal np (fn-hp-npages h salt))
                  (fn-hp-starts-okp starts)
                  (adt-placement-ok starts lens np)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt starts np))
                  (implies (and (natp p) (< p np) (not (equal (nth p (nth *pgs-di* mem2)) 1)))
                           (equal (take 2048 (nthcdr (* 2048 p) (fn-hp-iw h salt)))
                                  (adt-zeros 2048))))))
  :rule-classes nil)

; ----------------------------------------------------------------------------
; TEETH.  Ground evaluations (no proof owed beyond the executable counterparts).

(defconst *m13-fresh* '(nil nil nil nil nil nil))   ; the empty pgs-mem
(defconst *m13-h3* '((:other 1 nil) (:other 2 nil) (:other 3 nil)))

; The keystone's dirty clause, as a ground checker over pages P..NP-1.
(defun m13-dirty-covers (p np d iw)
  (declare (xargs :measure (nfix (- (nfix np) (nfix p)))))
  (if (zp (- (nfix np) (nfix p)))
      t
    (and (or (equal (nth p d) 1)
             (equal (take 2048 (nthcdr (* 2048 (nfix p)) iw)) (adt-zeros 2048)))
         (m13-dirty-covers (+ 1 (nfix p)) np d iw))))

; (a) positive: the whole antecedent and the whole conclusion, on 3 records.
(defthm fn-his-image-build-teeth-positive
  (let* ((h *m13-h3*) (salt 0) (pgs-mem *m13-fresh*)
         (res (fn-his-image-build h salt pgs-mem))
         (n (mv-nth 1 res)) (lens (mv-nth 2 res)) (starts (mv-nth 3 res))
         (np (mv-nth 4 res)) (mem2 (mv-nth 5 res)))
    (and (fn-hp-okp h salt)
         (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
         (equal (pgs-d-length pgs-mem) 0)
         (equal (mv-nth 0 res) :ok)
         (equal (nth *pgs-wi* mem2) (fn-hp-iw h salt))
         (equal (pgs-w-length mem2) (* 2048 (fn-hp-npages h salt)))
         (equal (pgs-v-length mem2) (fn-hp-npages h salt))
         (equal (pgs-d-length mem2) (fn-hp-npages h salt))
         (equal n (len h))
         (equal lens (fn-hp-lens h salt))
         (equal starts (fn-hp-starts h salt))
         (equal np (fn-hp-npages h salt))
         (fn-hp-starts-okp starts)
         (adt-placement-ok starts lens np)
         (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt starts np))
         (m13-dirty-covers 0 np (nth *pgs-di* mem2) (fn-hp-iw h salt))))
  :hints (("Goal" :in-theory (enable adt-placement-ok fn-hp-vhold-is-x fn-hp-vhold-x pgs-vi)))
  :rule-classes nil)

; (b) must-fail: ONE row's length mis-summed (the pass-1 plan counts 8 octets
; too many in the pool): the build is refused by name and what it left is not
; the canonical image.  The antecedent of the keystone holds throughout.
(defthm fn-his-image-build-teeth-missummed-row
  (let* ((h *m13-h3*) (salt 0) (pgs-mem *m13-fresh*)
         (good (mv-nth 1 (fn-his-plan-all h (list 0 '(0 0 0 0 0)))))
         (bad (list (car good) (update-nth 4 (+ 8 (nth 4 (cadr good))) (cadr good))))
         (res (fn-his-image-build-from-plan h salt bad pgs-mem))
         (mem2 (mv-nth 5 res)))
    (and (fn-hp-okp h salt)
         (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
         (equal (pgs-d-length pgs-mem) 0)
         (equal (mv-nth 0 res) '(:refused :plan-mismatch))
         (not (equal (nth *pgs-wi* mem2) (fn-hp-iw h salt)))))
  :rule-classes nil)

; (b') the dirty clause has teeth: with no page marked dirty the same image fails it.
(defthm fn-his-image-build-teeth-dirty-clause
  (and (not (m13-dirty-covers 0 (fn-hp-npages *m13-h3* 0) nil (fn-hp-iw *m13-h3* 0))))
  :rule-classes nil)

; (c) hypothesis removal: a non-empty store (one word) is refused, untouched.
(defthm fn-his-image-build-teeth-nonfresh-store
  (let* ((h *m13-h3*) (salt 0) (pgs-mem (list '(0) nil nil nil nil nil))
         (res (fn-his-image-build h salt pgs-mem)))
    (and (fn-hp-okp h salt)
         (not (equal (pgs-w-length pgs-mem) 0))
         (equal (mv-nth 0 res) '(:refused :image))
         (equal (mv-nth 5 res) pgs-mem)
         (not (equal (nth *pgs-wi* (mv-nth 5 res)) (fn-hp-iw h salt)))))
  :rule-classes nil)
