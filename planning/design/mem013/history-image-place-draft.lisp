; MEM-013 B' -- UNPROVED DRAFT, revision 2 (lane n-mem13, 2026-10-07; S audit of 489988572).
; NOT a book: it lives under planning/design/ so no closure, cert or green_check sees it.
; It becomes books/history-image-place.lisp when the proofs land, and the old checkpoint
; build path (history-image-row-step.lisp, fn-his-build-row/-recycle, the relocate cursor
; driver fnn-history-image-row-run) is deleted in the same change.
; Includes (as a book): history-image-build-rows, history-pages-import, pagestore-exec.
;
; THE PICTURE.  The checkpoint build has every record up front.
;   pass 1  fn-his-plan-run     lengths only (fn-scc-program-len; nothing encoded, nothing kept)
;   open    fn-his-image-open   layout, ONE pgs-x-grow-image of exactly 2048*NP words on the empty
;                               store, the header page, EVERY page 0..NP-1 marked dirty (the open
;                               needs a table entry for each page: fn-hib-root-holds, zero pages
;                               included -- the old path marked them via fn-hp-x-mark in relocate)
;   pass 2  fn-his-place-run    the only encode.  Five region cursors, each one open page (<= 2048
;                               words); a full page is flushed into pgs-mem at its final address.
;                               Resident buffer: 5 x 16 KiB.  MEM-013-STREAM later flushes to the file.
;   close   fn-his-image-close  flush the five partial pages; the plan must be exactly filled.
;
; SIZE (pessimistic).  NP = 1 + sum of the region caps, cap(u) < 2u/16384 + 1, so the image is
; < (6 + 2*L/16384) pages for L region octets, i.e. about 2x live plus 6 pages (pessimistic; the
; real image is the canonical one, between 1x and 2x).  Measured at 100k articles: 1,404 B/article
; live, which already includes the relocation holes of today's path.  B' allocates exactly 16384*NP
; octets once: the 217 MB of dead resize copies and the relocation zero-holes are gone.
(in-package "ACL2")

; ---------------------------------------------------------------------------
; A. The length of a row's tree, without encoding it.  (No length function and no directory
; carrying the encoded length exists: store-tree-codec.lisp has only fn-scc-encode/-program.)
(defun fn-scc-program-len (x acc)
  ; ACC + (len (fn-scc-program x)), by the program's own structure
  (declare (xargs :verify-guards nil :measure (acl2-count x)))
  (cond ((fn-scc-octets-valuep x)
         (+ acc 1 (len (fn-scc-nat-octets (len x))) (len x)))
        ((consp x)
         (fn-scc-program-len (cdr x) (+ 1 (fn-scc-program-len (car x) acc))))
        (t (+ acc (len (fn-scc-atom-octets x))))))

; STATEMENT (unproved): the length-only function is the encoder's length.
(defthm fn-scc-program-len-is-encode-len
  (equal (fn-scc-program-len x acc) (+ acc (len (fn-scc-encode x))))
  :rule-classes nil)

(defun fn-hp-x-rowlen (ev)
  ; (mv VERDICT TL PLEN): the tree's length and its padded pool length; no octets
  (declare (xargs :verify-guards nil))
  (if (not (fn-sccb-treep ev))
      (mv (list :refused :event) 0 0)
    (let ((tl (fn-scc-program-len ev 0)))
      (if (not (unsigned-byte-p 64 tl))
          (mv (list :refused :event) 0 0)
        (mv nil tl (+ tl (fn-hp-pad8-count tl)))))))

(defun fn-hp-x-row (ev)
  ; (mv VERDICT TL PE): the one encode (the encode half of fn-hp-x-append-plan, to be
  ; factored out of it, history-pages-write-exec.lisp:210)
  (declare (xargs :verify-guards nil))
  (if (not (fn-sccb-treep ev))
      (mv (list :refused :event) 0 nil)
    (let* ((enc (fn-scc-encode ev)) (tl (len enc)))
      (if (not (unsigned-byte-p 64 tl))
          (mv (list :refused :event) 0 nil)
        (mv nil tl (fn-hp-pad8 enc))))))

; ---------------------------------------------------------------------------
; B. Pass 1.  PLAN = (N LENS), host-carried like fn-hp-x-append's header answer.
(defun fn-his-plan-row (ev plan)
  (declare (xargs :verify-guards nil))
  (mv-let (v tl plen) (fn-hp-x-rowlen ev)
    (declare (ignore tl))
    (if v
        (mv v plan)
      (mv nil (list (+ 1 (nfix (car plan)))
                    (fn-hp-x-add (cadr plan) (list 8 8 8 8 plen)))))))

(defun fn-his-plan-all (evs plan)
  ; the specification of the pass: every row, or the first refusal with the plan before it
  (declare (xargs :verify-guards nil))
  (if (atom evs)
      (mv nil plan)
    (mv-let (v plan2) (fn-his-plan-row (car evs) plan)
      (if v (mv v plan) (fn-his-plan-all (cdr evs) plan2)))))

; The steppable entry the host calls: at most K rows (K <= *fn-his-build-yield-rows*, 256),
; so the work per call is K row-lengths.  (mv VERDICT REST PLAN'): :done (REST nil), :more
; (REST the rows left), or a refusal by name with REST its row.
(defun fn-his-plan-run (k evs plan)
  (declare (xargs :verify-guards nil))
  (cond ((atom evs) (mv :done nil plan))
        ((zp k) (mv :more evs plan))
        (t (mv-let (v plan2) (fn-his-plan-row (car evs) plan)
             (if v (mv v evs plan) (fn-his-plan-run (1- k) (cdr evs) plan2))))))

; The driver: quanta until done (the host yields between quanta).  FUEL bounds the quanta;
; (+ 1 (len evs)) always suffices.
; GEN: this and fn-his-place-drive are the instances of ONE run-with-quantum shape that
; def-loop does not have yet (owed: a `:shape :run' beside :step/:fold: NAME-run K XS ST, NAME-drive
; FUEL XS ST, and the bridge theorem below proved ONCE over constrained functions).
(defun fn-his-plan-drive (fuel evs plan)
  (declare (xargs :verify-guards nil))
  (if (zp fuel)
      (mv (list :refused :fuel) plan)
    (mv-let (v rest plan2) (fn-his-plan-run *fn-his-build-yield-rows* evs plan)
      (cond ((eq v :done) (mv nil plan2))
            ((eq v :more) (fn-his-plan-drive (1- fuel) rest plan2))
            (t (mv v plan2))))))

; EQUATION 1 (unproved): the stepped pass is the specification.
(defthm fn-his-plan-drive-is-plan-all
  (equal (fn-his-plan-drive (+ 1 (len evs)) evs plan) (fn-his-plan-all evs plan))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; C. Layout and the open.
(defun fn-his-layout (plan)
  ; (mv VERDICT STARTS NP): the canonical placement; the u64 checks of fn-hp-x-append-plan
  (declare (xargs :verify-guards nil))
  (let* ((n (car plan)) (lens (cadr plan))
         (starts (adt-starts-l lens 1)) (np (adt-end-l lens 1)))
    (if (and (unsigned-byte-p 64 n) (fn-hp-u64-listp lens) (fn-hp-u64-listp starts)
             (unsigned-byte-p 64 (* 16384 np)))
        (mv nil starts np)
      (mv (list :refused :out-of-range) nil 0))))

(defun fn-his-image-open (plan pgs-mem)
  ; (mv VERDICT STARTS NP pgs-mem).  The one grow (the arrays are empty: nothing is copied),
  ; the final header page, and every page 0..NP-1 dirty.
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (not (and (equal (pgs-v-length pgs-mem) 0) (equal (pgs-d-length pgs-mem) 0)
                (equal (pgs-w-length pgs-mem) 0)))
      (mv (list :refused :image) nil 0 pgs-mem)
    (mv-let (v starts np) (fn-his-layout plan)
      (if v
          (mv v nil 0 pgs-mem)
        (let* ((pgs-mem (pgs-x-grow-image np pgs-mem))
               (pgs-mem (fn-hp-x-put 0 (fn-hp-hdr2 (car plan) (cadr plan) starts np) pgs-mem))
               (pgs-mem (fn-hp-x-mark 0 np pgs-mem)))
          (mv nil starts np pgs-mem))))))

; ---------------------------------------------------------------------------
; D. Pass 2: five region cursors.  RC = (PAGE FILL WORDS-REVERSED), FILL = (len WORDS) < 2048,
; PAGE the region's next page (its address is START+PAGE).
(defconst *fn-his-rc0* '(0 0 nil))
(defconst *fn-his-pw0* (list 0 '(0 0 0 0 0) (list '(0 0 nil) '(0 0 nil) '(0 0 nil) '(0 0 nil) '(0 0 nil))))

(defun fn-his-rc-put (ws rc start pgs-mem)
  ; push the words WS; a page that fills is written at its final address
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom ws)
      (mv rc pgs-mem)
    (let ((page (car rc)) (cnt (+ 1 (cadr rc))) (rev (cons (car ws) (caddr rc))))
      (if (equal cnt 2048)
          (let ((pgs-mem (fn-hp-x-put (* 2048 (+ start page)) (reverse rev) pgs-mem)))
            (fn-his-rc-put (cdr ws) (list (+ 1 page) 0 nil) start pgs-mem))
        (fn-his-rc-put (cdr ws) (list page cnt rev) start pgs-mem)))))

(defun fn-his-rcs-put (cells rcs starts pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (or (atom cells) (atom rcs) (atom starts))
      (mv rcs pgs-mem)
    (mv-let (rc pgs-mem) (fn-his-rc-put (car cells) (car rcs) (car starts) pgs-mem)
      (mv-let (rest pgs-mem) (fn-his-rcs-put (cdr cells) (cdr rcs) (cdr starts) pgs-mem)
        (mv (cons rc rest) pgs-mem)))))

(defun fn-his-rcs-flush (rcs starts pgs-mem)
  ; the partial pages
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (or (atom rcs) (atom starts))
      pgs-mem
    (let ((pgs-mem (if (equal (cadr (car rcs)) 0)
                       pgs-mem
                     (fn-hp-x-put (* 2048 (+ (car starts) (car (car rcs))))
                                  (reverse (caddr (car rcs))) pgs-mem))))
      (fn-his-rcs-flush (cdr rcs) (cdr starts) pgs-mem))))

; PW = (N LENS RCS), the prefix header answer and the cursors the host carries.
(defun fn-his-place-row (ev salt pw starts np pgs-mem)
  ; (mv VERDICT PW' pgs-mem).  Row N's five cells are pushed to their regions.
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (let ((n (car pw)) (lens (cadr pw)) (rcs (caddr pw)))
    (mv-let (v tl pe) (fn-hp-x-row ev)
      (if v
          (mv v pw pgs-mem)
        (let* ((plen (len pe))
               (lens2 (fn-hp-x-add lens (list 8 8 8 8 plen))))
          (if (not (adt-placement-ok starts lens2 np))
              (mv (list :refused :plan-mismatch) pw pgs-mem)
            (mv-let (rcs pgs-mem)
              (fn-his-rcs-put (list (list (fn-hp-mkey ev salt)) (list tl) (list (nth 4 lens))
                                    (list plen) (fn-hp-pack8 (floor plen 8) pe))
                              rcs starts pgs-mem)
              (mv :ok (list (+ 1 n) lens2 rcs) pgs-mem))))))))

(defun fn-his-place-all (evs salt pw starts np pgs-mem)
  ; the specification of pass 2
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom evs)
      (mv :ok pw pgs-mem)
    (mv-let (v pw2 pgs-mem) (fn-his-place-row (car evs) salt pw starts np pgs-mem)
      (if (eq v :ok)
          (fn-his-place-all (cdr evs) salt pw2 starts np pgs-mem)
        (mv v pw pgs-mem)))))

; The steppable entry: at most K rows; (mv VERDICT REST PW' pgs-mem) as fn-his-plan-run.
(defun fn-his-place-run (k evs salt pw starts np pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (cond ((atom evs) (mv :done nil pw pgs-mem))
        ((zp k) (mv :more evs pw pgs-mem))
        (t (mv-let (v pw2 pgs-mem) (fn-his-place-row (car evs) salt pw starts np pgs-mem)
             (if (eq v :ok)
                 (fn-his-place-run (1- k) (cdr evs) salt pw2 starts np pgs-mem)
               (mv v evs pw pgs-mem))))))

(defun fn-his-place-drive (fuel evs salt pw starts np pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (zp fuel)
      (mv (list :refused :fuel) pw pgs-mem)
    (mv-let (v rest pw2 pgs-mem) (fn-his-place-run *fn-his-build-yield-rows* evs salt pw starts np pgs-mem)
      (cond ((eq v :done) (mv :ok pw2 pgs-mem))
            ((eq v :more) (fn-his-place-drive (1- fuel) rest salt pw2 starts np pgs-mem))
            (t (mv v pw2 pgs-mem))))))

; EQUATION 2 (unproved): the stepped pass is the specification, store and all.
(defthm fn-his-place-drive-is-place-all
  (let ((a (fn-his-place-drive (+ 1 (len evs)) evs salt pw starts np pgs-mem))
        (b (fn-his-place-all evs salt pw starts np pgs-mem)))
    (and (equal (mv-nth 0 a) (mv-nth 0 b))
         (equal (mv-nth 1 a) (mv-nth 1 b))
         (equal (mv-nth 2 a) (mv-nth 2 b))))
  :rule-classes nil)

(defun fn-his-image-close (plan pw starts pgs-mem)
  ; (mv VERDICT pgs-mem): the plan must be exactly what the rows filled; then the partial pages
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (not (equal (list (car pw) (cadr pw)) plan))
      (mv (list :refused :plan-mismatch) pgs-mem)
    (let ((pgs-mem (fn-his-rcs-flush (caddr pw) starts pgs-mem)))
      (mv :ok pgs-mem))))

; ---------------------------------------------------------------------------
; E. The pgs-mem composition (the LEMMA: its words = fn-hp-iw is the core).
(defun fn-his-image-build-pgs (h salt pgs-mem)
  ; (mv VERDICT N LENS STARTS NP pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (mv-let (v plan) (fn-his-plan-drive (+ 1 (len h)) h (list 0 '(0 0 0 0 0)))
    (if v
        (mv v 0 '(0 0 0 0 0) nil 0 pgs-mem)
      (mv-let (v starts np pgs-mem) (fn-his-image-open plan pgs-mem)
        (if v
            (mv v 0 '(0 0 0 0 0) nil 0 pgs-mem)
          (mv-let (v pw pgs-mem) (fn-his-place-drive (+ 1 (len h)) h salt *fn-his-pw0* starts np pgs-mem)
            (if (not (eq v :ok))
                (mv v (car pw) (cadr pw) starts np pgs-mem)
              (mv-let (v pgs-mem) (fn-his-image-close plan pw starts pgs-mem)
                (mv v (car pw) (cadr pw) starts np pgs-mem)))))))))

(defun fn-his-all-dirty (p np d)
  ; every page P..NP-1 has its dirty flag set
  (declare (xargs :measure (nfix (- (nfix np) (nfix p)))))
  (if (zp (- (nfix np) (nfix p)))
      t
    (and (equal (nth p d) 1) (fn-his-all-dirty (+ 1 (nfix p)) np d))))

; LEMMA (unproved).  On an empty store the build answers :ok and leaves exactly the canonical
; image: words = fn-hp-iw, exactly NPAGES pages, every page verified AND dirty (the commit
; tabulates every page below NP), the canonical header answer.
(defthm fn-his-image-build-pgs-is-canonical-image
  (implies (and (fn-hp-okp h salt)
                (equal (pgs-w-length pgs-mem) 0) (equal (pgs-v-length pgs-mem) 0)
                (equal (pgs-d-length pgs-mem) 0))
           (let* ((res (fn-his-image-build-pgs h salt pgs-mem))
                  (n (mv-nth 1 res)) (lens (mv-nth 2 res)) (starts (mv-nth 3 res))
                  (np (mv-nth 4 res)) (mem2 (mv-nth 5 res)))
             (and (equal (mv-nth 0 res) :ok)
                  (equal (nth *pgs-wi* mem2) (fn-hp-iw h salt))
                  (equal (pgs-w-length mem2) (* 2048 (fn-hp-npages h salt)))
                  (equal (pgs-v-length mem2) (fn-hp-npages h salt))
                  (equal (pgs-d-length mem2) (fn-hp-npages h salt))
                  (equal n (len h)) (equal lens (fn-hp-lens h salt))
                  (equal starts (fn-hp-starts h salt)) (equal np (fn-hp-npages h salt))
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt starts np))
                  (fn-his-all-dirty 0 np (nth *pgs-di* mem2)))))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; F. The entries on fn-hrecs$c the host calls, and the driver model over them.
(defun fn-his-build-open (plan fn-hrecs$c)
  ; (mv VERDICT STARTS NP fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (v starts np pgs-mem)
             (fn-his-image-open plan pgs-mem)
             (mv v starts np fn-hrecs$c)))

(defun fn-his-build-place-run (k evs pw starts np fn-hrecs$c)
  ; (mv VERDICT REST PW' fn-hrecs$c); the salt is the stobj's
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (let ((salt (fn-hrc-salt fn-hrecs$c)))
    (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
               (v rest pw2 pgs-mem)
               (fn-his-place-run k evs salt pw starts np pgs-mem)
               (mv v rest pw2 fn-hrecs$c))))

(defun fn-his-build-place-drive (fuel evs pw starts np fn-hrecs$c)
  ; the model of the host's pass-2 loop over the entry
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (if (zp fuel)
      (mv (list :refused :fuel) pw fn-hrecs$c)
    (mv-let (v rest pw2 fn-hrecs$c)
      (fn-his-build-place-run *fn-his-build-yield-rows* evs pw starts np fn-hrecs$c)
      (cond ((eq v :done) (mv :ok pw2 fn-hrecs$c))
            ((eq v :more) (fn-his-build-place-drive (1- fuel) rest pw2 starts np fn-hrecs$c))
            (t (mv v pw2 fn-hrecs$c))))))

(defun fn-his-build-close (plan pw starts np fn-hrecs$c)
  ; (mv VERDICT fn-hrecs$c): flush; on :ok the concrete holds the image (img 1, N, lens,
  ; starts, npages); the suffix stays empty
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (v pgs-mem)
             (fn-his-image-close plan pw starts pgs-mem)
             (if (eq v :ok)
                 (let* ((fn-hrecs$c (update-fn-hrc-img 1 fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-nimg (car pw) fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-lens (cadr pw) fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-starts starts fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-npages np fn-hrecs$c)))
                   (mv :ok fn-hrecs$c))
               (mv v fn-hrecs$c))))

(defun fn-his-image-build-c (h salt fn-hrecs$c)
  ; THE BUILD THE HOST RUNS: fn-his-build-begin, the pass-1 quanta (pure), open, the pass-2
  ; quanta, close.  (mv VERDICT fn-hrecs$c).  Replaces fn-his-row-begin/-step/-grow.
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (let ((fn-hrecs$c (fn-his-build-begin salt fn-hrecs$c)))
    (mv-let (v plan) (fn-his-plan-drive (+ 1 (len h)) h (list 0 '(0 0 0 0 0)))
      (if v
          (mv v fn-hrecs$c)
        (mv-let (v starts np fn-hrecs$c) (fn-his-build-open plan fn-hrecs$c)
          (if v
              (mv v fn-hrecs$c)
            (mv-let (v pw fn-hrecs$c) (fn-his-build-place-drive (+ 1 (len h)) h *fn-his-pw0* starts np fn-hrecs$c)
              (if (not (eq v :ok))
                  (mv v fn-hrecs$c)
                (fn-his-build-close plan pw starts np fn-hrecs$c)))))))))

; KEYSTONE (UNPROVED).  What fn-his-build gives today and the open and the commit consume,
; for the entries the host calls: the concrete holds H (wfp, rel) with the whole history in the
; image and an empty suffix; its header answer is the canonical one; the store is exactly
; NPAGES pages (the single grow) with EVERY page dirty, which the commit's table needs.
(defthm fn-his-image-build-c-is-canonical
  (implies (and (fn-hrecs$cp fn-hrecs$c) (natp salt) (fn-hp-okp h salt))
           (let* ((res (fn-his-image-build-c h salt fn-hrecs$c)) (c2 (mv-nth 1 res)))
             (and (equal (mv-nth 0 res) :ok)
                  (fn-hrc-wfp c2) (fn-hrs-rel h c2)
                  (equal (fn-hrc-img c2) 1)
                  (equal (fn-hrc-nimg c2) (len h))
                  (equal (fn-hrc-lo c2) (fn-hrc-hi c2))
                  (equal (fn-hrc-salt c2) salt)
                  (equal (fn-hrc-lens c2) (fn-hp-lens h salt))
                  (equal (fn-hrc-starts c2) (fn-hp-starts h salt))
                  (equal (fn-hrc-npages c2) (fn-hp-npages h salt))
                  (equal (pgs-w-length (fn-hrc-pgs c2)) (* 2048 (fn-hp-npages h salt)))
                  (fn-his-all-dirty 0 (fn-hp-npages h salt) (nth *pgs-di* (fn-hrc-pgs c2))))))
  :rule-classes nil)

; REFUSAL BY NAME (UNPROVED): a history the image cannot hold is refused, never dropped and
; never delivered as an image.
(defthm fn-his-image-build-c-refuses-unholdable
  (implies (and (fn-hrecs$cp fn-hrecs$c) (natp salt) (not (fn-hp-okp h salt)))
           (let ((res (fn-his-image-build-c h salt fn-hrecs$c)))
             (not (equal (mv-nth 0 res) :ok))))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; G. The claim the change is for (UNPROVED): the image is small.
(defthm fn-hp-cap-pessimistic
  (implies (natp u) (< (adt-cap u) (+ 1 (/ (* 2 u) 16384))))
  :rule-classes nil)

(defthm fn-hp-npages-pessimistic
  ; NP = 1 + sum of caps <= 1 + sum over 5 regions (1 + 2u/16384) -> 6 pages + 2x the octets
  (and (<= (fn-hp-npages h salt) (+ 1 (fn-hp-caps-sum (fn-hp-regs h salt))))
       (< (fn-hp-npages h salt) (+ 6 (/ (* 2 (fn-hp-regs-octets (fn-hp-regs h salt))) 16384))))
  :rule-classes nil)

; The single grow is the only allocation: the placement runs never change the word count
; (HWM-relevant: no resize after the open).
(defthm fn-his-place-run-keeps-w-length
  (equal (pgs-w-length (mv-nth 3 (fn-his-place-run k evs salt pw starts np pgs-mem)))
         (pgs-w-length pgs-mem))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; TEETH.  Ground evaluations.
(defconst *m13-fresh* '(nil nil nil nil nil nil))   ; the empty pgs-mem
(defconst *m13-c0*                                   ; the empty fn-hrecs$c
  '((nil nil nil nil nil nil) nil 0 0 0 (0 0 0 0 0) (1 1 1 1 1) 0 0 nil 0 0))
(defconst *m13-h3* '((:other 1 nil) (:other 2 nil) (:other 3 nil)))

;
; The entries are stobj-let functions, which have no ground logic value (update-fn-hrc-pgs is
; non-exec), so teeth on them RUN on the live fn-hrecs$c (assert-event, tests/acl2 style).
; fn-hrs-rel is a defun-nx and cannot run: the run asserts its conjuncts that can (img 1,
; nimg = len h, empty suffix, canonical lens/starts/npages, words = fn-hp-iw, all dirty), and
; the rel's own placement and vhold conjuncts are the ground defthm (a') on the pgs-level build.
(defun m13-dirty-live (p np pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil :measure (nfix (- (nfix np) (nfix p)))))
  (if (zp (- (nfix np) (nfix p)))
      t
    (and (equal (pgs-di p pgs-mem) 1) (m13-dirty-live (+ 1 (nfix p)) np pgs-mem))))

(defun m13-words-live (j iw pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil :measure (acl2-count iw)))
  (if (atom iw)
      t
    (and (equal (pgs-wi j pgs-mem) (car iw)) (m13-words-live (+ 1 (nfix j)) (cdr iw) pgs-mem))))

(defun m13-live-facts (h salt fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (r)
             (list (pgs-w-length pgs-mem) (pgs-v-length pgs-mem) (pgs-d-length pgs-mem)
                   (m13-dirty-live 0 (fn-hp-npages h salt) pgs-mem)
                   (m13-words-live 0 (fn-hp-iw h salt) pgs-mem))
             r))

; (a) positive, on the keystone's subject: the whole antecedent and the whole conclusion.
(assert-event
 (mv-let (v fn-hrecs$c) (fn-his-image-build-c *m13-h3* 0 fn-hrecs$c)
   (mv (and (natp 0) (fn-hp-okp *m13-h3* 0)
            (equal v :ok)
            (fn-hrc-wfp fn-hrecs$c)
            (equal (fn-hrc-img fn-hrecs$c) 1)
            (equal (fn-hrc-nimg fn-hrecs$c) (len *m13-h3*))
            (equal (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c))
            (equal (fn-hrc-salt fn-hrecs$c) 0)
            (equal (fn-hrc-lens fn-hrecs$c) (fn-hp-lens *m13-h3* 0))
            (equal (fn-hrc-starts fn-hrecs$c) (fn-hp-starts *m13-h3* 0))
            (equal (fn-hrc-npages fn-hrecs$c) (fn-hp-npages *m13-h3* 0))
            (let ((np (fn-hp-npages *m13-h3* 0)))
              (equal (m13-live-facts *m13-h3* 0 fn-hrecs$c) (list (* 2048 np) np np t t))))
       fn-hrecs$c))
 :stobjs-out '(nil fn-hrecs$c))

; (a') the rel's placement and vhold conjuncts, ground, on the pgs-level build.
(defthm fn-his-image-build-pgs-teeth-rel-conjuncts
  (let* ((res (fn-his-image-build-pgs *m13-h3* 0 *m13-fresh*)) (mem2 (mv-nth 5 res)))
    (and (equal (mv-nth 0 res) :ok)
         (adt-placement-ok (mv-nth 3 res) (mv-nth 2 res) (mv-nth 4 res))
         (fn-hp-vhold 0 (pgs-v-length mem2) mem2
                      (fn-hp-piw *m13-h3* 0 (mv-nth 3 res) (mv-nth 4 res)))
         (equal (nth *pgs-wi* mem2) (fn-hp-iw *m13-h3* 0))))
  :hints (("Goal" :in-theory (enable adt-placement-ok fn-hp-vhold-is-x fn-hp-vhold-x pgs-vi)))
  :rule-classes nil)

; (b) the dirty clause has teeth in the right direction: one clean page breaks it.
(defthm fn-his-image-build-teeth-one-clean-page
  (let* ((np (fn-hp-npages *m13-h3* 0))
         (res (fn-his-image-build-pgs *m13-h3* 0 *m13-fresh*))
         (d (nth *pgs-di* (mv-nth 5 res))))
    (and (fn-his-all-dirty 0 np d)
         (not (fn-his-all-dirty 0 np (update-nth 1 0 d)))
         (not (fn-his-all-dirty 0 np (update-nth (- np 1) 0 d)))))
  :rule-classes nil)

; (c) hypothesis removal for (fn-hp-okp h salt): a record whose tree is not encodable is
; refused BY NAME on the entry, and the concrete holds no image (nothing dropped, nothing
; half-delivered).  Also: the pass-1 lengths agree with the encoder on a real record.
(defconst *m13-bad* '((:other 1 nil) (:other 1/2 nil) (:other 3 nil)))
(assert-event
 (mv-let (v fn-hrecs$c) (fn-his-image-build-c *m13-bad* 0 fn-hrecs$c)
   (mv (and (not (fn-hp-okp *m13-bad* 0))
            (equal v '(:refused :event))
            (equal (fn-hrc-img fn-hrecs$c) 0) (equal (fn-hrc-nimg fn-hrecs$c) 0))
       fn-hrecs$c))
 :stobjs-out '(nil fn-hrecs$c))

(defthm fn-scc-program-len-teeth
  (and (equal (fn-scc-program-len '(:other 1 nil) 0) (len (fn-scc-encode '(:other 1 nil))))
       (equal (fn-scc-program-len '(:other 1 nil) 5) (+ 5 (len (fn-scc-encode '(:other 1 nil)))))
       (equal (fn-scc-program-len "abc" 0) (len (fn-scc-encode "abc"))))
  :rule-classes nil)

; (d) MUTATION witness of the plan check, on the sub-entry (not the keystone's subject): one
; row's length mis-summed (+8 octets in the pool) is refused by name and what it left is not
; the canonical image.  The stepped pass-2 and close are the real ones.
(defthm fn-his-image-build-teeth-missummed-plan
  (let* ((h *m13-h3*) (good (mv-nth 1 (fn-his-plan-all h (list 0 '(0 0 0 0 0)))))
         (bad (list (car good) (update-nth 4 (+ 8 (nth 4 (cadr good))) (cadr good)))))
    (mv-let (v starts np pgs-mem) (fn-his-image-open bad *m13-fresh*)
      (declare (ignore v))
      (mv-let (v pw pgs-mem) (fn-his-place-drive 4 h 0 *fn-his-pw0* starts np pgs-mem)
        (declare (ignore v))
        (mv-let (v pgs-mem) (fn-his-image-close bad pw starts pgs-mem)
          (and (equal v '(:refused :plan-mismatch))
               (not (equal (nth *pgs-wi* pgs-mem) (fn-hp-iw h 0))))))))
  :rule-classes nil)

; (e) HWM: the size claim, on the example (the bound is the statement above), and the
; allocation is exactly the canonical page count, once.
(defthm fn-his-image-build-teeth-size
  (let* ((h *m13-h3*) (np (fn-hp-npages h 0))
         (res (fn-his-image-build-pgs h 0 *m13-fresh*)) (mem2 (mv-nth 5 res)))
    (and (<= np (+ 1 (fn-hp-caps-sum (fn-hp-regs h 0))))
         (< np (+ 6 (/ (* 2 (fn-hp-regs-octets (fn-hp-regs h 0))) 16384)))
         (equal (pgs-w-length mem2) (* 2048 np))))
  :rule-classes nil)

; (f) steppable entries: the quantum is honoured (K rows, then :more with the rest) and
; composes: two runs of 1 then 2 rows = the plan of all three.
(defthm fn-his-plan-run-teeth-quantum
  (let ((p0 (list 0 '(0 0 0 0 0))))
    (mv-let (v1 r1 p1) (fn-his-plan-run 1 *m13-h3* p0)
      (mv-let (v2 r2 p2) (fn-his-plan-run 2 r1 p1)
        (and (equal v1 :more) (equal (len r1) 2) (equal v2 :done) (equal r2 nil)
             (equal p2 (mv-nth 1 (fn-his-plan-all *m13-h3* p0)))))))
  :rule-classes nil)

; (g) hypothesis removal for the fresh store: refused untouched.
(defthm fn-his-image-build-teeth-nonfresh-store
  (let* ((pgs-mem (list '(0) nil nil nil nil nil)))
    (mv-let (v starts np mem2) (fn-his-image-open '(3 (24 24 24 24 40)) pgs-mem)
      (declare (ignore starts np))
      (and (equal v '(:refused :image)) (equal mem2 pgs-mem))))
  :rule-classes nil)
