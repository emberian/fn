; Teeth and ground witnesses for books/paged-checkpoint-open.lisp
; (fn-pck-x-open-is-the-capture, fn-pck-x-open-reads-bound).
;
; What runs and what does not.  The open seals each record's payload BY REF
; (`fn-arena-seal-extent'), whose exec reads the host's realizer
; (`fn-durable-realize-octets', A-DURABLE-EXTENT).  ACL2 forbids attaching to
; that seam (it is an ancestor of an exported function of the abstract stobj
; fn-arena), so the open itself cannot be run on a real arena in this book; its
; behaviour is the proved fold (`pcko-tape-of-recs', `pcko-sim-is-the-fold',
; `pcko-open-model').  This book therefore witnesses, on a ground history, what
; is evaluable: every premise of the keystones that does not name the durable
; octets, the model side of every conclusion (full recovery's rows read back as
; the records, the roots), the descriptor each tape row makes the open seal, and
; the corrupted states.  The durable premise (fn-cpl-holdsp) is the host's
; (fsync, A-DURABLE-EXTENT) and is witnessed only as a statement, by the
; must-fail below that drops it.
;
;   1. PREMISE INHABITATION.  Two held wire records with consecutive sequences
;      from the fold seed; the payload file is the two frames end to end; the
;      image of `fn-pck-pages' is written into a real `pgs-mem' word by word;
;      every evaluable premise is T; the model side of the conclusion holds;
;      the words the open reads are a function of the history, the bound holds.
;   2. THE DESCRIPTOR.  For each tape row, the six arguments the open passes to
;      the extent seal are fn-cpl-extent's for the row's ref, and the ref lies
;      in the model file at the frame's payload.
;   3. CORRUPTED STATE (labelled): an image that differs from the flattened pages
;      at one word of a record's metadata, and at the word naming a payload's
;      offset: the equation premise is false.
;   4. HYPOTHESIS REMOVAL.  The keystone without `fn-pck-recordsp', without the
;      equation, and without the durable premise does not prove
;      (must-fail-checked); an unencodable record is an affirmative witness for
;      the first.

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-open")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

;; The constrained seams that execute, attached: the frame trailer's words, the
;; log position F (any encodable tree).
(defun pckot-f (configs recs) (declare (xargs :guard t) (ignore configs recs)) nil)
(defattach fn-pck-f pckot-f)

(defconst *pckot-r0*
  (fn-record-make 0 0 0 "<cp0@example.invalid>" '(65 13 10) '("fn.letters")
                  "cp-pin-0" "cp-content-0" "cp-release-0" 2 841000000))
(defconst *pckot-r1*
  (fn-record-make 1 4 4 "<cp1@example.invalid>" '(66 13 10 67) '("fn.test")
                  "cp-pin-1" "cp-content-1" "cp-release-1" 3 841000000))
(defconst *pckot-recs* (list *pckot-r0* *pckot-r1*))

; The model file: the two frames end to end.
(defun pckot-file ()
  (declare (xargs :verify-guards nil))
  (append (fn-cpl-frame (fn-record-payload *pckot-r0*)) (fn-cpl-frame (fn-record-payload *pckot-r1*))))

(defun pckot-pages () (declare (xargs :verify-guards nil)) (fn-pck-pages nil *pckot-recs*))
(defun pckot-w () (declare (xargs :verify-guards nil)) (adt-tp-flat (pckot-pages)))
(defun pckot-npg () (declare (xargs :verify-guards nil)) (len (pckot-pages)))

; Words into the image, from word I on.
(defun pckot-poke (i ws pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom ws)
      pgs-mem
    (let ((pgs-mem (update-pgs-wi i (car ws) pgs-mem)))
      (pckot-poke (1+ i) (cdr ws) pgs-mem))))

;; Full recovery's rows for the records, on a local arena of its own.
(defun pckot-f-rows (recs)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (mv-let (acc fn-arena)
        (fn-ssr-intern-step (fn-pck-seed) recs nil nil :resident nil fn-arena)
        (mv (fn-ssr-rows acc) fn-arena))
      rows)))

;; ... read back as the records, through the arena that fold leaves.
(defun pckot-f-wires (recs)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (wires fn-arena)
      (mv-let (acc fn-arena)
        (fn-ssr-intern-step (fn-pck-seed) recs nil nil :resident nil fn-arena)
        (mv (fn-rows-wire-of (fn-ssr-rows acc) fn-arena) fn-arena))
      wires)))

; The premises of the keystone that do not name the durable octets, with WORDS
; the image written into the pgs-mem.
(defun pckot-premises (configs recs words fid)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (out pgs-mem)
      (let* ((pages (fn-pck-pages configs recs))
             (npg (len pages))
             (pgs-mem (pgs-x-grow-image npg pgs-mem))
             (pgs-mem (pckot-poke 0 words pgs-mem)))
        (mv (list (fn-pck-recordsp configs recs)
                  (fn-pck-root-fitsp configs recs)
                  (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem) (adt-tp-flat pages))
                  (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                  (natp fid)
                  (true-listp (pckot-file))
                  (fn-pck-resolvesp recs 0 (pckot-file)))
            pgs-mem))
      out)))

; 1. The ground witness.
(assert-event
 (and (equal (pckot-premises nil *pckot-recs* (pckot-w) 5) '(t t t t t t t))
      ; full recovery's rows read back as the records, in order
      (equal (pckot-f-wires *pckot-recs*) *pckot-recs*)
      (equal (len (pckot-f-rows *pckot-recs*)) 2)
      ; the capture the pages hold, against the model file: the records, the roots
      (let ((c (fn-pck-capture-of-pages (pckot-pages) (pckot-file)))
            (x (fn-pck-root-tree nil *pckot-recs*)))
        (and (equal (fn-sco-records c) *pckot-recs*)
             (equal (list (fn-sco-cpr c) (fn-sco-identity c) (fn-sco-consumer c) (fn-sco-topic c))
                    (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x)))))
      ; the reads: the root row, the tape once, one more word; within the bound
      (let* ((tw (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows *pckot-recs*)))
             (prog (fn-scc-program (fn-pck-root-tree nil *pckot-recs*)))
             (reads (+ 2 (adt-tp-npk (len prog)) (len tw)
                       (if (consp (adt-tp-zeros (adt-tp-pad (len tw)))) 1 0))))
        (and (<= reads (+ (* 8 2048) (len tw) 1)) (< 0 (len tw))))))

; 2. The descriptor each row makes the open seal: the six arguments of
; fn-arena-seal-extent for the row (off len d0 d1 d2 d3), and fn-cpl-extent's
; for the same ref and trailer.
(defun pckot-descriptor (fid row)
  (declare (xargs :verify-guards nil))
  (let ((off (nth 1 row)) (len (nth 2 row)))
    (list fid (- off 37) (+ len 37) off len
          (fn-arx-trailer-nat (fn-cpl-unpack-words (list (nth 3 row) (nth 4 row) (nth 5 row) (nth 6 row)))))))

(defun pckot-extent (fid row)
  (declare (xargs :verify-guards nil))
  (fn-cpl-extent fid (list (nth 1 row) (nth 2 row))
                 (fn-cpl-unpack-words (list (nth 3 row) (nth 4 row) (nth 5 row) (nth 6 row)))))

(assert-event
 (let ((rows (fn-pck-rows *pckot-recs*)))
   (and (equal (pckot-descriptor 5 (car rows)) (pckot-extent 5 (car rows)))
        (equal (pckot-descriptor 5 (cadr rows)) (pckot-extent 5 (cadr rows)))
        ; the first frame starts at 0, the second where the first ends
        (equal (nth 1 (pckot-descriptor 5 (car rows))) 0)
        (equal (nth 1 (pckot-descriptor 5 (cadr rows)))
               (fn-cpl-frame-octets (len (fn-record-payload *pckot-r0*))))
        ; the ref lies in the model file at the payload
        (equal (take (nth 2 (car rows)) (nthcdr (nth 1 (car rows)) (pckot-file)))
               (fn-record-payload *pckot-r0*))
        (equal (take (nth 2 (cadr rows)) (nthcdr (nth 1 (cadr rows)) (pckot-file)))
               (fn-record-payload *pckot-r1*))
        ; a ref read relative to the frame's start (poff 37 for every frame) is
        ; a different, wrong extent for the second frame
        (not (equal (nth 3 (pckot-descriptor 5 (cadr rows))) 37)))))

; 3. Corrupted state: one word of the image differs from the flattened pages.
; (a) a word of the first record's metadata; (b) the word naming the first
; payload's offset.
(defun pckot-corrupt (i) (declare (xargs :verify-guards nil))
  (update-nth i (+ 1 (nth i (pckot-w))) (pckot-w)))
(assert-event
 (and (not (equal (pckot-corrupt (+ 16384 5)) (pckot-w)))
      (equal (pckot-premises nil *pckot-recs* (pckot-corrupt (+ 16384 5)) 5) '(t t nil t t t t))))
(assert-event
 (let ((off-word (+ 16384 2 (adt-tp-npk (len (fn-scc-program (fn-pck-meta (car *pckot-recs*) (fn-pck-seed))))))))
   (and (equal (nth off-word (pckot-w)) 37)
        (equal (pckot-premises nil *pckot-recs* (pckot-corrupt off-word) 5) '(t t nil t t t t)))))

; 4. An unencodable record makes recordsp NIL (the theorem says nothing about
; its pages).
(defconst *pckot-bad-recs* (list *pckot-r0* 1/2))
(assert-event
 (and (fn-pck-recordsp nil *pckot-recs*)
      (not (fn-pck-recordsp nil *pckot-bad-recs*))
      (not (fn-sccb-treep 1/2))))

; Hypothesis removal.  Each statement drops one premise of the keystone and does
; not prove.
(must-fail-checked
 (defthm pckot-no-recordsp
   (implies (and (fn-pck-root-fitsp configs recs)
                 (equal npg (len (fn-pck-pages configs recs)))
                 (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem) (adt-tp-flat (fn-pck-pages configs recs)))
                 (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                 (natp fid) (fn-arena-p fn-arena)
                 (true-listp file) (fn-pck-resolvesp recs 0 file) (fn-cpl-holdsp fid file 0))
            (equal (mv-nth 0 (fn-pck-x-open npg pgs-mem fid fn-arena fn-octets)) :ok))
   :hints (("Goal" :do-not-induct t))))

(must-fail-checked
 (defthm pckot-no-equation
   (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs)
                 (equal npg (len (fn-pck-pages configs recs)))
                 (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                 (natp fid) (fn-arena-p fn-arena)
                 (true-listp file) (fn-pck-resolvesp recs 0 file) (fn-cpl-holdsp fid file 0))
            (equal (mv-nth 0 (fn-pck-x-open npg pgs-mem fid fn-arena fn-octets)) :ok))
   :hints (("Goal" :do-not-induct t))))

(must-fail-checked
 (defthm pckot-no-holdsp
   (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs)
                 (equal npg (len (fn-pck-pages configs recs)))
                 (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem) (adt-tp-flat (fn-pck-pages configs recs)))
                 (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                 (natp fid) (fn-arena-p fn-arena)
                 (true-listp file) (fn-pck-resolvesp recs 0 file))
            (equal (fn-rows-wire-of (mv-nth 1 (fn-pck-x-open npg pgs-mem fid fn-arena fn-octets))
                                    (mv-nth 4 (fn-pck-x-open npg pgs-mem fid fn-arena fn-octets)))
                   (fn-sco-records (fn-pck-capture-of-pages (fn-pck-pages configs recs) file))))
   :hints (("Goal" :do-not-induct t))))

(must-fail-checked
 (defthm pckot-no-resolvesp
   (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs)
                 (equal npg (len (fn-pck-pages configs recs)))
                 (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem) (adt-tp-flat (fn-pck-pages configs recs)))
                 (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                 (natp fid) (fn-arena-p fn-arena)
                 (true-listp file) (fn-cpl-holdsp fid file 0))
            (equal (fn-rows-wire-of (mv-nth 1 (fn-pck-x-open npg pgs-mem fid fn-arena fn-octets))
                                    (mv-nth 4 (fn-pck-x-open npg pgs-mem fid fn-arena fn-octets)))
                   (fn-sco-records (fn-pck-capture-of-pages (fn-pck-pages configs recs) file))))
   :hints (("Goal" :do-not-induct t))))

; G-B: the executable root summary, with every resident-image antecedent.
; Empty history avoids a durable-extent realizer; F is deliberately non-NIL.
(defun pckot-summary-f (configs recs)
  (declare (xargs :guard t) (ignore configs recs))
  '(:log 17 23 29))
(defattach fn-pck-f pckot-summary-f)
(defun pckot-summary-run (pgs-mem fn-arena fn-octets)
  (declare (xargs :stobjs (pgs-mem fn-arena fn-octets) :verify-guards nil))
  (let* ((pages (fn-pck-pages nil nil)) (npg (len pages))
         (pgs-mem (pgs-x-grow-image npg pgs-mem))
         (pgs-mem (pckot-poke 0 (adt-tp-flat pages) pgs-mem))
         (hyps (and (fn-pck-recordsp nil nil) (fn-pck-root-fitsp nil nil)
                    (equal npg (len pages))
                    (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem) (adt-tp-flat pages))
                    (<= (* 2048 npg) (pgs-x-len 0 pgs-mem)) (natp 5))))
    (mv-let (verdict rows roots reads fn-arena fn-octets f plen)
      (fn-pck-x-open npg pgs-mem 5 fn-arena fn-octets)
      (declare (ignore rows roots reads))
      (mv (and hyps (equal verdict :ok)
               (equal f (nth 4 (fn-pck-root-tree nil nil)))
               (equal plen (nth 5 (fn-pck-root-tree nil nil)))
               (equal f '(:log 17 23 29)) (equal plen 0))
          pgs-mem fn-arena fn-octets))))
(defun pckot-summary-witness ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj pgs-mem
   (mv-let (ok pgs-mem)
     (with-local-stobj fn-arena
       (mv-let (ok pgs-mem fn-arena)
         (with-local-stobj fn-octets
           (mv-let (ok pgs-mem fn-arena fn-octets)
             (pckot-summary-run pgs-mem fn-arena fn-octets)
             (mv ok pgs-mem fn-arena)))
         (mv ok pgs-mem)))
     ok)))
(assert-event (pckot-summary-witness))
