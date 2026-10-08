; Teeth and a ground run for books/paged-checkpoint-open.lisp
; (fn-pck-x-open-is-the-capture, fn-pck-x-open-reads-bound).
;
;   1. PREMISE INHABITATION.  A ground (configs recs) of two held wire records
;      with consecutive sequences from the fold seed; the payload file is the
;      two frames end to end, attached as the durable octets of file 5; the
;      image of `fn-pck-pages' of it is written into a real `pgs-mem' word by
;      word; every premise of the keystone is evaluated to T and so is every
;      conclusion conjunct; the words read are the exact count and within the
;      bound.
;   2. MUTATION WITNESSES (labelled separately).  An exec open that starts the
;      tape one word late, and one that skips the first record, both leave the
;      keystone's premises true and give records that are not the capture's.
;   3. CORRUPTED-STATE WITNESSES (labelled separately).  An image that differs
;      from the flattened pages at ONE word of a record's metadata, and one that
;      differs at the word naming the payload's offset (the seal reads the
;      octets one word to the right): the equation premise is false and the
;      conclusion fails.
;   4. HYPOTHESIS REMOVAL.  The durable file does not hold the model file
;      (file 6, all zeros): every other premise is T, `fn-cpl-holdsp' is NIL, the
;      rows read back are not the records.  The keystone without `fn-pck-recordsp',
;      without the equation, and without the durable premises does not prove
;      (must-fail-checked); an unencodable record is an affirmative witness for
;      the first.

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-open")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

;; The constrained seams, attached: the frame trailer's words, the log position
;; F (any encodable tree), and the durable octets of files 5 (the model file)
;; and 6 (zeros).
(defun pckot-trailer (p) (declare (xargs :guard t) (ignore p)) (list 11 22 33 44))
(defattach fn-cpl-trailer-words pckot-trailer)
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

(defun pckot-octet (file pos)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (equal file 5) (natp pos) (< pos (len (pckot-file))))
      (nth pos (pckot-file))
    0))

(defun pckot-octets (file off len)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp len) nil (cons (pckot-octet file off) (pckot-octets file (+ 1 (nfix off)) (1- len)))))

(defun pckot-realize-octet (file eoff elen poff plen trailer i)
  (declare (xargs :guard t :verify-guards nil) (ignore eoff elen trailer))
  (nth i (pckot-octets file poff plen)))

(defun pckot-realize-octets (file eoff elen poff plen trailer)
  (declare (xargs :guard t :verify-guards nil) (ignore eoff elen trailer))
  (pckot-octets file poff plen))

(defattach (fn-durable-octet pckot-octet)
           (fn-durable-octets pckot-octets)
           (fn-durable-realize-octet pckot-realize-octet)
           (fn-durable-realize-octets pckot-realize-octets))

(defun pckot-pages () (declare (xargs :verify-guards nil)) (fn-pck-pages nil *pckot-recs*))
(defun pckot-w () (declare (xargs :verify-guards nil)) (adt-tp-flat (pckot-pages)))

; Words into the image, from word I on.
(defun pckot-poke (i ws pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom ws)
      pgs-mem
    (let ((pgs-mem (update-pgs-wi i (car ws) pgs-mem)))
      (pckot-poke (1+ i) (cdr ws) pgs-mem))))

; The mutants: the same open, the tape starting at a wrong word.
(defun pckot-mut-open (npg start fid pgs-mem fn-arena fn-octets)
  (declare (xargs :stobjs (pgs-mem fn-arena fn-octets) :verify-guards nil))
  (let* ((n (nfix (pcko-w 1 pgs-mem)))
         (fn-octets (fn-octets-clear fn-octets)))
    (mv-let (reads fn-octets) (pcko-copy 2 n 2 pgs-mem fn-octets)
      (let ((d (pcko-tree fn-octets)))
        (let ((root (cadr d)))
          (mv-let (verdict acc reads fn-arena fn-octets)
            (pcko-tape start (* 2048 npg) (fn-ssr-seed (fn-stxk-initial-context 0)) reads fid
                       pgs-mem fn-arena fn-octets)
            (mv verdict (fn-ssr-rows acc) root reads fn-arena fn-octets)))))))

;; Full recovery's rows for the records, on a local arena of its own.
(defun pckot-f-rows (recs)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (mv-let (acc fn-arena)
        (fn-ssr-intern-step (fn-pck-seed) recs nil nil :resident nil fn-arena)
        (mv (fn-ssr-rows acc) fn-arena))
      rows)))

;; The model's durable-file premises for file FID.
(defun pckot-durable-premises (recs fid)
  (declare (xargs :verify-guards nil))
  (list (true-listp (pckot-file))
        (fn-pck-resolvesp recs 0 (pckot-file))
        (fn-cpl-holdsp fid (pckot-file) 0)))

; WORDS is the image to write; FID the payload file; MUT is NIL for the exec,
; else the mutant's start.  The answer: (PREMISES CONCLUSION READS).
(defun pckot-run (configs recs words fid mut)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (out pgs-mem)
      (with-local-stobj fn-octets
        (mv-let (out pgs-mem fn-octets)
          (with-local-stobj fn-arena
            (mv-let (out pgs-mem fn-octets fn-arena)
              (let* ((pages (fn-pck-pages configs recs))
                     (npg (len pages))
                     (pgs-mem (pgs-x-grow-image npg pgs-mem))
                     (pgs-mem (pckot-poke 0 words pgs-mem))
                     (c (fn-pck-capture-of-pages pages (pckot-file)))
                     (premises
                      (append
                       (list (fn-pck-recordsp configs recs)
                             (fn-pck-root-fitsp configs recs)
                             (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem) (adt-tp-flat pages))
                             (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                             (natp fid)
                             (fn-arena-p fn-arena))
                       (pckot-durable-premises recs fid))))
                (mv-let (verdict rows roots reads fn-arena fn-octets)
                  (if mut
                      (pckot-mut-open npg mut fid pgs-mem fn-arena fn-octets)
                    (fn-pck-x-open npg pgs-mem fid fn-arena fn-octets))
                  (mv (list premises
                            (list (equal verdict :ok)
                                  (equal rows (pckot-f-rows recs))
                                  (equal (fn-rows-wire-of rows fn-arena) (fn-sco-records c))
                                  (equal roots (list (fn-sco-cpr c) (fn-sco-identity c)
                                                     (fn-sco-consumer c) (fn-sco-topic c))))
                            reads)
                      pgs-mem fn-octets fn-arena)))
              (mv out pgs-mem fn-octets)))
          (mv out pgs-mem)))
      out)))

(defun pckot-tw () (declare (xargs :verify-guards nil)) (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows *pckot-recs*)))
(defun pckot-prog0 () (declare (xargs :verify-guards nil))
  (fn-scc-program (fn-pck-meta (car *pckot-recs*) (fn-pck-seed))))
(defun pckot-rootprog () (declare (xargs :verify-guards nil))
  (fn-scc-program (fn-pck-root-tree nil *pckot-recs*)))

; 1. The ground witness: all premises T, all conclusions T, the exact reads.
(assert-event
 (let ((r (pckot-run nil *pckot-recs* (pckot-w) 5 nil)))
   (and (equal (car r) '(t t t t t t t t t))
        (equal (cadr r) '(t t t t))
        (equal (caddr r) (+ 2 (adt-tp-npk (len (pckot-rootprog))) (len (pckot-tw)) 1))
        (<= (caddr r) (+ (* 8 2048) (len (pckot-tw)) 1))
        (consp *pckot-recs*) (< 0 (len (pckot-tw))))))

; 2. Mutants: the tape one word late, and the first record skipped.  Premises
; stay T; the records are not the capture's.
(assert-event
 (let ((late (pckot-run nil *pckot-recs* (pckot-w) 5 (+ 16384 1)))
       (skip (pckot-run nil *pckot-recs* (pckot-w) 5
                        (+ 16384 (len (adt-tp-rw *fn-pck-row-schema* (car (fn-pck-rows *pckot-recs*))))))))
   (and (equal (car late) '(t t t t t t t t t))
        (equal (car skip) '(t t t t t t t t t))
        (not (nth 2 (cadr late)))
        (not (nth 2 (cadr skip))))))

; 3. Corrupted state: one word of the image differs from the flattened pages.
; (a) a word of the first record's metadata; (b) the word naming the first
; payload's offset (the seal would read one octet to the right).
(defun pckot-corrupt (i) (declare (xargs :verify-guards nil))
  (update-nth i (+ 1 (nth i (pckot-w))) (pckot-w)))
(assert-event
 (let ((r (pckot-run nil *pckot-recs* (pckot-corrupt (+ 16384 5)) 5 nil)))
   (and (not (equal (pckot-corrupt (+ 16384 5)) (pckot-w)))
        (equal (car r) '(t t nil t t t t t t))
        (not (and (nth 1 (cadr r)) (nth 2 (cadr r)))))))
(assert-event
 (let* ((off-word (+ 16384 2 (adt-tp-npk (len (pckot-prog0)))))
        (r (pckot-run nil *pckot-recs* (pckot-corrupt off-word) 5 nil)))
   (and (equal (nth off-word (pckot-w)) 37)
        (equal (car r) '(t t nil t t t t t t))
        (nth 0 (cadr r))
        (not (nth 2 (cadr r))))))

; 4. Hypothesis removal.  The durable file does not hold the model file (file 6
; is all zeros): the retained premises hold, holdsp is NIL, the rows read back
; are not the records.
(assert-event
 (let ((r (pckot-run nil *pckot-recs* (pckot-w) 6 nil)))
   (and (equal (car r) '(t t t t t t t t nil))
        (nth 0 (cadr r))
        (not (nth 2 (cadr r))))))

; An unencodable record makes recordsp NIL (the theorem says nothing about its
; pages); without the premise the statement does not prove.
(defconst *pckot-bad-recs* (list *pckot-r0* 1/2))
(assert-event
 (and (fn-pck-recordsp nil *pckot-recs*)
      (not (fn-pck-recordsp nil *pckot-bad-recs*))
      (not (fn-sccb-treep 1/2))))

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
