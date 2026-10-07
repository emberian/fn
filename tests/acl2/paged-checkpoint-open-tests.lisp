; Teeth and a ground run for books/paged-checkpoint-open.lisp
; (fn-pck-x-open-is-the-capture, fn-pck-x-open-reads-bound).
;
;   1. PREMISE INHABITATION.  A ground (configs recs) of two held wire records;
;      the image of `fn-pck-pages' of it is written into a real `pgs-mem' word
;      by word; every premise of the keystone is evaluated to T and so is every
;      conjunct of its conclusion; the words read are the exact count and
;      within the bound.
;   2. MUTATION WITNESSES (labelled separately).  An exec open that starts the
;      tape one word late, and one that skips the first record, both leave the
;      keystone's premises true and give records that are not the capture's.
;   3. THE EQUATION PREMISE IS LOAD-BEARING.  An image that differs from the
;      flattened pages at ONE word (a record's octet): the other premises hold,
;      the equation is false, and the conclusion fails.
;   4. HYPOTHESIS REMOVAL.  The keystone without `fn-pck-recordsp', and without
;      the equation, does not prove (must-fail-checked); an unencodable record
;      is an affirmative witness for the first: its recordsp is NIL and the
;      open of its pages does not answer the capture.

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-open")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *pckot-r0*
  (fn-record-make 0 0 0 "<cp0@example.invalid>" '(65 13 10) '("fn.letters")
                  "cp-pin-0" "cp-content-0" "cp-release-0" 2 841000000))
(defconst *pckot-r1*
  (fn-record-make 1 4 4 "<cp1@example.invalid>" '(66 13 10) '("fn.test")
                  "cp-pin-1" "cp-content-1" "cp-release-1" 3 841000000))
(defconst *pckot-recs* (list *pckot-r0* *pckot-r1*))
(defconst *pckot-pages* (fn-pck-pages nil *pckot-recs*))
(defconst *pckot-w* (adt-tp-flat *pckot-pages*))
(defconst *pckot-npg* (len *pckot-pages*))

; Words into the image, from word I on.
(defun pckot-poke (i ws pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom ws)
      pgs-mem
    (let ((pgs-mem (update-pgs-wi i (car ws) pgs-mem)))
      (pckot-poke (1+ i) (cdr ws) pgs-mem))))

; The mutants: the same open, the tape starting at a wrong word.
(defun pckot-mut-open (npg start pgs-mem fn-arena fn-octets)
  (declare (xargs :stobjs (pgs-mem fn-arena fn-octets) :verify-guards nil))
  (let* ((n (nfix (pcko-w 1 pgs-mem)))
         (fn-octets (fn-octets-clear fn-octets)))
    (mv-let (reads fn-octets) (pcko-copy 2 n 2 pgs-mem fn-octets)
      (let ((d (pcko-tree fn-octets)))
        (let ((root (cadr d)))
          (mv-let (verdict acc index reads fn-arena fn-octets)
            (pcko-tape start (* 2048 npg) 0 (fn-ssr-seed (fn-stxk-initial-context 0)) nil reads
                       pgs-mem fn-arena fn-octets)
            (mv verdict (fn-ssr-rows acc) root index reads fn-arena fn-octets)))))))

;; The intern premise, on a local arena of its own so the run's arena stays fresh.
(defun pckot-intern-ok (recs)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (ok fn-arena)
      (mv-let (acc fn-arena)
        (fn-ssr-intern-step (fn-ssr-seed (fn-stxk-initial-context 0)) recs nil nil :resident nil fn-arena)
        (mv (not (eq acc :bad)) fn-arena))
      ok)))

; WORDS is the image to write; MUT is NIL for the exec, else the mutant's start.
; The answer: (PREMISES CONCLUSION READS), each a list of booleans.
(defun pckot-run (configs recs words mut)
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
                     (c (fn-pck-capture-of-pages pages))
                     (premises
                      (list (fn-pck-recordsp configs recs)
                            (fn-pck-root-fitsp configs recs)
                            (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem) (adt-tp-flat pages))
                            (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                            (fn-arena-p fn-arena)
                            (pckot-intern-ok recs))))
                (mv-let (verdict rows roots index reads fn-arena fn-octets)
                  (if mut
                      (pckot-mut-open npg mut pgs-mem fn-arena fn-octets)
                    (fn-pck-x-open npg pgs-mem fn-arena fn-octets))
                  (mv (list premises
                            (list (equal verdict :ok)
                                  (equal (fn-rows-wire-of rows fn-arena) (fn-sco-records c))
                                  (equal roots (list (fn-sco-cpr c) (fn-sco-identity c)
                                                     (fn-sco-consumer c) (fn-sco-topic c)))
                                  (equal index (fn-sco-event-index c)))
                            reads)
                      pgs-mem fn-octets fn-arena)))
              (mv out pgs-mem fn-octets)))
          (mv out pgs-mem)))
      out)))

(defconst *pckot-tw* (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows *pckot-recs*)))
(defconst *pckot-rw0*
  (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row (fn-pck-root-tree nil *pckot-recs*))))

; 1. The ground witness: all premises T, all conclusions T, the exact reads.
(assert-event
 (let ((r (pckot-run nil *pckot-recs* *pckot-w* nil)))
   (and (equal (car r) '(t t t t t t))
        (equal (cadr r) '(t t t t))
        (equal (caddr r) (+ (len *pckot-rw0*) (len *pckot-tw*) 1))
        (<= (caddr r) (+ (* 8 2048) (len *pckot-tw*) 1))
        (consp *pckot-recs*) (< 0 (len *pckot-tw*)))))

; 2. Mutants: the tape one word late, and the first record skipped.  Premises
; stay T; the records are not the capture's.
(assert-event
 (let ((late (pckot-run nil *pckot-recs* *pckot-w* (+ 16384 1)))
       (skip (pckot-run nil *pckot-recs* *pckot-w* (+ 16384 (len (adt-tp-rw *fn-pck-row-schema*
                                                                            (fn-pck-enc-row *pckot-r0*)))))))
   (and (equal (car late) '(t t t t t t))
        (equal (car skip) '(t t t t t t))
        (not (nth 1 (cadr late)))
        (not (nth 1 (cadr skip))))))

; 3. One word of the image differs from the flattened pages: the equation
; premise is the only false premise, and the conclusion fails.
(defconst *pckot-w-bad*
  (update-nth (+ 16384 5) (+ 1 (nth (+ 16384 5) *pckot-w*)) *pckot-w*))
(assert-event
 (let ((r (pckot-run nil *pckot-recs* *pckot-w-bad* nil)))
   (and (not (equal *pckot-w-bad* *pckot-w*))
        (equal (car r) '(t t nil t t t))
        (not (and (nth 0 (cadr r)) (nth 1 (cadr r)))))))

; 4. Hypothesis removal.  An unencodable record: recordsp is NIL (the other
; premises hold) and the image of its pages is not opened as the capture.
(defconst *pckot-bad-recs* (list *pckot-r0* 1/2))
(set-guard-checking :none)
(assert-event
 (let ((r (pckot-run nil *pckot-bad-recs* (adt-tp-flat (fn-pck-pages nil *pckot-bad-recs*)) nil)))
   (and (not (fn-pck-recordsp nil *pckot-bad-recs*))
        (not (nth 0 (car r)))
        (not (and (nth 0 (cadr r)) (nth 1 (cadr r)))))))
(set-guard-checking t)

(must-fail-checked
 (defthm pckot-no-recordsp
   (implies (and (fn-pck-root-fitsp configs recs)
                 (equal npg (len (fn-pck-pages configs recs)))
                 (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem)
                        (adt-tp-flat (fn-pck-pages configs recs)))
                 (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                 (fn-arena-p fn-arena)
                 (not (eq (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed (fn-stxk-initial-context 0))
                                                        recs nil nil :resident nil fn-arena))
                          :bad)))
            (equal (mv-nth 0 (fn-pck-x-open npg pgs-mem fn-arena fn-octets)) :ok))
   :hints (("Goal" :do-not-induct t))))

(must-fail-checked
 (defthm pckot-no-equation
   (implies (and (fn-pck-recordsp configs recs)
                 (fn-pck-root-fitsp configs recs)
                 (equal npg (len (fn-pck-pages configs recs)))
                 (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                 (fn-arena-p fn-arena)
                 (not (eq (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed (fn-stxk-initial-context 0))
                                                        recs nil nil :resident nil fn-arena))
                          :bad)))
            (equal (mv-nth 0 (fn-pck-x-open npg pgs-mem fn-arena fn-octets)) :ok))
   :hints (("Goal" :do-not-induct t))))
