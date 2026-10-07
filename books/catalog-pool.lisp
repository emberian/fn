; fn: catalog reads bounded by a frame pool (lane s-pool, 2026-10-07; Phase 2b
; of build/coordinator/STORAGE-PROGRAM-20261006.md, section 3.4).  PHASE A:
; the readers and the STATEMENTS below; no theorem is proved here.
;
; The model.  The catalog's persisted image is (fn-pck-cat-pages h)
; (books/catalog-pages.lisp): a TAPE of the fn-crow rows' words cut into pages
; of 2048 words.  A reader holds a RESIDENT set RES of page numbers (most
; recent first; at most (fn-cpg-cap FRAMES) of them) and reads a word through
; it: a word of a resident page is the word, any other is the verdict
; (:need-page P) -- books/pagestore-exec.lisp's `pgs-x-read'.  The reader
; ANSWERS the verdict itself, in the loop: `fn-cpg-fill' (the host's in-place
; fill, evicting the least recent page past the frame count), then read on from
; the SAME word.  Progress is kept (the words already read are the loop's
; accumulator): a retry from the start of a row would not terminate when a row
; spans more pages than the pool has frames.  The measure is
; 2 * (words left) + (1 if the current page is not resident).
;
; Random access.  The tape is variable width and self delimiting, so a row's
; place is the sum of the widths before it.  The readers take the DIRECTORY
; DIR = (fn-cpg-dir rows), N + 1 word offsets, as a given.  It is O(N) words
; and is NOT derived here: where it lives (the root region, a second tape, or
; resident) is a decision for S (books/def-representation-pages.lisp scope
; note 2 names it "an index over the tape (the root's)").
;
; The index.  `fn-cpg-msgid-seqs' is given the CANDIDATES (today the resident
; fn-mlh answer, `fn-mlh-candidates'), reads each candidate's row through the
; pool and keeps those whose msgid is the key (`fn-cat$p-confirm').
; `fn-cpg-group-number' is given the dense map's answer CAND and reads the
; row's numbers to check it.  Both indexes stay in the heap in this phase.
;
; Generator.  The page-reading half (`fn-cpg-read-words', `fn-cpg-read-row'
; and the directory) is a function of the schema and is the `:pages' read the
; generator should emit next to NAME-of-pages (books/def-representation.lisp
; `rep-pages-events', books/def-representation-pages.lisp `adt-tp-*'); it is
; instanced here at *fn-crow-schema* and moves there in phase B.  Only
; the msgid and number tests are the catalog's.
;
; STATEMENTS (phase A; proved in phase B).  H a catalog, PAGES =
; (fn-pck-cat-pages h), DIR = (fn-cpg-dir (fn-pck-crow-rows h)).  Common
; premises P: (fn-cat-rowsp h), (fn-pck-carriedp h), (posp frames),
; (fn-cpg-res-okp res pages), (<= (len res) frames).
;
; 1 fn-cpg-msgid-seqs-of-pages
;   (implies (and P (nat-listp cands) (fn-mpx-ascendingp cands)
;                 (subsetp-equal (fn-cat$a-msgid-seqs msgid h) cands))
;            (equal (nth 0 (fn-cpg-msgid-seqs msgid cands dir pages res frames))
;                   (fn-cat$a-msgid-seqs msgid h)))
;   The COVER premise is the mlh's soundness (an answer is among the
;   candidates); it is about the index, not the pages, and is proved for the
;   mlh elsewhere.
;
; 2 fn-cpg-group-number-of-pages
;   (implies (and P (natp n)
;                 (equal cand (fn-cat$a-group-number group n h)))
;            (equal (nth 0 (fn-cpg-group-number group n cand dir pages res frames))
;                   (fn-cat$a-group-number group n h)))
;   The CAND premise is the dense map's existing correspondence
;   (fn-cp-group-number-is-seq).  The content is that the row read through the
;   pool confirms the number (the answer is never (:index-mismatch CAND)), so
;   this reader is a checked read, not a recomputation.
;
; 3 fn-cpg-msgid-seqs-fills / fn-cpg-group-number-fills (pages touched)
;   (implies (and P (nat-listp cands))
;            (<= (len (nth 2 (fn-cpg-msgid-seqs msgid cands dir pages res frames)))
;                (fn-cpg-bound cands h)))
;   fn-cpg-bound = the sum over the candidates below (len h) of
;   (1 + (fn-crow-pool-pages-of-row (fn-cp-row-of (nth c h)))), no term in
;   (len h).  NOTE for S: the program doc's "3 + the candidate rows' pages" is
;   not true of the crow tape: a row of W words starting mid page spans up to
;   ceil(W/2048) + 1 pages, so the straddle is one per candidate, not three in
;   all.  The three (two table pages for the lookup and one for the root) are
;   the page store's table fills (:need-table), which `fn-cpg-word' does not
;   see; they are an additive constant owed to the table model.  The group
;   number's bound is the same sum over the single candidate.
;
; 4 fn-cpg-fill-cap / fn-cpg-msgid-seqs-residency (the pool)
;   (<= (len (fn-cpg-fill p res frames)) (fn-cpg-cap frames))   [no premise]
;   (implies (and P (nat-listp cands))
;            (<= (len (nth 1 (fn-cpg-msgid-seqs msgid cands dir pages res frames)))
;                (fn-cpg-cap frames)))
;   and likewise for the group number.  Owed, named: the eviction is least
;   recent; "a frame the ledger allows" (books/page-read-ledger.lisp) is not
;   modelled -- one reader pins nothing -- and joins when a read holds a frame
;   across a yield.

(in-package "ACL2")
(include-book "catalog-pages")

; The pool holds at least one frame: a smaller profile cannot read at all.
(defun fn-cpg-cap (frames)
  (declare (xargs :guard t))
  (max 1 (nfix frames)))

; Resident pages, most recent first, all pages of the image.
(defun fn-cpg-res-okp (res pages)
  (declare (xargs :guard t))
  (if (consp res)
      (and (natp (car res)) (< (car res) (len pages)) (fn-cpg-res-okp (cdr res) pages))
    (null res)))

; The host's fill of page P into the pool: it becomes the most recent
; resident, the least recent leaves when the pool is full.
(defun fn-cpg-fill (p res frames)
  (declare (xargs :guard t :verify-guards nil))
  (take (fn-cpg-cap frames) (cons p (remove p res))))

; Word J (absolute) of the tape: the word, or the verdict.
(defun fn-cpg-word (j pages res)
  (declare (xargs :guard (natp j) :verify-guards nil))
  (let ((p (floor (nfix j) *pgs-page-words*)))
    (if (member p res)
        (nth (mod (nfix j) *pgs-page-words*) (nth p pages))
      (list :need-page p))))

; Word offsets of the rows and the end: N + 1 entries.
(defun fn-cpg-dir1 (rows off)
  (declare (xargs :guard (natp off) :verify-guards nil))
  (if (consp rows)
      (cons off (fn-cpg-dir1 (cdr rows) (+ off (len (adt-tp-rw *fn-crow-schema* (car rows))))))
    (list off)))

(defun fn-cpg-dir (rows)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cpg-dir1 rows 0))

(local
 (defthm fn-cpg-member-of-fill
   (member p (fn-cpg-fill p res frames))
   :hints (("Goal" :in-theory (enable fn-cpg-fill fn-cpg-cap)))))

; Read words [J, END) through the pool: a missing page is filled and the SAME
; word read again.  Returns (mv words res fills); FILLS the pages filled,
; most recent first.
(defun fn-cpg-read-words (j end pages res frames acc fills)
  (declare (xargs :guard (and (natp j) (natp end) (true-listp acc))
                  :measure (+ (* 2 (nfix (- (nfix end) (nfix j))))
                              (if (member (floor (nfix j) *pgs-page-words*) res) 0 1))
                  :verify-guards nil))
  (cond ((not (< (nfix j) (nfix end))) (mv (reverse acc) res fills))
        ((member (floor (nfix j) *pgs-page-words*) res)
         (fn-cpg-read-words (+ 1 (nfix j)) end pages res frames
                            (cons (fn-cpg-word j pages res) acc) fills))
        (t (let ((p (floor (nfix j) *pgs-page-words*)))
             (fn-cpg-read-words j end pages (fn-cpg-fill p res frames) frames acc (cons p fills))))))

; Row SEQ, decoded: (mv crow-row res fills).
(defun fn-cpg-read-row (seq dir pages res frames fills)
  (declare (xargs :guard (natp seq) :verify-guards nil))
  (mv-let (ws res fills)
    (fn-cpg-read-words (nth seq dir) (nth (+ 1 seq) dir) pages res frames nil fills)
    (mv (car (adt-tp-dseq *fn-crow-schema* ws)) res fills)))

(defun fn-cpg-msgid-loop (msgid cands dir pages res frames fills acc)
  (declare (xargs :guard (nat-listp cands) :verify-guards nil))
  (if (consp cands)
      (if (< (+ 1 (car cands)) (len dir))
          (mv-let (row res fills) (fn-cpg-read-row (car cands) dir pages res frames fills)
            (fn-cpg-msgid-loop msgid (cdr cands) dir pages res frames fills
                               (if (equal msgid (fn-record-msgid (fn-cp-row-held row)))
                                   (cons (car cands) acc)
                                 acc)))
        (fn-cpg-msgid-loop msgid (cdr cands) dir pages res frames fills acc))
    (mv (reverse acc) res fills)))

; The Message-ID reader: (list seqs res fills).
(defun fn-cpg-msgid-seqs (msgid cands dir pages res frames)
  (declare (xargs :guard (nat-listp cands) :verify-guards nil))
  (mv-let (seqs res fills) (fn-cpg-msgid-loop msgid cands dir pages res frames nil nil)
    (list seqs res fills)))

; The (group . number) reader, given the dense map's answer CAND (nil or a
; seq): (list answer res fills), the answer CAND, nil, or (:index-mismatch CAND).
(defun fn-cpg-group-number (group n cand dir pages res frames)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((null cand) (list nil res nil))
        ((not (and (natp cand) (< (+ 1 cand) (len dir)))) (list (list :index-mismatch cand) res nil))
        (t (mv-let (row res fills) (fn-cpg-read-row cand dir pages res frames nil)
             (let ((b (fn-held-number-in group (fn-cp-row-held row))))
               (if (and b (equal b n))
                   (list cand res fills)
                 (list (list :index-mismatch cand) res fills)))))))

; The pages-touched bound of statement 3.
(defun fn-cpg-bound (cands h)
  (declare (xargs :guard (nat-listp cands) :verify-guards nil))
  (if (consp cands)
      (+ (if (< (car cands) (len h))
             (+ 1 (fn-crow-pool-pages-of-row (fn-cp-row-of (nth (car cands) h))))
           0)
         (fn-cpg-bound (cdr cands) h))
    0))
