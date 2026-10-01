; fn: teeth for books/history-records-disk.lisp and books/store-records-field.lisp
; (lane arena-store-7, 2026-09-28, milestone (b1)).
;
; The page file is data here: FILE is an alist (PHYS . WORDS), and the host's
; page fill (A-PGS-HOST-IO's fn-pgs-page-words / fn-pgs-fill-realize) is
; attached to its lookup, so the decode EXECUTES over a committed image.  A
; history is loaded and flushed into an image (fn-hrc-flush-one), the image
; committed as a fresh page file's first transaction (pgs-x-commit), the
; pages it writes collected into FILE, and the handle made from the record
; and the image's header.  The keystones about the decode are witnessed by
; these live runs (the decode reads the page file through the attachment,
; which a proof cannot evaluate); their hypotheses are asserted in executed
; form (hrdt-holds: fn-hrs-disk-holds's parts).
(in-package "ACL2")
(include-book "../../books/store-records-field")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; The host runs compiled code: every executable is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-hrs-disk-history (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrs-disk-decode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrc-open-file (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrc-get (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrc-rows (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sfr-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sfr-snoc (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sfr-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sfr-last (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sfr-nth (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The page file as data.

(defun hrdt-page (file addr)
  (declare (xargs :guard t))
  (let ((w (cdr (hons-assoc-equal addr file))))
    (if (and (true-listp w) (equal (len w) 2048) (fn-pgs-u64-listp w)) w (make-list 2048 :initial-element 0))))

(defthm hrdt-page-shape
  (and (true-listp (hrdt-page file addr)) (equal (len (hrdt-page file addr)) 2048)
       (fn-pgs-u64-listp (hrdt-page file addr))))

(defattach (fn-pgs-page-words hrdt-page) (fn-pgs-fill-realize hrdt-page))
; the frame fill (A-PGS-HOST-IO's in-place form): the put of the same page
(defattach fn-pgs-fill-frame fn-pgs-fill-frame-via-words)

; -----------------------------------------------------------------------------
; Teeth for fn-pgs-fill-frame-is-frame-put, A-PGS-HOST-IO.
; Snapshot ALL six arrays: equality below compares the complete logical
; poststates of fill and (fn-pgs-frame-put sel base
;                       (fn-pgs-page-words file addr) pgs-mem).
; Each run starts from the same reachable constructor/resize/put state.
(local (defun hrdt-ramp-page (n)
         (declare (xargs :measure (nfix n)))
         (if (zp n) nil
           (append (hrdt-ramp-page (1- n)) (list n)))))

(local (defun hrdt-frame-array (sel i n pgs-mem)
         (declare (xargs :stobjs pgs-mem :verify-guards nil
                         :measure (nfix (- (nfix n) (nfix i)))))
         (if (zp (- (nfix n) (nfix i))) nil
           (cons (case sel
                   (0 (pgs-wi i pgs-mem)) (1 (pgs-mi i pgs-mem))
                   (2 (pgs-ti i pgs-mem)) (3 (pgs-di i pgs-mem))
                   (4 (pgs-vi i pgs-mem)) (otherwise (pgs-tvi i pgs-mem)))
                 (hrdt-frame-array sel (+ 1 (nfix i)) n pgs-mem)))))

(local (defun hrdt-frame-value (pgs-mem)
         (declare (xargs :stobjs pgs-mem :verify-guards nil))
         (list (hrdt-frame-array 0 0 (pgs-w-length pgs-mem) pgs-mem)
               (hrdt-frame-array 1 0 (pgs-m-length pgs-mem) pgs-mem)
               (hrdt-frame-array 2 0 (pgs-t-length pgs-mem) pgs-mem)
               (hrdt-frame-array 3 0 (pgs-d-length pgs-mem) pgs-mem)
               (hrdt-frame-array 4 0 (pgs-v-length pgs-mem) pgs-mem)
               (hrdt-frame-array 5 0 (pgs-tv-length pgs-mem) pgs-mem))))

; MUTANT, test-local: write at BASE+K+1 instead of BASE+K.
(local (defun hrdt-frame-offset-mutant (base ws pgs-mem)
         (declare (xargs :stobjs pgs-mem :verify-guards nil))
         (if (atom ws) pgs-mem
           (let ((pgs-mem (update-pgs-wi (+ 1 (nfix base)) (car ws) pgs-mem)))
             (hrdt-frame-offset-mutant (+ 1 (nfix base)) (cdr ws) pgs-mem)))))

(local (defun hrdt-frame-run (mode)
         (declare (xargs :verify-guards nil))
         (with-local-stobj pgs-mem
           (mv-let (out pgs-mem)
             (let* ((sel 0) (base 0) (addr 3)
                    (page (hrdt-ramp-page 2048))
                    (file (list (cons addr page)))
                    (pgs-mem (resize-pgs-w 2049 pgs-mem))
                    (pgs-mem (fn-pgs-frame-put
                              sel base (make-list 2049 :initial-element 7) pgs-mem))
                    (antecedent
                     (and (pgs-memp pgs-mem) (fn-pgs-frame-sel-p sel) (natp base)
                          (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem))
                          (fn-pgs-u64-listp page) (equal (len page) 2048)
                          (equal (fn-pgs-page-words file addr) page)
                          (<= (+ base 1 (len page)) (fn-pgs-frame-len sel pgs-mem))))
                    (pgs-mem
                     (case mode
                       (:fill (fn-pgs-fill-frame file addr sel base pgs-mem))
                       (:put (fn-pgs-frame-put sel base (fn-pgs-page-words file addr) pgs-mem))
                       (:mutant (hrdt-frame-offset-mutant base page pgs-mem))
                       (otherwise pgs-mem))))
               (mv (list antecedent (hrdt-frame-value pgs-mem)) pgs-mem))
             out))))

; REACHABLE POSITIVE: complete guard and whole-state equation, evaluated
; through fn-pgs-fill-frame's model attachment (not a theorem rewrite).
(assert-event
 (let ((filled (hrdt-frame-run :fill)) (put (hrdt-frame-run :put)))
   (and (car filled) (car put) (equal (cadr filled) (cadr put)))))

; LABELLED MUTATION witness (not hypothesis removal or corrupted state).
; Both ranges fit.  The intended fill preserves the extra sentinel; the
; shifted fill preserves the first sentinel and overwrites the extra one.
(assert-event
 (let* ((initial (hrdt-frame-run :initial))
        (filled (hrdt-frame-run :fill)) (put (hrdt-frame-run :put))
        (mutant (hrdt-frame-run :mutant))
        (correct-words (car (cadr filled))) (mutant-words (car (cadr mutant))))
   (and (car initial) (car filled) (car put) (car mutant)
        (equal (car (cadr initial)) (make-list 2049 :initial-element 7))
        (equal (cadr filled) (cadr put))
        (equal (nth 0 correct-words) 1) (equal (nth 2048 correct-words) 7)
        (equal (nth 0 mutant-words) 7) (equal (nth 2048 mutant-words) 2048)
        (not (equal (cadr mutant) (cadr put))))))

(defun hrdt-events (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i)))
      nil
    (cons (if (equal (mod i 5) 0)
              (list :retained i "<m@x>" (make-list 3000 :initial-element (mod i 251)) "subject")
            (list :other i nil))
          (hrdt-events (+ 1 (nfix i)) n))))

(defun hrdt-flush-all (k fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (if (zp k)
      (mv :ok fn-hrecs$c)
    (mv-let (v fn-hrecs$c) (fn-hrc-flush-one fn-hrecs$c)
      (if (eq v :ok) (hrdt-flush-all (1- k) fn-hrecs$c) (mv v fn-hrecs$c)))))

(defun hrdt-w-words (a k pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil :measure (nfix k)))
  (if (zp k) nil (cons (pgs-wi a pgs-mem) (hrdt-w-words (+ 1 a) (- k 1) pgs-mem))))

(defun hrdt-w-page (lp pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (hrdt-w-words (* 2048 lp) 2048 pgs-mem))

(defun hrdt-data-writes (lpages fresh pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (or (atom lpages) (atom fresh)) nil
    (cons (cons (car fresh) (hrdt-w-page (car lpages) pgs-mem))
          (hrdt-data-writes (cdr lpages) (cdr fresh) pgs-mem))))

(defun hrdt-table-writes (tl tfresh pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (or (atom tl) (atom tfresh)) nil
    (cons (cons (car tfresh) (pgs-x-words 2 (* 2048 (car tl)) 2048 pgs-mem))
          (hrdt-table-writes (cdr tl) (cdr tfresh) pgs-mem))))

(defun hrdt-dir-writes (rs j m pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil :measure (nfix (- (nfix m) (nfix j)))))
  (if (zp (- (nfix m) (nfix j))) nil
    (cons (cons (+ rs j) (pgs-x-words 1 (+ *pgs-x-dir-base* (* 2048 j)) 2048 pgs-mem))
          (hrdt-dir-writes rs (+ 1 (nfix j)) m pgs-mem))))

(defun hrdt-commit-pgs (bad pgs-mem fn-octets-pg)
  ; The image in PGS-MEM committed as the first transaction of a fresh page
  ; file: (mv RESULT FILE pgs-mem fn-octets-pg), FILE the pages written.
  (declare (xargs :stobjs (pgs-mem fn-octets-pg) :verify-guards nil))
  ; BAD (a page number or nil): the commit digests page BAD with its first
  ; word changed, and the file holds the page as the image has it -- tables,
  ; directory and record all consistent with a digest the page does not have.
  (let* ((pgs-mem (resize-pgs-m (+ *pgs-x-dir-base* 2048) pgs-mem))
         (lpages (pgs-x-dirty-list (pgs-v-length pgs-mem) nil pgs-mem))
         (w0 (if bad (pgs-wi (* 2048 bad) pgs-mem) 0))
         (pgs-mem (if bad (update-pgs-wi (* 2048 bad) (logxor w0 1) pgs-mem) pgs-mem)))
    (mv-let (res pgs-mem fn-octets-pg)
      (pgs-x-commit lpages 0 1 (list nil 1) 0 pgs-mem fn-octets-pg)
     (let ((pgs-mem (if bad (update-pgs-wi (* 2048 bad) w0 pgs-mem) pgs-mem)))
      (if (not (and (consp res) (eq (car res) :plan)))
          (mv res nil pgs-mem fn-octets-pg)
        (let ((fresh (nth 2 res)) (tl (nth 3 res)) (tfresh (nth 4 res)) (rs (nth 5 res)) (m (nth 6 res)))
          (mv res
              (append (hrdt-data-writes lpages fresh pgs-mem)
                      (hrdt-table-writes tl tfresh pgs-mem)
                      (hrdt-dir-writes rs 0 m pgs-mem))
              pgs-mem fn-octets-pg)))))))

(defun hrdt-build (events salt bad)
  ; EVENTS flushed into an image and committed:
  ; (list FLUSH-VERDICT COMMIT-RESULT FILE HANDLE).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (let ((fn-hrecs$c (fn-hrc-load events salt fn-hrecs$c)))
        (mv-let (v fn-hrecs$c) (hrdt-flush-all (len events) fn-hrecs$c)
          (mv-let (res file fn-hrecs$c)
            (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))
                        (fn-octets-pg (fn-hrc-oct fn-hrecs$c)))
                       (res file pgs-mem fn-octets-pg)
                       (hrdt-commit-pgs bad pgs-mem fn-octets-pg)
                       (mv res file fn-hrecs$c))
            (mv (list v res file
                      (fn-hrs-handle file (and (consp res) (nth 1 res)) salt (fn-hrc-nimg fn-hrecs$c)
                                     (fn-hrc-lens fn-hrecs$c) (fn-hrc-starts fn-hrecs$c) (fn-hrc-npages fn-hrecs$c)))
                fn-hrecs$c))))
      out)))


(defun hrdt-pages-hold (p n file h salt starts np fn-hrecs$c)
  ; every page P..N-1: the page file at the address the loaded table names
  ; holds H's placed image page (fn-hrs-disk-ok's body, executed)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil :measure (nfix (- (nfix n) (nfix p)))))
  (if (zp (- (nfix n) (nfix p))) t
    (and (equal (hrdt-page file (fn-hrc-phys (nfix p) fn-hrecs$c))
                (take 2048 (nthcdr (* 2048 (nfix p)) (fn-hp-piw h salt starts np))))
         (hrdt-pages-hold (+ 1 (nfix p)) n file h salt starts np fn-hrecs$c))))

(defun hrdt-none-verified (p n fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil :measure (nfix (- (nfix n) (nfix p)))))
  (if (zp (- (nfix n) (nfix p))) t
    (and (not (equal (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))) (x) (pgs-vi (nfix p) pgs-mem) x) 2))
         (hrdt-none-verified (+ 1 (nfix p)) n fn-hrecs$c))))

(defun hrdt-holds (handle h)
  ; fn-hrs-disk-holds HANDLE H, its parts executed over the attached page
  ; file: the open lands; the concrete holds H (header H's, count H's
  ; length, empty suffix, no page verified yet); the file holds H's image
  ; page at the loaded table's address for every page.
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (ok fn-hrecs$c)
      (mv-let (v fn-hrecs$c) (fn-hrc-open-file handle fn-hrecs$c)
        (let ((salt (fn-hrc-salt fn-hrecs$c)) (starts (fn-hrc-starts fn-hrecs$c))
              (np (fn-hrc-npages fn-hrecs$c)) (vlen (fn-hrc-vlen fn-hrecs$c)))
          (mv (list (null v)
                    (fn-hp-okp h salt)
                    (equal (fn-hrc-lens fn-hrecs$c) (fn-hp-lens h salt))
                    (adt-placement-ok starts (fn-hrc-lens fn-hrecs$c) np)
                    (equal (fn-hrc-nimg fn-hrecs$c) (len h))
                    (equal (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c))
                    (hrdt-none-verified 0 vlen fn-hrecs$c)
                    (hrdt-pages-hold 0 vlen (fn-hrs-h-file handle) h salt starts np fn-hrecs$c))
              fn-hrecs$c)))
      ok)))


; -----------------------------------------------------------------------------
; Three committed images: 40 events (every fifth a 3000-octet article, so
; the pool crosses pages); a different history; the first again with its
; last image page (a pool page the rows read; page 0, the header, the
; handle carries) digested with one word changed.

(defun hrdt-decode (handle)
  (declare (xargs :guard (fn-hrs-handlep handle)))
  (mv-let (clean rows) (fn-hrs-disk-decode handle) (list clean rows)))

(defconst *hrdt-evs* (hrdt-events 0 40))
(defconst *hrdt-evs2* (hrdt-events 3 43))
(defconst *hrdt-b* (hrdt-build *hrdt-evs* 5 nil))
(defconst *hrdt-b2* (hrdt-build *hrdt-evs2* 5 nil))
(defconst *hrdt-np* (nth 7 (fourth *hrdt-b*)))
(defconst *hrdt-bm* (hrdt-build *hrdt-evs* 5 (1- *hrdt-np*)))
(defconst *hrdt-handle* (fourth *hrdt-b*))
(defconst *hrdt-handle2* (fourth *hrdt-b2*))
(defconst *hrdt-handlem* (fourth *hrdt-bm*))

(assert-event (and (equal (first *hrdt-b*) :ok) (eq (car (second *hrdt-b*)) :plan)
                   (equal (first *hrdt-b2*) :ok) (eq (car (second *hrdt-b2*)) :plan)
                   (equal (first *hrdt-bm*) :ok) (eq (car (second *hrdt-bm*)) :plan)
                   (fn-hrs-handlep *hrdt-handle*) (fn-hrs-handlep *hrdt-handle2*)
                   (fn-hrs-handlep *hrdt-handlem*)
                   (not (equal *hrdt-evs* *hrdt-evs2*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hrs-disk-history-is-image (live-run witnesses).

; Positive: every hypothesis (fn-hrs-handlep; fn-hrs-disk-holds's parts;
; the clean decode) and the conclusion.
(assert-event (equal (hrdt-holds *hrdt-handle* *hrdt-evs*) (list t t t t t t t t)))
(assert-event (equal (hrdt-decode *hrdt-handle*) (list t *hrdt-evs*)))
(assert-event (equal (fn-hrs-disk-history *hrdt-handle*) *hrdt-evs*))

; Removal of fn-hrs-disk-holds: the handle of another history's image.  The
; handle is one and the decode is clean (retained); the page file does not
; hold *hrdt-evs*'s image (the omitted hypothesis fails at its pages); the
; history is not *hrdt-evs*.
(assert-event (fn-hrs-handlep *hrdt-handle2*))
(assert-event (car (hrdt-decode *hrdt-handle2*)))
(assert-event (not (car (last (hrdt-holds *hrdt-handle2* *hrdt-evs*)))))
(assert-event (not (equal (fn-hrs-disk-history *hrdt-handle2*) *hrdt-evs*)))
(assert-event (equal (fn-hrs-disk-history *hrdt-handle2*) *hrdt-evs2*))

; Removal of the clean decode: the last page's table entry names a digest the
; page does not have (tables, directory and record consistent with it).  The
; handle is one and the page file holds *hrdt-evs*'s image at every address
; (retained: every part of fn-hrs-disk-holds); the decode is not clean (the
; omitted hypothesis fails: the page store refuses the page); its rows are not
; *hrdt-evs*; and the history names the fault instead of answering.
(assert-event (fn-hrs-handlep *hrdt-handlem*))
(assert-event (equal (hrdt-holds *hrdt-handlem* *hrdt-evs*) (list t t t t t t t t)))
(assert-event (not (car (hrdt-decode *hrdt-handlem*))))
(assert-event (not (equal (cadr (hrdt-decode *hrdt-handlem*)) *hrdt-evs*)))
(must-fail-checked (assert-event (consp (fn-hrs-disk-history *hrdt-handlem*))))

; Mutation (a corrupted page file): one word of the last image page as
; the page file holds it changed.  fn-hrs-disk-holds fails there, the page store's
; digest check refuses the page, the decode is not clean.
(defconst *hrdt-bad-file*
  ; the data writes come first, in page order: the last image page's
  (let* ((file (third *hrdt-b*)) (k (1- *hrdt-np*)) (e (nth k file)))
    (append (take k file)
            (list (cons (car e) (cons (logxor 1 (cadr e)) (cddr e))))
            (nthcdr (+ 1 k) file))))
(defconst *hrdt-bad-handle* (fn-hrs-handle *hrdt-bad-file* (nth 2 *hrdt-handle*) (nth 3 *hrdt-handle*)
                                           (nth 4 *hrdt-handle*) (nth 5 *hrdt-handle*)
                                           (nth 6 *hrdt-handle*) (nth 7 *hrdt-handle*)))
(assert-event (not (car (last (hrdt-holds *hrdt-bad-handle* *hrdt-evs*)))))
(assert-event (not (car (hrdt-decode *hrdt-bad-handle*))))

; fn-hrs-disk-history-len: exactly N rows, clean or not.
(assert-event (and (equal (len (cadr (hrdt-decode *hrdt-handlem*))) 40)
                   (equal (len (cadr (hrdt-decode *hrdt-bad-handle*))) 40)))

; -----------------------------------------------------------------------------
; The records field over the image (books/store-records-field.lisp).

; KEYSTONE fn-sfr-list-of-fn-sfr-based(-is-image), live: the image's history
; then the suffix; the O(1) readers answer the list's count, last and I-th.
(defconst *hrdt-sfx* (list '(:other 900 nil) '(:other 901 nil)))
(defconst *hrdt-f* (fn-sfr-based *hrdt-handle* (fn-sl-of *hrdt-sfx*)))
(assert-event (equal (fn-sfr-list *hrdt-f*) (append *hrdt-evs* *hrdt-sfx*)))
(assert-event (and (equal (fn-sfr-count *hrdt-f*) 42)
                   (equal (fn-sfr-last *hrdt-f*) '(:other 901 nil))
                   (equal (fn-sfr-nth 41 *hrdt-f*) '(:other 901 nil))
                   (equal (fn-sfr-nth 3 *hrdt-f*) (nth 3 *hrdt-evs*))
                   (fn-sfr-canonp *hrdt-f*)))
; KEYSTONE fn-sfr-list-of-fn-sfr-snoc over a based field: one record onto
; the suffix, the image untouched.
(assert-event (let ((f2 (fn-sfr-snoc *hrdt-f* '(:other 902 nil))))
                (and (equal (fn-sfr-list f2) (append *hrdt-evs* *hrdt-sfx* (list '(:other 902 nil))))
                     (equal (fn-sfr-handle f2) *hrdt-handle*)
                     (equal (fn-sfr-count f2) 43))))
; With nothing appended since the image, the last record is the image's.
(assert-event (equal (fn-sfr-last (fn-sfr-based *hrdt-handle* (fn-sl-of nil))) (car (last *hrdt-evs*))))

; KEYSTONE fn-sfr-list-of-fn-sl-of, ground: an unbased field reads its list
; back, and fn-sl-of never builds a based value -- even of a list that
; starts with the tag and a handle.
(defthm hrdt-sl-of-witness
  (let ((x (list :hrs-based (fn-hrs-handle 0 nil 0 0 '(0 0 0 0 0) '(1 1 1 1 1) 0) 'r)))
    (and (not (fn-sfr-basedp (fn-sl-of x)))
         (equal (fn-sfr-list (fn-sl-of x)) x))))
