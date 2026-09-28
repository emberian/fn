; fn: teeth for books/history-records.lisp (lane arena-store-6, 2026-09-28).
(in-package "ACL2")
(include-book "../../books/history-records")
(include-book "must-fail-checked")

(local (in-theory (enable fn-hp-vhold-is-x fn-hrs-img-ok)))

; -----------------------------------------------------------------------------
; The host runs compiled code: every executable is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-hrc-at (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrc-append (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrc-fill (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrc-load (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrc-flush-one (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrecs-serve (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrecs-get (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hrecs-read (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; A ground history, loaded and flushed into the image.

(defconst *hrst-h* (list (list :retained 1 "<a@x>" (list 1 2 3) "subject line") (list :other 7 nil)))

;; A concrete holding *hrst-h* entirely in its image, at the canonical
;; placement, every page and table verified (the page store's arrays as the
;; lists they are logically; the octet buffer empty).
(defconst *hrst-np* (fn-hp-npages *hrst-h* 0))
(defconst *hrst-lens* (fn-hp-lens *hrst-h* 0))
(defconst *hrst-starts* (fn-hp-starts *hrst-h* 0))
(defconst *hrst-iw* (fn-hp-piw *hrst-h* 0 *hrst-starts* *hrst-np*))

(defun hrst-mem (w v)
  (update-nth *pgs-wi* w
              (update-nth *pgs-vi* v
                          (update-nth *pgs-di* (make-list *hrst-np* :initial-element 0)
                                      (update-nth *pgs-tvi* '(2) (list nil nil nil nil nil nil))))))

(defun hrst-c (w lo hi)
  (list (hrst-mem w (make-list *hrst-np* :initial-element 2)) nil 1 0 2 *hrst-lens* *hrst-starts* *hrst-np* 0 nil lo hi))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hrc-at-is-nth (the read over the concrete the export runs).

; Positive witness: every hypothesis, and the conclusion, at a record of the
; image and past the end.
(defthm hrst-at-witness
  (let ((c (hrst-c *hrst-iw* 0 0)))
    (and (fn-hrs-rel *hrst-h* c) (fn-hrc-wfp c) (natp 1) (natp 2)
         (equal (mv-nth 0 (fn-hrc-at 1 c)) :ok)
         (equal (mv-nth 1 (fn-hrc-at 1 c)) (list :ok (nth 1 *hrst-h*)))
         (equal (mv-nth 0 (fn-hrc-at 2 c)) :ok)
         (equal (mv-nth 1 (fn-hrc-at 2 c)) (list :refused :seq))))
  :rule-classes nil)

(defconst *hrst-row1-word* (+ (* 2048 (nth 4 *hrst-starts*)) (floor (fn-hp-pes-len (take 1 *hrst-h*)) 8)))

; Removal of the relation: a verified pool word of record 1 changed; the
; read answers :ok and not record 1.
(defthm hrst-at-rel-removal
  (let ((c (hrst-c (update-nth *hrst-row1-word* (logxor 1 (nth *hrst-row1-word* *hrst-iw*)) *hrst-iw*) 0 0)))
    (and (not (fn-hrs-rel *hrst-h* c)) (fn-hrc-wfp c) (natp 1)
         (equal (mv-nth 0 (fn-hrc-at 1 c)) :ok)
         (not (equal (mv-nth 1 (fn-hrc-at 1 c)) (list :ok (nth 1 *hrst-h*))))))
  :rule-classes nil)

; Removal of the shape: the suffix window starts at -1; the relation holds
; (an empty window), the read past the end answers a record.
(defthm hrst-at-wfp-removal
  (let ((c (hrst-c *hrst-iw* -1 0)))
    (and (fn-hrs-rel *hrst-h* c) (not (fn-hrc-wfp c)) (natp 2)
         (equal (mv-nth 0 (fn-hrc-at 2 c)) :ok)
         (not (equal (mv-nth 1 (fn-hrc-at 2 c)) (list :refused :seq)))))
  :hints (("Goal" :in-theory (enable fn-hrc-fields)))
  :rule-classes nil)

; Removal of (natp seq): SEQ -1 reads a cell before the image's.
(defthm hrst-at-natp-removal
  (let ((c (hrst-c *hrst-iw* 0 0)))
    (and (fn-hrs-rel *hrst-h* c) (fn-hrc-wfp c) (not (natp -1))
         (equal (mv-nth 0 (fn-hrc-at -1 c)) :ok)
         (not (equal (mv-nth 1 (fn-hrc-at -1 c))
                     (if (< -1 (len *hrst-h*)) (list :ok (nth -1 *hrst-h*)) (list :refused :seq))))))
  :hints (("Goal" :in-theory (enable fn-hrc-fields)))
  :rule-classes nil)

; The second conjunct: with record 1's cell page not verified, the read
; answers a need-verdict (never a record), for a record the history has.
(defconst *hrst-cell-page* (nth 0 *hrst-starts*))

(defthm hrst-at-need-witness
  (let ((c (list (hrst-mem *hrst-iw* (update-nth *hrst-cell-page* 0 (make-list *hrst-np* :initial-element 2)))
                 nil 1 0 2 *hrst-lens* *hrst-starts* *hrst-np* 0 nil 0 0)))
    (and (fn-hrs-rel *hrst-h* c) (fn-hrc-wfp c) (natp 1)
         (not (equal (mv-nth 0 (fn-hrc-at 1 c)) :ok))
         (< 1 (len *hrst-h*))
         (fn-hp-need-verdictp (mv-nth 0 (fn-hrc-at 1 c)))
         (equal (car (mv-nth 0 (fn-hrc-at 1 c))) :need-page)
         (equal (cadr (mv-nth 0 (fn-hrc-at 1 c))) *hrst-cell-page*)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The executable on live stobjs.
;
; (1) The exports (`fn-hrecs'): load a history, flush it into the image
; (the growth path relocates every region), read every record with the
; host's read (`fn-hrecs-read'; every page verified, so no fill is asked)
; and one past the end.  The answers are the list's.

(defun hrst-flush-all (k fn-hrecs)
  (declare (xargs :stobjs fn-hrecs :verify-guards nil))
  (if (zp k)
      (mv :ok fn-hrecs)
    (mv-let (v fn-hrecs) (fn-hrecs-flush fn-hrecs)
      (if (eq v :ok) (hrst-flush-all (1- k) fn-hrecs) (mv v fn-hrecs)))))

(defun hrst-reads (i n fn-hrecs)
  (declare (xargs :stobjs fn-hrecs :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i)))
      (mv nil fn-hrecs)
    (mv-let (v r fn-hrecs) (fn-hrecs-read (nfix i) 0 fn-hrecs)
      (mv-let (rest fn-hrecs) (hrst-reads (+ 1 (nfix i)) n fn-hrecs)
        (mv (cons (list v r) rest) fn-hrecs)))))

(defun hrst-live (events)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs
    (mv-let (res fn-hrecs)
      (let ((fn-hrecs (fn-hrecs-load events 0 fn-hrecs)))
        (mv-let (v fn-hrecs) (hrst-flush-all (len events) fn-hrecs)
          (mv-let (rs fn-hrecs) (hrst-reads 0 (+ 1 (len events)) fn-hrecs)
            (mv (list v (fn-hrecs-count fn-hrecs) rs) fn-hrecs))))
      res)))

(defun hrst-expect (events)
  (if (atom events) (list (list :ok (list :refused :seq)))
    (cons (list :ok (list :ok (car events))) (hrst-expect (cdr events)))))

(defun hrst-events (i n)
  ; N events: articles with 3000-octet bodies every fifth (the pool crosses
  ; pages), the rest short non-articles
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i)))
      nil
    (cons (if (equal (mod i 5) 0)
              (list :retained i "<m@x>" (make-list 3000 :initial-element (mod i 251)) "subject")
            (list :other i nil))
          (hrst-events (+ 1 (nfix i)) n))))

(assert-event (equal (hrst-live *hrst-h*) (list :ok 2 (hrst-expect *hrst-h*))))
(assert-event (let ((evs (hrst-events 0 40))) (equal (hrst-live evs) (list :ok 40 (hrst-expect evs)))))

; (2) The need path, on the concrete the exports run (`fn-hrecs$c'): after
; the flush, record 1's cell page P gets a table entry with its digest and
; is marked not verified (what an open leaves).  The read answers
; (:need-page P PHYS); a fill with P's words verifies it and the read then
; answers record 1.  A fill with other words is refused by the page
; store's check (:page-damaged), and the read still asks for P: a wrong
; page is never read.

(defun hrst-cflush-all (k fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (if (zp k)
      (mv :ok fn-hrecs$c)
    (mv-let (v fn-hrecs$c) (fn-hrc-flush-one fn-hrecs$c)
      (if (eq v :ok) (hrst-cflush-all (1- k) fn-hrecs$c) (mv v fn-hrecs$c)))))

(defun hrst-open-page (p phys pgs-mem fn-octets-pg)
  ; the table entry for P gets P's digest; P is marked not verified
  (declare (xargs :stobjs (pgs-mem fn-octets-pg) :verify-guards nil))
  (mv-let (d fn-octets-pg) (pgs-x-page-digest p pgs-mem fn-octets-pg)
    (let* ((pgs-mem (if (< (pgs-t-length pgs-mem) (* 2048 (pgs-tv-length pgs-mem)))
                        (resize-pgs-t (* 2048 (pgs-tv-length pgs-mem)) pgs-mem)
                      pgs-mem))
           (pgs-mem (pgs-x-set-entry 2 0 p (list phys 0 d) pgs-mem))
           (pgs-mem (update-pgs-vi p 0 pgs-mem)))
      (mv pgs-mem fn-octets-pg))))

(defun hrst-need (events bad fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (let ((fn-hrecs$c (fn-hrc-load events 0 fn-hrecs$c)))
    (mv-let (v0 fn-hrecs$c) (hrst-cflush-all (len events) fn-hrecs$c)
      (let* ((p (nth 0 (fn-hrc-starts fn-hrecs$c)))
             (words (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))) (ws) (fn-hp-x-words (* 2048 p) 2048 pgs-mem) ws))
             (words (if bad (cons (logxor 1 (car words)) (cdr words)) words))
             (fn-hrecs$c (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)) (fn-octets-pg (fn-hrc-oct fn-hrecs$c)))
                                    (pgs-mem fn-octets-pg)
                                    (hrst-open-page p 7 pgs-mem fn-octets-pg)
                                    fn-hrecs$c)))
        (mv-let (v1 r1) (fn-hrc-at 1 fn-hrecs$c)
          (declare (ignore r1))
          (mv-let (fv fn-hrecs$c) (fn-hrc-fill p words fn-hrecs$c)
            (mv-let (v2 r2) (fn-hrc-at 1 fn-hrecs$c)
              (mv (list v0 p v1 fv v2 r2) fn-hrecs$c))))))))

(defun hrst-need-run (events bad)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (res fn-hrecs$c) (hrst-need events bad fn-hrecs$c) res)))

(assert-event
 (let ((r (hrst-need-run *hrst-h* nil)))
   (and (equal (nth 0 r) :ok)
        (equal (nth 2 r) (list :need-page (nth 1 r) 7))
        (equal (nth 3 r) :ok)
        (equal (nth 4 r) :ok)
        (equal (nth 5 r) (list :ok (nth 1 *hrst-h*))))))

(assert-event
 (let ((r (hrst-need-run *hrst-h* t)))
   (and (equal (nth 2 r) (list :need-page (nth 1 r) 7))
        (equal (car (nth 3 r)) :page-damaged)
        (equal (nth 4 r) (list :need-page (nth 1 r) 7)))))

; -----------------------------------------------------------------------------
; The fill (fn-hrs-fill-pgs-vhold, the page-store step of fn-hrecs-fill and
; so of fn-hrecs-fill-keeps and fn-hrecs-serve-keeps).  Ground: the page
; store as a list, page P not verified, its table entry carrying the digest
; of the words the fill brings.  (The stobj-level keystones update the
; nested stobj through stobj-let, which ACL2 does not evaluate on ground
; lists in a proof; their executable witnesses are section (2) above.)

(defconst *hrst-p* *hrst-cell-page*)
(defconst *hrst-words* (take 2048 (nthcdr (* 2048 *hrst-p*) *hrst-iw*)))
(defconst *hrst-bad-words* (cons (logxor 1 (car *hrst-words*)) (cdr *hrst-words*)))

(defun hrst-open-mem0 ()
  (update-nth *pgs-ti* (make-list 2048 :initial-element 0)
              (hrst-mem *hrst-iw* (update-nth *hrst-p* 0 (make-list *hrst-np* :initial-element 2)))))

(defmacro hrst-open-mem (words)
  ; page P not verified; its table entry the digest of WORDS
  `(pgs-x-set-entry 2 0 *hrst-p*
                    (list 7 0 (mv-nth 0 (pgs-x-page-digest *hrst-p* (fn-hrs-put (* 2048 *hrst-p*) ,words (hrst-open-mem0)) nil)))
                    (hrst-open-mem0)))

; Positive witness: the words are the image's page; the fill verifies P and
; the verified pages still hold the image.
(defthm hrst-fill-witness
  (let* ((m (hrst-open-mem *hrst-words*))
         (r (fn-hrs-fill-pgs *hrst-p* *hrst-words* 0 m nil)))
    (and (natp *hrst-p*) (true-listp *hrst-iw*)
         (fn-hp-vhold 0 (pgs-v-length m) m *hrst-iw*)
         (< *hrst-p* (pgs-v-length m)) (not (equal (pgs-vi *hrst-p* m) 2))
         (equal *hrst-words* (take 2048 (nthcdr (* 2048 *hrst-p*) *hrst-iw*)))
         (equal (mv-nth 0 r) :ok)
         (equal (pgs-vi *hrst-p* (mv-nth 1 r)) 2)
         (equal (pgs-v-length (mv-nth 1 r)) (pgs-v-length m))
         (fn-hp-vhold 0 (pgs-v-length (mv-nth 1 r)) (mv-nth 1 r) *hrst-iw*)))
  :rule-classes nil)

; Removal of "the words are the image's page": a table entry that names
; other words' digest (what a page file that does not hold the image's
; page, and a table that matches it, would give) is accepted, and the
; verified page no longer holds the image.  The digest check alone does not
; make a fill faithful; the page file's relation (fn-hrecs-disk-faithful)
; does.
(defthm hrst-fill-words-removal
  (let* ((m (hrst-open-mem *hrst-bad-words*))
         (r (fn-hrs-fill-pgs *hrst-p* *hrst-bad-words* 0 m nil)))
    (and (natp *hrst-p*) (true-listp *hrst-iw*)
         (fn-hp-vhold 0 (pgs-v-length m) m *hrst-iw*)
         (< *hrst-p* (pgs-v-length m)) (not (equal (pgs-vi *hrst-p* m) 2))
         (not (equal *hrst-bad-words* (take 2048 (nthcdr (* 2048 *hrst-p*) *hrst-iw*))))
         (equal (mv-nth 0 r) :ok)
         (not (fn-hp-vhold 0 (pgs-v-length (mv-nth 1 r)) (mv-nth 1 r) *hrst-iw*))))
  :rule-classes nil)
