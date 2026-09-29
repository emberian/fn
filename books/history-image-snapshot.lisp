; fn: the history image written by the checkpoint and adopted by the open
; (lane composed-owner, 2026-09-29, the served half of rows A2 and A5).
; Prefix fn-his-.
;
; The served checkpoint (store-checkpoint.fnsc) carries the history image
; INSIDE its file: after the framed segments (the arena run, then the tables)
; the file is padded to a 16 KiB boundary and holds the image's page store
; pages at their physical addresses from there (page 0, the root slots'
; page, is not written: the root record travels in the F row, protected by
; the table segment's trailer).  One file, one rename: the image and the
; fold state are ONE durable write, so no crash between two publications
; exists, and the binding (books/history-image-binding.lisp, :hib NODE CODEC
; COUNT TRAIL REC SALT) rides in the F row's log position.
;
; The writer here (the publication thread, over its own concrete): the
; records loaded and flushed into an image on a fresh page store
; (`fn-his-build'), committed as transaction 1 (`fn-his-commit', the page
; store's `pgs-x-commit'); the host writes the pages the plan names from
; `fn-his-page-words'.  The open adopts it through `fn-hib-open' with the
; binding's record as the only root slot (`fn-his-open').
(in-package "ACL2")
(include-book "history-image-fold")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The writer.

(defun fn-his-flush-all (k fn-hrecs$c)
  ; K flushes (the oldest suffix record into the image each), stopping at
  ; the first that does not answer :ok.
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp k) (fn-hrc-wfp fn-hrecs$c)) :measure (nfix k)
                  :guard-hints (("Goal" :in-theory (disable fn-hrc-flush-one fn-hrc-wfp)))))
  (if (zp k)
      (mv :ok fn-hrecs$c)
    (mv-let (v fn-hrecs$c) (fn-hrc-flush-one fn-hrecs$c)
      (if (eq v :ok) (fn-his-flush-all (1- k) fn-hrecs$c) (mv v fn-hrecs$c)))))

(defthm fn-his-flush-all-wfp
  (implies (fn-hrc-wfp fn-hrecs$c) (fn-hrc-wfp (mv-nth 1 (fn-his-flush-all k fn-hrecs$c))))
  :hints (("Goal" :induct (fn-his-flush-all k fn-hrecs$c) :in-theory (disable fn-hrc-flush-one fn-hrc-wfp))))

(defthm fn-his-load-wfp
  (implies (and (natp salt) (true-listp records)) (fn-hrc-wfp (fn-hrc-load records salt fn-hrecs$c)))
  :hints (("Goal" :in-theory (disable fn-hrc-reset fn-hrc-wfp fn-hrc-load-events))))

(defun fn-his-build (records salt fn-hrecs$c)
  ; RECORDS (the checkpoint's, oldest first) as the image on a fresh page
  ; store: loaded, then flushed into the image one by one.  (mv VERDICT
  ; fn-hrecs$c): :ok when every record is in the image (the suffix empty),
  ; else the flush's verdict (a record the image cannot hold is refused by
  ; name, never dropped).
  (declare (xargs :stobjs fn-hrecs$c :guard (and (true-listp records) (natp salt))
                  :guard-hints (("Goal" :in-theory (disable fn-hrc-load fn-his-flush-all fn-hrc-wfp)))))
  (let ((fn-hrecs$c (fn-hrc-load records salt fn-hrecs$c)))
    (mv-let (v fn-hrecs$c) (fn-his-flush-all (len records) fn-hrecs$c)
      (cond ((not (eq v :ok)) (mv v fn-hrecs$c))
            ((not (equal (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c))) (mv (list :refused :suffix) fn-hrecs$c))
            (t (mv :ok fn-hrecs$c))))))

(defthm fn-his-nat-listp-dirty-list
  (implies (nat-listp acc) (nat-listp (pgs-x-dirty-list j acc pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-dirty-list))))

(defun fn-his-commit-pgs (pgs-mem fn-octets-pg)
  ; The image's dirty pages committed as transaction 1 of a fresh page store
  ; (allocation from address 1: address 0 is the root slots' page), the
  ; record into slot 0: (mv RESULT pgs-mem fn-octets-pg), RESULT the page
  ; store's (:plan RECORD FRESH TL TFRESH RUN-START M ALLOC2 ...) or its
  ; refusal.
  (declare (xargs :stobjs (pgs-mem fn-octets-pg)))
  (let ((pgs-mem (if (< (pgs-m-length pgs-mem) (+ *pgs-x-dir-base* 2048))
                     (resize-pgs-m (+ *pgs-x-dir-base* 2048) pgs-mem)
                   pgs-mem)))
    (if (not (<= (pgs-v-length pgs-mem) (pgs-d-length pgs-mem)))
        (mv (list :refused :image-shape) pgs-mem fn-octets-pg)
      (pgs-x-commit (pgs-x-dirty-list (pgs-v-length pgs-mem) nil pgs-mem) 0 1 (list nil 1) 0 pgs-mem fn-octets-pg))))

(defun fn-his-commit (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c
                  :guard-hints (("Goal" :in-theory (disable fn-his-commit-pgs)))))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))
              (fn-octets-pg (fn-hrc-oct fn-hrecs$c)))
             (res pgs-mem fn-octets-pg)
             (fn-his-commit-pgs pgs-mem fn-octets-pg)
             (mv res fn-hrecs$c)))

(defun fn-his-words (sel a fn-hrecs$c)
  ; the 2048 words from word A of array SEL of the image's page store (0 the
  ; image's data pages, 1 the metadata: the directory run from
  ; *pgs-x-dir-base*, 2 the table pages), for the host to write; nil when
  ; they are not there
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp sel) (natp a))))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (ws)
             (if (<= (+ a 2048) (pgs-x-len sel pgs-mem)) (pgs-x-words sel a 2048 pgs-mem) nil)
             ws))

(defun fn-his-page-writes (lpages fresh acc)
  ; the data pages: logical page L at the fresh address F (array 0)
  (declare (xargs :guard (and (true-listp lpages) (true-listp fresh) (true-listp acc))))
  (if (or (atom lpages) (atom fresh))
      (revappend acc nil)
    (fn-his-page-writes (cdr lpages) (cdr fresh)
                        (cons (list (nfix (car fresh)) 0 (* 2048 (nfix (car lpages)))) acc))))

(defun fn-his-table-writes (tl tfresh acc)
  ; the touched table pages: table page TP at the fresh address F (array 2)
  (declare (xargs :guard (and (true-listp tl) (true-listp tfresh) (true-listp acc))))
  (if (or (atom tl) (atom tfresh))
      (revappend acc nil)
    (fn-his-table-writes (cdr tl) (cdr tfresh)
                         (cons (list (nfix (car tfresh)) 2 (* 2048 (nfix (car tl)))) acc))))

(defun fn-his-dir-writes (run-start j m acc)
  ; the directory run: its page J at RUN-START + J (array 1, from the base)
  (declare (xargs :guard (and (natp run-start) (natp j) (natp m) (true-listp acc))
                  :measure (nfix (- (nfix m) (nfix j)))))
  (if (mbe :logic (zp (- (nfix m) (nfix j))) :exec (<= m j))
      (revappend acc nil)
    (fn-his-dir-writes run-start (+ 1 (nfix j)) m
                       (cons (list (+ run-start (nfix j)) 1 (+ *pgs-x-dir-base* (* 2048 (nfix j)))) acc))))


(defun fn-his-plan-okp (res)
  (declare (xargs :guard t))
  (and (true-listp res) (eq (car res) :plan) (<= 8 (len res))
       (true-listp (nth 2 res)) (true-listp (nth 3 res)) (true-listp (nth 4 res))
       (natp (nth 5 res)) (natp (nth 6 res))))

(defun fn-his-plan-writes (lpages res)
  ; the pages the commit plan RES writes, each (ADDR SEL A)
  (declare (xargs :guard (and (true-listp lpages) (fn-his-plan-okp res))))
  (append (fn-his-page-writes lpages (nth 2 res) nil)
          (fn-his-table-writes (nth 3 res) (nth 4 res) nil)
          (fn-his-dir-writes (nth 5 res) 0 (nth 6 res) nil)))

(defthm fn-his-true-listp-dirty-list
  (implies (true-listp acc) (true-listp (pgs-x-dirty-list j acc pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-dirty-list))))

(defun fn-his-lpages (fn-hrecs$c)
  ; the image's dirty pages, ascending
  (declare (xargs :stobjs fn-hrecs$c))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (l)
             (if (<= (pgs-v-length pgs-mem) (pgs-d-length pgs-mem))
                 (pgs-x-dirty-list (pgs-v-length pgs-mem) nil pgs-mem)
               nil)
             l))

(defthm fn-his-true-listp-lpages
  (true-listp (fn-his-lpages fn-hrecs$c))
  :rule-classes :type-prescription)


(defthm fn-his-plan-okp-true-listp
  (implies (fn-his-plan-okp res) (true-listp res))
  :rule-classes :forward-chaining)

(defun fn-his-snapshot (records salt fn-hrecs$c)
  ; The publication's image: RECORDS built into an image on a fresh page
  ; store and committed.  (mv VERDICT REC WRITES fn-hrecs$c): :ok, the
  ; commit record, and the pages to write, each (ADDR SEL A): the 2048 words
  ; from word A of array SEL (`fn-his-words') at page address ADDR; else the
  ; build's or the commit's refusal by name and nothing to write.
  (declare (xargs :stobjs fn-hrecs$c :guard (and (true-listp records) (natp salt))
                  :guard-hints (("Goal" :in-theory (union-theories '(fn-his-plan-okp-true-listp fn-his-true-listp-lpages natp (:e natp)
                                                                     true-listp (:e true-listp))
                                                                   (theory 'minimal-theory))))))
  (mv-let (v fn-hrecs$c) (fn-his-build records salt fn-hrecs$c)
    (if (not (eq v :ok))
        (mv v nil nil fn-hrecs$c)
      (let ((lpages (fn-his-lpages fn-hrecs$c)))
        (mv-let (res fn-hrecs$c) (fn-his-commit fn-hrecs$c)
          (if (not (fn-his-plan-okp res))
              (mv (if (consp res) res (list :refused :commit)) nil nil fn-hrecs$c)
            (mv :ok (nth 1 res) (fn-his-plan-writes lpages res) fn-hrecs$c)))))))

(defun fn-his-release (fn-hrecs$c)
  ; The concrete emptied (the page store's arrays given back): after the
  ; publication has written the image, and after the open's check, the
  ; words of a whole image are not kept.  Decides nothing.
  (declare (xargs :stobjs fn-hrecs$c))
  (fn-hrc-reset 0 fn-hrecs$c))

; -----------------------------------------------------------------------------
; The open.

(defun fn-his-open (b node salt trail file fn-hrecs$c)
  ; The open's adoption of the image in the checkpoint's file: the
  ; binding's record is the only root (the F row carries it, the table
  ; segment's trailer protects it); `fn-hib-open' checks the binding against
  ; the store (NODE, SALT: the genesis record's), the log (TRAIL: the chain
  ; value the suffix continues from) and the codec, then adopts.
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory (union-theories '(fn-hib-bindingp (:t true-list-fix)) (theory 'minimal-theory))))))
  (if (not (fn-hib-bindingp b))
      (mv (list :refused :binding) fn-hrecs$c)
    (let ((rec (fn-hib-b-rec b)))
      (fn-hib-open b node salt trail (list (list rec (nth 5 (true-list-fix rec)))) file fn-hrecs$c))))

(defun fn-his-check-row (seq expected file fn-hrecs$c)
  ; Row SEQ of the adopted image read (pages filled from FILE) and compared
  ; with EXPECTED: :ok, (:refused :image-row SEQ) when the image holds
  ; another record there, or the read's verdict by name (damage).
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp seq) (fn-hrc-wfp fn-hrecs$c))
                  :guard-hints (("Goal" :in-theory (disable fn-hrc-get fn-hrc-vlen fn-hrc-wfp)))))
  (mv-let (v r fn-hrecs$c) (fn-hrc-get seq file (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
    (cond ((not (eq v :ok)) (mv v fn-hrecs$c))
          ((equal r (list :ok expected)) (mv :ok fn-hrecs$c))
          (t (mv (list :refused :image-row seq) fn-hrecs$c)))))

; An :ok check says the image holds EXPECTED at SEQ, for the history the
; adopted concrete holds (fn-hib-open-is-log-prefix: the log's prefix).

(defthm fn-his-check-row-is-nth
  (implies (and (fn-hrc-wfp c) (fn-hrs-rel h c) (fn-hib-root-holds h c) (fn-hib-disk-bound file h c)
                (natp seq) (< seq (len h))
                (equal (mv-nth 0 (fn-his-check-row seq expected file c)) :ok))
           (equal (nth seq h) expected))
  :hints (("Goal" :use ((:instance fn-hib-get-keeps (fuel (fn-hrc-vlen c))))
           :in-theory (set-difference-theories
                       (union-theories '(fn-his-check-row car-cons cdr-cons (:e equal) eq) (theory 'minimal-theory))
                       '(mv-nth)))))
; -----------------------------------------------------------------------------
; The image region of the checkpoint's file.
;
; The file starts with the image region: a 37-octet header (the size of a
; checkpoint segment header, so the open's first read is the same), zeros to
; *fn-his-base*, then NP pages of 16 KiB, page A at *fn-his-base* + 16 KiB * A
; (page 0, the root slots' page, zeros: the root travels in the F row).  The
; framed segments follow at *fn-his-base* + 16 KiB * NP.  The header:
; "FNSI", the region's version, NP (u64, little-endian), *fn-his-base*
; (u64), sixteen zero octets.

(defconst *fn-his-magic* '(70 78 83 73))   ; "FNSI"
(defconst *fn-his-version* 1)
(defconst *fn-his-base* 16384)
(defconst *fn-his-page-octets* 16384)
(defconst *fn-his-header-octets* 37)

(defun fn-his-le (n k)
  ; N as K little-endian octets
  (declare (xargs :guard (and (natp n) (natp k))))
  (if (zp k) nil (cons (mod (nfix n) 256) (fn-his-le (floor (nfix n) 256) (1- k)))))

(defun fn-his-le-value (octets)
  (declare (xargs :guard t))
  (if (atom octets) 0 (+ (nfix (car octets)) (* 256 (fn-his-le-value (cdr octets))))))

(defun fn-his-image-header (np)
  (declare (xargs :guard (natp np)))
  (append *fn-his-magic* (list *fn-his-version*) (fn-his-le np 8) (fn-his-le *fn-his-base* 8)
          (make-list 16 :initial-element 0)))

(defun fn-his-image-header-np (header)
  ; NP when HEADER (the file's first 37 octets) is an image region's header,
  ; else nil (a file without an image: its first octets are a segment's)
  (declare (xargs :guard t))
  (if (and (true-listp header) (equal (len header) *fn-his-header-octets*)
           (equal (take 4 header) *fn-his-magic*)
           (equal (nth 4 header) *fn-his-version*)
           (equal (fn-his-le-value (take 8 (nthcdr 13 header))) *fn-his-base*))
      (fn-his-le-value (take 8 (nthcdr 5 header)))
    nil))

(defun fn-his-skip-octets (np)
  ; the octets after the header up to the framed segments
  (declare (xargs :guard (natp np)))
  (+ (- *fn-his-base* *fn-his-header-octets*) (* *fn-his-page-octets* np)))

; The open reads back the page count the writer put (ground witnesses; the
; symbolic round trip is the codec lemma's shape and is not needed by any
; keystone: a header the open does not parse is a file without an image).
(defthm fn-his-image-header-np-witness
  (and (equal (fn-his-image-header-np (fn-his-image-header 0)) 0)
       (equal (fn-his-image-header-np (fn-his-image-header 1234567)) 1234567)
       (equal (fn-his-image-header-np '(70 78 83 67 3 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) nil))
  :rule-classes nil)

(defun fn-his-base-octets ()
  ; the offset of page 0 of the image in the checkpoint's file
  (declare (xargs :guard t))
  *fn-his-base*)

(defun fn-his-region-octets (np)
  ; the image region's octets: the header, zeros to the base, NP pages
  (declare (xargs :guard (natp np)))
  (+ *fn-his-header-octets* (fn-his-skip-octets np)))

(defun fn-his-np (writes acc)
  ; one past the largest page address WRITES names
  (declare (xargs :guard (natp acc)))
  (if (atom writes)
      acc
    (fn-his-np (cdr writes)
               (if (and (consp (car writes)) (natp (car (car writes))) (<= acc (car (car writes))))
                   (+ 1 (car (car writes)))
                 acc))))

(defun fn-his-binding (node salt count trail rec)
  ; the binding the checkpoint's F row carries for its image
  (declare (xargs :guard t))
  (fn-hib-binding node *fn-hib-codec* count trail rec salt))
