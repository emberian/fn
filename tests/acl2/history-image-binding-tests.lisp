; fn: teeth for books/history-image-binding.lisp (lane composed-owner,
; 2026-09-29, rows A2-A4): the adoption that establishes the history's
; faithfulness, the binding to the exact log prefix, the asynchronous page
; request and its late completion, eviction with pins, and the adversarial
; cases of row A3, each refused by name.
;
; The page file is data here, as in tests/acl2/history-records-disk-tests.lisp:
; FILE is an alist (PHYS . WORDS) and the host's page fill (A-PGS-HOST-IO's
; fn-pgs-page-words / fn-pgs-fill-realize) is attached to its lookup, so the
; adoption and the reads EXECUTE over committed images.  Two histories of
; the SAME length are each loaded, flushed into an image and committed as a
; page file's first transaction; the first is then extended and committed
; again (a second generation in the other root slot, copy-on-write).  The
; log is modelled by its entries (one record per entry here); its chain
; value is `fn-hib-chain' from a stand-in genesis trailer.
;
; The keystones' hypotheses that are relations over non-executable
; definitions are asserted in executed form (hibt-root-is-image,
; hibt-file-bound: every part executed).  The digest bound (no second
; preimage of an image page, `fn-hib-disk-bound' / `fn-hib-file-bound') and
; the chain bound (`fn-hib-chain-distinct') have no hypothesis-removal
; witness: removing either while keeping the others needs a BLAKE3
; collision or second preimage.  What the digest check does without the
; tables being the history's is witnessed instead (root-is-image removed).
(in-package "ACL2")
(include-book "../../books/history-image-fold")

; -----------------------------------------------------------------------------
; The host runs compiled code: every executable the host will call is
; guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-hib-adopt (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hib-open (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hib-check (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hib-select (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hib-request (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hib-complete (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hib-evict (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hif-count-run (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hif-collect-run (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The page file as data.

(defun hibt-page (file addr)
  (declare (xargs :guard t))
  (let ((w (cdr (hons-assoc-equal addr file))))
    (if (and (true-listp w) (equal (len w) 2048) (fn-pgs-u64-listp w)) w (make-list 2048 :initial-element 0))))

(defthm hibt-page-shape
  (and (true-listp (hibt-page file addr)) (equal (len (hibt-page file addr)) 2048)
       (fn-pgs-u64-listp (hibt-page file addr))))

(defattach (fn-pgs-page-words hibt-page) (fn-pgs-fill-realize hibt-page))
; the frame fill (A-PGS-HOST-IO's in-place form): the put of the same page
(defattach fn-pgs-fill-frame fn-pgs-fill-frame-via-words)

; A root slot as the page store reads it (pgs-x-read-rec): the record and
; the check observed over its words, which for a slot the commit wrote is
; the record's own check field.
(defun hibt-slot (rec) (list rec (sixth rec)))

; A constant computed with the attachments above (the page file, BLAKE3 for
; the frame digest): defconst does not evaluate through attachments, a
; make-event expansion does.
(defmacro hibt-defconst (name form)
  `(make-event (let ((v ,form)) (value (list 'defconst ',name (list 'quote v))))))

(defun hibt-events (i n tag)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i)))
      nil
    (cons (if (equal (mod i 5) 0)
              (list :retained i "<m@x>" (make-list 3000 :initial-element (mod (+ i tag) 251)) "subject")
            (list :other i tag))
          (hibt-events (+ 1 (nfix i)) n tag))))

(defun hibt-flush-all (k fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (if (zp k)
      (mv :ok fn-hrecs$c)
    (mv-let (v fn-hrecs$c) (fn-hrc-flush-one fn-hrecs$c)
      (if (eq v :ok) (hibt-flush-all (1- k) fn-hrecs$c) (mv v fn-hrecs$c)))))

(defun hibt-w-words (a k pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil :measure (nfix k)))
  (if (zp k) nil (cons (pgs-wi a pgs-mem) (hibt-w-words (+ 1 a) (- k 1) pgs-mem))))

(defun hibt-data-writes (lpages fresh pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (or (atom lpages) (atom fresh)) nil
    (cons (cons (car fresh) (hibt-w-words (* 2048 (car lpages)) 2048 pgs-mem))
          (hibt-data-writes (cdr lpages) (cdr fresh) pgs-mem))))

(defun hibt-table-writes (tl tfresh pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (or (atom tl) (atom tfresh)) nil
    (cons (cons (car tfresh) (pgs-x-words 2 (* 2048 (car tl)) 2048 pgs-mem))
          (hibt-table-writes (cdr tl) (cdr tfresh) pgs-mem))))

(defun hibt-dir-writes (rs j m pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil :measure (nfix (- (nfix m) (nfix j)))))
  (if (zp (- (nfix m) (nfix j))) nil
    (cons (cons (+ rs j) (pgs-x-words 1 (+ *pgs-x-dir-base* (* 2048 j)) 2048 pgs-mem))
          (hibt-dir-writes rs (+ 1 (nfix j)) m pgs-mem))))

(defun hibt-commit (n txid alloc slot pgs-mem fn-octets-pg)
  ; The dirty pages committed as transaction TXID over the open table of N
  ; logical pages: (mv RESULT WRITES pgs-mem fn-octets-pg), WRITES the pages
  ; the commit writes (data, touched tables, the directory run).
  (declare (xargs :stobjs (pgs-mem fn-octets-pg) :verify-guards nil))
  (let* ((pgs-mem (if (< (pgs-m-length pgs-mem) (+ *pgs-x-dir-base* 2048))
                      (resize-pgs-m (+ *pgs-x-dir-base* 2048) pgs-mem)
                    pgs-mem))
         (lpages (pgs-x-dirty-list (pgs-v-length pgs-mem) nil pgs-mem)))
    (mv-let (res pgs-mem fn-octets-pg)
      (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)
      (if (not (and (consp res) (eq (car res) :plan)))
          (mv res nil pgs-mem fn-octets-pg)
        (let ((fresh (nth 2 res)) (tl (nth 3 res)) (tfresh (nth 4 res)) (rs (nth 5 res)) (m (nth 6 res)))
          (mv res
              (append (hibt-data-writes lpages fresh pgs-mem)
                      (hibt-table-writes tl tfresh pgs-mem)
                      (hibt-dir-writes rs 0 m pgs-mem))
              pgs-mem fn-octets-pg))))))

(defun hibt-header (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (list (fn-hrc-nimg fn-hrecs$c) (fn-hrc-lens fn-hrecs$c) (fn-hrc-starts fn-hrecs$c) (fn-hrc-npages fn-hrecs$c)))

(defun hibt-build (evs more salt)
  ; EVS flushed into an image and committed (transaction 1, slot 0); then
  ; MORE appended, flushed and committed again (transaction 2, slot 512)
  ; when MORE is not empty.  (list RES1 FILE1 HDR1 RES2 FILE2 HDR2), FILE2
  ; the second commit's pages over FILE1's (copy-on-write: fresh addresses).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (let ((fn-hrecs$c (fn-hrc-load evs salt fn-hrecs$c)))
        (mv-let (v fn-hrecs$c) (hibt-flush-all (len evs) fn-hrecs$c)
          (declare (ignore v))
          (mv-let (res1 w1 fn-hrecs$c)
            (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))
                        (fn-octets-pg (fn-hrc-oct fn-hrecs$c)))
                       (res file pgs-mem fn-octets-pg)
                       (hibt-commit 0 1 (list nil 1) 0 pgs-mem fn-octets-pg)
                       (mv res file fn-hrecs$c))
            (let ((hdr1 (hibt-header fn-hrecs$c)))
              (if (atom more)
                  (mv (list res1 w1 hdr1 nil w1 hdr1) fn-hrecs$c)
                (let ((fn-hrecs$c (fn-hrc-load-events more fn-hrecs$c)))
                  (mv-let (v2 fn-hrecs$c) (hibt-flush-all (len more) fn-hrecs$c)
                    (declare (ignore v2))
                    (mv-let (res2 w2 fn-hrecs$c)
                      (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))
                                  (fn-octets-pg (fn-hrc-oct fn-hrecs$c)))
                                 (res file pgs-mem fn-octets-pg)
                                 (hibt-commit (nth 3 hdr1) 2 (nth 7 res1) 512 pgs-mem fn-octets-pg)
                                 (mv res file fn-hrecs$c))
                      (mv (list res1 w1 hdr1 res2 (append w2 w1) (hibt-header fn-hrecs$c)) fn-hrecs$c)))))))))
      out)))

; -----------------------------------------------------------------------------
; Executed forms of the keystones' relations.

(defun hibt-words (p fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))) (w) (hibt-w-words (* 2048 p) 2048 pgs-mem) w))

(defun hibt-flag (p fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))) (x) (pgs-vi p pgs-mem) x))

(defun hibt-tw (p n iw fn-hrecs$c)
  ; fn-hib-tw executed over the concrete's pgs-mem
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil :measure (nfix (- (nfix n) (nfix p)))))
  (if (zp (- (nfix n) (nfix p))) t
    (and (equal (third (fn-hib-entry (nfix p) fn-hrecs$c))
                (fn-hib-page-digest (take 2048 (nthcdr (* 2048 (nfix p)) iw))))
         (hibt-tw (+ 1 (nfix p)) n iw fn-hrecs$c))))

(defun hibt-fb (file p n iw fn-hrecs$c)
  ; the page file holds IW's page at every address the table names (which
  ; implies fn-hib-nw's implication for each page)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil :measure (nfix (- (nfix n) (nfix p)))))
  (if (zp (- (nfix n) (nfix p))) t
    (and (equal (hibt-page file (fn-hrc-phys (nfix p) fn-hrecs$c)) (take 2048 (nthcdr (* 2048 (nfix p)) iw)))
         (hibt-fb file (+ 1 (nfix p)) n iw fn-hrecs$c))))

(defun hibt-vhold (p n iw fn-hrecs$c)
  ; fn-hp-vhold executed: every verified page holds IW's page
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil :measure (nfix (- (nfix n) (nfix p)))))
  (if (zp (- (nfix n) (nfix p))) t
    (and (implies (equal (hibt-flag (nfix p) fn-hrecs$c) 2)
                  (equal (hibt-words (nfix p) fn-hrecs$c) (take 2048 (nthcdr (* 2048 (nfix p)) iw))))
         (hibt-vhold (+ 1 (nfix p)) n iw fn-hrecs$c))))

(defun hibt-rows (i n file fn-hrecs$c)
  ; rows I..N-1 through the retry loop: (mv ANSWERS fn-hrecs$c), each (V R)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i)))
      (mv nil fn-hrecs$c)
    (mv-let (v r fn-hrecs$c) (fn-hrc-get i file (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
      (mv-let (rest fn-hrecs$c) (hibt-rows (+ 1 (nfix i)) n file fn-hrecs$c)
        (mv (cons (list v r) rest) fn-hrecs$c)))))

(defun hibt-oks (evs)
  (if (atom evs) nil (cons (list :ok (list :ok (car evs))) (hibt-oks (cdr evs)))))

(defun hibt-root-is-image (file rec h salt starts)
  ; fn-hib-root-is-image executed: the writer's invariants and the loaded
  ; tables naming the digests of H's placed image pages
  (declare (xargs :verify-guards nil))
  (let ((np (pgs-rec-npages rec)))
    (with-local-stobj fn-hrecs$c
      (mv-let (ok fn-hrecs$c)
        (mv-let (v fn-hrecs$c) (fn-hib-open-root file rec fn-hrecs$c)
          (mv (and (null v) (fn-hp-okp h salt) (fn-hp-starts-okp starts)
                   (adt-placement-ok starts (fn-hp-lens h salt) np)
                   (hibt-tw 0 np (fn-hp-piw h salt starts np) fn-hrecs$c))
              fn-hrecs$c))
        ok))))

(defun hibt-file-bound (file rec h salt starts)
  ; a sufficient executed form of fn-hib-file-bound: the file holds H's
  ; image page at every address the loaded tables name
  (declare (xargs :verify-guards nil))
  (let ((np (pgs-rec-npages rec)))
    (with-local-stobj fn-hrecs$c
      (mv-let (ok fn-hrecs$c)
        (mv-let (v fn-hrecs$c) (fn-hib-open-root file rec fn-hrecs$c)
          (mv (and (null v) (hibt-fb file 0 np (fn-hp-piw h salt starts np) fn-hrecs$c)) fn-hrecs$c))
        ok))))

(defun hibt-open (b node salt trail slots file)
  ; The open, then the concrete's state and every row read back:
  ; (list VERDICT NIMG LENS STARTS NPAGES LO HI ROWS VHOLD-OF H?)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (mv-let (v fn-hrecs$c) (fn-hib-open b node salt trail slots file fn-hrecs$c)
        (if v
            (mv (list v) fn-hrecs$c)
          (let ((n (fn-hrc-nimg fn-hrecs$c)))
            (mv-let (rows fn-hrecs$c) (hibt-rows 0 n file fn-hrecs$c)
              (mv (list v n (fn-hrc-lens fn-hrecs$c) (fn-hrc-starts fn-hrecs$c) (fn-hrc-npages fn-hrecs$c)
                        (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c) rows)
                  fn-hrecs$c)))))
      out)))

; -----------------------------------------------------------------------------
; The histories, the page files, the log.

(defconst *hibt-salt* 5)
(defconst *hibt-h1* (hibt-events 0 40 0))           ; history A
(defconst *hibt-h2* (hibt-events 0 40 7))           ; history B: the same length, other records
(defconst *hibt-more* (hibt-events 40 45 0))        ; A's next records
(defconst *hibt-b1* (hibt-build *hibt-h1* *hibt-more* *hibt-salt*))
(defconst *hibt-b2* (hibt-build *hibt-h2* nil *hibt-salt*))

(defconst *hibt-rec1* (nth 1 (nth 0 *hibt-b1*)))    ; A's first commit (40 records)
(defconst *hibt-file1* (nth 1 *hibt-b1*))
(defconst *hibt-hdr1* (nth 2 *hibt-b1*))
(defconst *hibt-rec1b* (nth 1 (nth 3 *hibt-b1*)))   ; A's second commit (45 records)
(defconst *hibt-file1b* (nth 4 *hibt-b1*))          ; both generations' pages
(defconst *hibt-hdr1b* (nth 5 *hibt-b1*))
(defconst *hibt-rec2* (nth 1 (nth 0 *hibt-b2*)))    ; B's commit (40 records)
(defconst *hibt-file2* (nth 1 *hibt-b2*))
(defconst *hibt-hdr2* (nth 2 *hibt-b2*))
(defconst *hibt-np1* (pgs-rec-npages *hibt-rec1*))

(assert-event (and (eq (car (nth 0 *hibt-b1*)) :plan) (eq (car (nth 3 *hibt-b1*)) :plan)
                   (eq (car (nth 0 *hibt-b2*)) :plan)
                   (pgs-rec-shape-p *hibt-rec1*) (pgs-rec-shape-p *hibt-rec1b*) (pgs-rec-shape-p *hibt-rec2*)
                   (equal (car *hibt-hdr1*) 40) (equal (car *hibt-hdr2*) 40) (equal (car *hibt-hdr1b*) 45)
                   (equal (len *hibt-h1*) (len *hibt-h2*)) (not (equal *hibt-h1* *hibt-h2*))
                   (equal (pgs-rec-txid *hibt-rec1*) 1) (equal (pgs-rec-txid *hibt-rec1b*) 2)))

; The log: one entry per record (its tree octets), chained from a stand-in
; genesis trailer; each history's prefix identity is its chain value.
(defun hibt-entries (evs)
  (if (atom evs) nil (cons (list (fn-scc-encode (car evs))) (hibt-entries (cdr evs)))))
(defconst *hibt-t0* (make-list 32 :initial-element 0))
(defconst *hibt-e1* (hibt-entries *hibt-h1*))
(defconst *hibt-e1b* (hibt-entries (append *hibt-h1* *hibt-more*)))
(defconst *hibt-e2* (hibt-entries *hibt-h2*))
(hibt-defconst *hibt-t1* (fn-hib-chain *hibt-t0* *hibt-e1*))
(hibt-defconst *hibt-t1b* (fn-hib-chain *hibt-t0* *hibt-e1b*))
(hibt-defconst *hibt-t2* (fn-hib-chain *hibt-t0* *hibt-e2*))
(defconst *hibt-node* (make-list 32 :initial-element 17))
(defconst *hibt-node2* (make-list 32 :initial-element 18))

(assert-event (and (not (equal *hibt-t1* *hibt-t2*)) (not (equal *hibt-t1* *hibt-t1b*))
                   (equal (len *hibt-t1*) 32)))

(defconst *hibt-bind1* (fn-hib-binding *hibt-node* *fn-hib-codec* 40 *hibt-t1* *hibt-rec1* *hibt-salt*))
(defconst *hibt-bind1b* (fn-hib-binding *hibt-node* *fn-hib-codec* 45 *hibt-t1b* *hibt-rec1b* *hibt-salt*))
(defconst *hibt-bind2* (fn-hib-binding *hibt-node* *fn-hib-codec* 40 *hibt-t2* *hibt-rec2* *hibt-salt*))
(defconst *hibt-starts1* (nth 2 *hibt-hdr1*))
(defconst *hibt-starts2* (nth 2 *hibt-hdr2*))
(defconst *hibt-starts1b* (nth 2 *hibt-hdr1b*))

; -----------------------------------------------------------------------------
; KEYSTONE fn-hib-open-is-log-prefix (and fn-hib-adopt-establishes,
; fn-hib-open-binds-prefix, fn-hib-get-keeps): live-run witnesses.

; Positive: every hypothesis executed -- the concrete well formed (fresh);
; the binding's TRAIL the chain of the snapshot's entries EW = *hibt-e1*;
; the root is the image of HW = *hibt-h1* (the writer's invariants and the
; loaded tables); the page file holds HW's pages; the log's value at the
; prefix is the chain of its entries EL = *hibt-e1*; EW = EL (so the chain
; bound holds); the open lands -- and the conclusion: the adopted concrete
; holds HW (count, header from page 0, empty suffix), every row reads HW's
; record, HW's length is the binding's count, EW = EL.
(assert-event (equal (fn-hib-b-trail *hibt-bind1*) (fn-hib-chain *hibt-t0* *hibt-e1*)))
(assert-event (hibt-root-is-image *hibt-file1* *hibt-rec1* *hibt-h1* *hibt-salt* *hibt-starts1*))
(assert-event (hibt-file-bound *hibt-file1* *hibt-rec1* *hibt-h1* *hibt-salt* *hibt-starts1*))
(hibt-defconst *hibt-o1* (hibt-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*)) *hibt-file1*))
(assert-event (equal (car *hibt-o1*) nil))
(assert-event (and (equal (nth 1 *hibt-o1*) 40) (equal (nth 2 *hibt-o1*) (fn-hp-lens *hibt-h1* *hibt-salt*))
                   (equal (nth 3 *hibt-o1*) *hibt-starts1*) (equal (nth 5 *hibt-o1*) 0) (equal (nth 6 *hibt-o1*) 0)
                   (equal (nth 7 *hibt-o1*) (hibt-oks *hibt-h1*))
                   (equal (len *hibt-h1*) (fn-hib-b-count *hibt-bind1*))))

; Removal of fn-hib-root-is-image: HW = *hibt-h2*, a history of the same
; length the root is not the image of.  Retained: the binding's trail is
; the chain of EW = *hibt-e1*, the log's the chain of EL = EW, the open
; lands (the file holds its own pages).  Omitted: the root's tables do not
; name *hibt-h2*'s pages.  Conclusion fails: the rows are not *hibt-h2*'s.
(assert-event (not (hibt-root-is-image *hibt-file1* *hibt-rec1* *hibt-h2* *hibt-salt* *hibt-starts2*)))
(assert-event (not (equal (nth 7 *hibt-o1*) (hibt-oks *hibt-h2*))))

; Removal of "the binding's TRAIL is the snapshot's entries' chain" (EW =
; *hibt-e2* while the binding carries *hibt-t1*).  Retained: the log's value
; is the chain of EL = *hibt-e1*, the chain bound (the two chains differ, so
; it holds vacuously), the root is *hibt-h1*'s image, the open lands.
; Conclusion fails: EW is not EL.
(assert-event (not (equal (fn-hib-b-trail *hibt-bind1*) (fn-hib-chain *hibt-t0* *hibt-e2*))))
(assert-event (not (equal (fn-hib-chain *hibt-t0* *hibt-e2*) (fn-hib-chain *hibt-t0* *hibt-e1*))))
(assert-event (not (equal *hibt-e2* *hibt-e1*)))

; Removal of "the log's value is its entries' chain" (EL = *hibt-e2*, the
; open given *hibt-t1*).  Retained: the binding's trail is EW = *hibt-e1*'s
; chain, the chain bound (vacuous: the chains differ), the root, the open
; lands.  Conclusion fails: EW is not EL.
(assert-event (not (equal *hibt-t1* (fn-hib-chain *hibt-t0* *hibt-e2*))))

; -----------------------------------------------------------------------------
; ROW A3: the adversarial cases, each refused by name.

; (1) Two legitimate histories of equal count, image and binding swapped.
; A's binding over B's page file: B's root slots hold B's record, not the
; one A's binding names.
(assert-event (equal (car (hibt-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec2*)) *hibt-file2*))
                     '(:refused :root-absent)))
; ... and with A's record copied into B's root slot: the page store's open
; refuses B's pages under A's record (the directory's digest), by name.
(hibt-defconst *hibt-swap* (hibt-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*)) *hibt-file2*))
(assert-event (equal (car *hibt-swap*) '(:dir-damaged 1)))
; B's binding and page file (consistent with each other) under A's log:
; the prefix identity differs though the counts are equal.
(assert-event (equal (car (hibt-open *hibt-bind2* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec2*)) *hibt-file2*))
                     '(:refused :prefix 40)))
; B's binding under B's log opens B (the positive case for B).
(assert-event (equal (nth 7 (hibt-open *hibt-bind2* *hibt-node* *hibt-salt* *hibt-t2* (list (hibt-slot *hibt-rec2*)) *hibt-file2*))
                     (hibt-oks *hibt-h2*)))
; Another store's binding (node identity) or salt, or another codec.
(assert-event (equal (fn-hib-check *hibt-bind1* *hibt-node2* *hibt-salt* *hibt-t1*) '(:refused :store-identity)))
(assert-event (equal (fn-hib-check *hibt-bind1* *hibt-node* 6 *hibt-t1*) '(:refused :salt)))
(assert-event (equal (car (fn-hib-check (fn-hib-binding *hibt-node* (list :fnadtsn2 1 3) 40 *hibt-t1* *hibt-rec1* 5)
                                        *hibt-node* *hibt-salt* *hibt-t1*))
                     :refused))
; A binding whose count is not the image's (page 0's header, read from the
; page file, not from the binding).
(assert-event (equal (car (hibt-open (fn-hib-binding *hibt-node* *fn-hib-codec* 39 *hibt-t1* *hibt-rec1* 5)
                                     *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*)) *hibt-file1*))
                     '(:refused :count 40 39)))

; (2) An old root with a newer table generation.  Copy-on-write keeps the
; old root's pages: the old record still opens the old image over the file
; holding both generations...
(assert-event (equal (nth 7 (hibt-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1*
                                       (list (hibt-slot *hibt-rec1*) (hibt-slot *hibt-rec1b*)) *hibt-file1b*))
                     (hibt-oks *hibt-h1*)))
; ... and the new one the new image.
(assert-event (equal (nth 7 (hibt-open *hibt-bind1b* *hibt-node* *hibt-salt* *hibt-t1b*
                                       (list (hibt-slot *hibt-rec1*) (hibt-slot *hibt-rec1b*)) *hibt-file1b*))
                     (hibt-oks (append *hibt-h1* *hibt-more*))))
; A file whose old table page was overwritten in place by the newer
; generation's (the pages the old record names now hold the new table):
; refused by the page store's check of the table page, by name.
(defun hibt-overwrite (file from to)
  ; FILE with page TO holding what page FROM holds
  (cons (cons to (hibt-page file from)) file))
(defconst *hibt-old-dir* (pgs-rec-dir-addr *hibt-rec1*))
(defconst *hibt-new-dir* (pgs-rec-dir-addr *hibt-rec1b*))
(defconst *hibt-mixed* (hibt-overwrite *hibt-file1b* *hibt-new-dir* *hibt-old-dir*))
(hibt-defconst *hibt-mixed-open*
  (hibt-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*) (hibt-slot *hibt-rec1b*)) *hibt-mixed*))
(assert-event (equal (car *hibt-mixed-open*) '(:dir-damaged 1)))
; ... and a table page the old directory names holding the newer
; generation's table page instead: refused by the table page's check.
(defun hibt-table-phys (file rec tp)
  ; the address the directory of REC names for table page TP
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (a fn-hrecs$c)
      (mv-let (v fn-hrecs$c) (fn-hib-open-root file rec fn-hrecs$c)
        (declare (ignore v))
        (mv (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))) (x) (first (pgs-x-get-entry 1 *pgs-x-dir-base* tp pgs-mem)) x)
            fn-hrecs$c))
      a)))
(hibt-defconst *hibt-old-table* (hibt-table-phys *hibt-file1b* *hibt-rec1* 0))
(hibt-defconst *hibt-new-table* (hibt-table-phys *hibt-file1b* *hibt-rec1b* 0))
(assert-event (not (equal *hibt-old-table* *hibt-new-table*)))
(hibt-defconst *hibt-mixed-table-open*
  (hibt-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*) (hibt-slot *hibt-rec1b*))
             (hibt-overwrite *hibt-file1b* *hibt-new-table* *hibt-old-table*)))
(assert-event (and (consp (car *hibt-mixed-table-open*)) (eq (car (car *hibt-mixed-table-open*)) :table-damaged)))
; The new root's binding with the old root's page file only (the newer
; generation not in the file): the record the binding names is absent.
(assert-event (equal (car (hibt-open *hibt-bind1b* *hibt-node* *hibt-salt* *hibt-t1b* (list (hibt-slot *hibt-rec1*)) *hibt-file1*))
                     '(:refused :root-absent)))

; (3) A late page fill after the active root changes.  A read of A's image
; at root 1 asks for a page; the request is taken; the owner then adopts
; root 2 (the next snapshot); the completion arrives late with the words the
; file held at the old address: refused :stale-root, nothing changes, and
; the read at root 2 still answers.  (A request whose root is current but
; whose entry is not -- the same txid, another image -- is :stale-page.)
(defun hibt-late (file)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (mv-let (v1 fn-hrecs$c)
        (fn-hib-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*) (hibt-slot *hibt-rec1b*)) file fn-hrecs$c)
        (mv-let (a r) (fn-hrc-at 39 fn-hrecs$c)
          (declare (ignore r))
          (let* ((p (if (and (consp a) (eq (car a) :need-page)) (cadr a) 0))
                 (q (fn-hib-request :op-1 p fn-hrecs$c))
                 (words (hibt-page file (fn-hib-q-phys q))))
            (mv-let (v2 fn-hrecs$c)
              (fn-hib-open *hibt-bind1b* *hibt-node* *hibt-salt* *hibt-t1b* (list (hibt-slot *hibt-rec1*) (hibt-slot *hibt-rec1b*)) file fn-hrecs$c)
              (mv-let (cv fn-hrecs$c) (fn-hib-complete q words fn-hrecs$c)
                (mv-let (gv gr fn-hrecs$c) (fn-hrc-get 44 file (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
                  (mv (list v1 a v2 cv gv gr) fn-hrecs$c)))))))
      out)))
(hibt-defconst *hibt-late-run* (hibt-late *hibt-file1b*))
(assert-event (and (null (nth 0 *hibt-late-run*)) (eq (car (nth 1 *hibt-late-run*)) :need-page)
                   (null (nth 2 *hibt-late-run*))
                   (equal (nth 3 *hibt-late-run*) '(:refused :stale-root 1 2))
                   (equal (nth 4 *hibt-late-run*) :ok)
                   (equal (nth 5 *hibt-late-run*) (list :ok (nth 44 (append *hibt-h1* *hibt-more*))))))

(defun hibt-stale-page ()
  ; a request taken over A's image, completed over B's (the same txid)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (mv-let (v1 fn-hrecs$c)
        (fn-hib-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*)) *hibt-file1* fn-hrecs$c)
        (declare (ignore v1))
        (let ((q (fn-hib-request :op-1 (1- (fn-hrc-vlen fn-hrecs$c)) fn-hrecs$c)))
          (mv-let (v2 fn-hrecs$c)
            (fn-hib-open *hibt-bind2* *hibt-node* *hibt-salt* *hibt-t2* (list (hibt-slot *hibt-rec2*)) *hibt-file2* fn-hrecs$c)
            (declare (ignore v2))
            (mv-let (cv fn-hrecs$c) (fn-hib-complete q (hibt-page *hibt-file1* (fn-hib-q-phys q)) fn-hrecs$c)
              (mv cv fn-hrecs$c)))))
      out)))
(assert-event (equal (hibt-stale-page) (list :refused :stale-page (1- *hibt-np1*))))

; (4) A crash between the two publications (the page file's commit, then
; the checkpoint's binding).  The new root landed in its slot, the binding
; is still the old one: the old root (the other slot) is selected and still
; holds its pages -- the old image opens.
(assert-event (equal (nth 7 (hibt-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1*
                                       (list (hibt-slot *hibt-rec1*) (hibt-slot *hibt-rec1b*)) *hibt-file1b*))
                     (hibt-oks *hibt-h1*)))
; The publications out of order (the binding durable, the page file's
; commit not): the root the binding names is not in the file -- refused by
; name, a recovery event, never an empty history.
(assert-event (equal (car (hibt-open *hibt-bind1b* *hibt-node* *hibt-salt* *hibt-t1b* (list (hibt-slot *hibt-rec1*)) *hibt-file1b*))
                     '(:refused :root-absent)))

; -----------------------------------------------------------------------------
; Damage is never absence: a data page corrupted in the file is refused at
; first touch, by name; page 0 corrupted refuses the adoption.

(defun hibt-corrupt (file addr)
  (let ((w (hibt-page file addr)))
    (cons (cons addr (cons (logxor 1 (car w)) (cdr w))) file)))

(defun hibt-phys (file rec p)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (a fn-hrecs$c)
      (mv-let (v fn-hrecs$c) (fn-hib-open-root file rec fn-hrecs$c)
        (declare (ignore v))
        (mv (fn-hrc-phys p fn-hrecs$c) fn-hrecs$c))
      a)))

(hibt-defconst *hibt-last-phys* (hibt-phys *hibt-file1* *hibt-rec1* (1- *hibt-np1*)))
(hibt-defconst *hibt-page0-phys* (hibt-phys *hibt-file1* *hibt-rec1* 0))
(hibt-defconst *hibt-dmg* (hibt-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*))
                                (hibt-corrupt *hibt-file1* *hibt-last-phys*)))
(assert-event (and (null (car *hibt-dmg*))
                   (member-equal (list :page-damaged (1- *hibt-np1*) *hibt-last-phys*)
                                 (strip-cars (nth 7 *hibt-dmg*)))
                   (not (member-equal (list :ok (list :refused :seq)) (nth 7 *hibt-dmg*)))))
(assert-event (equal (car (hibt-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*))
                                     (hibt-corrupt *hibt-file1* *hibt-page0-phys*)))
                     (list :page-damaged 0 *hibt-page0-phys*)))

; -----------------------------------------------------------------------------
; Eviction and progress (fn-hib-evict-keeps, fn-hib-undone-evict,
; fn-hib-complete-progress): a pinned page is refused; an unpinned verified
; page evicted is asked for again and the read still answers the record.

(defun hibt-evict-run ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (mv-let (v fn-hrecs$c)
        (fn-hib-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*)) *hibt-file1* fn-hrecs$c)
        (declare (ignore v))
        (mv-let (g1 r1 fn-hrecs$c) (fn-hrc-get 39 *hibt-file1* (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
          (declare (ignore g1))
          (let ((p (1- (fn-hrc-vlen fn-hrecs$c))))
            (mv-let (e1 fn-hrecs$c) (fn-hib-evict p (list p) fn-hrecs$c)
              (let ((f1 (hibt-flag p fn-hrecs$c)))
                (mv-let (e2 fn-hrecs$c) (fn-hib-evict p nil fn-hrecs$c)
                  (let ((f2 (hibt-flag p fn-hrecs$c)))
                    (mv-let (a r) (fn-hrc-at 39 fn-hrecs$c)
                      (declare (ignore r))
                      (let* ((q (fn-hib-request :op-2 (if (consp a) (cadr a) 0) fn-hrecs$c))
                             (u0 (hibt-flag (fn-hib-q-page q) fn-hrecs$c)))
                        (mv-let (cv fn-hrecs$c)
                          (fn-hib-complete q (hibt-page *hibt-file1* (fn-hib-q-phys q)) fn-hrecs$c)
                          (mv-let (g2 r2 fn-hrecs$c) (fn-hrc-get 39 *hibt-file1* (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
                            (mv (list r1 e1 f1 e2 f2 a u0 cv (hibt-flag (fn-hib-q-page q) fn-hrecs$c) g2 r2)
                                fn-hrecs$c))))))))))))
      out)))
(hibt-defconst *hibt-ev* (hibt-evict-run))
(assert-event (and (equal (nth 0 *hibt-ev*) (list :ok (nth 39 *hibt-h1*)))
                   (equal (nth 1 *hibt-ev*) (list :refused :pinned (1- *hibt-np1*)))
                   (equal (nth 2 *hibt-ev*) 2)
                   (equal (nth 3 *hibt-ev*) :ok)
                   (equal (nth 4 *hibt-ev*) 0)
                   (eq (car (nth 5 *hibt-ev*)) :need-page)
                   (not (equal (nth 6 *hibt-ev*) 2))
                   (equal (nth 7 *hibt-ev*) :ok)
                   (equal (nth 8 *hibt-ev*) 2)
                   (equal (nth 9 *hibt-ev*) :ok)
                   (equal (nth 10 *hibt-ev*) (list :ok (nth 39 *hibt-h1*)))))

; -----------------------------------------------------------------------------
; The fold over the image (books/history-image-fold.lisp): KEYSTONE
; fn-hif-run-is-foldl, instantiated (fn-hif-collect-run-is-foldl).  The run
; reads without filling: over the freshly adopted image it stops at the
; first row whose page is not verified and answers the need with its cursor
; and accumulator; the host serves the request (fn-hib-request /
; fn-hib-complete: the asynchronous path) and resumes at the cursor.  The
; composed loop ends :done with the fold of every row (the rows newest
; first), after one completion per page the rows touch.

(defun hibt-fold-loop (fuel i acc file completions fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-hif-collect-run fn-hib-complete fn-hib-request)))))
  (if (zp fuel)
      (mv :fuel i acc completions fn-hrecs$c)
    (mv-let (v j a) (fn-hif-collect-run i (fn-hrc-nimg fn-hrecs$c) acc fn-hrecs$c)
      (cond ((eq v :done) (mv :done j a completions fn-hrecs$c))
            ((and (consp v) (eq (car v) :need-page))
             (let ((q (fn-hib-request :fold (cadr v) fn-hrecs$c)))
               (mv-let (cv fn-hrecs$c) (fn-hib-complete q (hibt-page file (fn-hib-q-phys q)) fn-hrecs$c)
                 (if (eq cv :ok)
                     (hibt-fold-loop (1- fuel) j a file (+ 1 completions) fn-hrecs$c)
                   (mv cv j a completions fn-hrecs$c)))))
            (t (mv v j a completions fn-hrecs$c))))))

(defun hibt-fold (file)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (mv-let (v0 fn-hrecs$c)
        (fn-hib-open *hibt-bind1* *hibt-node* *hibt-salt* *hibt-t1* (list (hibt-slot *hibt-rec1*)) file fn-hrecs$c)
        (mv-let (v1 j1 a1) (fn-hif-collect-run 0 40 nil fn-hrecs$c)
          (mv-let (v j a n fn-hrecs$c) (hibt-fold-loop 100 0 nil file 0 fn-hrecs$c)
            (mv (list v0 v1 j1 a1 v j a n (fn-hrc-vlen fn-hrecs$c)) fn-hrecs$c))))
      out)))

(hibt-defconst *hibt-fold* (hibt-fold *hibt-file1*))
(assert-event (and (null (nth 0 *hibt-fold*))
                   (eq (car (nth 1 *hibt-fold*)) :need-page)   ; the first run stops at a need,
                   (equal (nth 2 *hibt-fold*) 0)                  ; at cursor 0, nothing folded
                   (equal (nth 3 *hibt-fold*) nil)
                   (equal (nth 4 *hibt-fold*) :done)               ; the composed loop ends :done
                   (equal (nth 5 *hibt-fold*) 40)
                   (equal (nth 6 *hibt-fold*) (reverse *hibt-h1*)) ; the fold of every row
                   (<= (nth 7 *hibt-fold*) (nth 8 *hibt-fold*))))  ; at most one completion per page
; Damage stops the fold by name at the damaged page's first row, with the
; rows before it folded -- never a shorter answer presented as whole.
(hibt-defconst *hibt-fold-dmg* (hibt-fold (hibt-corrupt *hibt-file1* *hibt-last-phys*)))
(assert-event (and (eq (car (nth 4 *hibt-fold-dmg*)) :page-damaged)
                   (< (nth 5 *hibt-fold-dmg*) 40)
                   (equal (nth 6 *hibt-fold-dmg*) (reverse (take (nth 5 *hibt-fold-dmg*) *hibt-h1*)))))
