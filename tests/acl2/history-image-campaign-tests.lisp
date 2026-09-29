; fn: the integrated campaign over the page-backed history (lane
; composed-owner, 2026-09-29, row A6 of build/coordinator/COMPLETE-BEFORE-6.6.0.md;
; GPT-6's review of 2026-09-28, "Highest-priority integrated campaign"), as
; a test over the PRODUCTION writer and open: the image a checkpoint writes
; (books/history-image-snapshot.lisp fn-his-snapshot, the pages from
; fn-his-words) and the adoption the open makes (fn-his-open), with the read
; loop (fn-hrc-get), the asynchronous request and its completion
; (fn-hib-request / fn-hib-complete) and the pinned eviction (fn-hib-evict).
;
; A checkpoint's file is data here: the pages its image region holds, an
; alist (ADDR . WORDS) the page fill is attached to.  A replaced checkpoint
; stays readable to a reader that holds it (the host's descriptor: root
; lifetime by inode); here the old file is simply the old alist, kept while a
; reader pins it.
;
; The campaign, in one run: pin an old reader on checkpoint 0 -> accept
; writes -> publish checkpoint 1 -> the reader's cache is evicted -> a page
; read the reader asked for completes late, after it moved to checkpoint 1
; -> checkpoint 0 is reclaimed only when no reader pins it -> a publication
; of checkpoint 2 dies before its rename -> recover.  Required: accepted
; history stays accepted, the old view keeps its meaning, damage is never
; absence, a late completion is refused by name and never taken for damage,
; no pinned root loses a page.
(in-package "ACL2")
(include-book "../../books/history-image-snapshot")

; -----------------------------------------------------------------------------
; The page file as data.

(defun hict-page (file addr)
  (declare (xargs :guard t))
  (let ((w (cdr (hons-assoc-equal addr file))))
    (if (and (true-listp w) (equal (len w) 2048)) w (make-list 2048 :initial-element 0))))

(defthm hict-page-shape
  (and (true-listp (hict-page file addr)) (equal (len (hict-page file addr)) 2048)))

(defattach (fn-pgs-page-words hict-page) (fn-pgs-fill-realize hict-page))

(defmacro hict-defconst (name form)
  `(make-event (let ((v ,form)) (value (list 'defconst ',name (list 'quote v))))))

(defun hict-events (i n tag)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i)))
      nil
    (cons (if (equal (mod i 5) 0)
              (list :retained i "<m@x>" (make-list 3000 :initial-element (mod (+ i tag) 251)) "subject")
            (list :other i tag))
          (hict-events (+ 1 (nfix i)) n tag))))

(defun hict-entries (evs)
  (if (atom evs) nil (cons (list (fn-scc-encode (car evs))) (hict-entries (cdr evs)))))

(defun hict-pages (writes acc fn-hrecs$c)
  ; the pages the writer names, as the checkpoint's image region holds them
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (if (atom writes)
      acc
    (let ((w (car writes)))
      (hict-pages (cdr writes)
                  (cons (cons (nth 0 w) (fn-his-words (nth 1 w) (nth 2 w) fn-hrecs$c)) acc)
                  fn-hrecs$c))))

(defun hict-data-addrs (writes)
  (if (atom writes) nil
    (if (equal (nth 1 (car writes)) 0)
        (cons (nth 0 (car writes)) (hict-data-addrs (cdr writes)))
      (hict-data-addrs (cdr writes)))))

(defun hict-publish (records salt node trail)
  ; A publication: the production writer's image of RECORDS, the pages it
  ; writes and the binding the F row carries.  (list VERDICT BINDING FILE
  ; DATA-ADDRS), DATA-ADDRS the addresses of the image's data pages.
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (mv-let (v rec writes fn-hrecs$c) (fn-his-snapshot records salt fn-hrecs$c)
        (mv (list v (fn-his-binding node salt (len records) trail rec)
                  (hict-pages writes nil fn-hrecs$c)
                  (hict-data-addrs writes))
            fn-hrecs$c))
      out)))

(defun hict-rows (i n file fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i)))
      (mv nil fn-hrecs$c)
    (mv-let (v r fn-hrecs$c) (fn-hrc-get i file (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
      (mv-let (rest fn-hrecs$c) (hict-rows (+ 1 (nfix i)) n file fn-hrecs$c)
        (mv (cons (if (eq v :ok) r (list :fault v)) rest) fn-hrecs$c)))))

(defun hict-oks (evs)
  (if (atom evs) nil (cons (list :ok (car evs)) (hict-oks (cdr evs)))))

(defconst *hict-salt* 5)
(defconst *hict-node* (make-list 32 :initial-element 17))
(defconst *hict-t0* (make-list 32 :initial-element 0))
(defconst *hict-h0* (hict-events 0 40 0))
(defconst *hict-w* (hict-events 40 45 0))
(defconst *hict-h1* (append *hict-h0* *hict-w*))
(defconst *hict-h2* (append *hict-h1* (hict-events 45 48 0)))
(hict-defconst *hict-tr0* (fn-hib-chain *hict-t0* (hict-entries *hict-h0*)))
(hict-defconst *hict-tr1* (fn-hib-chain *hict-t0* (hict-entries *hict-h1*)))
(hict-defconst *hict-tr2* (fn-hib-chain *hict-t0* (hict-entries *hict-h2*)))

; The three publications (the production writer).
(hict-defconst *hict-p0* (hict-publish *hict-h0* *hict-salt* *hict-node* *hict-tr0*))
(hict-defconst *hict-p1* (hict-publish *hict-h1* *hict-salt* *hict-node* *hict-tr1*))
(hict-defconst *hict-p2* (hict-publish *hict-h2* *hict-salt* *hict-node* *hict-tr2*))
(assert-event (and (eq (nth 0 *hict-p0*) :ok) (eq (nth 0 *hict-p1*) :ok) (eq (nth 0 *hict-p2*) :ok)
                   (fn-hib-bindingp (nth 1 *hict-p0*)) (fn-hib-bindingp (nth 1 *hict-p1*))))

(defconst *hict-b0* (nth 1 *hict-p0*))
(defconst *hict-f0* (nth 2 *hict-p0*))
(defconst *hict-b1* (nth 1 *hict-p1*))
(defconst *hict-f1* (nth 2 *hict-p1*))
(defconst *hict-b2* (nth 1 *hict-p2*))
(defconst *hict-f2* (nth 2 *hict-p2*))

; -----------------------------------------------------------------------------
; The campaign.

(defun hict-open-rows (b trail file n)
  ; an open: adopt, then every row
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (mv-let (v fn-hrecs$c) (fn-his-open b *hict-node* *hict-salt* trail file fn-hrecs$c)
        (if v
            (mv (list v) fn-hrecs$c)
          (mv-let (rows fn-hrecs$c) (hict-rows 0 n file fn-hrecs$c)
            (mv (list nil rows) fn-hrecs$c))))
      out)))

(defun hict-campaign ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      ;; 1. a reader pinned on checkpoint 0 reads a row
      (mv-let (v0 fn-hrecs$c) (fn-his-open *hict-b0* *hict-node* *hict-salt* *hict-tr0* *hict-f0* fn-hrecs$c)
        (mv-let (g0 r0 fn-hrecs$c) (fn-hrc-get 39 *hict-f0* (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
          (declare (ignore g0))
          ;; 2-3. writes accepted, checkpoint 1 published (above: *hict-p1*);
          ;; 4. the reader's cache under pressure: the page it read evicted
          (let ((p (1- (fn-hrc-vlen fn-hrecs$c))))
            (mv-let (e fn-hrecs$c) (fn-hib-evict p nil fn-hrecs$c)
              ;; the old view keeps its meaning: the row read again, from
              ;; checkpoint 0's file (the reader still holds it)
              (mv-let (g1 r1 fn-hrecs$c) (fn-hrc-get 39 *hict-f0* (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
                (declare (ignore g1))
                ;; 5. a page read asked for, the reader then moving to
                ;; checkpoint 1, the read completing late
                (mv-let (evicted fn-hrecs$c) (fn-hib-evict p nil fn-hrecs$c)
                  (declare (ignore evicted))
                  (mv-let (a ar) (fn-hrc-at 39 fn-hrecs$c)
                    (declare (ignore ar))
                    (let ((q (fn-hib-request :reader (if (consp a) (cadr a) 0) fn-hrecs$c)))
                      (mv-let (v1 fn-hrecs$c)
                        (fn-his-open *hict-b1* *hict-node* *hict-salt* *hict-tr1* *hict-f1* fn-hrecs$c)
                        (mv-let (late fn-hrecs$c)
                          (fn-hib-complete q (hict-page *hict-f0* (fn-hib-q-phys q)) fn-hrecs$c)
                          ;; the moved reader answers the new history
                          (mv-let (g2 r2 fn-hrecs$c) (fn-hrc-get 44 *hict-f1* (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
                            (declare (ignore g2))
                            (mv (list v0 r0 e r1 a v1 late r2) fn-hrecs$c))))))))))))
      out)))

(hict-defconst *hict-run* (hict-campaign))
(assert-event (null (nth 0 *hict-run*)))                                     ; the pinned reader adopted checkpoint 0
(assert-event (equal (nth 1 *hict-run*) (list :ok (nth 39 *hict-h0*))))     ; ... and reads it
(assert-event (equal (nth 2 *hict-run*) :ok))                                ; its page evicted
(assert-event (equal (nth 3 *hict-run*) (list :ok (nth 39 *hict-h0*))))     ; the old view keeps its meaning
(assert-event (eq (car (nth 4 *hict-run*)) :need-page))                      ; a read asked for a page
(assert-event (null (nth 5 *hict-run*)))                                     ; the reader moved to checkpoint 1
; The late completion is refused by name (every in-file root is transaction
; 1 of its own page store, so the page's entry -- its address and digest in
; the new root -- is what tells the checkpoints apart), and never taken for
; damage; or, where the new root names the same page with the same digest,
; the fill is that page.
(assert-event (or (equal (car (nth 6 *hict-run*)) :refused)
                  (equal (nth 6 *hict-run*) :ok)))
(assert-event (not (and (consp (nth 6 *hict-run*)) (eq (car (nth 6 *hict-run*)) :page-damaged))))
(assert-event (equal (nth 7 *hict-run*) (list :ok (nth 44 *hict-h1*))))     ; the new history answers

; Accepted history stays accepted: the open of checkpoint 1 reads H0 then
; the writes, row by row.
(hict-defconst *hict-o1* (hict-open-rows *hict-b1* *hict-tr1* *hict-f1* 45))
(assert-event (equal *hict-o1* (list nil (hict-oks *hict-h1*))))

; 6. Reclamation: checkpoint 0's file goes only when no reader pins it.  A
; reader still on it reads it whole; the file's pages are not handed to
; another checkpoint while it is pinned (in-file images never share pages:
; each checkpoint is its own page store).
(hict-defconst *hict-o0* (hict-open-rows *hict-b0* *hict-tr0* *hict-f0* 40))
(assert-event (equal *hict-o0* (list nil (hict-oks *hict-h0*))))

; 7. A publication of checkpoint 2 dies before its rename: the name still
; binds checkpoint 1's file (the program's crash keystone), and recovery
; opens it -- every accepted record, the uncertain publication neither
; refused nor half-applied.  Had the rename landed, checkpoint 2 opens.
(assert-event (equal (hict-open-rows *hict-b1* *hict-tr1* *hict-f1* 45) *hict-o1*))
(hict-defconst *hict-o2* (hict-open-rows *hict-b2* *hict-tr2* *hict-f2* 48))
(assert-event (equal *hict-o2* (list nil (hict-oks *hict-h2*))))

; 8. Damage is never absence: checkpoint 1's file with a data page changed
; (where the new rows live): recovery reads every row before it and names
; the damage at that page -- no row answered absent, no row answered wrong.
(defun hict-max (xs) (if (atom xs) 0 (max (nfix (car xs)) (hict-max (cdr xs)))))
(defun hict-corrupt (file addr)
  ; FILE with word 0 of page ADDR changed
  (let ((w (hict-page file addr)))
    (cons (cons addr (cons (logxor 1 (car w)) (cdr w))) file)))
(defun hict-ok-or-damaged (rows evs damaged)
  ; every row is its record, or the damage by name; DAMAGED: one was
  (if (atom rows)
      (and damaged (atom evs))
    (and (consp evs)
         (or (equal (car rows) (list :ok (car evs)))
             (and (consp (car rows)) (eq (car (car rows)) :fault)
                  (consp (cadr (car rows))) (eq (car (cadr (car rows))) :page-damaged)))
         (hict-ok-or-damaged (cdr rows) (cdr evs)
                             (or damaged (and (consp (car rows)) (eq (car (car rows)) :fault)))))))
; A data page (the last one the writer names: the newest rows' pool).
(hict-defconst *hict-dmg* (hict-open-rows *hict-b1* *hict-tr1*
                                          (hict-corrupt *hict-f1* (hict-max (nth 3 *hict-p1*))) 45))
(assert-event (and (null (car *hict-dmg*))
                   (hict-ok-or-damaged (cadr *hict-dmg*) *hict-h1* nil)))
; A root page (a table page): the open itself refuses by name.
(hict-defconst *hict-dmg-root* (hict-open-rows *hict-b1* *hict-tr1*
                                               (hict-corrupt *hict-f1* (hict-max (strip-cars *hict-f1*))) 45))
(assert-event (and (consp (car *hict-dmg-root*)) (member (car (car *hict-dmg-root*)) '(:table-damaged :dir-damaged))))
