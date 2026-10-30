; Layer C in the served core, seam C-S2 (fn2/docs/c-ordered-runs.md §8 item 7):
; the batch's private successor for identity facts (stage, bind, publish,
; drop) over the tables machines-c.lisp registers, the engine row it adds,
; their defcosts and core wrappers (fn2-identity-successor-core-events,
; materialized in assembly-callbacks-c.lisp). Its own book so that neither
; it nor machines-c nears the minute (C-SUCCESSOR-BOOK).
(in-package "ACL2")
(include-book "machines-c")
(fn2-book-layer :c)

; ---------------------------------------------------------------------------
; C-S2: the batch's private successor. A decision's fact is recorded only
; through its batch: stage (in the transaction's :ready arm, before B's
; admission) validates the decision against the published state and holds
; room; bind (after admission, the same arm) writes the fact into its batch's
; private overlay; publish (B, after the root swap) makes the batch's private
; overlays readable in one step and moves the stamps of their facts' buckets;
; drop (B, a refused batch) frees them. A private overlay is invisible to
; every decision (fn2-id-next-overlay reads active and frozen ones only).
;
; C-ENGINE-OWNER (interim until C1c declares the sealer machine, whose row
; becomes the owner): the engine's workspaces (overlay arenas, the bind
; scratch) are owned by the MRef (*fn2-idc-owner-kind* 0 1); no machine kind
; takes that number (kinds are assigned from 0 by the machine index).
(defconst *fn2-idc-owner-kind* 254)
(defconst *fn2-idc-owner-slot* 0)
(defconst *fn2-idc-owner-gen* 1)
; The bind scratch: the offer's content at 0, its Message-ID at 32 (pool
; writes are sequential from the reset fill).
(defconst *fn2-idc-scratch-bytes* 512)
(defconst *fn2-idc-scratch-mid* 32)
; An identity entry is at most the Message-ID, the 32-byte content and this
; much more (lengths, state, three identifiers).
(defconst *fn2-idc-entry-overhead* 48)
; The engine row: the bind scratch (held once taken) and the arena size.
(defcolumns fn2-id-engine ((scratch :bool) (slot :u32) (gen :u60) (arena :u32)))
(defun fn2-id-engine-init-arena (bytes fn2-id-engine)
 (declare (xargs :stobjs fn2-id-engine :guard (unsigned-byte-p 32 bytes)))
 (let ((fn2-id-engine (fn2-id-engine-init 1 fn2-id-engine)))
  (fn2-id-engine-set-arena 0 bytes fn2-id-engine)))
(fn2-idc-child fn2-core-id-engine fn2-id-engine (fn2-id-engine-init-arena (fn2-b-capacity :identity-arena-bytes 65536 profile) fn2-id-engine)
 "The engine's bind scratch and arena size (C-S2).")

; The first overlay row at or after O in phase PHASE (and, for a private
; one, of batch B); past the last, the row count.
(defun fn2-idc-find-overlay (k o phase b fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :measure (nfix k) :guard (and (fn2-overlays-wfp fn2-overlays) (natp k))))
 (cond ((not (and (natp o) (< o (fn2-overlays-rows fn2-overlays)) (posp k))) (nfix (fn2-overlays-rows fn2-overlays)))
       ((and (equal (fn2-overlays-phase o fn2-overlays) phase)
             (or (not (equal phase *fn2-overlay-phase-private*)) (equal (fn2-overlays-batch o fn2-overlays) b)))
        o)
       (t (fn2-idc-find-overlay (- k 1) (+ 1 o) phase b fn2-overlays))))
(defthm fn2-idc-find-overlay-natp (natp (fn2-idc-find-overlay k o phase b fn2-overlays)) :rule-classes :type-prescription)

;; Shapes of the overlay operations the successor uses (type, wfp, rows of
;; every stobj each returns), proved here once, each operation opened alone.
(defmacro fn2-idc-op-shape (fn args outs hyps &optional (plain 'nil) reads)
 `(defthm ,(fn2-columns-sym fn "-IDC-SHAPE")
   (implies (and ,@hyps) (and ,@(fn2-fc-shape-claims (if (consp (car outs)) outs (fn2-idc-shape-outs outs 1)) (cons fn args))))
   :hints (("Goal" :in-theory ,(cond ((eq plain :min) `(e/d (,fn) (fn2-overlays-rows fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows ,@reads)))
                                     ((eq plain :mid) `(e/d (,fn) (fn2-overlays-rows fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows
                                                   fn2-id-engine-rows fn2-id-stamps-rows
                                                   fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read
                                                   fn2-pool-write fn2-pool-class-for ,@reads)))
                                     (plain `(e/d (,fn) (fn2-overlays-rows fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows
                                                   fn2-id-engine-rows fn2-id-decides-rows fn2-id-stamps-rows
                                                   fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read
                                                   fn2-pool-write fn2-pool-class-for ,@reads)))
                                     (t
                                 `(e/d (,fn) (fn2-overlaysp fn2-overlays-wfp fn2-overlay-indexp fn2-overlay-index-wfp
                                          fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-overlays-rows
                                          fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows
                                          fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                          fn2-pool-class-for fn2-id-enginep fn2-id-engine-wfp fn2-id-engine-rows
                                          fn2-id-decidesp fn2-id-decides-wfp fn2-id-decides-rows
                                          fn2-id-stampsp fn2-id-stamps-wfp fn2-id-stamps-rows ,@reads))))))))
(fn2-idc-op-shape fn2-ov-start (o schema slot gen ibase icap okind oslot ogen cov fn2-overlays fn2-overlay-index fn2-pool)
 (fn2-overlays fn2-pool) ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))
(fn2-idc-op-shape fn2-ov-advance (o from to fn2-overlays) (fn2-overlays) ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays)))
(fn2-idc-op-shape fn2-ov-write (o pos ebase repl fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-overlays fn2-overlay-index fn2-pool)
 ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
  (fn2-overlay-index-wfp fn2-overlay-index) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))
(fn2-idc-op-shape fn2-ov-insert (o ebase eb fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
  (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))
(fn2-idc-op-shape fn2-id-record-insert (d o ebase article binding principal fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 ((fn2-id-decidesp fn2-id-decides) (fn2-id-decides-wfp fn2-id-decides)
  (fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
  (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 :min)
(in-theory (disable fn2-ov-start fn2-ov-advance))

;; Each function's output shapes (type, wfp, rows), proved right after it.
(defun fn2-idc-hyp-list (stobjs)
 (declare (xargs :verify-guards nil))
 (if (atom stobjs) nil
  (list* `(,(fn2-columns-sym (car stobjs) "P") ,(car stobjs)) `(,(fn2-columns-sym (car stobjs) "-WFP") ,(car stobjs))
         (fn2-idc-hyp-list (cdr stobjs)))))
(defmacro fn2-idc-fn-shape (fn args outs stobjs &optional (mode 't) reads)
 `(fn2-idc-op-shape ,fn ,args ,outs ,(fn2-idc-hyp-list stobjs) ,mode ,reads))

; Copy N bytes from [SOFF..) of SSLOT/SGEN (read under SK SS SG) to
; [DOFF..) of DSLOT/DGEN (written under the engine's owner). Interim until
; A-S8's fn2-pool-copy-across lands (D's interim is the same loop).
(defun fn2-idc-copy (n sslot sgen soff sk ss sg dslot dgen doff fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix n) :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp soff) (natp doff))
 :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert)))))
 (if (zp n) (mv :ok fn2-pool)
  (b* (((mv code byte) (fn2-pool-read sslot sgen soff sk ss sg fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool))
       ((mv code fn2-pool) (fn2-pool-write dslot dgen doff byte *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool)))
   (fn2-idc-copy (- n 1) sslot sgen (+ 1 soff) sk ss sg dslot dgen (+ 1 doff) fn2-pool))))
(fn2-pool-preserves fn2-idc-copy (n sslot sgen soff sk ss sg dslot dgen doff fn2-pool) :position 1)

; Hold the bind scratch (once): :ok, or :full when the pool has none.
(defun fn2-idc-scratch (fn2-id-engine fn2-pool)
 (declare (xargs :stobjs (fn2-id-engine fn2-pool) :guard (and (fn2-id-engine-wfp fn2-id-engine) (fn2-pool-wfp fn2-pool))
 :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert)))))
 (b* (((unless (< 0 (fn2-id-engine-rows fn2-id-engine))) (mv :state fn2-id-engine fn2-pool))
      ((when (equal (fn2-id-engine-scratch 0 fn2-id-engine) 1)) (mv :ok fn2-id-engine fn2-pool))
      (class (fn2-pool-class-for *fn2-idc-scratch-bytes* fn2-pool))
      ((unless (natp class)) (mv :capacity fn2-id-engine fn2-pool))
      ((mv code slot gen fn2-pool) (fn2-pool-reserve class *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
      ((unless (eq code :ok)) (mv (if (eq code :exhausted) :full code) fn2-id-engine fn2-pool))
      ((unless (and (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))) (mv :bounds fn2-id-engine fn2-pool))
      (fn2-id-engine (fn2-id-engine-put 0 (scratch 1) (slot slot) (gen gen))))
  (mv :ok fn2-id-engine fn2-pool)))
(fn2-idc-fn-shape fn2-idc-scratch (fn2-id-engine fn2-pool) (fn2-id-engine fn2-pool) (fn2-id-engine fn2-pool))
(in-theory (disable fn2-idc-scratch))

; Hold one spare overlay (an engine arena, not yet any batch's): :ok, :full
; when no overlay row or arena is free, :capacity when no pool class holds
; the arena.
(defun fn2-idc-spare (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool)
 (declare (xargs :stobjs (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool)
  :guard (and (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-pool-wfp fn2-pool))
 :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert)))))
 (b* ((rows (fn2-overlays-rows fn2-overlays))
      ((when (< (fn2-idc-find-overlay rows 0 *fn2-overlay-phase-spare* 0 fn2-overlays) rows)) (mv :ok fn2-overlays fn2-pool))
      (o (fn2-idc-find-overlay rows 0 *fn2-overlay-phase-free* 0 fn2-overlays))
      ((unless (and (< o rows) (< 0 (fn2-id-engine-rows fn2-id-engine)) (posp rows))) (mv :full fn2-overlays fn2-pool))
      (arena (fn2-id-engine-arena 0 fn2-id-engine))
      ((unless (natp arena)) (mv :state fn2-overlays fn2-pool))
      (class (fn2-pool-class-for arena fn2-pool))
      ((unless (natp class)) (mv :capacity fn2-overlays fn2-pool))
      ((mv code slot gen fn2-pool) (fn2-pool-reserve class *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
      ((unless (eq code :ok)) (mv (if (eq code :exhausted) :full code) fn2-overlays fn2-pool))
      (icap (floor (fn2-overlay-index-rows fn2-overlay-index) rows))
      ((mv code fn2-overlays fn2-pool)
       (fn2-ov-start o 1 slot gen (* o icap) icap *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* 0
                     fn2-overlays fn2-overlay-index fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-overlays fn2-pool)))
  (mv-let (code fn2-overlays) (fn2-ov-advance o *fn2-overlay-phase-active* *fn2-overlay-phase-spare* fn2-overlays)
   (mv code fn2-overlays fn2-pool))))
(fn2-idc-fn-shape fn2-idc-spare (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool) (fn2-overlays fn2-pool)
 (fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool))
(in-theory (disable fn2-idc-spare))

; Stage decision D (done): :ok with room held for its fact, :stale when its
; bucket's stamp or the identity version moved since it started (decide
; again), :duplicate or :evidence (nothing to record), :identity-conflict-bound,
; :full (no room now: backpressure), :capacity (its entry exceeds an arena).
(defun fn2-idc-stage (d fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  :guard t
 :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert)))))
 (b* (((unless (and (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps) (fn2-run-installed-wfp fn2-run-installed)
                    (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
                    (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (< 0 (fn2-id-engine-rows fn2-id-engine))))
       (mv :state fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      ((unless (and (natp d) (< d (fn2-id-decides-rows fn2-id-decides)))) (mv :bounds fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      ((unless (equal (fn2-id-decides-phase d fn2-id-decides) *fn2-id-decide-phase-done*))
       (mv :state fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      (bucket (fn2-id-decides-bucket d fn2-id-decides))
      ((unless (< bucket (fn2-id-stamps-rows fn2-id-stamps))) (mv :bounds fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      ((unless (and (equal (fn2-id-stamps-gen bucket fn2-id-stamps) (fn2-id-decides-stamp d fn2-id-decides))
                    (equal (fn2-run-version 1 (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)
                           (fn2-id-decides-vrun d fn2-id-decides))))
       (mv :stale fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      ((when (equal (fn2-id-decides-exact d fn2-id-decides) 1)) (mv :duplicate fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      ((when (equal (fn2-id-decides-exact d fn2-id-decides) 2)) (mv :evidence fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      ((unless (< (fn2-id-decides-others d fn2-id-decides) *fn2-identity-contents-max*))
       (mv :identity-conflict-bound fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      (row (+ (fn2-id-decides-qbase d fn2-id-decides) *fn2-id-mid*))
      ((unless (< row (fn2-fields-rows fn2-fields))) (mv :bounds fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      (arena (fn2-id-engine-arena 0 fn2-id-engine)) (mlen (fn2-fields-ref-len row fn2-fields))
      ((unless (and (natp arena) (natp mlen))) (mv :state fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      ((unless (<= (+ mlen 32 *fn2-idc-entry-overhead*) arena))
       (mv :capacity fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      ((mv code fn2-id-engine fn2-pool) (fn2-idc-scratch fn2-id-engine fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      ((mv code fn2-overlays fn2-pool) (fn2-idc-spare fn2-id-engine fn2-overlays fn2-overlay-index fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-id-engine fn2-overlays fn2-pool))
      (fn2-id-decides (fn2-id-decides-set-phase d *fn2-id-decide-phase-staged* fn2-id-decides)))
  (mv :ok fn2-id-decides fn2-id-engine fn2-overlays fn2-pool)))
(fn2-idc-fn-shape fn2-idc-stage (d fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-id-decides fn2-id-engine fn2-overlays fn2-pool)
 (fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-fields-ref-len fn2-id-decides-phase fn2-id-decides-bucket fn2-id-decides-stamp fn2-id-decides-vrun fn2-id-decides-exact
  fn2-id-decides-others fn2-id-stamps-gen fn2-id-engine-arena))
(in-theory (disable fn2-idc-stage))

; Point the offer's rows at the scratch copy of its octets, now under the
; engine's owner (the arena's), so the entry encodes from it.
(defun fn2-idc-rehome (d fn2-id-decides fn2-id-engine fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-id-engine fn2-fields fn2-pool)
  :guard (and (fn2-id-decides-wfp fn2-id-decides) (fn2-id-engine-wfp fn2-id-engine) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
 :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert fn2-idc-copy)))))
 (b* (((unless (and (natp d) (< d (fn2-id-decides-rows fn2-id-decides)) (< 0 (fn2-id-engine-rows fn2-id-engine))
                    (equal (fn2-id-engine-scratch 0 fn2-id-engine) 1)))
       (mv :state fn2-id-decides fn2-fields fn2-pool))
      (q (fn2-id-decides-qbase d fn2-id-decides))
      ((unless (< (+ q 1) (fn2-fields-rows fn2-fields))) (mv :bounds fn2-id-decides fn2-fields fn2-pool))
      (mrow (+ q *fn2-id-mid*)) (crow (+ q *fn2-id-con*))
      (mlen (fn2-fields-ref-len mrow fn2-fields))
      ((unless (and (<= mlen 250) (equal (fn2-fields-ref-len crow fn2-fields) 32))) (mv :bounds fn2-id-decides fn2-fields fn2-pool))
      (sslot (fn2-id-engine-slot 0 fn2-id-engine)) (sgen (fn2-id-engine-gen 0 fn2-id-engine))
      (qk (fn2-id-decides-qk d fn2-id-decides)) (qs (fn2-id-decides-qs d fn2-id-decides)) (qg (fn2-id-decides-qg d fn2-id-decides))
      ((unless (and (natp mlen) (unsigned-byte-p 32 sslot) (unsigned-byte-p 60 sgen)
                    (natp (fn2-fields-ref-off mrow fn2-fields)) (natp (fn2-fields-ref-off crow fn2-fields))))
       (mv :state fn2-id-decides fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-pool-reset sslot sgen *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-idc-copy 32 (fn2-fields-ref-slot crow fn2-fields) (fn2-fields-ref-gen crow fn2-fields)
                                        (fn2-fields-ref-off crow fn2-fields) qk qs qg sslot sgen 0 fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-idc-copy mlen (fn2-fields-ref-slot mrow fn2-fields) (fn2-fields-ref-gen mrow fn2-fields)
                                        (fn2-fields-ref-off mrow fn2-fields) qk qs qg sslot sgen *fn2-idc-scratch-mid* fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-put crow (ref-slot sslot) (ref-gen sgen) (ref-off 0)))
      (fn2-fields (fn2-fields-put mrow (ref-slot sslot) (ref-gen sgen) (ref-off *fn2-idc-scratch-mid*)))
      (fn2-id-decides (fn2-id-decides-put d (qk *fn2-idc-owner-kind*) (qs *fn2-idc-owner-slot*) (qg *fn2-idc-owner-gen*))))
  (mv :ok fn2-id-decides fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-idc-rehome (d fn2-id-decides fn2-id-engine fn2-fields fn2-pool) (fn2-id-decides fn2-fields fn2-pool)
 (fn2-id-decides fn2-id-engine fn2-fields fn2-pool) :mid
 (fn2-fields-ref-len fn2-fields-ref-off fn2-fields-ref-slot fn2-fields-ref-gen fn2-id-decides-qk fn2-id-decides-qs
  fn2-id-decides-qg fn2-id-engine-slot fn2-id-engine-gen fn2-id-engine-scratch))
(in-theory (disable fn2-idc-rehome))

; Bind staged decision D's fact into batch B's private overlay: the first
; private overlay of B with room, else the spare (which becomes B's). After
; an :ok stage in the same arm nothing here can fail but a broken invariant.
(defun fn2-idc-bind-into (o d article binding principal fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  :guard (and (fn2-id-decides-wfp fn2-id-decides) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
 :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert)))))
 (if (not (and (natp d) (< d (fn2-id-decides-rows fn2-id-decides))))
     (mv :bounds fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  (fn2-id-record-insert d o (fn2-id-decides-rb d fn2-id-decides) article binding principal
                        fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-idc-bind-into (o d article binding principal fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool) :mid)
(in-theory (disable fn2-idc-bind-into))
; The spare overlay becomes batch B's private successor: (mv code row).
(defun fn2-idc-take-spare (b fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :guard (fn2-overlays-wfp fn2-overlays)
  :guard-hints (("Goal" :in-theory (disable fn2-overlays-rows)))))
 (b* ((rows (fn2-overlays-rows fn2-overlays))
      (s (fn2-idc-find-overlay rows 0 *fn2-overlay-phase-spare* 0 fn2-overlays))
      ((unless (and (< s rows) (unsigned-byte-p 60 b))) (mv :spare 0 fn2-overlays))
      ((mv code fn2-overlays) (fn2-ov-advance s *fn2-overlay-phase-spare* *fn2-overlay-phase-private* fn2-overlays))
      ((unless (eq code :ok)) (mv code 0 fn2-overlays))
      (fn2-overlays (fn2-overlays-set-batch s b fn2-overlays)))
  (mv :ok s fn2-overlays)))
(fn2-idc-op-shape fn2-idc-take-spare (b fn2-overlays) ((fn2-overlays 2)) ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays)) :min)
(defthm fn2-idc-take-spare-row
 (implies (equal (car (fn2-idc-take-spare b fn2-overlays)) :ok)
          (and (natp (mv-nth 1 (fn2-idc-take-spare b fn2-overlays)))
               (< (mv-nth 1 (fn2-idc-take-spare b fn2-overlays)) (fn2-overlays-rows fn2-overlays))))
 :hints (("Goal" :in-theory (enable fn2-idc-take-spare))))
(in-theory (disable fn2-idc-take-spare))

(defun fn2-idc-bind (d b article binding principal fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) :guard t
 :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert
                                             fn2-id-decides-rows fn2-overlays-rows fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows)))))
 (b* (((unless (and (fn2-id-decides-wfp fn2-id-decides) (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays)
                    (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (and (natp d) (< d (fn2-id-decides-rows fn2-id-decides)) (posp b) (unsigned-byte-p 60 b)))
       (mv :bounds fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (equal (fn2-id-decides-phase d fn2-id-decides) *fn2-id-decide-phase-staged*))
       (mv :state fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code fn2-id-decides fn2-fields fn2-pool) (fn2-idc-rehome d fn2-id-decides fn2-id-engine fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (rows (fn2-overlays-rows fn2-overlays))
      (o (fn2-idc-find-overlay rows 0 *fn2-overlay-phase-private* b fn2-overlays))
      ((mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (if (< o rows)
           (fn2-idc-bind-into o d article binding principal fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
         (mv :full fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
      ((mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (if (eq code :full)
           (b* (((mv code s fn2-overlays) (fn2-idc-take-spare b fn2-overlays))
                ((unless (eq code :ok)) (mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
            (fn2-idc-bind-into s d article binding principal fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
         (mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (fn2-id-decides (fn2-id-decides-put d (phase *fn2-id-decide-phase-bound*) (batch b))))
  (mv :ok fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-idc-bind (d b article binding principal fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-id-decides-phase))
(in-theory (disable fn2-idc-bind))

; Publication of batch B: every fact bound to B moves its bucket's stamp
; (decisions in flight around it go :stale) and is published; then B's
; private overlays become readable (frozen: sealed into runs by C1c's sealer).
;; Two passes over the decision rows bound to B: move each fact's bucket
;; stamp, then mark the rows published.
(defun fn2-idc-publish-stamps (k d b fn2-id-decides fn2-id-stamps)
 (declare (xargs :stobjs (fn2-id-decides fn2-id-stamps) :measure (nfix k)
  :guard (and (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps) (natp k) (natp d))))
 (cond ((or (zp k) (not (and (natp d) (< d (fn2-id-decides-rows fn2-id-decides))))) (mv :ok fn2-id-stamps))
       ((not (and (equal (fn2-id-decides-phase d fn2-id-decides) *fn2-id-decide-phase-bound*)
                  (equal (fn2-id-decides-batch d fn2-id-decides) b)))
        (fn2-idc-publish-stamps (- k 1) (+ 1 d) b fn2-id-decides fn2-id-stamps))
       (t (b* ((bucket (fn2-id-decides-bucket d fn2-id-decides))
               ((unless (and (natp bucket) (< bucket (fn2-id-stamps-rows fn2-id-stamps)))) (mv :bounds fn2-id-stamps))
               (stamp (+ 1 (nfix (fn2-id-stamps-gen bucket fn2-id-stamps))))
               ((unless (unsigned-byte-p 60 stamp)) (mv :bounds fn2-id-stamps))
               (fn2-id-stamps (fn2-id-stamps-set-gen bucket stamp fn2-id-stamps)))
           (fn2-idc-publish-stamps (- k 1) (+ 1 d) b fn2-id-decides fn2-id-stamps)))))
(fn2-id-stamps-preserves fn2-idc-publish-stamps (k d b fn2-id-decides fn2-id-stamps) :position 1)
(defun fn2-idc-publish-marks (k d b fn2-id-decides)
 (declare (xargs :stobjs fn2-id-decides :measure (nfix k) :guard (and (fn2-id-decides-wfp fn2-id-decides) (natp k) (natp d))))
 (cond ((or (zp k) (not (and (natp d) (< d (fn2-id-decides-rows fn2-id-decides))))) fn2-id-decides)
       ((and (equal (fn2-id-decides-phase d fn2-id-decides) *fn2-id-decide-phase-bound*)
             (equal (fn2-id-decides-batch d fn2-id-decides) b))
        (let ((fn2-id-decides (fn2-id-decides-set-phase d *fn2-id-decide-phase-published* fn2-id-decides)))
         (fn2-idc-publish-marks (- k 1) (+ 1 d) b fn2-id-decides)))
       (t (fn2-idc-publish-marks (- k 1) (+ 1 d) b fn2-id-decides))))
(fn2-id-decides-preserves fn2-idc-publish-marks (k d b fn2-id-decides) :position nil)
(defun fn2-idc-publish-overlays (k o b fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :measure (nfix k) :guard (and (fn2-overlays-wfp fn2-overlays) (natp k) (natp o))))
 (cond ((or (zp k) (not (and (natp o) (< o (fn2-overlays-rows fn2-overlays))))) (mv :ok fn2-overlays))
       ((not (and (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-private*)
                  (equal (fn2-overlays-batch o fn2-overlays) b)))
        (fn2-idc-publish-overlays (- k 1) (+ 1 o) b fn2-overlays))
       (t (let ((fn2-overlays (fn2-overlays-put o (phase *fn2-overlay-phase-frozen*) (batch 0))))
           (fn2-idc-publish-overlays (- k 1) (+ 1 o) b fn2-overlays)))))
(fn2-overlays-preserves fn2-idc-publish-overlays (k o b fn2-overlays) :position 1)
(in-theory (disable fn2-idc-publish-overlays))
(defun fn2-idc-publish (b fn2-id-decides fn2-id-stamps fn2-overlays)
 (declare (xargs :stobjs (fn2-id-decides fn2-id-stamps fn2-overlays) :guard t))
 (b* (((unless (and (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps) (fn2-overlays-wfp fn2-overlays)))
       (mv :state fn2-id-decides fn2-id-stamps fn2-overlays))
      ((unless (and (posp b) (unsigned-byte-p 60 b))) (mv :bounds fn2-id-decides fn2-id-stamps fn2-overlays))
      ((mv code fn2-id-stamps) (fn2-idc-publish-stamps (fn2-id-decides-rows fn2-id-decides) 0 b fn2-id-decides fn2-id-stamps))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-id-stamps fn2-overlays))
      (fn2-id-decides (fn2-idc-publish-marks (fn2-id-decides-rows fn2-id-decides) 0 b fn2-id-decides))
      ((mv code fn2-overlays) (fn2-idc-publish-overlays (fn2-overlays-rows fn2-overlays) 0 b fn2-overlays)))
  (mv code fn2-id-decides fn2-id-stamps fn2-overlays)))
(fn2-idc-fn-shape fn2-idc-publish (b fn2-id-decides fn2-id-stamps fn2-overlays) (fn2-id-decides fn2-id-stamps fn2-overlays)
 (fn2-id-decides fn2-id-stamps fn2-overlays))
(in-theory (disable fn2-idc-publish))

; Batch B ended refused: its bound decisions are done again (nothing
; recorded) and its private overlays' arenas are released.
(defun fn2-idc-drop-decisions (k d b fn2-id-decides)
 (declare (xargs :stobjs fn2-id-decides :measure (nfix k) :guard (and (fn2-id-decides-wfp fn2-id-decides) (natp k) (natp d))))
 (cond ((or (zp k) (not (and (natp d) (< d (fn2-id-decides-rows fn2-id-decides))))) fn2-id-decides)
       ((and (equal (fn2-id-decides-phase d fn2-id-decides) *fn2-id-decide-phase-bound*)
             (equal (fn2-id-decides-batch d fn2-id-decides) b))
        (let ((fn2-id-decides (fn2-id-decides-put d (phase *fn2-id-decide-phase-done*) (batch 0))))
         (fn2-idc-drop-decisions (- k 1) (+ 1 d) b fn2-id-decides)))
       (t (fn2-idc-drop-decisions (- k 1) (+ 1 d) b fn2-id-decides))))
(fn2-id-decides-preserves fn2-idc-drop-decisions (k d b fn2-id-decides) :position nil :disable nil)
(in-theory (disable fn2-idc-drop-decisions))
(defun fn2-idc-drop-overlays (k o b fn2-overlays fn2-pool)
 (declare (xargs :stobjs (fn2-overlays fn2-pool) :measure (nfix k)
  :guard (and (fn2-overlays-wfp fn2-overlays) (fn2-pool-wfp fn2-pool) (natp k) (natp o))
 :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert)))))
 (cond ((or (zp k) (not (and (natp o) (< o (fn2-overlays-rows fn2-overlays))))) (mv :ok fn2-overlays fn2-pool))
       ((not (and (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-private*)
                  (equal (fn2-overlays-batch o fn2-overlays) b)))
        (fn2-idc-drop-overlays (- k 1) (+ 1 o) b fn2-overlays fn2-pool))
       (t (b* ((slot (fn2-overlays-slot o fn2-overlays)) (gen (fn2-overlays-gen o fn2-overlays))
               ((unless (fn2-pool-release-countp slot fn2-pool)) (mv :bounds fn2-overlays fn2-pool))
               ((mv code fn2-pool) (fn2-pool-release slot gen *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
               ((unless (eq code :ok)) (mv code fn2-overlays fn2-pool))
               (fn2-overlays (fn2-overlays-put o (phase *fn2-overlay-phase-free*) (batch 0) (count 0) (fill 0))))
           (fn2-idc-drop-overlays (- k 1) (+ 1 o) b fn2-overlays fn2-pool)))))
(fn2-overlays-preserves fn2-idc-drop-overlays (k o b fn2-overlays fn2-pool) :position 1 :disable nil
 :hints (("Goal" :in-theory (disable fn2-pool-release fn2-pool-release-countp fn2-pool-rows fn2-overlays-rows))))
(fn2-pool-preserves fn2-idc-drop-overlays (k o b fn2-overlays fn2-pool) :position 2 :prefix "-POOL-PRESERVES"
 :hints (("Goal" :in-theory (disable fn2-pool-release fn2-pool-release-countp fn2-pool-rows fn2-overlays-rows))))
(in-theory (disable fn2-idc-drop-overlays))
(defun fn2-idc-drop (b fn2-id-decides fn2-overlays fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-overlays fn2-pool) :guard t))
 (b* (((unless (and (fn2-id-decides-wfp fn2-id-decides) (fn2-overlays-wfp fn2-overlays) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-id-decides fn2-overlays fn2-pool))
      ((unless (and (posp b) (unsigned-byte-p 60 b))) (mv :bounds fn2-id-decides fn2-overlays fn2-pool))
      (fn2-id-decides (fn2-idc-drop-decisions (fn2-id-decides-rows fn2-id-decides) 0 b fn2-id-decides))
      ((mv code fn2-overlays fn2-pool) (fn2-idc-drop-overlays (fn2-overlays-rows fn2-overlays) 0 b fn2-overlays fn2-pool)))
  (mv code fn2-id-decides fn2-overlays fn2-pool)))
(fn2-idc-fn-shape fn2-idc-drop (b fn2-id-decides fn2-overlays fn2-pool) (fn2-id-decides fn2-overlays fn2-pool)
 (fn2-id-decides fn2-overlays fn2-pool))
(in-theory (disable fn2-idc-drop))

(in-theory (disable fn2-idc-scratch fn2-idc-spare fn2-idc-stage fn2-idc-rehome fn2-idc-bind-into fn2-idc-bind
                    fn2-idc-publish-stamps fn2-idc-publish-marks fn2-idc-publish-overlays fn2-idc-publish fn2-idc-drop-decisions
                    fn2-idc-drop-overlays fn2-idc-drop))


(defcost fn2-identity-stage :bytes 64
 :tables (fn2-core-id-decides fn2-core-id-stamps fn2-core-run-installed fn2-core-id-engine fn2-core-overlays
          fn2-core-overlay-index fn2-core-fields fn2-core-pool)
 :doc "Validate a finished decision against the published state and hold room for its fact (at most one arena reserved).")
(defcost fn2-identity-bind :bytes 1024
 :tables (fn2-core-id-decides fn2-core-id-engine fn2-core-overlays fn2-core-overlay-index fn2-core-fields fn2-core-pool)
 :doc "Copy a staged offer's octets (at most 282) and insert its fact into its batch's private overlay.")
(defcost fn2-identity-publish :tables (fn2-core-id-decides fn2-core-id-stamps fn2-core-overlays)
 :doc "Make a batch's private overlays readable and move its facts' bucket stamps (one pass over decision and overlay rows).")
(defcost fn2-identity-drop :tables (fn2-core-id-decides fn2-core-overlays fn2-core-pool)
 :doc "Free a refused batch's private overlays and return its decisions to done.")


; Core wrappers of the successor, materialized after the core instance
; (assembly-callbacks-c, after fn2-identity-core-events).
(defmacro fn2-identity-successor-core-events ()
 '(progn
   (defun fn2-identity-stage (d fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-id-stamps (fn2-core-id-stamps fn2-core))
                (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-id-engine (fn2-core-id-engine fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
     (code fn2-id-decides fn2-id-engine fn2-overlays fn2-pool)
     (fn2-idc-stage d fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-identity-stage (d fn2-core) :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-identity-bind (d batch article binding principal fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-id-engine (fn2-core-id-engine fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
     (code fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
     (fn2-idc-bind d batch article binding principal fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-identity-bind (d batch article binding principal fn2-core) :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-identity-publish (batch fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-id-stamps (fn2-core-id-stamps fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)))
     (code fn2-id-decides fn2-id-stamps fn2-overlays)
     (fn2-idc-publish batch fn2-id-decides fn2-id-stamps fn2-overlays)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-identity-publish (batch fn2-core) :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-identity-drop (batch fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
                (fn2-pool (fn2-core-pool fn2-core)))
     (code fn2-id-decides fn2-overlays fn2-pool)
     (fn2-idc-drop batch fn2-id-decides fn2-overlays fn2-pool)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-identity-drop (batch fn2-core) :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (in-theory (disable fn2-identity-stage fn2-identity-bind fn2-identity-publish fn2-identity-drop))
   (assert-event (fn2-assert-compliant-p '(fn2-identity-stage fn2-identity-bind fn2-identity-publish fn2-identity-drop) (w state)))))
