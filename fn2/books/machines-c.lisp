; Layer C in the served core (C-ONE-ASSEMBLY; seam C-S1, fn2/docs/c-ordered-runs.md
; §4 and §8): the engine's resident tables registered as core children, the
; identity decision over them (one decision row per transaction, each with
; its own field-row stripe), the defcosts of the operations layer D's
; transaction machine calls, and their core wrappers (fn2-identity-core-events,
; materialized after the core instance in assembly-callbacks-c.lisp). The
; run, identity and range assemblies are range-served.lisp's.
(in-package "ACL2")
(include-book "range-served")
(include-book "machines-b")
(fn2-book-layer :c)

; ---------------------------------------------------------------------------
; Field rows. B's format work uses a 128-row stripe per format slot from row 0
; (commit.lisp: base = 128 * row); C's decision D uses the 256-row stripe
; ending (decisions - D) stripes before the table's end. machines-b sizes the
; table for both (fn2-b-field-rows). In a stripe: the offer at +0 (Message-ID,
; content), its lower bound at +2, the decoded entry at +4, the run reader at
; +84 (its rows also take the entry a bind writes).
(defconst *fn2-idc-stride* 256)
(defconst *fn2-idc-b-stripe* 128)
(defconst *fn2-idc-q* 0)
(defconst *fn2-idc-lbq* 2)
(defconst *fn2-idc-eb* 4)
(defconst *fn2-idc-rb* (+ *fn2-idc-eb* *fn2-run-entry-rows*))
(assert-event (and (<= (+ *fn2-idc-rb* *fn2-run-reader-fields*) *fn2-idc-stride*)
                   (<= (+ *fn2-idc-rb* *fn2-run-entry-rows*) *fn2-idc-stride*)
                   (equal (fn2-b-field-rows '((:t . 3) (:format-slots . 2))) (+ (* 2 *fn2-idc-b-stripe*) (* 3 *fn2-idc-stride*)))))

(defun fn2-idc-profilep (profile)
 (declare (xargs :guard t))
 (and (unsigned-byte-p 32 (fn2-profile-t profile))
      (unsigned-byte-p 32 (* *fn2-run-max-levels* (nfix (fn2-profile-t profile))))
      (unsigned-byte-p 32 (fn2-b-capacity :identity-stamps 4096 profile))
      (unsigned-byte-p 32 (fn2-b-capacity :identity-overlays 8 profile))
      (unsigned-byte-p 32 (* (nfix (fn2-b-capacity :identity-overlays 8 profile))
                             (nfix (fn2-b-capacity :identity-overlay-entries 256 profile))))
      (unsigned-byte-p 32 (fn2-b-capacity :identity-runs 64 profile))
      (unsigned-byte-p 32 (fn2-b-capacity :run-cache 1024 profile))
      (unsigned-byte-p 32 (fn2-b-capacity :identity-arena-bytes 65536 profile))
      (<= (+ (* *fn2-idc-b-stripe* (nfix (fn2-b-capacity :format-slots 2 profile)))
             (* *fn2-idc-stride* (nfix (fn2-profile-t profile))))
          (nfix (fn2-b-capacity :format-field-slots (fn2-b-field-rows profile) profile)))))
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

;; Each child's init is a function whose guard is proved here once, so the
;; core init's guard (assembly-init) meets only the opaque profile predicate.
(defmacro fn2-idc-child (field stobj init why)
 (let ((fn (fn2-columns-sym stobj "-INIT-FOR")))
  `(progn
    (defun ,fn (profile ,stobj)
     (declare (xargs :stobjs ,stobj :guard (fn2-idc-profilep profile)
                     :guard-hints (("Goal" :in-theory (enable fn2-idc-profilep)))))
     ,init)
    (defthm ,(fn2-columns-sym fn "-TYPE")
     (implies (and (,(fn2-columns-sym stobj "P") ,stobj) (fn2-idc-profilep profile))
              (,(fn2-columns-sym stobj "P") (,fn profile ,stobj)))
     :hints (("Goal" :in-theory (enable fn2-idc-profilep))))
    (defthm ,(fn2-columns-sym fn "-WFP")
     (implies (fn2-idc-profilep profile) (,(fn2-columns-sym stobj "-WFP") (,fn profile ,stobj)))
     :hints (("Goal" :in-theory (enable fn2-idc-profilep))))
    (in-theory (disable ,fn))
    (defcorechild ,field ,stobj :init (,fn profile ,stobj) :profilep (fn2-idc-profilep profile) :why ,why))))
(in-theory (disable fn2-idc-profilep))
(fn2-idc-child fn2-core-id-decides fn2-id-decides (fn2-id-decides-init (fn2-profile-t profile) fn2-id-decides)
 "One identity decision per transaction survives the transaction's yields (C-S1).")
(fn2-idc-child fn2-core-id-stamps fn2-id-stamps (fn2-id-stamps-init (fn2-b-capacity :identity-stamps 4096 profile) fn2-id-stamps)
 "Bucket stamps make a decision refuse :stale when a fact for its bucket became visible (C-IDENTITY-STALE).")
(fn2-idc-child fn2-core-overlays fn2-overlays (fn2-overlays-init (fn2-b-capacity :identity-overlays 8 profile) fn2-overlays)
 "Bounded sorted overlays hold facts not yet sealed into runs.")
(fn2-idc-child fn2-core-overlay-index fn2-overlay-index
 (fn2-overlay-index-init (* (nfix (fn2-b-capacity :identity-overlays 8 profile))
                            (nfix (fn2-b-capacity :identity-overlay-entries 256 profile))) fn2-overlay-index)
 "Each overlay's key-ordered index of its arena's entries.")
(fn2-idc-child fn2-core-run-installed fn2-run-installed (fn2-run-installed-init (fn2-b-capacity :identity-runs 64 profile) fn2-run-installed)
 "The resident view of each schema's sealed runs.")
(fn2-idc-child fn2-core-run-cursors fn2-run-cursors (fn2-run-cursors-init (fn2-profile-t profile) fn2-run-cursors)
 "A decision's resumable run cursor (cursor row = decision row).")
(fn2-idc-child fn2-core-run-paths fn2-run-paths (fn2-run-paths-init (* *fn2-run-max-levels* (nfix (fn2-profile-t profile))) fn2-run-paths)
 "Each cursor's descent, one row per level.")
(fn2-idc-child fn2-core-id-engine fn2-id-engine (fn2-id-engine-init-arena (fn2-b-capacity :identity-arena-bytes 65536 profile) fn2-id-engine)
 "The engine's bind scratch and arena size (C-S2).")
(fn2-idc-child fn2-core-run-cache fn2-run-cache (fn2-run-cache-init (fn2-b-capacity :run-cache 1024 profile) fn2-run-cache)
 "Verified run pages, keyed by exact (unit, allocation counter).")

; ---------------------------------------------------------------------------
; The decision over the engine's tables. Each checks the tables' shape at run
; time and answers :state when it fails (callers stop).
(defmacro fn2-idc-tables-ok ()
 '(and (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps) (fn2-overlays-wfp fn2-overlays)
       (fn2-overlay-index-wfp fn2-overlay-index) (fn2-run-installed-wfp fn2-run-installed)
       (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache)
       (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))

; Decision D's stripe base, or :bounds when D is no decision row or the
; stripes would reach into B's (FCROWS format slots).
(defun fn2-idc-stripe (d fcrows fn2-id-decides fn2-fields)
 (declare (xargs :stobjs (fn2-id-decides fn2-fields) :guard t))
 (let* ((n (fn2-id-decides-rows fn2-id-decides)) (rows (fn2-fields-rows fn2-fields)))
  (if (and (natp d) (< d n) (natp rows) (natp n)
           (<= (* *fn2-idc-b-stripe* (nfix fcrows)) (- rows (* *fn2-idc-stride* n))))
      (mv :ok (+ (- rows (* *fn2-idc-stride* n)) (* *fn2-idc-stride* d)))
    (mv :bounds 0))))

;; The decision's start, its output shapes proved once.
(fn2-id-decides-preserves fn2-id-decide-start (d qbase lbq eb cursor rb qk qs qg fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool)
 :position 1 :rows nil :disable nil :hints (("Goal" :in-theory (disable fn2-id-lower-query fn2-id-bucket))))
(fn2-fields-preserves fn2-id-decide-start (d qbase lbq eb cursor rb qk qs qg fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool)
 :position 2 :rows nil :prefix "-FIELDS-PRESERVES" :hints (("Goal" :in-theory (disable fn2-id-lower-query fn2-id-bucket))))

; Point decision row D's offer rows (stripe base Q) at the Message-ID octets
; [MOFF, MOFF+MLEN) of MSLOT/MGEN and the content digest [DOFF, DOFF+32) of
; DSLOT/DGEN.
(defun fn2-idc-place (q mslot mgen moff mlen dslot dgen doff fn2-fields)
 (declare (xargs :stobjs fn2-fields :guard (fn2-fields-wfp fn2-fields)))
 (b* (((unless (and (natp q) (< (+ q *fn2-idc-q* 1) (fn2-fields-rows fn2-fields)) (posp mlen) (<= mlen 250)
                    (unsigned-byte-p 32 mslot) (unsigned-byte-p 60 mgen) (unsigned-byte-p 32 moff)
                    (unsigned-byte-p 32 dslot) (unsigned-byte-p 60 dgen) (unsigned-byte-p 32 doff)))
       (mv :bounds fn2-fields))
      (fn2-fields (fn2-fields-put (+ q *fn2-idc-q* *fn2-id-mid*) (value 0) (ref-slot mslot) (ref-gen mgen) (ref-off moff) (ref-len mlen)))
      (fn2-fields (fn2-fields-put (+ q *fn2-idc-q* *fn2-id-con*) (value 1) (ref-slot dslot) (ref-gen dgen) (ref-off doff) (ref-len 32))))
  (mv :ok fn2-fields)))
(fn2-fields-preserves fn2-idc-place (q mslot mgen moff mlen dslot dgen doff fn2-fields) :position 1 :rows nil)

; Offer (Message-ID octets [MOFF, MOFF+MLEN) of MSLOT/MGEN, content digest
; [DOFF, DOFF+32) of DSLOT/DGEN, both readable under OKIND OSLOT OGEN for the
; decision's life) to decision row D, which must be idle or done.
(defun fn2-idc-offer (d mslot mgen moff mlen dslot dgen doff okind oslot ogen fcrows
                      fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool) :guard t))
 (b* (((unless (and (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps)
                    (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-id-decides fn2-fields))
      ((mv code q) (fn2-idc-stripe d fcrows fn2-id-decides fn2-fields))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-fields))
      ((unless (member (fn2-id-decides-phase d fn2-id-decides)
                       (list *fn2-id-decide-phase-idle* *fn2-id-decide-phase-done* *fn2-id-decide-phase-published*)))
       (mv :state fn2-id-decides fn2-fields))
      ((mv code fn2-fields) (fn2-idc-place q mslot mgen moff mlen dslot dgen doff fn2-fields))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-fields)))
  (fn2-id-decide-start d (+ q *fn2-idc-q*) (+ q *fn2-idc-lbq*) (+ q *fn2-idc-eb*) d (+ q *fn2-idc-rb*) okind oslot ogen
                       fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool)))
(fn2-id-decides-preserves fn2-idc-offer (d mslot mgen moff mlen dslot dgen doff okind oslot ogen fcrows
  fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool) :position 1 :rows nil :disable nil)
(fn2-fields-preserves fn2-idc-offer (d mslot mgen moff mlen dslot dgen doff okind oslot ogen fcrows
  fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool) :position 2 :rows nil :prefix "-FIELDS-PRESERVES")

;; The decision step's output shapes, proved once per phase helper: one
;; theorem per helper (type, wfp and rows of every stobj it returns), the
;; helper opened alone, its callees' shapes their books'.
(defun fn2-idc-shape-outs (outs pos)
 (declare (xargs :verify-guards nil))
 (if (atom outs) nil (cons (list (car outs) pos) (fn2-idc-shape-outs (cdr outs) (+ 1 pos)))))
(defmacro fn2-idc-shapes (fn args outs &optional disables (dhyps 't))
 `(progn
   (defthm ,(fn2-columns-sym fn "-IDC-SHAPE")
    (implies (and (fn2-id-decidesp fn2-id-decides) (fn2-id-decides-wfp fn2-id-decides)
                  ,@(and dhyps '((natp d) (< d (fn2-id-decides-rows fn2-id-decides))))
                  (fn2-run-cursorsp fn2-run-cursors) (fn2-run-cursors-wfp fn2-run-cursors)
                  (fn2-run-pathsp fn2-run-paths) (fn2-run-paths-wfp fn2-run-paths)
                  (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))
             (and ,@(fn2-fc-shape-claims (fn2-idc-shape-outs outs 1) (cons fn args))))
    :hints (("Goal" :in-theory (e/d (,fn) (fn2-id-decidesp fn2-id-decides-wfp fn2-run-cursorsp fn2-run-cursors-wfp
                                          fn2-run-pathsp fn2-run-paths-wfp fn2-fieldsp fn2-fields-wfp
                                          fn2-id-decides-rows fn2-run-cursors-rows fn2-run-paths-rows fn2-fields-rows
                                          ,@disables)))))
   (in-theory (disable ,fn))))
(fn2-id-decides-preserves fn2-id-decide-fold (d phase src exact others fn2-id-decides) :position 1
 :hints (("Goal" :in-theory (enable fn2-id-decide-fold))))
(fn2-idc-shapes fn2-id-step-overlay (d fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-id-decides fn2-fields))
(fn2-idc-shapes fn2-id-step-run-start (d fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-cache fn2-fields fn2-pool)
 (fn2-id-decides fn2-run-cursors fn2-fields))
(fn2-idc-shapes fn2-id-step-run-scan (d budget fn2-id-decides fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (fn2-id-decides fn2-run-cursors fn2-run-paths fn2-fields)
 (fn2-id-classify fn2-id-decides-src fn2-id-decides-qbase fn2-id-decides-lbq fn2-id-decides-eb fn2-id-decides-cursor
  fn2-id-decides-rb fn2-id-decides-qk fn2-id-decides-qs fn2-id-decides-qg fn2-id-decides-exact fn2-id-decides-others
  fn2-id-decides-rexact fn2-id-decides-rothers fn2-id-decides-seen fn2-run-cursors-rb fn2-run-cursors-okind
  fn2-run-cursors-oslot fn2-run-cursors-ogen))
(fn2-idc-shapes fn2-id-decide-step (d budget fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                                    fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (fn2-id-decides fn2-run-cursors fn2-run-paths fn2-fields))

; One bounded step of decision D (BUDGET at most 4,096 pool reads): :more,
; :miss (a run page to load: C1c's), or the answer :stored, :duplicate,
; :evidence or :conflict.
(defun fn2-idc-step (d budget fn2-id-decides fn2-id-stamps fn2-overlays fn2-overlay-index fn2-run-installed
                     fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-id-stamps fn2-overlays fn2-overlay-index fn2-run-installed
                          fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) :guard t))
 (if (not (and (fn2-idc-tables-ok) (natp budget) (<= budget 4096) (natp d) (< d (fn2-id-decides-rows fn2-id-decides))))
     (mv (if (fn2-idc-tables-ok) :bounds :state) fn2-id-decides fn2-run-cursors fn2-run-paths fn2-fields)
  (fn2-id-decide-step d budget fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                      fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
(fn2-idc-shapes fn2-idc-step (d budget fn2-id-decides fn2-id-stamps fn2-overlays fn2-overlay-index fn2-run-installed
                              fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (fn2-id-decides fn2-run-cursors fn2-run-paths fn2-fields) nil nil)

; Release decision row D (idle again); a staged or bound decision, whose
; fact waits on its batch, is refused :state.
(defun fn2-idc-release (d fn2-id-decides)
 (declare (xargs :stobjs fn2-id-decides :guard t))
 (cond ((not (and (fn2-id-decides-wfp fn2-id-decides) (natp d) (< d (fn2-id-decides-rows fn2-id-decides))))
        (mv :bounds fn2-id-decides))
       ((member (fn2-id-decides-phase d fn2-id-decides) (list *fn2-id-decide-phase-staged* *fn2-id-decide-phase-bound*))
        (mv :state fn2-id-decides))
       (t (let ((fn2-id-decides (fn2-id-decides-set-phase d *fn2-id-decide-phase-idle* fn2-id-decides)))
           (mv :ok fn2-id-decides)))))
(fn2-id-decides-preserves fn2-idc-release (d fn2-id-decides) :position 1 :rows nil)

(defmacro fn2-idc-owner () '(mv *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen*))

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
(defmacro fn2-idc-op-shape (fn args outs hyps &optional (plain 'nil))
 `(defthm ,(fn2-columns-sym fn "-IDC-SHAPE")
   (implies (and ,@hyps) (and ,@(fn2-fc-shape-claims (if (consp (car outs)) outs (fn2-idc-shape-outs outs 1)) (cons fn args))))
   :hints (("Goal" :in-theory ,(cond ((eq plain :min) `(e/d (,fn) (fn2-overlays-rows fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows)))
                                     ((eq plain :mid) `(e/d (,fn) (fn2-overlays-rows fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows
                                                   fn2-id-engine-rows fn2-id-stamps-rows
                                                   fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read
                                                   fn2-pool-write fn2-pool-class-for)))
                                     (plain `(e/d (,fn) (fn2-overlays-rows fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows
                                                   fn2-id-engine-rows fn2-id-decides-rows fn2-id-stamps-rows
                                                   fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read
                                                   fn2-pool-write fn2-pool-class-for)))
                                     (t
                                 `(e/d (,fn) (fn2-overlaysp fn2-overlays-wfp fn2-overlay-indexp fn2-overlay-index-wfp
                                          fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-overlays-rows
                                          fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows
                                          fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                          fn2-pool-class-for fn2-id-enginep fn2-id-engine-wfp fn2-id-engine-rows
                                          fn2-id-decidesp fn2-id-decides-wfp fn2-id-decides-rows
                                          fn2-id-stampsp fn2-id-stamps-wfp fn2-id-stamps-rows))))))))
(fn2-idc-op-shape fn2-ov-start (o schema slot gen ibase icap okind oslot ogen cov fn2-overlays fn2-overlay-index fn2-pool)
 (fn2-overlays fn2-pool) ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))
(fn2-idc-op-shape fn2-ov-advance (o from to fn2-overlays) (fn2-overlays) ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays)))
(fn2-idc-op-shape fn2-ov-write (o pos ebase fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-overlays fn2-overlay-index fn2-pool)
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
(defmacro fn2-idc-fn-shape (fn args outs stobjs &optional (mode 't))
 `(fn2-idc-op-shape ,fn ,args ,outs ,(fn2-idc-hyp-list stobjs) ,mode))

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
 (fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
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
 (fn2-id-decides fn2-id-engine fn2-fields fn2-pool) :mid)
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
 (fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t)
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


(defcost fn2-identity-offer :bytes 256
 :tables (fn2-core-id-decides fn2-core-id-stamps fn2-core-run-installed fn2-core-fields fn2-core-pool fn2-core-fc)
 :doc "Stage an offer's Message-ID and content into its decision row and start the decision (hashes at most 250 octets).")
(defcost fn2-identity-step :bytes 4096
 :tables (fn2-core-id-decides fn2-core-id-stamps fn2-core-overlays fn2-core-overlay-index fn2-core-run-installed
          fn2-core-run-cursors fn2-core-run-paths fn2-core-run-cache fn2-core-fields fn2-core-pool)
 :doc "One bounded step of an identity decision: at most 4,096 pool reads and one overlay block or 32 run entries.")
(defcost fn2-identity-release :tables (fn2-core-id-decides)
 :doc "Return a decision row to idle.")
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

; Core wrappers, materialized after the core instance (assembly-callbacks-c).
(defmacro fn2-identity-core-events ()
 '(progn
   (defun fn2-identity-offer (d mslot mgen moff mlen dslot dgen doff okind oslot ogen fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-id-stamps (fn2-core-id-stamps fn2-core))
                (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-fields (fn2-core-fields fn2-core))
                (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code fn2-id-decides fn2-fields)
     (fn2-idc-offer d mslot mgen moff mlen dslot dgen doff okind oslot ogen (fn2-fc-rows fn2-fc)
                    fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-identity-offer (d mslot mgen moff mlen dslot dgen doff okind oslot ogen fn2-core)
    :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-identity-step (d budget fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-id-stamps (fn2-core-id-stamps fn2-core))
                (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
                (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-run-cursors (fn2-core-run-cursors fn2-core))
                (fn2-run-paths (fn2-core-run-paths fn2-core)) (fn2-run-cache (fn2-core-run-cache fn2-core))
                (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
     (answer fn2-id-decides fn2-run-cursors fn2-run-paths fn2-fields)
     (fn2-idc-step d budget fn2-id-decides fn2-id-stamps fn2-overlays fn2-overlay-index fn2-run-installed
                   fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
     (mv answer fn2-core)))
   (fn2-core-preserves fn2-identity-step (d budget fn2-core)
    :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
   (defun fn2-identity-release (d fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)))
     (code fn2-id-decides)
     (fn2-idc-release d fn2-id-decides)
     (mv code fn2-core)))
   (fn2-core-preserves fn2-identity-release (d fn2-core)
    :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
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
   (in-theory (disable fn2-identity-offer fn2-identity-step fn2-identity-release fn2-identity-stage fn2-identity-bind
                       fn2-identity-publish fn2-identity-drop))
   (assert-event (fn2-assert-compliant-p '(fn2-identity-offer fn2-identity-step fn2-identity-release fn2-identity-stage
                                           fn2-identity-bind fn2-identity-publish fn2-identity-drop) (w state)))))
