; Layer C in the served core (C-ONE-ASSEMBLY; seam C-S1, fn2/docs/c-ordered-runs.md
; §4 and §8): the engine's resident tables registered as core children, the
; identity decision over them (one decision row per transaction, each in its
; transaction's field-row stripe), the defcosts of the decision's operations
; layer D's transaction machine calls, and their core wrappers
; (fn2-identity-core-events, materialized after the core instance in
; assembly-callbacks-c.lisp). A transaction's writes, the decision's fact
; among them, go through the private successor (C-S3,
; machines-c-successor.lisp), which releases the decision. The run, identity
; and range assemblies are range-served.lisp's.
(in-package "ACL2")
(include-book "range-served")
(include-book "machines-b")
(fn2-book-layer :c)

; ---------------------------------------------------------------------------
; Field rows. B's format work uses a 128-row stripe per format slot from row 0
; (commit.lisp: base = 128 * row); transaction T's stripe is the 1024-row
; stripe ending (transactions - T) stripes before the table's end. machines-b
; sizes the table for both (fn2-b-field-rows). In a stripe (C-STRIPE): the
; successor's write slots from +0, one 48-row block each (C-S3,
; machines-c-successor.lisp), then the identity decision from +768: its offer
; at +0 (Message-ID, content), its lower bound at +2, the decoded entry at
; +4, the run reader at +84 (its rows also take the entry a bind writes).
(defconst *fn2-idc-stride* 1024)
(defconst *fn2-idc-b-stripe* 128)
(defconst *fn2-succ-slots* 16)
(defconst *fn2-succ-block* 48)
(defconst *fn2-idc-ident* (* *fn2-succ-slots* *fn2-succ-block*))
(defconst *fn2-idc-q* *fn2-idc-ident*)
(defconst *fn2-idc-lbq* (+ *fn2-idc-ident* 2))
(defconst *fn2-idc-eb* (+ *fn2-idc-ident* 4))
(defconst *fn2-idc-rb* (+ *fn2-idc-eb* *fn2-run-entry-rows*))
(assert-event (and (<= (+ *fn2-idc-rb* *fn2-run-reader-fields*) *fn2-idc-stride*)
                   (<= (+ *fn2-idc-rb* *fn2-run-entry-rows*) *fn2-idc-stride*)
                   (<= (+ (* (- *fn2-succ-slots* 1) *fn2-succ-block*) *fn2-run-entry-rows*) *fn2-idc-stride*)
                   (equal (fn2-b-field-rows '((:t . 3) (:format-slots . 2))) (+ (* 2 *fn2-idc-b-stripe*) (* 3 *fn2-idc-stride*)))))

(defun fn2-idc-profilep (profile)
 (declare (xargs :guard t))
 (and (unsigned-byte-p 32 (fn2-profile-t profile))
      (unsigned-byte-p 32 (* *fn2-run-max-levels* (nfix (fn2-profile-t profile))))
      (unsigned-byte-p 32 (* *fn2-succ-slots* (nfix (fn2-profile-t profile))))
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
; decision's life) to decision row D, which must be idle or done (a :held
; decision's fact waits on its transaction's batch: refused :state).
(defun fn2-idc-offer (d mslot mgen moff mlen dslot dgen doff okind oslot ogen fcrows
                      fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool) :guard t))
 (b* (((unless (and (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps)
                    (fn2-run-installed-wfp fn2-run-installed) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-id-decides fn2-fields))
      ((mv code q) (fn2-idc-stripe d fcrows fn2-id-decides fn2-fields))
      ((unless (eq code :ok)) (mv code fn2-id-decides fn2-fields))
      ((unless (member (fn2-id-decides-phase d fn2-id-decides)
                       (list *fn2-id-decide-phase-idle* *fn2-id-decide-phase-done*)))
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

(defcost fn2-identity-offer :bytes 256
 :tables (fn2-core-id-decides fn2-core-id-stamps fn2-core-run-installed fn2-core-fields fn2-core-pool fn2-core-fc)
 :doc "Stage an offer's Message-ID and content into its decision row and start the decision (hashes at most 250 octets).")
(defcost fn2-identity-step :bytes 4096
 :tables (fn2-core-id-decides fn2-core-id-stamps fn2-core-overlays fn2-core-overlay-index fn2-core-run-installed
          fn2-core-run-cursors fn2-core-run-paths fn2-core-run-cache fn2-core-fields fn2-core-pool)
 :doc "One bounded step of an identity decision: at most 4,096 pool reads and one overlay block or 32 run entries.")
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
   (in-theory (disable fn2-identity-offer fn2-identity-step))
   (assert-event (fn2-assert-compliant-p '(fn2-identity-offer fn2-identity-step) (w state)))))
