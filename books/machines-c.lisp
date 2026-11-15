; Layer C in the served core (C-ONE-ASSEMBLY; seam C-S1, docs/c-ordered-runs.md
; §4a and §8): the engine's resident tables registered as core children, and
; each transaction's field-row stripe. The identity decision over them is
; machines-c-groups.lisp's (two exact reads); a transaction's writes go
; through the private successor (C-S3, machines-c-successor.lisp). The run
; and range assemblies are range-served.lisp's.
(in-package "ACL2")
(include-book "range-served")
(include-book "machines-b")
(include-book "successor-schema-geometry")
(include-book "c-snapshot")
(include-book "checkpoint-summary-state")
(include-book "run-physical-geometry")
(include-book "run-physical-harvest")
(include-book "startup-genesis-state")
(include-book "c-source-observer")
(fn2-book-layer :c)

; ---------------------------------------------------------------------------
; Field rows. B's format work uses a 128-row stripe per format slot from row 0
; (commit.lisp: base = 128 * row); transaction T's stripe is the
; *fn2-b-txn-field-rows*-row supported stripe ending (transactions - T) stripes before
; the table's end. machines-b sizes the table for both (fn2-b-field-rows). In
; a stripe (C-STRIPE): the successor's 24 write slots from +0, one 48-row
; block each (C-S3, machines-c-successor.lisp), then the exact lookup's area
; from +1152: its query at +4 (the identity decision's key: namespace, name,
; profile, algorithm, digest), the run reader at +84 (its rows also take the
; entry a bind writes).
(defconst *fn2-idc-stride* *fn2-b-txn-field-rows*)
(defconst *fn2-idc-b-stripe* 128)
(defconst *fn2-succ-slots* 24)

(defconst *fn2-idc-ident* (* *fn2-succ-slots* *fn2-succ-block*))
(defconst *fn2-idc-eb* (+ *fn2-idc-ident* 4))
(defconst *fn2-idc-rb* (+ *fn2-idc-eb* *fn2-run-entry-rows*))
(defconst *fn2-idc-required-fields*
 (fn2-successor-required-fields *fn2-succ-fields-max* *fn2-succ-values-max*
  *fn2-succ-slots* *fn2-run-entry-rows* *fn2-run-reader-fields*))
(assert-event (<= *fn2-idc-required-fields* *fn2-idc-stride*))
(assert-event (and (<= (+ *fn2-idc-rb* *fn2-run-reader-fields*) *fn2-idc-stride*)
                   (<= (+ *fn2-idc-rb* *fn2-run-entry-rows*) *fn2-idc-stride*)
                   (<= (+ (* (- *fn2-succ-slots* 1) *fn2-succ-block*) *fn2-run-entry-rows*) *fn2-idc-stride*)
                   (equal (fn2-b-field-rows '((:t . 3) (:format-slots . 2))) (+ (* 2 *fn2-idc-b-stripe*) (* 3 *fn2-idc-stride*) *fn2-b-seal-field-rows* *fn2-b-checkpoint-field-rows*))))

;; The overlay rows a profile gets when it names none (:identity-overlays):
;; a batch takes one private overlay per schema it writes, and a POST
;; writes up to 10 today (the five identity records, article, outcome,
;; counts, overview, addr) of the 16 a transaction could name; B keeps two
;; batches in flight (its two commit rows) and the sealer works on the
;; frozen ones behind them. So 16 schemas x 3 batches. Each overlay in use
;; holds one arena of :identity-arena-bytes from the pool; the pool must
;; carry them (c-ordered-runs.md §5, capacity).
(defconst *fn2-idc-overlays-default* 48)
;; The sealer's merge (C5, sealer.lisp) reads at most eight sources, one run
;; cursor each, after every read row's (t + 9R ..).
(defconst *fn2-idc-seal-cursors* 8)
;; A reader merges at most *fn2-idc-seal-cursors* (8) sources of a schema:
;; its overlays (active, frozen or private) and its live runs. The sealer
;; keeps a schema to *fn2-idc-run-budget* runs (it merges every run once a
;; schema holds that many, sealer.lisp) and stage keeps it to
;; *fn2-idc-overlay-budget* overlays (a transaction that would take one more
;; waits, :full, until the sealer catches up: machines-c-stage.lisp).
(defconst *fn2-idc-run-budget* 4)
(defconst *fn2-idc-overlay-budget* (- *fn2-idc-seal-cursors* *fn2-idc-run-budget*))
;; Source observers name actual resumable operation rows, not actor identities.
;; Reads and successor resolutions have distinct endpoints even when one actor
;; owns both.  Their following endpoint protects the complete sealer merge;
;; cursor-response and CNS-metadata parents occupy the disjoint tail.
(defun fn2-c-source-endpoint-rows (profile)
 (declare (xargs :guard t))
 (+ 1 (nfix (fn2-profile-t profile)) (* 2 (fn2-b-read-rows profile))
    (fn2-b-cursor-rows profile) (fn2-b-cns-rows profile)))
(defun fn2-c-source-successor-endpoint (read-rows tx)
 (declare (xargs :guard (and (natp read-rows) (natp tx))))
 (+ read-rows tx))
(defun fn2-c-source-sealer-endpoint (read-rows successor-rows)
 (declare (xargs :guard (and (natp read-rows) (natp successor-rows))))
 (+ read-rows successor-rows))
(defun fn2-c-source-request-endpoint (read-rows successor-rows cursor-row)
 (declare (xargs :guard (and (natp read-rows) (natp successor-rows) (natp cursor-row))))
 (+ 1 read-rows successor-rows cursor-row))
(defun fn2-c-source-cns-endpoint (read-rows successor-rows cursor-rows cns-row)
 (declare (xargs :guard (and (natp read-rows) (natp successor-rows) (natp cursor-rows) (natp cns-row))))
 (+ 1 read-rows successor-rows cursor-rows cns-row))
(defthm fn2-c-source-endpoint-rows-natp
 (natp (fn2-c-source-endpoint-rows profile)) :rule-classes :type-prescription)
(defun fn2-idc-profilep (profile)
 (declare (xargs :guard t))
 (and (unsigned-byte-p 32 (fn2-c-source-endpoint-rows profile))
      (unsigned-byte-p 32 (fn2-profile-t profile))
      (unsigned-byte-p 32 (* *fn2-run-max-levels* (nfix (fn2-profile-t profile))))
      (unsigned-byte-p 32 (* *fn2-succ-slots* (nfix (fn2-profile-t profile))))
      (unsigned-byte-p 32 (fn2-b-capacity :identity-overlays *fn2-idc-overlays-default* profile))
      (unsigned-byte-p 32 (* (nfix (fn2-b-capacity :identity-overlays *fn2-idc-overlays-default* profile))
                             (nfix (fn2-b-capacity :identity-overlay-entries 256 profile))))
      (unsigned-byte-p 32 (fn2-b-capacity :identity-runs 64 profile))
      (unsigned-byte-p 32 (fn2-b-capacity :run-cache 1024 profile))
      (unsigned-byte-p 32 (fn2-b-capacity :identity-arena-bytes 65536 profile))
      ;; Layer D's read rows (C-S4, machines-c-read.lisp): R of them, each
      ;; with 8 range sources, a lookup row and cursor after the
      ;; transactions' (t + R) and 8 source cursors after those (t + 9R).
      (unsigned-byte-p 32 (fn2-b-run-cursor-rows profile))
      (unsigned-byte-p 32 (* *fn2-run-max-levels* (fn2-b-run-cursor-rows profile)))
<<<<<<< HEAD
      (<= (+ (* *fn2-idc-b-stripe* (nfix (fn2-b-format-slots profile)))
             (* *fn2-idc-stride* (nfix (fn2-profile-t profile))) *fn2-b-seal-field-rows* *fn2-b-checkpoint-field-rows*
             (* *fn2-b-read-stride* (fn2-b-read-rows profile)))
          (nfix (fn2-b-capacity :format-field-slots (fn2-b-field-rows profile) profile)))
      (unsigned-byte-p 32 (fn2-b-run-cursor-rows profile))
      (unsigned-byte-p 32 (+ 4 (fn2-b-upload-windows profile) (fn2-b-run-cursor-rows profile)))))
=======
      (and (posp (fn2-b-capacity :extent-slots 16 profile)) (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile)) (unsigned-byte-p 32 (+ (fn2-b-capacity :identity-runs 64 profile) (* 2 (fn2-b-capacity :extent-slots 16 profile)))))))
>>>>>>> 4161477a4 (Configure resident prefix and two physical replacement banks)

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
(fn2-idc-child fn2-core-c-source-control fn2-c-source-control
 (fn2-c-source-control-init 1 fn2-c-source-control)
 "Writer preference closes new semantic observers before bounded live source replacement.")
(fn2-idc-child fn2-core-c-source-readers fn2-c-source-readers
 (fn2-c-source-readers-init (fn2-c-source-endpoint-rows profile) fn2-c-source-readers)
 "One exact receipt per read, successor, sealer, complete cursor response, and CNS metadata endpoint survives yields until references are dead.")
(fn2-idc-child fn2-core-csnapshot fn2-csnapshot (fn2-csnapshot-init 1 fn2-csnapshot)
 "One exact-owner resident metadata cut excludes staging and materialization until released.")
(fn2-idc-child fn2-core-id-decides fn2-id-decides (fn2-id-decides-init (fn2-profile-t profile) fn2-id-decides)
 "One identity decision per transaction survives the transaction's yields (C-S1).")
(fn2-idc-child fn2-core-overlays fn2-overlays (fn2-overlays-init (fn2-b-capacity :identity-overlays *fn2-idc-overlays-default* profile) fn2-overlays)
 "Bounded sorted overlays hold facts not yet sealed into runs.")
(fn2-idc-child fn2-core-overlay-index fn2-overlay-index
 (fn2-overlay-index-init (* (nfix (fn2-b-capacity :identity-overlays *fn2-idc-overlays-default* profile))
                            (nfix (fn2-b-capacity :identity-overlay-entries 256 profile))) fn2-overlay-index)
 "Each overlay's key-ordered index of its arena's entries.")
(fn2-idc-child fn2-core-run-installed fn2-run-installed (fn2-run-installed-init-configured (fn2-b-capacity :identity-runs 64 profile) (fn2-b-capacity :extent-slots 16 profile) fn2-run-installed)
 "The resident view of each schema's sealed runs.")
(fn2-idc-child fn2-core-run-cursors fn2-run-cursors
 (fn2-run-cursors-init (fn2-b-run-cursor-rows profile) fn2-run-cursors)
 "A decision's resumable run cursor (cursor row = decision row), then each read row's lookup cursor and its range sources' (C-S4).")
(fn2-idc-child fn2-core-checkpoint-summary-leases fn2-checkpoint-summary-leases
 (fn2-checkpoint-summary-leases-init (fn2-b-run-cursor-rows profile) fn2-checkpoint-summary-leases)
 "Every actual C cursor can retain one exact selected physical source across yields.")
(fn2-idc-child fn2-core-run-loads fn2-run-loads
 (fn2-run-load-profile-init profile fn2-run-loads)
 "A private authenticated 64KiB page and sector workspace per active physical cursor.")
(defcorechild fn2-core-run-load-ops fn2-run-load-ops
 :init (fn2-run-load-ops-init (fn2-profile-o profile) fn2-run-load-ops)
 :profilep (unsigned-byte-p 32 (fn2-profile-o profile))
 :harvest (fn2-run-load-harvest ((fn2-core-run-loads fn2-run-loads) (fn2-core-run-load-ops fn2-run-load-ops)))
 :why "Route exact physical read completions before operation finish, without scanning active cursors.")
(defcorechild fn2-core-run-load-geometry fn2-run-load-geometry
 :init (fn2-run-load-geometry-profile-init profile fn2-run-load-geometry)
 :profilep (fn2-run-load-geometry-profilep profile)
 :why "Readonly profile-derived cursor/checker geometry binds the cold loader capability scan.")
(defcorechild fn2-core-run-load-readiness fn2-run-load-readiness
 :init (fn2-run-load-readiness-init 1 fn2-run-load-readiness) :profilep t
 :why "The cold capability scan retains selected identity, exact EOF and admissions serial across turns.")
(fn2-idc-child fn2-core-run-paths fn2-run-paths
 (fn2-run-paths-init (* *fn2-run-max-levels* (fn2-b-run-cursor-rows profile)) fn2-run-paths)
 "Each cursor's descent, one row per level.")
(fn2-idc-child fn2-core-run-cache fn2-run-cache (fn2-run-cache-init (fn2-b-capacity :run-cache 1024 profile) fn2-run-cache)
 "Verified run pages, keyed by exact (unit, allocation counter).")

; ---------------------------------------------------------------------------
; Decision D's stripe base, or :bounds when D is no decision row or the
; stripes would reach into B's (FCROWS format slots).
(defun fn2-idc-stripe (d fcrows fn2-id-decides fn2-fields)
 (declare (xargs :stobjs (fn2-id-decides fn2-fields) :guard t))
 (let* ((n (fn2-id-decides-rows fn2-id-decides)) (rows (fn2-fields-rows fn2-fields)))
  (if (and (natp d) (< d n) (natp rows) (natp n)
           (<= (* *fn2-idc-b-stripe* (nfix fcrows)) (- rows (* *fn2-idc-stride* n))))
      (mv :ok (+ (- rows (* *fn2-idc-stride* n)) (* *fn2-idc-stride* d)))
    (mv :bounds 0))))

; The output positions of OUTS from POS, for the shape theorems
; (machines-c-successor.lisp's fn2-idc-fn-shape).
(defun fn2-idc-shape-outs (outs pos)
 (declare (xargs :verify-guards nil))
 (if (atom outs) nil (cons (list (car outs) pos) (fn2-idc-shape-outs (cdr outs) (+ 1 pos)))))

(include-book "run-physical-step")
(include-book "run-physical-release")

; Included after machines-c registers the actual cursor, catalog lease and
; loader children. Every issue is explicit in a machine :issue arm.
(defcost fn2-run-page-reserve :child fn2-run-load-reserve :answers t
 :tables (fn2-core-run-loads fn2-core-pool) :effects :per-use
 :doc "Acquire both private cursor windows atomically or refuse without parking.")
(defcost fn2-run-page-bind :child fn2-run-load-bind :answers t
 :tables (fn2-core-run-loads fn2-core-run-cursors fn2-core-checkpoint-summary fn2-core-checkpoint-summary-sources fn2-core-checkpoint-summary-leases fn2-core-run-installed fn2-core-pool)
 :bytes 64
 :doc "Bind a current physical MISS Ref and exact catalog lease to the request-owned page.")
(defcost fn2-run-page-step :child fn2-run-load-step :answers t
 :tables (fn2-core-run-loads fn2-core-run-cursors fn2-core-checkpoint-summary fn2-core-checkpoint-summary-sources fn2-core-checkpoint-summary-leases fn2-core-run-installed fn2-core-boot-config fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-fields fn2-core-pool fn2-core-digests)
 :bytes 4096
 :doc "Copy or authenticate one bounded page fragment; expose only after full Ref and typed header verification.")
(make-event
 (value (cons 'progn
  (append (fn2-issue-wrapper-effect-events '(fn2-run-load-issue) (w state))
          (fn2-issued-wrapper-events '(fn2-run-load-issue) (w state))))))
(defcost fn2-run-page-read :child fn2-run-load-issue :answers t :descriptors 1
 :tables (fn2-core-run-loads fn2-core-run-load-ops fn2-core-run-cursors fn2-core-checkpoint-summary fn2-core-checkpoint-summary-sources fn2-core-checkpoint-summary-leases fn2-core-run-installed fn2-core-extents fn2-core-alloc-edges fn2-core-pool fn2-core-ops fn2-core-control)
 :effects ((:acquire (:operation)))
 :doc "Pin and issue exactly one 4KiB read, returning its actual operation slot/generation.")
(defcost fn2-run-page-release :child fn2-run-load-release :answers t
 :tables (fn2-core-run-loads fn2-core-run-cursors fn2-core-checkpoint-summary fn2-core-checkpoint-summary-leases fn2-core-pool)
 :effects :per-use
 :doc "Release request-owned pages only after pending0 and workspace return, then release the catalog lease.")
