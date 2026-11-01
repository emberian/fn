; Layer C1c: the sealer machine in the served core. The kind is declared in
; machines-c-sealer-kind.lisp (its registry position is the engine owner's
; kind); here: its tables registered as core children, the field stripe,
; and the genesis and readiness over its own tables. The core events
; (wrappers, C's attachment of the grant service's :sealable source, the
; engine genesis, the continuations and run) are machines-c-sealer-events.lisp.
;
; Resources. The seal row, one run build, the build's six level writers and
; the filter's (*fn2-seal-writer-rows*), their restart rows, one Ribbon build
; and its band (sized for one overlay's entries) are C's own children. The
; field rows are the sealer's stripe of B's fields table (*fn2-b-seal-field-rows*,
; just below the transactions' stripes, which are anchored at the table's
; end); the checker row is 3 + :large-upload-windows of B's format-check
; tables, its digest regions 129-135 (B's named regions are 0-128).
(in-package "ACL2")
(include-book "sealer")
(fn2-book-layer :c)

(assert-event (<= *fn2-seal-field-rows* *fn2-b-seal-field-rows*))
(defconst *fn2-sealer-fill* *fn2-run-page-size*)
(defun fn2-sealer-windows (profile)
 (declare (xargs :guard t))
 (fn2-b-upload-windows profile))
(defun fn2-sealer-profilep (profile)
 (declare (xargs :guard t))
 (and (unsigned-byte-p 32 (fn2-b-capacity :identity-overlay-entries 256 profile))
      (natp (fn2-b-capacity :identity-overlay-entries 256 profile))
      (unsigned-byte-p 32 (fn2-ribbon-slots (nfix (fn2-b-capacity :identity-overlay-entries 256 profile))))))
(in-theory (disable fn2-sealer-windows))

(defmacro fn2-sealer-child (field stobj init why)
 (let ((fn (fn2-columns-sym stobj "-INIT-FOR")))
  `(progn
    (defun ,fn (profile ,stobj)
     (declare (xargs :stobjs ,stobj :guard (fn2-sealer-profilep profile)
                     :guard-hints (("Goal" :in-theory (enable fn2-sealer-profilep))))
              (ignorable profile))
     ,init)
    (defthm ,(fn2-columns-sym fn "-TYPE")
     (implies (and (,(fn2-columns-sym stobj "P") ,stobj) (fn2-sealer-profilep profile))
              (,(fn2-columns-sym stobj "P") (,fn profile ,stobj)))
     :hints (("Goal" :in-theory (enable fn2-sealer-profilep))))
    (defthm ,(fn2-columns-sym fn "-WFP")
     (implies (fn2-sealer-profilep profile) (,(fn2-columns-sym stobj "-WFP") (,fn profile ,stobj)))
     :hints (("Goal" :in-theory (enable fn2-sealer-profilep))))
    (in-theory (disable ,fn))
    (defcorechild ,field ,stobj :init (,fn profile ,stobj) :profilep (fn2-sealer-profilep profile) :why ,why))))
(in-theory (disable fn2-sealer-profilep))
(fn2-sealer-child fn2-core-seals fn2-seals (fn2-seals-init 1 fn2-seals)
 "The sealer's one seal row: its phase, the overlay, the next entry, the run, and its resources (C1c).")
(fn2-sealer-child fn2-core-run-builds fn2-run-builds (fn2-run-builds-init 1 fn2-run-builds)
 "The sealer's run build survives its yields.")
(fn2-sealer-child fn2-core-run-writers fn2-run-writers (fn2-run-writers-init *fn2-seal-writer-rows* fn2-run-writers)
 "The build's level writers and the filter's page writer.")
(fn2-sealer-child fn2-core-run-restarts fn2-run-restarts
 (fn2-run-restarts-init (* *fn2-seal-writer-rows* *fn2-run-restart-capacity*) fn2-run-restarts)
 "Each writer's restart points, written after its page's last entry.")
(fn2-sealer-child fn2-core-ribbon-builds fn2-ribbon-builds (fn2-ribbon-builds-init 1 fn2-ribbon-builds)
 "The sealer's Ribbon filter build for an identity run.")
(fn2-sealer-child fn2-core-ribbon-band fn2-ribbon-band
 (fn2-ribbon-band-init (fn2-ribbon-slots (nfix (fn2-b-capacity :identity-overlay-entries 256 profile))) fn2-ribbon-band)
 "The filter build's band, one row per slot of one overlay's keys.")

; The sealer's field stripe: just below the transactions' stripes (C-STRIPE
; anchors them at the table's end), above B's per-slot stripes.
(defun fn2-sealer-fbase (fcrows trows rows)
 (declare (xargs :guard t))
 (let ((top (- (nfix rows) (+ (* *fn2-idc-stride* (nfix trows)) *fn2-b-seal-field-rows*))))
  (if (and (<= (* *fn2-idc-b-stripe* (nfix fcrows)) top) (unsigned-byte-p 32 top)) (mv :ok top) (mv :bounds 0))))

;; The genesis and readiness over the sealer's own tables (their core
;; wrappers below only bind the children).
(defun fn2-seal-genesis (profile fcrows trows frows fn2-seals)
 (declare (xargs :stobjs fn2-seals :guard (fn2-seals-wfp fn2-seals)))
 (b* ((crow (+ 3 (fn2-sealer-windows profile)))
      ((unless (< crow (nfix fcrows))) (mv :no-row fn2-seals))
      ((mv c fbase) (fn2-sealer-fbase fcrows trows frows))
      ((unless (eq c :ok)) (mv c fn2-seals)))
  (fn2-seal-init 0 fbase crow *fn2-sealer-fill* *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-seals)))
(fn2-seal-shape fn2-seal-genesis (profile fcrows trows frows fn2-seals) (fn2-seals) (fn2-seals) t (fn2-seal-init fn2-sealer-fbase))
(defun fn2-seal-pending-p (fn2-seals fn2-overlays)
 (declare (xargs :stobjs (fn2-seals fn2-overlays) :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays))))
 (and (< 0 (fn2-seals-rows fn2-seals)) (equal (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-idle*)
      (< (fn2-seal-pick (fn2-overlays-rows fn2-overlays) 0 (fn2-overlays-rows fn2-overlays) fn2-overlays)
         (fn2-overlays-rows fn2-overlays))))
(in-theory (disable fn2-seal-pending-p))

