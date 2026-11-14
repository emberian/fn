; A coordinated resident C cut. These handles are sources for a persistent
; builder, never physical references. B publication/drain remains runnable.
(in-package "ACL2")
(include-book "overlay")
(fn2-book-layer :c)

(defcolumns fn2-csnapshot
 ((phase (:enum fn2-csnapshot-phase (:idle :closing :held)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (scan :u32) (blocked :bool) (cut-commit :u60) (cut-event :u60)
  (source :u8) (row :u32) (complete :bool)))

(defcost fn2-csnapshot-state :tables (fn2-core-csnapshot)
 :doc "Read resident snapshot exclusion state.")
(defcost fn2-csnapshot-begin :answers (:ok :busy :bounds :exhausted) :tables (fn2-core-csnapshot)
 :doc "Close new C staging while admitted work drains.")
(defcost fn2-csnapshot-poll :answers (:owner :bounds :more :held) :tables (fn2-core-csnapshot)
 :doc "Inspect one draining transaction, then retain the actual settled commit/event cut.")
(defcost fn2-csnapshot-next :answers (:owner :bounds :more :overlay :run :done) :tables (fn2-core-csnapshot)
 :doc "Enumerate one retained source row; DONE covers every overlay and installed run row.")
(defcost fn2-csnapshot-overlay-entry :answers t :bytes 4096 :tables (fn2-core-fields)
 :doc "Decode one retained sorted overlay entry using its served schema codec.")
(defcost fn2-csnapshot-run-page :answers (:owner :bounds :missing :ok) :bytes 4096
 :doc "Return one held resident run page range; its identity is not a physical reference.")
(defcost fn2-csnapshot-run-info :answers (:owner :bounds :ok)
 :doc "Read a held run's resident root and page interval for codec-based rebuilding.")
(defcost fn2-csnapshot-release :answers (:owner :ok) :tables (fn2-core-csnapshot)
 :doc "Release an exact owner/token resident cut; ambiguous persistence must retain it.")

(defun fn2-csnapshot-ownerp (token okind oslot ogen fn2-csnapshot)
  (declare (xargs :stobjs fn2-csnapshot :guard (fn2-csnapshot-wfp fn2-csnapshot)))
  (and (< 0 (fn2-csnapshot-rows fn2-csnapshot))
       (not (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-idle*))
       (equal token (fn2-csnapshot-token 0 fn2-csnapshot))
       (equal okind (fn2-csnapshot-owner-kind 0 fn2-csnapshot))
       (equal oslot (fn2-csnapshot-owner-slot 0 fn2-csnapshot))
       (equal ogen (fn2-csnapshot-owner-gen 0 fn2-csnapshot))))

(defmacro fn2-csnapshot-op (name args position body)
 `(progn
   (defun ,name (,@args fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    ,body)
   (fn2-core-preserves ,name (,@args fn2-core) :position ,position :rows nil)))

; Core operations are materialized with C's successor wrappers, after the
; assembled core and C's transaction phase constants exist.
(defmacro fn2-csnapshot-core-events ()
 '(progn
 (fn2-csnapshot-op fn2-csnapshot-state () 1
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))) (phase)
   (if (< 0 (fn2-csnapshot-rows fn2-csnapshot)) (fn2-csnapshot-phase 0 fn2-csnapshot)
     *fn2-csnapshot-phase-idle*) (mv phase fn2-core)))

 (fn2-csnapshot-op fn2-csnapshot-begin (okind oslot ogen) 2
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core)))
   (code token fn2-csnapshot)
   (cond ((not (and (< 0 (fn2-csnapshot-rows fn2-csnapshot))
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
          (mv :bounds 0 fn2-csnapshot))
         ((not (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-idle*))
          (mv :busy 0 fn2-csnapshot))
         ((not (unsigned-byte-p 60 (+ 1 (fn2-csnapshot-token 0 fn2-csnapshot))))
          (mv :exhausted 0 fn2-csnapshot))
         (t (let* ((token (+ 1 (fn2-csnapshot-token 0 fn2-csnapshot)))
                   (fn2-csnapshot (fn2-csnapshot-put 0 (phase *fn2-csnapshot-phase-closing*)
                      (token token) (owner-kind okind) (owner-slot oslot) (owner-gen ogen)
                      (scan 0) (blocked 0) (source 0) (row 0) (complete 0))))
              (mv :ok token fn2-csnapshot))))
   (mv code token fn2-core)))



 ; One transaction per poll. No new OPEN transaction may stage after BEGIN;
 ; STAGED/BOUND ones still finish through the ordinary B writer. OPEN rows
 ; are unadmitted work and cannot alter the held visible view.
 (fn2-csnapshot-op fn2-csnapshot-poll (token okind oslot ogen) 3
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))
              (fn2-succ-txns (fn2-core-succ-txns fn2-core))
              (fn2-commit-root (fn2-core-commit-root fn2-core)))
   (code cut event fn2-csnapshot)
   (cond ((not (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot))
          (mv :owner 0 0 fn2-csnapshot))
         ((= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
          (mv :held (fn2-csnapshot-cut-commit 0 fn2-csnapshot)
                    (fn2-csnapshot-cut-event 0 fn2-csnapshot) fn2-csnapshot))
         ((< (fn2-csnapshot-scan 0 fn2-csnapshot) (fn2-succ-txns-rows fn2-succ-txns))
          (if (not (unsigned-byte-p 32 (+ 1 (fn2-csnapshot-scan 0 fn2-csnapshot))))
              (mv :bounds 0 0 fn2-csnapshot)
          (let* ((r (fn2-csnapshot-scan 0 fn2-csnapshot))
                 (phase (fn2-succ-txns-phase r fn2-succ-txns))
                 (blocked (or (= (fn2-csnapshot-blocked 0 fn2-csnapshot) 1)
                              (= phase *fn2-succ-phase-staged*) (= phase *fn2-succ-phase-bound*)))
                 (fn2-csnapshot (fn2-csnapshot-put 0 (scan (+ 1 r)) (blocked (if blocked 1 0)))))
           (mv :more 0 0 fn2-csnapshot))))
         ((or (= (fn2-csnapshot-blocked 0 fn2-csnapshot) 1)
              (not (< 0 (fn2-commit-root-rows fn2-commit-root)))
              (not (= (fn2-commit-root-installed 0 fn2-commit-root)
                      (fn2-commit-root-published 0 fn2-commit-root)))
              (not (= (fn2-commit-root-proposed 0 fn2-commit-root)
                      (fn2-commit-root-published 0 fn2-commit-root))))
          (let ((fn2-csnapshot (fn2-csnapshot-put 0 (scan 0) (blocked 0))))
           (mv :more 0 0 fn2-csnapshot)))
         (t (let* ((cut (fn2-commit-root-published 0 fn2-commit-root))
                   (event (if (zp (fn2-commit-root-first-key 0 fn2-commit-root)) 0
                            (- (fn2-commit-root-first-key 0 fn2-commit-root) 1)))
                   (fn2-csnapshot (fn2-csnapshot-put 0 (phase *fn2-csnapshot-phase-held*)
                                    (cut-commit cut) (cut-event event) (source 0) (row 0) (complete 0))))
              (mv :held cut event fn2-csnapshot))))
   (mv code cut event fn2-core)))

 ; Enumerate the complete resident source set without silently truncating it.
 ; Overlay SEQ and run RUN preserve the served merge precedence. A source is
 ; retained until exact release, including while a builder waits on B I/O.
 (fn2-csnapshot-op fn2-csnapshot-next (token okind oslot ogen) 5
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))
              (fn2-overlays (fn2-core-overlays fn2-core))
              (fn2-run-installed (fn2-core-run-installed fn2-core)))
   (code row sid order entries fn2-csnapshot)
   (b* (((unless (and (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot)
                     (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)))
         (mv :owner 0 0 0 0 fn2-csnapshot))
        (r (fn2-csnapshot-row 0 fn2-csnapshot))
        (source (fn2-csnapshot-source 0 fn2-csnapshot))
        ((unless (or (unsigned-byte-p 32 (+ 1 r))
                     (and (= source 0) (>= r (fn2-overlays-rows fn2-overlays)))
                     (and (= source 1) (>= r (fn2-run-installed-rows fn2-run-installed)))))
         (mv :bounds 0 0 0 0 fn2-csnapshot)))
    (cond ((= source 0)
           (if (>= r (fn2-overlays-rows fn2-overlays))
               (let ((fn2-csnapshot (fn2-csnapshot-put 0 (source 1) (row 0))))
                (mv :more 0 0 0 0 fn2-csnapshot))
            (let* ((phase (fn2-overlays-phase r fn2-overlays))
                   (fn2-csnapshot (fn2-csnapshot-set-row 0 (+ 1 r) fn2-csnapshot)))
             (mv (if (or (= phase *fn2-overlay-phase-active*) (= phase *fn2-overlay-phase-frozen*)) :overlay :more)
                 r (fn2-overlays-schema r fn2-overlays) (fn2-overlays-seq r fn2-overlays)
                 (fn2-overlays-count r fn2-overlays) fn2-csnapshot))))
          ((< r (fn2-run-installed-rows fn2-run-installed))
           (let ((fn2-csnapshot (fn2-csnapshot-set-row 0 (+ 1 r) fn2-csnapshot)))
            (mv (if (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*) :run :more)
                r (fn2-run-installed-schema r fn2-run-installed) (fn2-run-installed-run r fn2-run-installed)
                (fn2-run-installed-entries r fn2-run-installed) fn2-csnapshot)))
          (t (let ((fn2-csnapshot (fn2-csnapshot-set-complete 0 1 fn2-csnapshot)))
              (mv :done 0 0 0 0 fn2-csnapshot)))))
   (mv code row sid order entries fn2-core)))

 ; Decode one overlay entry with the existing served schema codec. The caller
 ; owns its fields stripe and consumes it before another operation reuses it.
 (fn2-csnapshot-op fn2-csnapshot-overlay-entry (token okind oslot ogen row pos base) 2
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))
              (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
              (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
   (code end fn2-fields)
   (if (not (and (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot)
                 (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
                 (natp row) (< row (fn2-overlays-rows fn2-overlays))
                 (or (= (fn2-overlays-phase row fn2-overlays) *fn2-overlay-phase-active*)
                     (= (fn2-overlays-phase row fn2-overlays) *fn2-overlay-phase-frozen*))))
       (mv :owner 0 fn2-fields)
     (fn2-ov-entry row pos base fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
   (mv code end fn2-core)))

 (fn2-csnapshot-op fn2-csnapshot-run-info (token okind oslot ogen row) 7
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))
              (fn2-run-installed (fn2-core-run-installed fn2-core)))
   (code top root counter first last filter)
   (cond ((not (and (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot)
                    (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)))
          (mv :owner 0 0 0 0 0 0))
         ((not (and (natp row) (< row (fn2-run-installed-rows fn2-run-installed))
                    (= (fn2-run-installed-state row fn2-run-installed) *fn2-run-installed-state-live*)))
          (mv :bounds 0 0 0 0 0 0))
         (t (mv :ok (fn2-run-installed-top row fn2-run-installed)
                    (fn2-run-installed-unit row fn2-run-installed) (fn2-run-installed-counter row fn2-run-installed)
                    (fn2-run-installed-ufirst row fn2-run-installed) (fn2-run-installed-ulast row fn2-run-installed)
                    (fn2-run-installed-filter row fn2-run-installed))))
   (mv code top root counter first last filter fn2-core)))

 ; Page intervals are resident source handles. In particular UNIT and COUNTER
 ; here must not escape as persistent Refs: the builder allocates real pages,
 ; re-encodes child references with those identities, then writes and fences.
 (fn2-csnapshot-op fn2-csnapshot-run-page (token okind oslot ogen row unit off len) 9
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))
              (fn2-run-installed (fn2-core-run-installed fn2-core))
              (fn2-run-cache (fn2-core-run-cache fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
   (code slot gen source-kind source-slot source-gen offset length counter)
   (b* (((unless (and (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot)
                     (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)))
         (mv :owner 0 0 0 0 0 0 0 0))
        ((unless (and (natp row) (< row (fn2-run-installed-rows fn2-run-installed))
                      (= (fn2-run-installed-state row fn2-run-installed) *fn2-run-installed-state-live*)
                      (natp unit) (<= (fn2-run-installed-ufirst row fn2-run-installed) unit)
                      (<= unit (fn2-run-installed-ulast row fn2-run-installed))
                      (< 0 (fn2-run-cache-rows fn2-run-cache))
                      (natp off) (natp len) (<= len 4096) (<= (+ off len) *fn2-run-page-size*)))
         (mv :bounds 0 0 0 0 0 0 0 0))
        (c (fn2-run-cache-row unit fn2-run-cache))
        ((unless (and (= (fn2-run-cache-state c fn2-run-cache) *fn2-run-cache-state-ready*)
                      (= (fn2-run-cache-unit c fn2-run-cache) unit)))
         (mv :missing 0 0 0 0 0 0 0 0))
        (slot (fn2-run-cache-slot c fn2-run-cache)) (gen (fn2-run-cache-gen c fn2-run-cache))
        (kind (fn2-run-installed-okind row fn2-run-installed))
        (owner (fn2-run-installed-oslot row fn2-run-installed))
        (generation (fn2-run-installed-ogen row fn2-run-installed))
        ((unless (and (eq (fn2-pool-workspace-code slot gen kind owner generation fn2-pool) :ok)
                      (<= *fn2-run-page-size* (fn2-pool-fill slot fn2-pool))))
         (mv :missing 0 0 0 0 0 0 0 0)))
    (mv :ok slot gen kind owner generation off len (fn2-run-cache-counter c fn2-run-cache)))
   (mv code slot gen source-kind source-slot source-gen offset length counter fn2-core)))

 ; Release never implies persistence or checkpoint completion. The coordinator
 ; must retain this ownership on an ambiguous write/install outcome.
 (fn2-csnapshot-op fn2-csnapshot-release (token okind oslot ogen) 1
  (stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core))) (code fn2-csnapshot)
   (if (not (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot))
       (mv :owner fn2-csnapshot)
     (let ((fn2-csnapshot (fn2-csnapshot-set-phase 0 *fn2-csnapshot-phase-idle* fn2-csnapshot)))
      (mv :ok fn2-csnapshot)))
   (mv code fn2-core)))
 ))
