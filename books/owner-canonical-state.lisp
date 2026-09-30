; Full-context canonical sidecar installation/lifecycle boundary.
; Correspondence is a producer proof obligation, never a served graph scan.
(in-package "ACL2")
(include-book "store-tree-size")
(include-book "owner-canonical-epoch")
(include-book "snapshot-source-token")

(defun fn-owner-canonical-state (state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-owner-canonical-state state)
       (f-get-global 'fn-owner-canonical-state state)))

(defun fn-owner-canonical-reset (state)
  (declare (xargs :stobjs state :guard t))
  (let* ((epoch (fn-owner-canonical-epoch state))
         (state (f-put-global 'fn-owner-canonical-state nil state))
         (state (f-put-global 'fn-owner-canonical-pending nil state)))
    ; An invalid prior epoch stays unavailable; it is never silently reused.
    (f-put-global 'fn-owner-canonical-epoch
                  (if (natp epoch) (1+ epoch) :fault) state)))

; Ten retained cells: ready,owner epoch,durable count,ORIGINAL fullctx6,
; six field carries,actual CP7,seven field carries,padded pool bytes,rows,source4.
; COUNT is the complete Store event count (fn-sf-records-count at ready),
; never the process completion ledger count. ROWS is a separate coordinate.
; Counter width, ten-cell retention and all producer allocation funding are
; preflight obligations of the actual installer; no supported-profile claim
; follows from these natural-integer representation checks.
; The caller establishes correspondence through its actual authenticated
; bootstrap. This function checks only bounded metadata and scalar lineage.
(defun fn-owner-canonical-install (epoch count ctx fields cp7 cpfields
                                        pool rows source state)
  (declare (xargs :stobjs state :guard t))
  (if (not (and (natp epoch) (equal epoch (fn-owner-canonical-epoch state))
                (natp count) (natp pool) (equal (mod pool 8) 0) (natp rows)
                (fn-omk-widthp ctx 6) (eq (fn-omk-at 0 ctx) :ok)
                (natp (fn-omk-at 1 ctx))
                (or (natp (fn-omk-at 4 ctx)) (null (fn-omk-at 4 ctx)))
                (symbolp (fn-omk-at 5 ctx)) (fn-omk-widthp cp7 7)
                (fn-scs-fixed-carriesp 6 fields)
                (fn-scs-fixed-carriesp 7 cpfields) (fn-omk-tokenp source)))
      (mv :refused state)
    (let* ((state (f-put-global 'fn-owner-canonical-state
                               (list :ready epoch count ctx fields cp7 cpfields
                                     pool rows source) state))
           (state (f-put-global 'fn-owner-canonical-pending nil state)))
      (mv :installed state))))

(defun fn-owner-canonical-availablep (durable-count state)
  (declare (xargs :stobjs state :guard t))
  (let ((c (fn-owner-canonical-state state)))
    (and (fn-omk-widthp c 10) (eq (fn-omk-at 0 c) :ready)
         (natp (fn-owner-canonical-epoch state))
         (equal (fn-omk-at 1 c) (fn-owner-canonical-epoch state))
         (natp durable-count) (equal (fn-omk-at 2 c) durable-count))))

; Called under the same owner mutex as cheapcapture6. Return the existing
; immutable ten-cell tuple, without copying its graphs or widening cheap6.
; The actual capture controller checks its Store count with AVAILABLEP under
; that mutex; producer/writer correspondence remains its carried invariant.
(defun fn-owner-canonical-ready-capture (state)
  (declare (xargs :stobjs state :guard t))
  (let ((c (fn-owner-canonical-state state)))
    (if (and (fn-omk-widthp c 10) (eq (fn-omk-at 0 c) :ready)
             (natp (fn-owner-canonical-epoch state))
             (equal (fn-omk-at 1 c) (fn-owner-canonical-epoch state)))
        c
      '(:unavailable :canonical-size))))

(defthm fn-owner-canonical-reset-clears-ready-by-definition
 (not (fn-owner-canonical-state (fn-owner-canonical-reset state)))
 :hints (("Goal" :in-theory (enable fn-owner-canonical-state fn-owner-canonical-reset))))
(defthm fn-owner-canonical-install-stores-inputs-by-definition
 (implies (equal (mv-nth 0 (fn-owner-canonical-install
                           epoch count ctx fields cp7 cpfields pool rows source state))
                 :installed)
  (equal (fn-owner-canonical-state
          (mv-nth 1 (fn-owner-canonical-install
                     epoch count ctx fields cp7 cpfields pool rows source state)))
         (list :ready epoch count ctx fields cp7 cpfields pool rows source)))
 :hints (("Goal" :in-theory (enable fn-owner-canonical-state fn-owner-canonical-install))))

(defthm fn-owner-canonical-reset-epoch-by-definition
 (equal (fn-owner-canonical-epoch (fn-owner-canonical-reset state))
        (if (natp (fn-owner-canonical-epoch state))
            (1+ (fn-owner-canonical-epoch state)) :fault))
 :hints (("Goal" :in-theory (enable fn-owner-canonical-epoch fn-owner-canonical-reset))))

(defthm fn-owner-canonical-reset-preserves-state-p1-by-definition
 (implies (state-p1 state) (state-p1 (fn-owner-canonical-reset state)))
 :hints (("Goal" :in-theory (enable fn-owner-canonical-reset))))
(defthm fn-owner-canonical-install-preserves-state-p1-by-definition
 (implies (state-p1 state)
  (state-p1 (mv-nth 1 (fn-owner-canonical-install
                      epoch count ctx fields cp7 cpfields pool rows source state))))
 :hints (("Goal" :in-theory (enable fn-owner-canonical-install))))
(defthm fn-owner-canonical-reset-frames-global-by-definition
 (implies (not (member-equal key '(fn-owner-canonical-state fn-owner-canonical-pending
                                  fn-owner-canonical-epoch)))
  (equal (assoc-equal key (nth 2 (fn-owner-canonical-reset state)))
         (assoc-equal key (nth 2 state))))
 :hints (("Goal" :in-theory (enable fn-owner-canonical-reset))))

(in-theory (disable fn-owner-canonical-epoch fn-owner-canonical-state
                    fn-owner-canonical-reset fn-owner-canonical-install
                    fn-owner-canonical-availablep
                    fn-owner-canonical-ready-capture))
