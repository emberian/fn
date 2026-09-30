; Actual retained writer executor. Native holds owner exclusion over sealed
; prepare, gate, BODY, reservation and arena capture. No host demand authority.
(in-package "ACL2")
(include-book "index-writer-begin-host")
(include-book "../books/index-backing-writer-step")
(include-book "../books/allocation-turn-raw-bridge")
(include-book "owner-host")
(include-book "../books/index-writer-ticket")
(program)

; Missing selected-runtime BODY lowering is this exact unit. An available
; PRS demand is not a heap-allocation tariff. No caller supplies BODY bytes.
(defun fn-owner-index-writer-body-request (census family table)
 (declare (ignore census family table))
 (mv :runtime-operation-unavailable nil))

(defun fn-owner-index-writer-refuse (slot nonce reason fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)))
 (mv-let (word fn-allocation-turn-slots fn-page-read-pool)
  (fn-ats-finish-owned slot nonce fn-allocation-turn-slots fn-page-read-pool)
  (mv (if (eq word :left) reason :recovery-required)
      fn-allocation-turn-slots fn-page-read-pool state)))

; SLOT selects an actual precreated ATS slot; only successful ENTER issues
; authority. All receipt coordinates below come from that return.
(defun fn-owner-index-writer-prepare
 (slot fuel fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)))
 (let ((prior (fn-owner-index-writer-ticket state))
       (candidate (if (f-boundp-global 'fn-owner-cat-candidate state)
                      (f-get-global 'fn-owner-cat-candidate state) nil)))
  (if (or (not (fn-iwt-idlep prior))
          (not (consp candidate))
          (and (f-boundp-global 'fn-owner-cat-pending state)
               (f-get-global 'fn-owner-cat-pending state)))
      (mv :recovery-required fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
   (mv-let (family-word family)
    (fn-owner-runtime-operation-source :index-writer fn-page-read-pool state)
    (mv-let (table-word table)
     (fn-owner-runtime-operation-role-table :index-writer fn-page-read-pool state)
     (if (not (and (eq family-word :runtime-operation-available)
                   (eq table-word :runtime-operation-available)))
         (mv :runtime-operation-unavailable fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
      (mv-let (entered nonce fn-allocation-turn-slots fn-page-read-pool)
       (fn-ats-enter-internal slot :index-writer fn-allocation-turn-slots fn-page-read-pool)
       (if (not (eq entered :gate-owned))
           (mv entered fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
        ; This missing selected-runtime tariff MUST cover the actual sealed
        ; producer and complete holder/census/reserve/capture/epilogue stream.
        ; Post-produced IWD census alone cannot license its own construction.
        (mv-let (body-word body) (fn-owner-index-writer-body-request nil family table)
         (if (not (and (eq body-word :runtime-operation-available) (natp body)))
             (mv-let (word fn-allocation-turn-slots fn-page-read-pool state)
              (fn-owner-index-writer-refuse slot nonce :runtime-operation-unavailable
               fn-allocation-turn-slots fn-page-read-pool state)
              (mv word fn-allocation-turn-slots fn-mio$c fn-page-read-pool state))
           (mv-let (paid fn-allocation-turn-slots fn-page-read-pool)
            (fn-ats-prepay-body-internal slot nonce body fn-allocation-turn-slots fn-page-read-pool)
            (if (not (eq paid :prepaid))
                (if (eq paid :yield)
                    (mv-let (word fn-allocation-turn-slots fn-page-read-pool state)
                     (fn-owner-index-writer-refuse slot nonce :yield
                      fn-allocation-turn-slots fn-page-read-pool state)
                     (mv word fn-allocation-turn-slots fn-mio$c fn-page-read-pool state))
                  (mv :recovery-required fn-allocation-turn-slots fn-mio$c fn-page-read-pool state))
              (let* ((ledger (fn-owner-query-payload-ledger state))
                     (state
                      (f-put-global 'fn-owner-index-writer-ticket
                       (list :index-writer-ticket :seal-intent slot nonce
                        (fn-prp-alloc-epoch fn-page-read-pool) candidate
                        (fn-omk-at 0 ledger) (fn-arena-count fn-arena)
                        (nfix fuel) family table nil) state)))
               (mv :prepared fn-allocation-turn-slots fn-mio$c fn-page-read-pool state))))))))))))

))

; No supplied slot/nonce at START. Validate the retained actual receipt and
; source coordinate before the nonyielding first reservation/capture span.
(defun fn-owner-index-writer-start-fresh
 (fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)))
 (let* ((ticket (fn-owner-index-writer-ticket state))
        (ledger (fn-owner-query-payload-ledger state))
        (pc (if (f-boundp-global 'fn-owner-cat-pending state)
                (f-get-global 'fn-owner-cat-pending state) nil)))
  (if (not (and (fn-omk-widthp ticket 12)
                (eq (fn-omk-at 0 ticket) :index-writer-ticket)
                (eq (fn-omk-at 1 ticket) :prepaid)
                (fn-pc-tokenp (fn-pc-token pc))
                (fn-pc-tokenp (fn-pc-token (fn-omk-at 5 ticket)))
                (equal (fn-pc-token pc) (fn-pc-token (fn-omk-at 5 ticket)))
                (equal (fn-pc-expected pc) (fn-pc-expected (fn-omk-at 5 ticket)))
                (fn-ats-role-bodyp (fn-omk-at 2 ticket) (fn-omk-at 3 ticket) :index-writer
                 fn-allocation-turn-slots fn-page-read-pool)
                (equal (fn-prp-alloc-epoch fn-page-read-pool) (fn-omk-at 4 ticket))
                (equal (fn-omk-at 0 ledger) (fn-omk-at 6 ticket))
                (equal (fn-arena-count fn-arena) (fn-omk-at 7 ticket))))
      (mv :recovery-required nil fn-mio$c fn-page-read-pool state)
    ; Persist before any issuer/child mutation. Never re-enter PREPAID on escape.
    (let ((state (f-put-global 'fn-owner-index-writer-ticket
                   (update-nth 1 :start-intent ticket) state)))
     (mv-let (word token left fn-mio$c fn-page-read-pool)
      (fn-owner-index-writer-begin-issued (fn-omk-at 2 ticket) (fn-omk-at 3 ticket)
       (nfix (fn-omk-at 8 ticket)) fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)
      (declare (ignore left))
      (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
       (builder-phase)
       (fn-omk-at 1 (fn-ibp-builder fn-index-backing))
       (let ((state (f-put-global 'fn-owner-index-writer-ticket
                     (update-nth 11 token
                      (update-nth 1
                       (cond ((eq word :arena-held) :started)
                             ((and (eq word :yield) (not token)) :prepaid)
                             ((and token (eq builder-phase :reserved)
                                   (member-eq word '(:yield :unavailable))) :reserved)
                             ((and token (eq builder-phase :registered)
                                   (eq word :yield)) :registered)
                             (t :start-intent)) ticket)) state)))
        (mv (if (and (eq word :unavailable) (eq builder-phase :reserved))
                :constructor-required word)
            token fn-mio$c fn-page-read-pool state))))))))

; Definite suspension uses SAME token/current builder, never the issuer.
; Intent phases have no automatic retry: an interrupted effect is recovery.
(defun fn-owner-index-writer-resume
 (fuel fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)))
 (let* ((ticket (fn-owner-index-writer-ticket state))
        (phase (fn-omk-at 1 ticket)) (token (fn-omk-at 11 ticket))
        (ledger (fn-owner-query-payload-ledger state)))
  (if (not (and (fn-omk-widthp ticket 12)
                (eq (fn-omk-at 0 ticket) :index-writer-ticket)
                (member-eq phase '(:reserved :registered))
                (fn-ibp-generation-tokenp token)
                (fn-ats-role-bodyp (fn-omk-at 2 ticket) (fn-omk-at 3 ticket) :index-writer
                 fn-allocation-turn-slots fn-page-read-pool)
                (equal (fn-prp-alloc-epoch fn-page-read-pool) (fn-omk-at 4 ticket))
                (equal (fn-omk-at 0 ledger) (fn-omk-at 6 ticket))
                (equal (fn-arena-count fn-arena) (fn-omk-at 7 ticket))))
      (mv :recovery-required token fn-mio$c fn-page-read-pool state)
    (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
     (current-phase current-token)
     (let ((builder (fn-ibp-builder fn-index-backing)))
      (mv (fn-omk-at 1 builder) (fn-omk-at 2 builder)))
     (if (not (and (eq phase current-phase)
                   (fn-ibp-generation-tokenp current-token)
                   (equal token current-token)))
         (mv :recovery-required token fn-mio$c fn-page-read-pool state)
       (let ((state (f-put-global 'fn-owner-index-writer-ticket
                     (update-nth 1 (if (eq phase :reserved) :register-intent :capture-intent)
                                 ticket) state)))
        (mv-let (word left fn-mio$c)
         (if (eq phase :registered)
             (fn-owner-index-writer-arena-capture (nfix fuel) fn-mio$c fn-arena state)
           (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
            (word left fn-index-backing)
            (fn-igr-register (nfix fuel) fn-index-backing)
            (mv word left fn-mio$c)))
         (declare (ignore left))
         (let* ((next-phase
                  (cond ((and (eq phase :reserved) (eq word :registered)) :registered)
                        ((and (eq phase :registered) (eq word :arena-held)) :started)
                        ((eq word :yield) phase)
                        ((and (eq phase :reserved) (eq word :unavailable)) :reserved)
                        (t (if (eq phase :reserved) :register-intent :capture-intent))))
                (state (f-put-global 'fn-owner-index-writer-ticket
                         (update-nth 1 next-phase ticket) state)))
          (mv (if (and (eq phase :reserved) (eq word :unavailable))
                  :constructor-required word)
              token fn-mio$c fn-page-read-pool state)))))))))

(defun fn-owner-index-writer-start
 (fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)))
 (let ((ticket (fn-owner-index-writer-ticket state)))
  (if (member-eq (fn-omk-at 1 ticket) '(:reserved :registered))
      (fn-owner-index-writer-resume (nfix (fn-omk-at 8 ticket))
       fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)
    (fn-owner-index-writer-start-fresh
     fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state))))

; The actual sealed prepare is the sole PC producer. This wrapper preserves
; SAME bound arena through prepare and the complete initial executor span.
(defun fn-owner-cat-prepare-indexed
 (slot fuel fn-allocation-turn-slots fn-mio$c fn-arena fn-cat fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-arena fn-cat fn-page-read-pool state)))
 (mv-let (prepared fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
  (fn-owner-index-writer-prepare slot fuel fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)
  (if (not (eq prepared :prepared))
      (mv nil prepared nil fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
    (let ((ticket (fn-owner-index-writer-ticket state)))
     (if (not (and (fn-omk-widthp ticket 12)
                   (eq (fn-omk-at 1 ticket) :seal-intent)
                   (fn-ats-role-bodyp (fn-omk-at 2 ticket) (fn-omk-at 3 ticket) :index-writer
                    fn-allocation-turn-slots fn-page-read-pool)))
         (mv nil :recovery-required nil fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
       (mv-let (erp word state) (fn-owner-cat-prepare-sealed-produced fn-arena fn-cat state)
        (if (or erp (not (eq word :prepared)))
            (mv erp word nil fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
          (let* ((pc (f-get-global 'fn-owner-cat-pending state))
                 (state (f-put-global 'fn-owner-index-writer-ticket
                          (update-nth 5 pc (update-nth 1 :prepaid ticket)) state)))
           (mv-let (started token fn-mio$c fn-page-read-pool state)
            (fn-owner-index-writer-start fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)
            (mv nil started token fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)))))))))

 )

; Public source entry consumes only the actual retained executor holder.
(defun fn-owner-index-writer-begin
 (fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state)))
 (fn-owner-index-writer-start fn-allocation-turn-slots fn-mio$c fn-arena fn-page-read-pool state))

; One prepaid scheduling action. Readiness is a carried representation guard,
; never a whole-builder body validation. Raw escape leaves step-intent.
(defun fn-owner-index-writer-step-owned
 (fuel fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
                 :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*)
                             (fn-mio-writer-step-ready-p fn-mio$c))))
 (let ((ticket (fn-owner-index-writer-ticket state)))
  (if (not (and (fn-omk-widthp ticket 12)
                (eq (fn-omk-at 0 ticket) :index-writer-ticket)
                (eq (fn-omk-at 1 ticket) :started)
                (fn-ats-role-bodyp (fn-omk-at 2 ticket) (fn-omk-at 3 ticket) :index-writer
                                  fn-allocation-turn-slots fn-page-read-pool)))
      (mv :recovery-required fuel fn-mio$c state)
    (let ((state (f-put-global 'fn-owner-index-writer-ticket
                              (update-nth 1 :step-intent ticket) state)))
     (mv-let (word left fn-mio$c) (fn-mio-writer-step fuel fn-mio$c)
      (let ((state (if (member-eq word '(:recovery-required :unavailable)) state
                    (f-put-global 'fn-owner-index-writer-ticket ticket state))))
       (mv word left fn-mio$c state)))))))

; Durable completion calls the actual publication producer. ATS completion
; belongs to the later outer epilogue, after all allocating aliases return.
(defun fn-owner-index-writer-complete-owned
 (fuel fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)))
 (let ((ticket (fn-owner-index-writer-ticket state)))
  (if (not (and (fn-omk-widthp ticket 12)
                (eq (fn-omk-at 0 ticket) :index-writer-ticket)
                (eq (fn-omk-at 1 ticket) :started)
                (fn-ats-role-bodyp (fn-omk-at 2 ticket) (fn-omk-at 3 ticket) :index-writer
                 fn-allocation-turn-slots fn-page-read-pool)))
      (mv :recovery-required (nfix fuel) fn-mio$c state)
    (mv-let (word left fn-mio$c)
     (fn-owner-index-publication-complete (nfix fuel) fn-mio$c state)
     (let ((state (if (eq word :published)
                      (f-put-global 'fn-owner-index-writer-ticket
                       (update-nth 1 :published ticket) state) state)))
      (mv word left fn-mio$c state))))))

; Called only by the actual owner-excluded outer epilogue after allocations
; and borrowed results end. A raw escape preserves finish-intent and fences.
(defun fn-owner-index-writer-finish
 (fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)))
 (let ((ticket (fn-owner-index-writer-ticket state)))
  (if (not (and (fn-omk-widthp ticket 12)
                (eq (fn-omk-at 0 ticket) :index-writer-ticket)
                (eq (fn-omk-at 1 ticket) :published)))
      (mv :recovery-required fn-allocation-turn-slots fn-page-read-pool state)
    (let ((state (f-put-global 'fn-owner-index-writer-ticket
                  (update-nth 1 :finish-intent ticket) state)))
     (mv-let (word fn-allocation-turn-slots fn-page-read-pool)
      (fn-ats-finish-owned (fn-omk-at 2 ticket) (fn-omk-at 3 ticket)
       fn-allocation-turn-slots fn-page-read-pool)
      (let ((state (if (eq word :left)
                       (f-put-global 'fn-owner-index-writer-ticket
                        (update-nth 1 :finished ticket) state) state)))
       (mv word fn-allocation-turn-slots fn-page-read-pool state)))))))

(defun fn-owner-index-writer-fault (fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)))
 (mv-let (word fn-allocation-turn-slots fn-page-read-pool)
  (fn-ats-uncertain-internal fn-allocation-turn-slots fn-page-read-pool)
  (mv word fn-allocation-turn-slots fn-page-read-pool state)))
