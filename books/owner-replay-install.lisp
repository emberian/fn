; Installer-facing original-context bootstrap boundary. Actual authenticated
; row/summary producers establish the context, CP7 and pool correspondence.
(in-package "ACL2")
(include-book "owner-replay-context")
(include-book "owner-canonical-state")

(defun fn-owner-orcb-install-complete (bootstrap source epoch cp7 cpfields pool rows state)
 (declare (xargs :stobjs state :guard (fn-orcb-statep bootstrap)))
 (let ((packet (fn-orcb-install bootstrap source)))
  (if (not (eq (car packet) :ready))
   (mv :refused state)
   (fn-owner-canonical-install epoch (fn-orcb-at 5 packet)
     (fn-orcb-at 1 packet) (fn-orcb-at 3 packet) cp7 cpfields
     pool rows (fn-orcb-at 4 packet) state))))

(defthm fn-owner-orcb-incomplete-bootstrap-cannot-install
 (implies (not (eq (car (fn-orcb-install bootstrap source)) :ready))
  (and (equal (mv-nth 0 (fn-owner-orcb-install-complete
                         bootstrap source epoch cp7 cpfields pool rows state)) :refused)
       (equal (mv-nth 1 (fn-owner-orcb-install-complete
                         bootstrap source epoch cp7 cpfields pool rows state)) state)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-owner-orcb-install-complete))))

(in-theory (disable fn-owner-orcb-install-complete))

; Pending bootstrap belongs to the epoch at its actual start. The host never
; reissues an epoch at completion; reset invalidates and clears this packet.
(defun fn-owner-orcb-pending (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-canonical-pending state)
      (f-get-global 'fn-owner-canonical-pending state)))
(defun fn-owner-orcb-start (source total state)
 (declare (xargs :stobjs state :guard t))
 (let ((epoch (fn-owner-canonical-epoch state)))
  (if (not (and (natp epoch) (fn-omk-tokenp source) (natp total)
                (not (fn-owner-orcb-pending state))))
   (mv :refused state)
   (mv-let (phase bootstrap) (fn-orcb-begin source total)
    (let ((state (f-put-global 'fn-owner-canonical-pending
                               (list epoch source bootstrap) state)))
     (mv phase state))))))
(defun fn-owner-orcb-feed (source row child-carry state)
 (declare (xargs :stobjs state :guard t))
 (let ((p (fn-owner-orcb-pending state)))
  (if (not (and (fn-omk-widthp p 3)
                (natp (fn-omk-at 0 p))
                (equal (fn-omk-at 0 p) (fn-owner-canonical-epoch state))
                (fn-orcb-statep (fn-omk-at 2 p))
                (fn-scs-carryp child-carry)))
   (mv :refused state)
   (mv-let (phase bootstrap)
           (fn-orcb-step (fn-omk-at 2 p) source row child-carry)
    (let ((state (f-put-global 'fn-owner-canonical-pending
                    (list (fn-omk-at 0 p) (fn-omk-at 1 p) bootstrap) state)))
     (mv phase state))))))
(defun fn-owner-orcb-complete (cp7 cpfields pool rows state)
 (declare (xargs :stobjs state :guard t))
 (let ((p (fn-owner-orcb-pending state)))
  (if (not (and (fn-omk-widthp p 3)
                (natp (fn-omk-at 0 p))
                (equal (fn-omk-at 0 p) (fn-owner-canonical-epoch state))
                (fn-orcb-statep (fn-omk-at 2 p))))
   (mv :refused state)
   (fn-owner-orcb-install-complete (fn-omk-at 2 p) (fn-omk-at 1 p)
     (fn-omk-at 0 p) cp7 cpfields pool rows state))))

(defthm fn-owner-orcb-reset-invalidates-pending-bootstrap
 (and (equal (mv-nth 0 (fn-owner-orcb-complete cp7 cpfields pool rows
                        (fn-owner-canonical-reset state))) :refused)
      (equal (mv-nth 1 (fn-owner-orcb-complete cp7 cpfields pool rows
                        (fn-owner-canonical-reset state)))
             (fn-owner-canonical-reset state)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-owner-orcb-complete fn-owner-orcb-pending
                          fn-owner-canonical-reset fn-omk-widthp))))

; The current summary decoder already returns the original resident context.
; Its companion producer must supply corresponding field carries at that
; same authenticated source. This installs only into the pending bootstrap;
; publication remains the epoch-checked, one-use complete operation.
(defun fn-owner-orcb-supply-resident (source count ctx fields state)
 (declare (xargs :stobjs state :guard t))
 (let ((p (fn-owner-orcb-pending state)))
  (if (not (and (fn-omk-widthp p 3) (natp (fn-omk-at 0 p))
                (equal (fn-omk-at 0 p) (fn-owner-canonical-epoch state))
                (fn-orcb-statep (fn-omk-at 2 p))
                (fn-omk-tokenp source)
                (fn-omk-token-matchp source (fn-omk-at 1 p))
                (natp count) (equal count (fn-orcb-at 2 (fn-omk-at 2 p)))
                (fn-omk-widthp ctx 6) (fn-ics-contextp ctx)
                (fn-ics-carriesp fields)))
   (mv :refused state)
   (mv-let (phase bootstrap) (fn-orcb-resident source count ctx fields)
    (let ((state (f-put-global 'fn-owner-canonical-pending
                   (list (fn-omk-at 0 p) (fn-omk-at 1 p) bootstrap) state)))
     (mv phase state))))))

(defthm fn-owner-orcb-stale-epoch-cannot-complete
 (implies (not (equal (fn-omk-at 0 (fn-owner-orcb-pending state))
                      (fn-owner-canonical-epoch state)))
  (and (equal (mv-nth 0 (fn-owner-orcb-complete cp7 cpfields pool rows state)) :refused)
       (equal (mv-nth 1 (fn-owner-orcb-complete cp7 cpfields pool rows state)) state)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-owner-orcb-complete))))

(defthm fn-owner-orcb-success-consumes-pending-bootstrap
 (implies (equal (mv-nth 0 (fn-owner-orcb-complete cp7 cpfields pool rows state)) :installed)
  (not (fn-owner-orcb-pending
         (mv-nth 1 (fn-owner-orcb-complete cp7 cpfields pool rows state)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-owner-orcb-complete fn-owner-orcb-install-complete
                 fn-owner-canonical-install fn-owner-orcb-pending))))

; Prefix identity is an authenticated producer obligation, not this bounded
; counter check. Actual source still names the full captured history cursor.
(defun fn-owner-orcb-supply-prefix (source consumed ctx fields state)
 (declare (xargs :stobjs state :guard t))
 (let ((p (fn-owner-orcb-pending state)))
  (if (not (and (fn-omk-widthp p 3) (natp (fn-omk-at 0 p))
                (equal (fn-omk-at 0 p) (fn-owner-canonical-epoch state))
                (fn-orcb-statep (fn-omk-at 2 p)) (fn-omk-tokenp source)
                (fn-omk-token-matchp source (fn-omk-at 1 p))
                (natp consumed) (<= consumed (fn-orcb-at 2 (fn-omk-at 2 p)))
                (fn-omk-widthp ctx 6) (fn-ics-contextp ctx) (fn-ics-carriesp fields)))
   (mv :refused state)
   (mv-let (phase bootstrap)
           (fn-orcb-seed source (fn-orcb-at 2 (fn-omk-at 2 p)) consumed ctx fields)
    (let ((state (f-put-global 'fn-owner-canonical-pending
                   (list (fn-omk-at 0 p) (fn-omk-at 1 p) bootstrap) state)))
     (mv phase state))))))

; ORIGINAL replay remains usable while the independent CP7/pool join is
; unfinished. This readout never labels a partial tuple canonical-ready.
(defun fn-owner-orcb-context (filecount state)
 (declare (xargs :stobjs state :guard t))
 (let ((c (fn-owner-canonical-state state)))
  (if (and (fn-owner-canonical-availablep filecount state)
           (fn-omk-widthp (fn-omk-at 3 c) 6)
           (fn-ics-contextp (fn-omk-at 3 c))
           (equal (fn-stxk-context-next (fn-omk-at 3 c)) filecount)
           (fn-ics-carriesp (fn-omk-at 4 c)) (fn-omk-tokenp (fn-omk-at 9 c)))
   (list :context (fn-omk-at 1 c) filecount (fn-omk-at 3 c)
         (fn-omk-at 4 c) (fn-omk-at 9 c))
   (let ((p (fn-owner-orcb-pending state)))
    (if (not (and (fn-omk-widthp p 3) (natp (fn-omk-at 0 p))
                  (equal (fn-omk-at 0 p) (fn-owner-canonical-epoch state))
                  (fn-orcb-statep (fn-omk-at 2 p)) (natp filecount)
                  (equal (fn-orcb-at 2 (fn-omk-at 2 p)) filecount)))
     (list :unavailable :replay-context)
     (let ((packet (fn-orcb-install (fn-omk-at 2 p) (fn-omk-at 1 p))))
      (if (eq (car packet) :ready)
       (list :context (fn-omk-at 0 p) filecount (fn-orcb-at 1 packet)
             (fn-orcb-at 3 packet) (fn-orcb-at 4 packet))
       (list :unavailable :replay-context))))))))

; The caller supplies the actual authorized durable operation and its exact
; predecessor event count. Captured Store frontier may change. The process
; epoch is read from retained context, never substituted at completion.
(defun fn-owner-orcb-append-current (source previous-count row child-carry state)
 (declare (xargs :stobjs state :guard t))
 (let ((c (fn-owner-orcb-context previous-count state)))
  (if (not (and (fn-omk-widthp c 6) (eq (fn-omk-at 0 c) :context)
                (natp (fn-omk-at 1 c)) (natp previous-count)
                (equal (fn-omk-at 1 c) (fn-owner-canonical-epoch state))
                (fn-omk-tokenp (fn-omk-at 5 c)) (fn-omk-tokenp source)
                (fn-ics-contextp (fn-omk-at 3 c))
                (fn-ics-carriesp (fn-omk-at 4 c)) (fn-scs-carryp child-carry)))
   (mv :refused state)
   (mv-let (phase bootstrap)
           (fn-orcb-resident (fn-omk-at 5 c) previous-count
                              (fn-omk-at 3 c) (fn-omk-at 4 c))
    (if (not (eq phase :ready)) (mv :refused state)
     ; Resident constructs the fixed state recognized below; the check is
     ; bounded and makes this caller independently guard-verifiable.
     (if (not (fn-orcb-statep bootstrap)) (mv :refused state)
      (mv-let (next appended) (fn-orcb-append bootstrap source row child-carry)
       (let* ((state (f-put-global 'fn-owner-canonical-state nil state))
              (state (f-put-global 'fn-owner-canonical-pending
                       (list (fn-omk-at 1 c) source appended) state)))
        (mv next state)))))))))
