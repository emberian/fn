; INTERNAL source-changing completion with retained RX-origin transfer.
(in-package "ACL2")
(include-book "index-reader-request")
(include-book "index-connection-rx-repin")
(defun fn-irr-request-finish-source-rx (nonce fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool)
                 :guard (natp fuel) :verify-guards nil))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (request (fn-irr-receipt-request receipt))
        (phase (fn-omk-at 7 receipt))
        (intent (fn-irr-receipt-repin receipt))
        (new (fn-omk-at 1 intent)) (pin (fn-omk-at 2 intent))
        (rc (fn-irr-request-rc request))
        (accepted (and (consp rc) (fn-own-tls-result-repinned (car rc))))
        (units (+ 1 (fn-ibp-slot-depth fn-index-backing))))
  (cond
   ((not (and (posp nonce) (equal nonce (fn-omk-at 2 receipt))))
    (mv :stale fuel fn-index-backing fn-page-read-pool))
   ((fn-irq-ready-phasep phase)
    (mv phase fuel fn-index-backing fn-page-read-pool))
   ((not (and (eq phase :read-offer-ready) intent (consp rc)))
    (mv :recovery-required fuel fn-index-backing fn-page-read-pool))
   ((not (let ((prepared (fn-ibp-connection-pending fn-index-backing)))
           (and (fn-omk-widthp prepared 8)
                (equal (fn-omk-at 1 prepared) new)
                (equal (fn-omk-at 2 prepared) (fn-omk-at 1 request))
                (eq (fn-omk-at 6 prepared) :source-owned)
                (equal (fn-omk-at 1 (fn-omk-at 7 prepared)) (fn-omk-at 1 pin))
                (fn-irr-publication-coordinatesp
                 (fn-omk-at 2 (fn-omk-at 7 prepared)) (fn-omk-at 2 pin)))))
    (mv :recovery-required fuel fn-index-backing fn-page-read-pool))
   ((< fuel (* (if accepted 10 6) units))
    ; The actual RC span was already entered: escaping it is recovery.
    ; The producer must preflight this full allowance before constructing RC.
    (mv :recovery-required fuel fn-index-backing fn-page-read-pool))
   ((and accepted
         (not (eq (fn-icr-repin-preflight (fn-omk-at 1 request)
                    (fn-irr-request-holder request) new fuel fn-index-backing) :ready)))
    (mv :recovery-required fuel fn-index-backing fn-page-read-pool))
   (t
    (let ((fn-index-backing
           (update-fn-ibp-request-pending
            (fn-irr-receipt-keep receipt request
              (if accepted :repin-accept-intent :offer-drop-intent) intent)
            fn-index-backing)))
     (if accepted
      (mv-let (joined left fn-index-backing fn-page-read-pool)
       (fn-icr-repin-rx-accept (fn-omk-at 1 request)
        (fn-irr-request-holder request) new fuel fn-index-backing fn-page-read-pool)
       (if (not (and (member-eq joined '(:repinned :repinned-held)) (natp left)))
        (mv :recovery-required fuel fn-index-backing fn-page-read-pool)
        (let ((fn-index-backing
               (update-fn-ibp-request-pending
                (fn-irr-receipt-keep receipt request :old-query-drop-intent intent)
                fn-index-backing)))
         (mv-let (dropped ignored remaining fn-index-backing)
          (fn-ibp-generation-reference
           (fn-omk-at 1 (fn-irr-request-pin request)) :drop :query nil left fn-index-backing)
          (declare (ignore ignored))
          (if (not (member-eq dropped '(:live :retiring)))
           (mv :recovery-required remaining fn-index-backing fn-page-read-pool)
           (let* ((next-request
                   (list (fn-omk-at 0 request) (fn-omk-at 1 request)
                    pin (fn-omk-at 2 pin) (fn-omk-at 4 request) rc
                    (fn-irr-request-effects request) (fn-irr-request-origin request)
                    (fn-irr-request-holder request) (fn-irr-request-input-source request)))
                  (next-phase (if (eq joined :repinned)
                                  :read-ready-repin-released :read-ready-repin-held))
                  (fn-index-backing
                   (update-fn-ibp-request-pending
                    (fn-irr-receipt-keep receipt next-request next-phase new)
                    fn-index-backing)))
            (mv next-phase remaining fn-index-backing fn-page-read-pool)))))))
      (mv-let (dropped ignored left fn-index-backing)
       (fn-ibp-generation-reference (fn-omk-at 1 pin) :drop :query nil fuel fn-index-backing)
       (declare (ignore ignored))
       (if (not (and (member-eq dropped '(:live :retiring)) (natp left)))
        (mv :recovery-required fuel fn-index-backing fn-page-read-pool)
        (let ((fn-index-backing
               (update-fn-ibp-request-pending
                (fn-irr-receipt-keep receipt request :offer-abort-intent intent)
                fn-index-backing)))
         (mv-let (aborted remaining fn-index-backing fn-page-read-pool)
          (fn-icr-abort new left fn-index-backing fn-page-read-pool)
          (if (not (eq aborted :released))
           (mv :recovery-required remaining fn-index-backing fn-page-read-pool)
           (let ((fn-index-backing
                  (update-fn-ibp-request-pending
                   (fn-irr-receipt-keep receipt request :read-ready-repin-aborted new)
                   fn-index-backing)))
            (mv :read-ready-repin-aborted remaining fn-index-backing fn-page-read-pool)))))))))))))

(verify-guards fn-irr-request-finish-source-rx
 :hints (("Goal" :in-theory
          (disable fn-icr-repin-rx-accept fn-icr-repin-preflight fn-icr-abort
                   fn-ibp-generation-reference fn-irr-publication-coordinatesp))))
