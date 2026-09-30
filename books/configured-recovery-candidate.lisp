; Bounded-mode recovery candidate. Legacy FnCRPAppend is a separate entry.
; Source assembly: backing issuer, guards and complete caller refinement open.
(in-package "ACL2")
(include-book "statement-recover-produced-row")
(include-book "history-event-backing")

(defun fn-crpc-offer-event (acc fields wire raw position mode dicts snapshot-carry
                            producer-token fn-arena fn-history-backing)
 (declare (xargs :stobjs (fn-arena fn-history-backing) :verify-guards nil
                 :guard (and (fn-ssr-statep acc) (fn-lzr-dictsp dicts))))
 ; The registered producer must be issued before any actual intern allocation.
 ; NIL is unavailable, never an implicit issuer or current-token refresh.
 (if (not producer-token)
     (mv :unavailable acc fields fn-arena fn-history-backing)
  (mv-let (next-acc next-fields status effect child sizes row fn-arena)
   (fn-ssrp-intern-row acc fields wire raw position mode dicts snapshot-carry fn-arena)
   (if (eq next-acc :bad)
       (mv :refused next-acc next-fields fn-arena fn-history-backing)
    (let ((produced (list (fn-ssr-at 3 next-acc) next-fields status effect child sizes)))
     ; All aliases remain private. No legacy history append or context install.
     (mv-let (word fn-history-backing)
      (fn-hep-offer-produced row produced (fn-ssr-at 3 next-acc)
                            next-fields producer-token fn-history-backing)
      (mv word next-acc next-fields fn-arena fn-history-backing)))))))

(defun fn-crpc-candidate-read-begin (ordinal fn-history-backing)
 (declare (xargs :stobjs fn-history-backing :verify-guards nil :guard t))
 ; old F is the exact pending row; lower ordinals use retained old source.
 (fn-hep-candidate-read-begin ordinal fn-history-backing))

(defun fn-crpc-candidate-read-step (fuel fn-history-backing)
 (declare (xargs :stobjs fn-history-backing :verify-guards nil :guard t))
 (fn-hep-candidate-read-step fuel fn-history-backing))

(defun fn-crpc-prepared-readout (fn-history-backing)
 (declare (xargs :stobjs fn-history-backing :verify-guards nil :guard t))
 ; Preparation is not acceptance or install authority. SAME row and packet
 ; are consumed by the actual account/control completion, without re-intern.
 (fn-hep-builder-readout fn-history-backing))
