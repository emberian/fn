; Program-mode bridge for the ACL2-owned deployed RoughTime v1 wire grammar.
;
; A native caller supplies only the received datagram, the nonce it sent, and
; the configured pinned key.  ACL2 parses every nested message and returns the
; exact signature subjects it reconstructed.  This bridge performs no crypto,
; window, pinning, freshness, or acceptance decision.

(in-package "ACL2")
(include-book "../books/anchor-wire")

(set-state-ok t)
(program)

(defun fn-anchor-wire-host-fields (a)
  (if (not (fn-anchor-p a))
      nil
    (list (fn-anchor-key a)
          (fn-anchor-delegate a)
          (fn-anchor-mint a)
          (fn-anchor-maxt a)
          (fn-anchor-delegation-signature a)
          (fn-anchor-midpoint a)
          (fn-anchor-radius a)
          (fn-anchor-nonce a)
          (fn-anchor-signature a)
          (fn-anchor-root a))))

(defun fn-anchor-wire-host-parse (packet nonce pinned-key)
  (let ((result (fn-anchor-wire-parse-response packet nonce pinned-key)))
    (if (not (fn-anchor-wire-result-okp result))
        (list :refused (fn-anchor-wire-result-reason result))
      (let* ((parsed (fn-anchor-wire-result-value result))
             (a (fn-anchor-wire-parsed-anchor parsed)))
        (list :parsed
              (fn-anchor-wire-host-fields a)
              (fn-anchor-wire-parsed-path parsed)
              (fn-anchor-wire-parsed-index parsed)
              (fn-anchor-delegation-signed-octets a)
              (fn-anchor-signed-octets a)
              (if (fn-anchor-wire-single-leafp parsed) 1 0))))))

(defun fn-anchor-wire-host-max-response ()
  *fn-anchor-wire-max-response*)

; Restore the prompt expected by persistent native bridge sessions.
(logic)
