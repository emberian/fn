; Image-time grammar dimensions for the first bounded Store profile read.
; This is NOT the operator's Store profile, a PRS budget, or an I/O grant.
; The actual image builder saves workspace from this readout. The recovery
; controller must retain that SAME workspace and its issued custody through
; actual EOF/overflow observation before invoking fn-spo-config-open.
(in-package "ACL2")
(include-book "byte-store-frame")

; Zero-based fields: tag, grammar identity, header, maximum payload, trailer,
; maximum complete file, overflow probe, total saved workspace capacity.
; The extra octet detects trailing data at the maximum accepted frame size;
; it is never part of a successfully decoded profile. Reading into a bounded
; workspace does not establish integrity, supported format or representation.
(defun fn-recovery-profile-envelope ()
  (declare (xargs :guard t))
  (let* ((file (+ *fn-frame-header-octets*
                  *fn-bs-meta-max-config-payload*
                  *fn-frame-trailer-octets*))
         (probe 1))
    (list :profile-envelope :fnsm-v1
          *fn-frame-header-octets* *fn-bs-meta-max-config-payload*
          *fn-frame-trailer-octets* file probe (+ file probe))))

(in-theory (disable fn-recovery-profile-envelope))
