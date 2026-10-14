; OVER framing and the per-holder lease capacity.  Include over-window for
; status text and its nntp-syntax/nntp-xref encoders, without the renderer:
; memory-model must charge capacity without importing pool writers.

(in-package "ACL2")
(include-book "over-window")

(defun fn-ovr-status-octets ()
  (declare (xargs :guard t))
  (fn-ovw-status (fn-proto-text * :overview)))

(defun fn-ovr-close-octets (owed2 legacyp)
  (declare (xargs :guard t))
  (if owed2 (fn-ovw-status (fn-ovw-empty-text legacyp)) '(46 13 10)))

(defun fn-ovr-frame-max ()
  (declare (xargs :guard t))
  (+ (len (fn-ovr-status-octets))
     (max (len (fn-ovr-close-octets t t)) (max (len (fn-ovr-close-octets t nil)) 3))))

(defun fn-ovr-over-capl (hdr a server-octets)
  (declare (xargs :guard t))
  (+ 2 (nfix hdr) *fn-nntp-max-decimal-octets* 7 (* 2 (len (fn-nntp-decimal (nfix a))))
     1 (len *fn-xref-name*) (nfix server-octets) (max 31 (* 12 (+ 1 (nfix hdr))))
     (fn-ovr-frame-max)))
