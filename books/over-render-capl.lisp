; OVER's lease-capacity term: one NOV line within its stored header plus
; CRLF plus the framing, over the server name's octet count.  The memory
; equation charges it per holder (books/memory-model.lisp fn-ovr-over-capl-of).
;
; Include only over-render-quantum: it owns fn-ovr-frame-max and brings
; nntp-syntax's decimal encoder/width and nntp-xref's field-name octets.
; No stored-limits or owner-history proof book is added to this world.

(in-package "ACL2")
(include-book "over-render-quantum")

(defun fn-ovr-over-capl (hdr a server-octets)
  (declare (xargs :guard t))
  (+ 2 (nfix hdr) *fn-nntp-max-decimal-octets* 7 (* 2 (len (fn-nntp-decimal (nfix a))))
     1 (len *fn-xref-name*) (nfix server-octets) (max 31 (* 12 (+ 1 (nfix hdr))))
     (fn-ovr-frame-max)))
