; The FNBS recovery row shape and the strict arrival order every FNBS
; replay checks.  Rows are bounded final-name/file-octet observations; the
; codec owns their meaning.  The served recovery fold is
; `fn-bpnf-family-replay-rows' (books/bp-fnbs-family-replay.lisp, called
; through `fn-bpnf-family-recover-auto-event'); the kind-5-only fold that
; lived here and its kind-5/7 successor (bp-fnbs-delivery-replay) were
; retired (Q3a, PKT-298): no host function reached either.
(in-package "ACL2")
(include-book "bp-fnbs-codec")
(set-verify-guards-eagerness 0)

(defun fn-bpnf-replay-rowp (row)
  (declare (xargs :guard t))
  (and (true-listp row) (equal (len row) 2)
       (stringp (car row))
       (fn-cbor-octet-listp (cadr row))))

(verify-guards fn-bpnf-replay-rowp)

(defun fn-bpnf-replay-pair-afterp (epoch operation-id prior)
  (declare (xargs :guard (and (natp epoch) (natp operation-id)
                              (or (null prior)
                                  (and (consp prior)
                                       (natp (car prior))
                                       (natp (cdr prior)))))))
  (or (null prior)
      (< (car prior) epoch)
      (and (equal (car prior) epoch)
           (< (cdr prior) operation-id))))

(verify-guards fn-bpnf-replay-pair-afterp)
