(in-package "ACL2")
(logic)
(include-book "index-generation-issuer")

; Private readonly scalar lineage fence. Ticket is read from actual STATE by
; the effecting caller; compare issued token and original PC identity only.
(defun fn-owner-index-writer-currentp (ticket fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard t))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (current)
  (let* ((builder (fn-ibp-builder fn-index-backing))
         (token (fn-omk-at 2 builder))
         (issued (fn-omk-at 11 ticket))
         (pc (fn-omk-at 5 ticket))
         (pc-token (fn-pc-token pc)))
   (and (fn-ibp-generation-tokenp token)
        (fn-ibp-generation-tokenp issued)
        (equal token issued)
        (natp (fn-omk-at 6 builder)) (natp (fn-pc-expected pc))
        (equal (fn-omk-at 6 builder) (fn-pc-expected pc))
        (consp pc-token) (natp (car pc-token)) (natp (cdr pc-token))
        (equal (fn-omk-at 7 builder) pc-token)))
  current))

