; Same-source seed component witnesses; no native issuer or installation claim.
(in-package "ACL2")
(include-book "../../host/store-statement-replay-size-host")

(assert-event
 (let ((ctx (fn-stxk-initial-context 0)))
  (mv-let (acc fields status) (fn-store-srs-seed nil nil)
   (and (equal acc (fn-ssr-seed ctx))
        (equal (fn-ssr-at 3 acc) ctx)
        (eq status :carried)
        (fn-ics-carriesp fields)
        (fn-scs-correspondsp fields ctx)))))

; A selected checkpoint lacking its same-load annotation never borrows the
; empty constructor's metadata, even when its value is the empty context.
(assert-event
 (let ((checkpoint (fn-sco-capture nil nil)))
  (mv-let (acc fields status) (fn-store-srs-seed checkpoint nil)
   (and checkpoint
        (equal acc (fn-ssr-seed (fn-sco-identity checkpoint)))
        (not fields) (eq status :unavailable)))))
