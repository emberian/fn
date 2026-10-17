; SOURCE MODEL: synthetic ledger funding and constructed RC, actual same local stobjs.
; No native copy, serialized STATE, constructor envelope or terminal authority.
(in-package "ACL2")
(include-book "../../books/receiver-output-association")
; MODEL funding/constructed RC only. Actual functions and same local stobjs.
; No serialized STATE producer, native copy, constructor allowance or terminal receipt.
(defun fn-rxo-chain-fill-v2 (fn-rx-provider)
 (declare (xargs :stobjs fn-rx-provider))
 (stobj-let ((fn-octets-rx (fn-rxp-octets fn-rx-provider)))
  (fn-octets-rx) (fn-octets-rx-from-list '(81 82) fn-octets-rx) fn-rx-provider))

