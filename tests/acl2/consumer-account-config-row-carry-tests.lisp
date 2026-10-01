(in-package "ACL2")
(include-book "../../books/consumer-account-config-row-carry")

(defconst *bcprt-row* (fn-cfg-row-make "legacy" "principal" "" 2))

;@positive-witness fn-bcpr-row-carry-is-canonical-row-size
(assert-event
 (and (fn-bcpr-row-domainp *bcprt-row*)
      (equal (fn-bcpr-row-carry *bcprt-row*) (fn-scs-summary *bcprt-row*))))

; A stored string is read as a scalar, never converted or truncated to match
; the authority login domain. This model witness exceeds that domain.
;@mutation-witness selected-long-stored-row-keeps-exact-canonical-size
(assert-event
 (let ((row (fn-cfg-row-make (coerce (make-list 320 :initial-element #\a) 'string)
                            "kept" "" 1)))
  (and (fn-bcpr-row-domainp row)
       (equal (fn-bcpr-row-carry row) (fn-scs-summary row)))))

;@hypothesis-removal fn-bcpr-row-carry-is-canonical-row-size fn-bcpr-row-domainp
;@corrupted-state non-scalar-field
(assert-event
 (let ((row (fn-cfg-row-make '(1 2) "principal" "" 2)))
  (and (not (fn-bcpr-row-domainp row))
       (not (equal (fn-bcpr-row-carry row) (fn-scs-summary row))))))
