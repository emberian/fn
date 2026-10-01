; Actual selected CFG row has four scalar fields. Its size constructor reads
; native string lengths and one bounded integer width; it neither encodes the
; strings nor walks a shared row/table/tree. Table/source and funding are the
; caller's maintained relations, not established by this fixed leaf gate.
(in-package "ACL2")
(include-book "consumer-account-config-preparation")

(defun fn-bcpr-row-domainp (row)
 (declare (xargs :guard t))
 (and (consp row) (consp (cdr row)) (consp (cddr row))
      (consp (cdddr row)) (null (cddddr row))
      (stringp (fn-cfg-row-a row)) (stringp (fn-cfg-row-b row))
      (stringp (fn-cfg-row-c row)) (fn-record-uint32p (fn-cfg-row-n row))))

(defun fn-bcpr-row-carry (row)
 (declare (xargs :guard t))
 (and (fn-bcpr-row-domainp row)
      (fn-caac-spine
       (list (fn-caac-atom (fn-cfg-row-a row))
             (fn-caac-atom (fn-cfg-row-b row))
             (fn-caac-atom (fn-cfg-row-c row))
             (fn-caac-atom (fn-cfg-row-n row))))))

(defthm fn-bcpr-row-carry-is-canonical-row-size
 (implies (fn-bcpr-row-domainp row)
          (equal (fn-bcpr-row-carry row) (fn-scs-summary row)))
 :hints (("Goal"
          :use ((:instance fn-caac-spine-keeps-canonical-size
                   (cs (list (fn-caac-atom (fn-cfg-row-a row))
                             (fn-caac-atom (fn-cfg-row-b row))
                             (fn-caac-atom (fn-cfg-row-c row))
                             (fn-caac-atom (fn-cfg-row-n row))))
                   (xs row)))
          :in-theory
          (e/d (fn-bcpr-row-domainp fn-bcpr-row-carry fn-caac-atom
                 fn-scs-correspondsp fn-cfg-row-a fn-cfg-row-b
                 fn-cfg-row-c fn-cfg-row-n fn-cfg-ag-car fn-cfg-ag-cdr
                 fn-record-uint32p)
               (fn-caac-spine fn-scs-summary fn-scs-atom)))))

(in-theory (disable fn-bcpr-row-domainp fn-bcpr-row-carry))
