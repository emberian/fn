; Scalar literal step boundary to actual paid head renderer.
(in-package "ACL2")
(include-book "index-range-render-trajectory")
(encapsulate ()
 (local (defthm fn-ibr-octet-head-implies-consp-by-definition
  (implies (fn-cbor-octetp (car x)) (consp x))
  :hints (("Goal" :in-theory (enable fn-ag-car fn-cbor-octetp)))))
 (local (defthm fn-ibr-literal-fill-one-by-definition
  (implies (and (consp cur) (fn-cbor-octetp (car cur)))
   (equal (fn-splan-fill cur nil 1 fn-octets)
     (list :ok (cons (cdr cur) nil)
           (fn-octets-append-octet (car cur) fn-octets))))
  :hints (("Goal" :expand ((fn-splan-fill cur nil 1 fn-octets)
           (fn-splan-fill (cdr cur) nil 0
             (fn-octets-append-octet (car cur) fn-octets)))
          :in-theory (disable fn-octets-append-octet fn-cbor-octetp)))))
(defthm fn-ibr-literal-reply-one-is-actual-head-window
 (let* ((cur (if (consp (fn-spp-cur plan)) (fn-spp-cur plan)
                 (fn-srb-effect-octets (fn-ag-car (fn-spp-rest plan)))))
        (actual (fn-ibr-literal-reply-one plan))
        (head (fn-spp-head-window plan 1 fn-octets)))
  (implies (and (eq (fn-spp-status plan) :reply)
                (fn-cbor-octetp (fn-ag-car cur)))
   (and (eq (mv-nth 0 actual) :reply-byte)
        (eq (mv-nth 0 head) :ok)
        (equal (mv-nth 2 actual) (mv-nth 1 head))
        (equal (fn-octets-list (mv-nth 2 head)) (list (mv-nth 1 actual))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-ibr-literal-reply-one fn-spp-head-window fn-splan-fill
        fn-splan-cur fn-ag-car fn-ag-cdr fn-spp-cur fn-spp-rest)
       (fn-spp-status fn-spp-save-active fn-srb-effect-octets fn-cbor-octetp)))))

)
