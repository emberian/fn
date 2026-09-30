; Literal shared UTF-8 scalar producer domain for the bounded report reader.
; This is not a supported-profile domain for report counts/decimal fields,
; and supplies no primitive allocation/frame/GC or stream lifetime tariff.
(in-package "ACL2")
(include-book "utf8")

(defthm fn-oru-actual-next-success-has-bounded-scalar
  (implies (fn-wildmat-result-okp (fn-wildmat-utf8-next prefix))
           (and (natp (fn-wildmat-result-value (fn-wildmat-utf8-next prefix)))
                (<= (fn-wildmat-result-value (fn-wildmat-utf8-next prefix))
                    1114111)))
  :hints (("Goal" :in-theory
           (enable fn-wildmat-utf8-next fn-wildmat-result-okp
                   fn-wildmat-result-value fn-wildmat-utf8-ok fn-wildmat-error
                   fn-wildmat-octetp fn-wildmat-utf8-tailp fn-wildmat-utf8-2p
                   fn-wildmat-utf8-3-tailsp fn-wildmat-utf8-4-tailsp
                   fn-wildmat-utf8-2-value fn-wildmat-utf8-3-value
                   fn-wildmat-utf8-4-value))))
