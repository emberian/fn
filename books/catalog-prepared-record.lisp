; Exact catalog definitions factored without changing names or bodies.
(in-package "ACL2")
(include-book "held-record")

(defun fn-pc-tokenp (x)
  (declare (xargs :guard t))
  (and (consp x) (natp (car x)) (natp (cdr x))))

(defun fn-pc-anyp (x)
  (declare (xargs :guard t) (ignore x))
  t)

(fn-defrecord fn-pc
  :constructor (fn-pc-make token expected held plan reservation)
  :fields ((fn-pc-token fn-pc-tokenp)
           (fn-pc-expected natp)
           (fn-pc-held fn-held-p)
           (fn-pc-plan fn-pc-anyp)
           (fn-pc-reservation fn-pc-anyp))
  :recognizer fn-pc-p
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

(defun fn-pc-optionp (x)
  (declare (xargs :guard t))
  (or (null x) (fn-pc-p x)))

(defthm fn-pc-p-fields
  (implies (fn-pc-p pc)
           (and (fn-pc-tokenp (fn-pc-token pc))
                (natp (fn-pc-expected pc))
                (fn-held-p (fn-pc-held pc))))
  :hints (("Goal" :in-theory (enable fn-pc-p))))
