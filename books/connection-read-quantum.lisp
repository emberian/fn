; Exact unchanged work quantum, never a stored payload ceiling.
(in-package "ACL2")
(include-book "public-exposure-selectors")

(defconst *fn-cbud-step-octets* 512)
(defconst *fn-cbud-read-quantum* 4096)

(defun fn-cbud-step-read-octets (lim)
  (declare (xargs :guard t))
  (if (posp (fn-exp-lim-steps lim))
      *fn-cbud-step-octets*
    *fn-cbud-read-quantum*))

(defthm fn-cbud-step-read-octets-is-bounded
  (and (posp (fn-cbud-step-read-octets lim))
       (<= (fn-cbud-step-read-octets lim) *fn-cbud-read-quantum*))
  :rule-classes ((:type-prescription :corollary (posp (fn-cbud-step-read-octets lim)))
                 (:linear :corollary (<= (fn-cbud-step-read-octets lim)
                                         *fn-cbud-read-quantum*))))

; Under a step rate the step is the rate's unit: 512 octets, as before.
(defthm fn-cbud-step-read-octets-under-a-rate-by-definition
  (implies (posp (fn-exp-lim-steps lim))
           (equal (fn-cbud-step-read-octets lim) *fn-cbud-step-octets*)))

(in-theory (disable fn-cbud-step-read-octets))

