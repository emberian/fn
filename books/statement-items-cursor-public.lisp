; Public semantic boundary. The explicit constrained equality, not DEFATTACH,
; connects the unchanged executable reference to the public decoder.
(in-package "ACL2")
(include-book "statement-items-cursor-refinement")
(include-book "statement-seam")
(defthm fn-sic-paid-begin-is-public-bounded-result
 (implies (and (natp fuel) (natp outer-budget) (natp item-budget))
  (let* ((c (fn-sic-begin fuel octets outer-budget item-budget))
         (d (fn-sic-run (fn-sic-completion-cost c) c)))
   (and (equal (fn-sic-at 0 d) :done)
    (equal (fn-sic-result-abstract d)
     (fn-stmt-decode-items-bounded fuel octets outer-budget item-budget)))))
 :hints (("Goal" :use ((:instance fn-stmt-decode-items-bounded-reference-by-definition))
 :in-theory (disable fn-sic-begin fn-sic-run fn-sic-at fn-sic-result-abstract
 fn-sic-completion-cost fn-stmt-decode-items-bounded-impl))))
(defthm fn-sic-paid-legacy-is-public-result
 (implies (natp fuel)
  (let* ((c (fn-sic-begin-legacy fuel octets))
         (d (fn-sic-run (fn-sic-completion-cost c) c)))
   (equal (fn-sic-result-abstract d) (fn-stmt-decode-items fuel octets))))
 :hints (("Goal" :use ((:instance fn-stmt-decode-items-bounded-reference-by-definition (outer-budget *fn-cbor-max-input*) (item-budget *fn-cbor-max-bytes*)))
 :in-theory (e/d (fn-sic-begin-legacy fn-stmt-decode-items)
 (fn-sic-begin fn-sic-run fn-sic-at fn-sic-result-abstract fn-sic-completion-cost)))))
(defthm fn-sic-paid-legacy-success-is-canonical
 (implies (and (natp fuel)
  (fn-stmt-okp (fn-sic-result-abstract
   (fn-sic-run (fn-sic-completion-cost (fn-sic-begin-legacy fuel octets))
    (fn-sic-begin-legacy fuel octets)))))
  (equal (fn-stmt-encode-items
   (fn-stmt-value (fn-sic-result-abstract
    (fn-sic-run (fn-sic-completion-cost (fn-sic-begin-legacy fuel octets))
     (fn-sic-begin-legacy fuel octets))))) octets))
 :hints (("Goal" :use ((:instance fn-sic-paid-legacy-is-public-result) (:instance fn-stmt-decode-items-bounded-canonical))
 :in-theory (e/d (fn-stmt-decode-items)
 (fn-sic-begin-legacy fn-sic-run fn-sic-completion-cost fn-sic-result-abstract
 fn-stmt-value fn-stmt-okp
 fn-stmt-decode-items-bounded-canonical)))))
