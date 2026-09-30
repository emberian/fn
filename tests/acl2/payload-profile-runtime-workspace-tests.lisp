; SCN-1039. Actual arithmetic-family domain and conditional primitive join.
(in-package "ACL2")
(include-book "../../books/payload-profile-runtime-workspace")
(include-book "selected-runtime-positive-tests")

(defthm pprt-actual-allowance-full-positive
 (let* ((c 9223372036854775807) (observed (fn-pzt-zin-stored-allowance c))
        (trace (cdr observed)))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (< (nfix c) 9223372036854775808)
       (equal (car observed) (fn-zin-stored-allowance c))
       (fn-ppr-arithmetic-domain trace 18889465931478580854784)
       (equal (fn-pzt-count :add trace) 1)
       (equal (fn-pzt-count :multiply trace) 1)
       (equal (fn-pzt-count :negate trace) 0)
       (<= (fn-ppr-arithmetic-octets trace *fn-srp-selected-coordinate*) 64)))
 :hints (("Goal" :use ((:instance fn-ppr-actual-stored-allowance-primitive-workspace
    (coordinate *fn-srp-selected-coordinate*) (compressed 9223372036854775807))
   (:instance fn-ppr-actual-stored-allowance-arithmetic-domain
    (compressed 9223372036854775807)))
   :in-theory (e/d (fn-pzt-zin-stored-allowance fn-ppr-arithmetic-domain
      fn-srp-operand-domain-p fn-srp-integer-inputs-fit
      fn-spp-operand-domain-p fn-spp-factorp fn-ppr-scale-factor fn-ppr-scale-value)
     (fn-ppr-arithmetic-octets))))
 :rule-classes nil)

(defthm pprt-actual-budget-full-positive
 (let* ((c 9223372036854775807) (n (fn-zin-stored-allowance 9223372036854775807))
        (observed (fn-pzt-pzd-budget c n)) (trace (cdr observed)))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (< (nfix c) 9223372036854775808)
       (< (nfix n) 4722366482869645213696)
       (fn-pzw-stored-admissiblep c n)
       (equal (car observed) (fn-pzd-budget c n))
       (fn-ppr-arithmetic-domain trace 18889465931478580854784)
       (equal (fn-pzt-count :add trace) 2)
       (equal (fn-pzt-count :multiply trace) 2)
       (equal (fn-pzt-count :negate trace) 0)
       (<= (fn-ppr-arithmetic-octets trace *fn-srp-selected-coordinate*) 128)))
 :hints (("Goal" :use ((:instance fn-ppr-actual-budget-primitive-workspace
    (coordinate *fn-srp-selected-coordinate*) (compressed 9223372036854775807)
    (expected (fn-zin-stored-allowance 9223372036854775807)))
   (:instance fn-ppr-actual-budget-arithmetic-domain
    (compressed 9223372036854775807) (expected (fn-zin-stored-allowance 9223372036854775807))))
   :in-theory (e/d (fn-pzt-pzd-budget fn-zin-stored-allowance
      fn-pzw-stored-admissiblep fn-pzw-stored-allowance fn-ppr-arithmetic-domain
      fn-srp-operand-domain-p fn-srp-integer-inputs-fit
      fn-spp-operand-domain-p fn-spp-factorp fn-ppr-scale-factor fn-ppr-scale-value)
     (fn-ppr-arithmetic-octets))))
 :rule-classes nil)

(defthm pprt-allowance-domain-remove-source-bound
 (let ((c 1267650600228229401496703205376))
  (and (not (< (nfix c) 9223372036854775808))
       (not (fn-ppr-arithmetic-domain
             (cdr (fn-pzt-zin-stored-allowance c)) 18889465931478580854784))))
 :hints (("Goal" :in-theory (enable fn-pzt-zin-stored-allowance
   fn-ppr-arithmetic-domain fn-srp-operand-domain-p fn-srp-integer-inputs-fit
   fn-spp-operand-domain-p fn-spp-factorp fn-ppr-scale-factor fn-ppr-scale-value)))
 :rule-classes nil)

(defthm pprt-budget-domain-remove-source-bound
 (let ((c 1267650600228229401496703205376) (n 0))
  (and (not (< (nfix c) 9223372036854775808))
       (< (nfix n) 4722366482869645213696)
       (not (fn-ppr-arithmetic-domain
             (cdr (fn-pzt-pzd-budget c n)) 18889465931478580854784))))
 :hints (("Goal" :in-theory (enable fn-pzt-pzd-budget fn-ppr-arithmetic-domain
   fn-srp-operand-domain-p fn-srp-integer-inputs-fit
   fn-spp-operand-domain-p fn-spp-factorp fn-ppr-scale-factor fn-ppr-scale-value)))
 :rule-classes nil)

(defthm pprt-budget-domain-remove-decoded-bound
 (let ((c 0) (n 1267650600228229401496703205376))
  (and (< (nfix c) 9223372036854775808)
       (not (< (nfix n) 4722366482869645213696))
       (not (fn-ppr-arithmetic-domain
             (cdr (fn-pzt-pzd-budget c n)) 18889465931478580854784))))
 :hints (("Goal" :in-theory (enable fn-pzt-pzd-budget fn-ppr-arithmetic-domain
   fn-srp-operand-domain-p fn-srp-integer-inputs-fit
   fn-spp-operand-domain-p fn-spp-factorp fn-ppr-scale-factor fn-ppr-scale-value)))
 :rule-classes nil)

; The decoded72bit bound alone allows N above actual stored admissibility.
; Its budget's intermediate sum can exceed2^73, so do not truncate it there.
; Unsupported-stored-input mutation: this N is not an admitted stored length.
(defthm pprt-budget-intermediate-73bit-mutation
 (let ((c 9223372036854775807) (n 4722366482869645213695))
  (and (< (nfix c) 9223372036854775808)
       (< (nfix n) 4722366482869645213696)
       (not (fn-pzw-stored-admissiblep c n))
       (< 9444732965739290427392 (+ (* 16 c) (* 2 n)))
       (fn-ppr-arithmetic-domain
        (cdr (fn-pzt-pzd-budget c n)) 18889465931478580854784)))
 :hints (("Goal" :in-theory (enable fn-pzt-pzd-budget fn-zin-stored-allowance
   fn-pzw-stored-admissiblep fn-pzw-stored-allowance fn-ppr-arithmetic-domain
   fn-srp-operand-domain-p fn-srp-integer-inputs-fit
   fn-spp-operand-domain-p fn-spp-factorp fn-ppr-scale-factor fn-ppr-scale-value)))
 :rule-classes nil)
