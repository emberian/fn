; PRF-1132: actual action arithmetic conditional joins, no borrowed costs.
(in-package "ACL2")
(include-book "payload-action-source-counts")
(include-book "payload-copy-runtime-workspace")
(include-book "payload-profile-runtime-workspace")

(defthm fn-paw-arithmetic-domain-append
 (equal (fn-ppr-arithmetic-domain (append left right) limit)
        (and (fn-ppr-arithmetic-domain left limit)
             (fn-ppr-arithmetic-domain right limit)))
 :hints (("Goal" :in-theory (enable fn-ppr-arithmetic-domain))))

(defthm fn-paw-counter-source-domain
 (implies (and (natp limit) (fn-pwc-counter-tracep trace)
               (fn-pzc-trace-operands-below limit trace))
          (fn-ppr-arithmetic-domain trace limit))
 :hints (("Goal" :induct (fn-pwc-counter-tracep trace)
   :in-theory (enable fn-pwc-counter-tracep fn-pzc-trace-operands-below
                    fn-ppr-arithmetic-domain fn-srp-operand-domain-p))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (local
  (defthm fn-paw-integer-operands-monotone
  (implies (and (<= low high) (fn-pzc-operands-below low xs))
           (fn-pzc-operands-below high xs))
  :hints (("Goal" :induct (fn-pzc-operands-below low xs)
                  :in-theory (enable fn-pzc-operands-below)))))
 (local
  (defthm fn-paw-trace-operands-monotone
  (implies (and (<= low high) (fn-pzc-trace-operands-below low trace))
           (fn-pzc-trace-operands-below high trace))
  :hints (("Goal" :induct (fn-pzc-trace-operands-below low trace)
                  :in-theory (enable fn-pzc-trace-operands-below)))))
 (defthm fn-paw-copy-arithmetic-domain
  (implies (<= (+ (nfix tout) (nfix k)) 4722366482869645213696)
           (fn-ppr-arithmetic-domain
            (cdr (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out))
            18889465931478580854784))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pzc-copy-counter-operands-width)
         (:instance fn-paw-trace-operands-monotone
             (low 4722366482869645213696) (high 18889465931478580854784)
             (trace (cdr (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out)))))
   :in-theory (disable fn-pzc-copy fn-pzc-trace-operands-below
                       fn-ppr-arithmetic-domain fn-pwc-counter-tracep))))
 (defthm fn-paw-emit-arithmetic-domain
  (implies (and (< (fn-zin-tin fn-zin-st) 18446744073709551616)
                (< (fn-zin-tout fn-zin-st) 4722366482869645213696))
           (fn-ppr-arithmetic-domain
            (cdr (fn-pat-zin-emit o fn-zin-st fn-zin-win fn-zin-out))
            18889465931478580854784))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-pat-zin-emit fn-pzt-zin-bomb-limit fn-ppr-arithmetic-domain
                 fn-srp-operand-domain-p fn-srp-integer-inputs-fit
                 fn-srp-positive-operand-domain-p fn-srp-positive-factorp
                 fn-ppr-scale-factor fn-ppr-scale-value)
                (fn-zin-fld fn-zin-wrap fn-zin-set fn-zin-win-put
                 fn-zin-out-append-octet binary-append)))))
 (defthm fn-paw-pull-arithmetic-domain
  (implies (and (< (fn-zin-tin fn-zin-st) 18446744073709551616)
                (< (fn-zin-nbits fn-zin-st) 64))
           (fn-ppr-arithmetic-domain
            (cdr (fn-pat-zin-pull ip fn-zin-st fn-octets))
            18889465931478580854784))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-pat-zin-pull fn-ppr-arithmetic-domain
                 fn-srp-operand-domain-p fn-srp-integer-inputs-fit)
                (fn-zin-fld fn-zin-set fn-zin-shift-in fn-octets-get binary-append)))))
 (defthm fn-paw-match-copied-span
  (implies (<= (+ (fn-zin-tout fn-zin-st) (nfix room))
               4722366482869645213696)
           (<= (+ (fn-zin-tout fn-zin-st)
                  (nfix (fn-pat-match-count room fn-zin-st)))
               4722366482869645213696))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pat-match-count))))
 (defthm fn-paw-match-arithmetic-domain
  (implies (and (< (fn-zin-tin fn-zin-st) 18446744073709551616)
                (<= (+ (fn-zin-tout fn-zin-st) (nfix room))
                    4722366482869645213696)
                (< (fn-zin-n fn-zin-st) 259))
           (fn-ppr-arithmetic-domain
            (cdr (fn-pat-zin-match room fn-zin-st fn-zin-win fn-zin-out))
            18889465931478580854784))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-paw-match-copied-span)
                 (:instance fn-paw-copy-arithmetic-domain
                   (k (fn-pat-match-count room fn-zin-st))
                   (w (fn-zin-wpos fn-zin-st)) (d (fn-zin-dist fn-zin-st))
                   (tout (fn-zin-tout fn-zin-st)) (h (fn-zin-preset fn-zin-st))))
           :in-theory
           (e/d (fn-pat-zin-match fn-pat-match-count fn-pzt-zin-bomb-limit
                 fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                 fn-srp-integer-inputs-fit fn-srp-positive-operand-domain-p
                 fn-srp-positive-factorp fn-ppr-scale-factor fn-ppr-scale-value)
                (fn-zin-fld fn-zin-set fn-pzc-copy fn-zin-copy binary-append))))))

(defthm fn-paw-actual-emit-arithmetic-workspace
 (implies (and (fn-srp-coordinate-p coordinate)
               (< (fn-zin-tin fn-zin-st) 18446744073709551616)
               (< (fn-zin-tout fn-zin-st) 4722366482869645213696))
          (<= (fn-ppr-arithmetic-octets
               (cdr (fn-pat-zin-emit o fn-zin-st fn-zin-win fn-zin-out)) coordinate)
              (if (< (fn-zin-bomb-limit fn-zin-st)
                     (1+ (fn-zin-tout fn-zin-st))) 96 160)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-paw-emit-arithmetic-domain)
        (:instance fn-pat-emit-arithmetic-counts)
        (:instance fn-ppr-arithmetic-family-primitive-bound
          (limit 18889465931478580854784)
          (trace (cdr (fn-pat-zin-emit o fn-zin-st fn-zin-win fn-zin-out)))))
  :in-theory (e/d (fn-crw-primitive-buffer-octets fn-crl-align16)
                 (fn-pat-zin-emit fn-ppr-arithmetic-domain
                  fn-ppr-arithmetic-octets fn-srp-coordinate-p)))))

(defthm fn-paw-actual-pull-arithmetic-workspace
 (implies (and (fn-srp-coordinate-p coordinate)
               (< (fn-zin-tin fn-zin-st) 18446744073709551616)
               (< (fn-zin-nbits fn-zin-st) 64))
          (<= (fn-ppr-arithmetic-octets
               (cdr (fn-pat-zin-pull ip fn-zin-st fn-octets)) coordinate) 64))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-paw-pull-arithmetic-domain)
        (:instance fn-pat-pull-arithmetic-counts)
        (:instance fn-ppr-arithmetic-family-primitive-bound
          (limit 18889465931478580854784)
          (trace (cdr (fn-pat-zin-pull ip fn-zin-st fn-octets)))))
  :in-theory (e/d (fn-crw-primitive-buffer-octets fn-crl-align16)
                 (fn-pat-zin-pull fn-ppr-arithmetic-domain
                  fn-ppr-arithmetic-octets fn-srp-coordinate-p)))))

(defthm fn-paw-actual-match-arithmetic-workspace
 (implies (and (fn-srp-coordinate-p coordinate)
               (< (fn-zin-tin fn-zin-st) 18446744073709551616)
               (<= (+ (fn-zin-tout fn-zin-st) (nfix room))
                   4722366482869645213696)
               (< (fn-zin-n fn-zin-st) 259))
          (<= (fn-ppr-arithmetic-octets
               (cdr (fn-pat-zin-match room fn-zin-st fn-zin-win fn-zin-out)) coordinate)
              (if (zp (fn-pat-match-count room fn-zin-st)) 128
                (+ 224 (* 96 (nfix (fn-pat-match-count room fn-zin-st)))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-paw-match-arithmetic-domain)
        (:instance fn-pat-match-arithmetic-counts)
        (:instance fn-ppr-arithmetic-family-primitive-bound
          (limit 18889465931478580854784)
          (trace (cdr (fn-pat-zin-match room fn-zin-st fn-zin-win fn-zin-out)))))
  :in-theory (e/d (fn-crw-primitive-buffer-octets fn-crl-align16)
                 (fn-pat-zin-match fn-ppr-arithmetic-domain
                  fn-ppr-arithmetic-octets fn-srp-coordinate-p)))))
