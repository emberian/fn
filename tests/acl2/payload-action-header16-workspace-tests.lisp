; PRF-1132 / SCN-1039: genuinely weaker generic16-bit pending carry.
(in-package "ACL2")
(include-book "../../books/payload-action-header16-workspace")

(defthm paw16-t-complete-match-positive
 (let ((r (fn-pat-zin-match 64 (fn-zin-set 0 12 (fn-zin-set 3 258 (fn-zin-set 4 1 (fn-zin-set 6 32768 (fn-zin-set 7 1024 (fn-zin-reset (create-fn-zin-st))))))) (make-list 65536 :initial-element 23) nil)))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (fn-pzw-state-header-widthp (fn-zin-set 0 12 (fn-zin-set 3 258 (fn-zin-set 4 1 (fn-zin-set 6 32768 (fn-zin-set 7 1024 (fn-zin-reset (create-fn-zin-st))))))))
       (equal (fn-zin-mode (fn-zin-set 0 12 (fn-zin-set 3 258 (fn-zin-set 4 1 (fn-zin-set 6 32768 (fn-zin-set 7 1024 (fn-zin-reset (create-fn-zin-st)))))))) 12)
       (fn-zin-window-ready-p (make-list 65536 :initial-element 23))
       (< (fn-zin-tin (fn-zin-set 0 12 (fn-zin-set 3 258 (fn-zin-set 4 1 (fn-zin-set 6 32768 (fn-zin-set 7 1024 (fn-zin-reset (create-fn-zin-st)))))))) 18446744073709551616)
       (<= (+ (fn-zin-tout (fn-zin-set 0 12 (fn-zin-set 3 258 (fn-zin-set 4 1 (fn-zin-set 6 32768 (fn-zin-set 7 1024 (fn-zin-reset (create-fn-zin-st)))))))) (nfix 64)) 4722366482869645213696)
       (< (fn-zin-n (fn-zin-set 0 12 (fn-zin-set 3 258 (fn-zin-set 4 1 (fn-zin-set 6 32768 (fn-zin-set 7 1024 (fn-zin-reset (create-fn-zin-st)))))))) 65536)
       (equal (fn-pat-match-count 64 (fn-zin-set 0 12 (fn-zin-set 3 258 (fn-zin-set 4 1 (fn-zin-set 6 32768 (fn-zin-set 7 1024 (fn-zin-reset (create-fn-zin-st)))))))) 64)
       (fn-ppr-arithmetic-domain (cdr r) 18889465931478580854784)
       (<= (fn-ppr-arithmetic-octets (cdr r) *fn-srp-selected-coordinate*) 6368)))
 :rule-classes nil
 :hints (("Goal"
   :use ((:instance fn-paw-match-header16-arithmetic-domain
             (room 64) (fn-zin-st (fn-zin-set 0 12 (fn-zin-set 3 258 (fn-zin-set 4 1 (fn-zin-set 6 32768 (fn-zin-set 7 1024 (fn-zin-reset (create-fn-zin-st)))))))) (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil))
         (:instance fn-paw-actual-match-header16-arithmetic-workspace
             (coordinate *fn-srp-selected-coordinate*)
             (room 64) (fn-zin-st (fn-zin-set 0 12 (fn-zin-set 3 258 (fn-zin-set 4 1 (fn-zin-set 6 32768 (fn-zin-set 7 1024 (fn-zin-reset (create-fn-zin-st)))))))) (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil)))
   :in-theory (e/d (fn-pat-match-count fn-pzw-state-header-widthp fn-zin-window-ready-p)
                   (fn-pat-zin-match fn-ppr-arithmetic-domain fn-ppr-arithmetic-octets)))))

(defthm paw16-t-remove-input-corrupted-state
 (and (not (< (fn-zin-tin (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616)) (<= (+ (fn-zin-tout (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) (nfix 1)) 4722366482869645213696) (< (fn-zin-n (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 65536)
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-match 1 (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) nil nil)) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-match fn-pzt-zin-bomb-limit
                     fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                     fn-srp-integer-inputs-fit fn-ppr-scale-factor fn-ppr-scale-value
                     fn-srp-positive-factorp fn-srp-positive-operand-domain-p)
                    (fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                     fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

(defthm paw16-t-remove-span-corrupted-state
 (and (< (fn-zin-tin (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616) (not (<= (+ (fn-zin-tout (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) (nfix 1)) 4722366482869645213696)) (< (fn-zin-n (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 65536)
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-match 1 (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) nil nil)) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-match fn-pzt-zin-bomb-limit
                     fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                     fn-srp-integer-inputs-fit fn-ppr-scale-factor fn-ppr-scale-value
                     fn-srp-positive-factorp fn-srp-positive-operand-domain-p)
                    (fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                     fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

(defthm paw16-t-remove-header-corrupted-state
 (and (< (fn-zin-tin (fn-zin-set 3 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616) (<= (+ (fn-zin-tout (fn-zin-set 3 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) (nfix 1)) 4722366482869645213696) (not (< (fn-zin-n (fn-zin-set 3 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 65536))
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-match 1 (fn-zin-set 3 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) nil nil)) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-match fn-pzt-zin-bomb-limit
                     fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                     fn-srp-integer-inputs-fit fn-ppr-scale-factor fn-ppr-scale-value
                     fn-srp-positive-factorp fn-srp-positive-operand-domain-p)
                    (fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                     fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

(defthm paw16-t-generic-header-origin-corruption
 (and (fn-pzw-state-header-widthp (fn-zin-set 0 12 (fn-zin-set 3 65535 (fn-zin-reset (create-fn-zin-st)))))
      (equal (fn-zin-mode (fn-zin-set 0 12 (fn-zin-set 3 65535 (fn-zin-reset (create-fn-zin-st))))) 12)
      (not (< (fn-zin-n (fn-zin-set 0 12 (fn-zin-set 3 65535 (fn-zin-reset (create-fn-zin-st))))) 259))
      (< (fn-zin-n (fn-zin-set 0 12 (fn-zin-set 3 65535 (fn-zin-reset (create-fn-zin-st))))) 65536))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzw-state-header-widthp))))
