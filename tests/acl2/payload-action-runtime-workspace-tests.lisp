; PRF-1132 / SCN-1039: full conditional arithmetic positives and domain teeth.
; Corrupted-state removals do not claim real allocator counterexamples.
(in-package "ACL2")
(include-book "../../books/payload-action-runtime-workspace")

(defthm paw-t-emit-0-full-conditional-positive
 (let ((r (fn-pat-zin-emit 65 (fn-zin-reset (create-fn-zin-st)) (make-list 65536 :initial-element 23) nil)))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (< (fn-zin-tin (fn-zin-reset (create-fn-zin-st))) 18446744073709551616)
       (< (fn-zin-tout (fn-zin-reset (create-fn-zin-st))) 4722366482869645213696)
       (equal (car r) (fn-zin-emit 65 (fn-zin-reset (create-fn-zin-st)) (make-list 65536 :initial-element 23) nil))
       (fn-ppr-arithmetic-domain (cdr r) 18889465931478580854784)
       (<= (fn-ppr-arithmetic-octets (cdr r) *fn-srp-selected-coordinate*) 160)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-paw-emit-arithmetic-domain (o 65) (fn-zin-st (fn-zin-reset (create-fn-zin-st))) (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil))
                       (:instance fn-paw-actual-emit-arithmetic-workspace
                          (coordinate *fn-srp-selected-coordinate*) (o 65) (fn-zin-st (fn-zin-reset (create-fn-zin-st))) (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil)))
          :in-theory (e/d (fn-pat-match-count)
                 (fn-pat-zin-emit fn-ppr-arithmetic-domain fn-ppr-arithmetic-octets)))))

(defthm paw-t-pull-1-full-conditional-positive
 (let ((r (fn-pat-zin-pull 0 (fn-zin-reset (create-fn-zin-st)) (list 65))))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (< (fn-zin-tin (fn-zin-reset (create-fn-zin-st))) 18446744073709551616)
       (< (fn-zin-nbits (fn-zin-reset (create-fn-zin-st))) 64)
       (equal (car r) (fn-zin-pull 0 (fn-zin-reset (create-fn-zin-st)) (list 65)))
       (fn-ppr-arithmetic-domain (cdr r) 18889465931478580854784)
       (<= (fn-ppr-arithmetic-octets (cdr r) *fn-srp-selected-coordinate*) 64)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-paw-pull-arithmetic-domain (ip 0) (fn-zin-st (fn-zin-reset (create-fn-zin-st))) (fn-octets (list 65)))
                       (:instance fn-paw-actual-pull-arithmetic-workspace
                          (coordinate *fn-srp-selected-coordinate*) (ip 0) (fn-zin-st (fn-zin-reset (create-fn-zin-st))) (fn-octets (list 65))))
          :in-theory (e/d (fn-pat-match-count)
                 (fn-pat-zin-pull fn-ppr-arithmetic-domain fn-ppr-arithmetic-octets)))))

(defthm paw-t-match-2-full-conditional-positive
 (let ((r (fn-pat-zin-match 64 (fn-zin-set 3 64 (fn-zin-set 4 1 (fn-zin-set 6 2361183241434822600000 (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st)))))) (make-list 65536 :initial-element 23) nil)))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (< (fn-zin-tin (fn-zin-set 3 64 (fn-zin-set 4 1 (fn-zin-set 6 2361183241434822600000 (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st))))))) 18446744073709551616)
       (<= (+ (fn-zin-tout (fn-zin-set 3 64 (fn-zin-set 4 1 (fn-zin-set 6 2361183241434822600000 (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st))))))) (nfix 64)) 4722366482869645213696)
       (< (fn-zin-n (fn-zin-set 3 64 (fn-zin-set 4 1 (fn-zin-set 6 2361183241434822600000 (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st))))))) 259)
       (equal (fn-pat-match-count 64 (fn-zin-set 3 64 (fn-zin-set 4 1 (fn-zin-set 6 2361183241434822600000 (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st))))))) 64)
       (equal (car r) (fn-zin-match 64 (fn-zin-set 3 64 (fn-zin-set 4 1 (fn-zin-set 6 2361183241434822600000 (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st)))))) (make-list 65536 :initial-element 23) nil))
       (fn-ppr-arithmetic-domain (cdr r) 18889465931478580854784)
       (<= (fn-ppr-arithmetic-octets (cdr r) *fn-srp-selected-coordinate*) 6368)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-paw-match-arithmetic-domain (room 64) (fn-zin-st (fn-zin-set 3 64 (fn-zin-set 4 1 (fn-zin-set 6 2361183241434822600000 (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st))))))) (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil))
                       (:instance fn-paw-actual-match-arithmetic-workspace
                          (coordinate *fn-srp-selected-coordinate*) (room 64) (fn-zin-st (fn-zin-set 3 64 (fn-zin-set 4 1 (fn-zin-set 6 2361183241434822600000 (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st))))))) (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil)))
          :in-theory (e/d (fn-pat-match-count)
                 (fn-pat-zin-match fn-ppr-arithmetic-domain fn-ppr-arithmetic-octets)))))

(defthm paw-t-match-3-full-conditional-positive
 (let ((r (fn-pat-zin-match 64 (fn-zin-reset (create-fn-zin-st)) (make-list 65536 :initial-element 23) nil)))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (< (fn-zin-tin (fn-zin-reset (create-fn-zin-st))) 18446744073709551616)
       (<= (+ (fn-zin-tout (fn-zin-reset (create-fn-zin-st))) (nfix 64)) 4722366482869645213696)
       (< (fn-zin-n (fn-zin-reset (create-fn-zin-st))) 259)
       (equal (fn-pat-match-count 64 (fn-zin-reset (create-fn-zin-st))) 0)
       (equal (car r) (fn-zin-match 64 (fn-zin-reset (create-fn-zin-st)) (make-list 65536 :initial-element 23) nil))
       (fn-ppr-arithmetic-domain (cdr r) 18889465931478580854784)
       (<= (fn-ppr-arithmetic-octets (cdr r) *fn-srp-selected-coordinate*) 128)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-paw-match-arithmetic-domain (room 64) (fn-zin-st (fn-zin-reset (create-fn-zin-st))) (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil))
                       (:instance fn-paw-actual-match-arithmetic-workspace
                          (coordinate *fn-srp-selected-coordinate*) (room 64) (fn-zin-st (fn-zin-reset (create-fn-zin-st))) (fn-zin-win (make-list 65536 :initial-element 23)) (fn-zin-out nil)))
          :in-theory (e/d (fn-pat-match-count)
                 (fn-pat-zin-match fn-ppr-arithmetic-domain fn-ppr-arithmetic-octets)))))

(defthm paw-t-emit-remove-input-corrupted-state
 (and (not (< (fn-zin-tin (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616))
       (< (fn-zin-tout (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 4722366482869645213696)
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-emit 65 (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) nil nil)) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-emit fn-pzt-zin-bomb-limit
                    fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                    fn-srp-integer-inputs-fit fn-ppr-scale-factor
                    fn-ppr-scale-value fn-srp-positive-factorp
                    fn-srp-positive-operand-domain-p)
                   (fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                    fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

(defthm paw-t-emit-remove-output-corrupted-state
 (and (< (fn-zin-tin (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616)
       (not (< (fn-zin-tout (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 4722366482869645213696))
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-emit 65 (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) nil nil)) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-emit fn-pzt-zin-bomb-limit
                    fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                    fn-srp-integer-inputs-fit fn-ppr-scale-factor
                    fn-ppr-scale-value fn-srp-positive-factorp
                    fn-srp-positive-operand-domain-p)
                   (fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                    fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

(defthm paw-t-pull-remove-input-corrupted-state
 (and (not (< (fn-zin-tin (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616))
       (< (fn-zin-nbits (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 64)
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-pull 0 (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) (list 65))) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-pull fn-pzt-zin-bomb-limit
                    fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                    fn-srp-integer-inputs-fit fn-ppr-scale-factor
                    fn-ppr-scale-value fn-srp-positive-factorp
                    fn-srp-positive-operand-domain-p)
                   (fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                    fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

(defthm paw-t-match-remove-input-corrupted-state
 (and (not (< (fn-zin-tin (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616))
       (<= (+ (fn-zin-tout (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) (nfix 1)) 4722366482869645213696)
       (< (fn-zin-n (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 259)
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-match 1 (fn-zin-set 7 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) nil nil)) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-match fn-pzt-zin-bomb-limit
                    fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                    fn-srp-integer-inputs-fit fn-ppr-scale-factor
                    fn-ppr-scale-value fn-srp-positive-factorp
                    fn-srp-positive-operand-domain-p)
                   (fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                    fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

(defthm paw-t-match-remove-span-corrupted-state
 (and (< (fn-zin-tin (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616)
       (not (<= (+ (fn-zin-tout (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) (nfix 1)) 4722366482869645213696))
       (< (fn-zin-n (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 259)
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-match 1 (fn-zin-set 6 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) nil nil)) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-match fn-pzt-zin-bomb-limit
                    fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                    fn-srp-integer-inputs-fit fn-ppr-scale-factor
                    fn-ppr-scale-value fn-srp-positive-factorp
                    fn-srp-positive-operand-domain-p)
                   (fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                    fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

(defthm paw-t-match-remove-header-corrupted-state
 (and (< (fn-zin-tin (fn-zin-set 3 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616)
       (<= (+ (fn-zin-tout (fn-zin-set 3 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) (nfix 1)) 4722366482869645213696)
       (not (< (fn-zin-n (fn-zin-set 3 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 259))
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-match 1 (fn-zin-set 3 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) nil nil)) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-match fn-pzt-zin-bomb-limit
                    fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                    fn-srp-integer-inputs-fit fn-ppr-scale-factor
                    fn-ppr-scale-value fn-srp-positive-factorp
                    fn-srp-positive-operand-domain-p)
                   (fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                    fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

; The corrupted NBITS is fixed; conclusion holds for every external buffer.
; Keep that irrelevant input symbolic to avoid eagerly executing malformed
; state EXPT during theorem preprocessing. Actual supported carry forbids it.
(defthm paw-t-pull-remove-bits-corrupted-state
 (and (< (fn-zin-tin (fn-zin-set 2 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 18446744073709551616)
       (not (< (fn-zin-nbits (fn-zin-set 2 18889465931478580854785 (fn-zin-reset (create-fn-zin-st)))) 64))
      (not (fn-ppr-arithmetic-domain (cdr (fn-pat-zin-pull 0 (fn-zin-set 2 18889465931478580854785 (fn-zin-reset (create-fn-zin-st))) fn-octets)) 18889465931478580854784)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-pull fn-pzt-zin-bomb-limit
                    fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                    fn-srp-integer-inputs-fit fn-ppr-scale-factor
                    fn-ppr-scale-value fn-srp-positive-factorp
                    fn-srp-positive-operand-domain-p)
                   ((:executable-counterpart fn-pat-zin-pull)
                    fn-oct-get-is-nth fn-octets-get
                    fn-zin-shift-in fn-zin-win-put fn-zin-out-append-octet
                    fn-pzc-copy fn-zin-copy fn-zin-wrap binary-append)))))

