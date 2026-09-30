; SCN-1039: actual counter-domain and typed conditional demand teeth.
; Assumed primitive allocation is opaque. These do not invent a counterexample
; to a real allocator or pretend the local zero witness is that allocator.
(in-package "ACL2")
(include-book "../../books/payload-copy-runtime-workspace")

(defthm pwcrt-copy-demand-full-positive
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (<= (+ (nfix 2361183241434822674433) (nfix 2))
           4722366482869645213696)
       (natp (fn-pwc-copy-counter-demand 2361183241434822674433 2
                                         *fn-srp-selected-coordinate*))
       (equal (fn-pwc-copy-counter-demand 2361183241434822674433 2
                                          *fn-srp-selected-coordinate*) 192))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-copy-counter-demand))))

(defthm pwcrt-copy-demand-zero-positive
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (<= (+ (nfix 4722366482869645213696) (nfix 0))
           4722366482869645213696)
       (natp (fn-pwc-copy-counter-demand 4722366482869645213696 0
                                         *fn-srp-selected-coordinate*))
       (equal (fn-pwc-copy-counter-demand 4722366482869645213696 0
                                          *fn-srp-selected-coordinate*) 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-copy-counter-demand))))

(defthm pwcrt-copy-demand-remove-coordinate
  (and (not (fn-srp-coordinate-p '(:wrong-compiler)))
       (<= (+ (nfix 2361183241434822674433) (nfix 2))
           4722366482869645213696)
       (not (natp (fn-pwc-copy-counter-demand 2361183241434822674433 2
                                               '(:wrong-compiler))))
       (equal (fn-pwc-copy-counter-demand 2361183241434822674433 2
                                          '(:wrong-compiler)) nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-copy-counter-demand))))

(defthm pwcrt-copy-demand-remove-counter-domain
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (not (<= (+ (nfix 4722366482869645213696) (nfix 1))
                4722366482869645213696))
       (not (natp (fn-pwc-copy-counter-demand 4722366482869645213696 1
                                               *fn-srp-selected-coordinate*)))
       (equal (fn-pwc-copy-counter-demand 4722366482869645213696 1
                                          *fn-srp-selected-coordinate*) nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-copy-counter-demand))))

(defthm pwcrt-copy-negation-cost-mutation
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (<= (+ (nfix 2361183241434822674433) (nfix 2))
           4722366482869645213696)
       (equal (fn-pwc-copy-counter-demand 2361183241434822674433 2
                                          *fn-srp-selected-coordinate*) 192)
       (not (equal (fn-pwc-copy-counter-demand 2361183241434822674433 2
                                               *fn-srp-selected-coordinate*)
                   (* 64 2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-copy-counter-demand))))

(defthm pwcrt-actual-copy-conditional-workspace-positive
  (let* ((window (make-list 65536 :initial-element 23))
         (trace (cdr (fn-pzc-copy 2 0 1 2361183241434822674433 0 window nil)))
         (lowered (fn-pwc-lower-counter-trace trace)))
    (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
         (<= (+ (nfix 2361183241434822674433) (nfix 2))
             4722366482869645213696)
         (fn-srp-operation-trace-domain-p lowered 4722366482869645213696)
         (equal (fn-srp-operation-count :neg lowered) 2)
         (equal (fn-srp-operation-count :add lowered) 4)
         (<= (fn-srp-operation-trace-octets lowered *fn-srp-selected-coordinate*)
             (* 96 (nfix 2)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pwc-actual-copy-counter-primitive-workspace
                   (coordinate *fn-srp-selected-coordinate*) (k 2) (w 0) (d 1)
                   (tout 2361183241434822674433) (h 0)
                   (fn-zin-win (make-list 65536 :initial-element 23))
                   (fn-zin-out nil))
                 (:instance fn-pwc-actual-copy-counter-roster-domain
                   (k 2) (w 0) (d 1) (tout 2361183241434822674433) (h 0)
                   (fn-zin-win (make-list 65536 :initial-element 23))
                   (fn-zin-out nil))
                 (:instance fn-pzc-copy-counter-source-counts
                   (k 2) (w 0) (d 1) (tout 2361183241434822674433) (h 0)
                   (fn-zin-win (make-list 65536 :initial-element 23))
                   (fn-zin-out nil)))
           :in-theory (disable fn-pzc-copy fn-pwc-lower-counter-trace
               fn-srp-operation-trace-octets fn-srp-operation-trace-domain-p))))


(defthm pwcrt-actual-copy-domain-remove-width
  (let* ((trace (cdr (fn-pzc-copy 1 0 1 4722366482869645213697 0 nil nil)))
         (lowered (fn-pwc-lower-counter-trace trace)))
    (and (not (<= (+ (nfix 4722366482869645213697) (nfix 1))
                  4722366482869645213696))
         (not (fn-srp-operation-trace-domain-p lowered
                                                4722366482869645213696))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :expand ((:free (w d tout h fn-zin-win fn-zin-out)
                       (fn-pzc-copy 1 w d tout h fn-zin-win fn-zin-out))
                    (:free (w d tout h fn-zin-win fn-zin-out)
                       (fn-pzc-copy 0 w d tout h fn-zin-win fn-zin-out)))
           :in-theory (enable fn-pzc-copy fn-pzc-source
                  fn-pwc-lower-counter-trace fn-srp-operation-trace-domain-p
                  fn-srp-operand-domain-p fn-srp-integer-inputs-fit
                  fn-srp-head fn-srp-tail))))
