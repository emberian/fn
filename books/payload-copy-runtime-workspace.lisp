; PRF-1132. Conditional selected single NEG/ADD workspace for the actual
; copy output-counter trace. Not total decoder/compiler/job adequacy.
(in-package "ACL2")
(include-book "payload-copy-source-trace")
(include-book "assumptions-selected-runtime-primitives")

(defun fn-pwc-lower-counter-trace (trace)
  (if (consp trace)
      (cons (list (case (caar trace) (:negate :neg) (:add :add)
                       (otherwise :unsupported))
                  (cadar trace))
            (fn-pwc-lower-counter-trace (cdr trace)))
    nil))

(defun fn-pwc-counter-tracep (trace)
  (if (consp trace)
      (and (true-listp (cadar trace))
           (case (caar trace)
             (:negate (equal (len (cadar trace)) 1))
             (:add (equal (len (cadar trace)) 2))
             (otherwise nil))
           (fn-pwc-counter-tracep (cdr trace)))
    t))

(defthm fn-pwc-counter-tracep-append
  (equal (fn-pwc-counter-tracep (append left right))
         (and (fn-pwc-counter-tracep left)
              (fn-pwc-counter-tracep right))))

(defthm fn-pwc-lower-counter-counts
  (and (equal (fn-srp-operation-count :neg
                 (fn-pwc-lower-counter-trace trace))
              (fn-pzt-count :negate trace))
       (equal (fn-srp-operation-count :add
                 (fn-pwc-lower-counter-trace trace))
              (fn-pzt-count :add trace)))
  :hints (("Goal" :in-theory (enable fn-srp-operation-count
                                    fn-srp-head fn-srp-tail))))

(defthm fn-pwc-operands-imply-selected-inputs
  (implies (and (natp limit) (fn-pzc-operands-below limit xs))
           (fn-srp-integer-inputs-fit xs limit))
  :hints (("Goal" :induct (fn-pzc-operands-below limit xs)
                  :in-theory (enable fn-pzc-operands-below
                                     fn-srp-integer-inputs-fit))))

(defthm fn-pwc-lowered-counter-domain
  (implies (and (natp limit) (fn-pwc-counter-tracep trace)
                (fn-pzc-trace-operands-below limit trace))
           (fn-srp-operation-trace-domain-p
            (fn-pwc-lower-counter-trace trace) limit))
  :hints (("Goal" :induct (fn-pwc-lower-counter-trace trace)
                  :in-theory (enable fn-pwc-counter-tracep
                      fn-pzc-trace-operands-below
                      fn-srp-operation-trace-domain-p fn-srp-operand-domain-p
                      fn-srp-head fn-srp-tail))))

(defthm fn-pwc-actual-copy-counter-trace-shape
  (fn-pwc-counter-tracep
   (cdr (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out)))
  :hints (("Goal" :induct (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out)
                  :in-theory (e/d (fn-pzc-copy fn-pzc-source)
                              (fn-zin-wrap fn-zin-win-get fn-zin-win-put
                               fn-zin-out-append-octet min)))))

(defthm fn-pwc-actual-copy-counter-roster-domain
  (implies (<= (+ (nfix tout) (nfix k)) 4722366482869645213696)
           (fn-srp-operation-trace-domain-p
            (fn-pwc-lower-counter-trace
             (cdr (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out)))
            4722366482869645213696))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pzc-copy-counter-operands-width)
                       (:instance fn-pwc-lowered-counter-domain
                         (limit 4722366482869645213696)
                         (trace (cdr (fn-pzc-copy k w d tout h
                                                 fn-zin-win fn-zin-out)))))
                  :in-theory (disable fn-pzc-copy fn-pwc-lower-counter-trace
                      fn-srp-operation-trace-domain-p
                      fn-pzc-trace-operands-below fn-pwc-counter-tracep))))

(defun fn-pwc-copy-counter-demand (tout k coordinate)
  (declare (xargs :guard t))
  (and (fn-srp-coordinate-p coordinate)
       (<= (+ (nfix tout) (nfix k)) 4722366482869645213696)
       (* 96 (nfix k))))

(defthm fn-pwc-copy-counter-demand-selects-exact-domain
  (iff (natp (fn-pwc-copy-counter-demand tout k coordinate))
       (and (fn-srp-coordinate-p coordinate)
            (<= (+ (nfix tout) (nfix k)) 4722366482869645213696)))
  :hints (("Goal" :in-theory (enable fn-pwc-copy-counter-demand)))
  :rule-classes nil)

(defthm fn-pwc-actual-copy-counter-primitive-workspace
  (implies (and (fn-srp-coordinate-p coordinate)
                (<= (+ (nfix tout) (nfix k)) 4722366482869645213696))
           (<= (fn-srp-operation-trace-octets
                (fn-pwc-lower-counter-trace
                 (cdr (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out)))
                coordinate)
               (* 96 (nfix k))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pwc-actual-copy-counter-roster-domain)
                       (:instance fn-pzc-copy-counter-source-counts)
                       (:instance fn-srp-operation-trace-primitive-bound
                         (limit 4722366482869645213696)
                         (trace (fn-pwc-lower-counter-trace
                                 (cdr (fn-pzc-copy k w d tout h
                                                  fn-zin-win fn-zin-out))))))
                  :in-theory (e/d (fn-crw-primitive-buffer-octets fn-crl-align16)
                       (fn-pzc-copy fn-srp-coordinate-p
                        fn-srp-operation-trace-domain-p
                        fn-srp-operation-trace-octets
                        fn-pwc-lower-counter-trace)))))

(in-theory (disable fn-pwc-lower-counter-trace fn-pwc-counter-tracep))
