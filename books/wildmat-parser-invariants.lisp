; Grammar-result invariants for the bounded RFC 3977 wildmat parser.
;
; This book proves a result-shape property only: a successful parser result is
; a nonempty list of nonempty positive/negative item patterns.  UTF-8 scalar
; safety and decoder progress are established separately in
; wildmat-utf8-invariants.lisp.

(in-package "ACL2")

(include-book "wildmat-utf8-invariants")

; The scanner carries a reversed item accumulator.  Starting it with NIL, as
; parse-one does, means every successful end or separator has produced at
; least one syntactically valid item.
(defthm fn-wm-scan-end-nil-items
  (implies (fn-wildmat-scan-endp (fn-wildmat-scan-pattern codepoints nil))
           (and (consp (fn-wildmat-scan-items
                        (fn-wildmat-scan-pattern codepoints nil)))
                (fn-wildmat-items-p
                 (fn-wildmat-scan-items
                  (fn-wildmat-scan-pattern codepoints nil)))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-scan-end-success-items
                            (items-rev nil)))
           :in-theory (enable fn-wildmat-scan-endp fn-wildmat-items-p))))

(defthm fn-wm-scan-more-nil-items
  (implies (fn-wildmat-scan-morep (fn-wildmat-scan-pattern codepoints nil))
           (and (consp (fn-wildmat-scan-items
                        (fn-wildmat-scan-pattern codepoints nil)))
                (fn-wildmat-items-p
                 (fn-wildmat-scan-items
                  (fn-wildmat-scan-pattern codepoints nil)))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-scan-more-success-items
                            (items-rev nil)))
           :in-theory (enable fn-wildmat-scan-morep fn-wildmat-items-p))))

(defthm fn-wm-scan-end-nil-items-consp
  (implies (fn-wildmat-scan-endp (fn-wildmat-scan-pattern codepoints nil))
           (consp (fn-wildmat-scan-items
                   (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal" :use fn-wm-scan-end-nil-items))
  :rule-classes :forward-chaining)

(defthm fn-wm-scan-end-nil-items-valid
  (implies (fn-wildmat-scan-endp (fn-wildmat-scan-pattern codepoints nil))
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal" :use fn-wm-scan-end-nil-items))
  :rule-classes :forward-chaining)

(defthm fn-wm-scan-more-nil-items-consp
  (implies (fn-wildmat-scan-morep (fn-wildmat-scan-pattern codepoints nil))
           (consp (fn-wildmat-scan-items
                   (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal" :use fn-wm-scan-more-nil-items))
  :rule-classes :forward-chaining)

(defthm fn-wm-scan-more-nil-items-valid
  (implies (fn-wildmat-scan-morep (fn-wildmat-scan-pattern codepoints nil))
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal" :use fn-wm-scan-more-nil-items))
  :rule-classes :forward-chaining)

(defthm fn-wm-scan-more-excludes-end
  (implies (fn-wildmat-scan-morep scan)
           (not (fn-wildmat-scan-endp scan)))
  :hints (("Goal" :in-theory (enable fn-wildmat-scan-morep
                                      fn-wildmat-scan-endp))))

; This recursion mirrors parse-one's only recursive call.  In particular, its
; induction hypothesis changes both the remaining codepoints and the sign in
; the same way as the executable parser after a comma.
(defun fn-wm-parse-one-induct (codepoints positivep fuel)
  (declare (ignore positivep)
           (xargs :measure (nfix fuel)))
  (if (zp fuel)
      nil
    (let ((scan (fn-wildmat-scan-pattern codepoints nil)))
      (if (fn-wildmat-scan-morep scan)
          (let* ((rest (fn-wildmat-scan-rest scan))
                 (negativep (and (consp rest) (equal (car rest) 33))))
            (fn-wm-parse-one-induct
             (if negativep (cdr rest) rest)
             (if negativep nil t)
             (1- fuel)))
        nil))))

(defthm fn-wm-parse-one-success-pattern-listp
  (implies (fn-wildmat-result-okp
            (fn-wildmat-parse-one codepoints positivep fuel))
           (and (consp (fn-wildmat-result-value
                        (fn-wildmat-parse-one codepoints positivep fuel)))
                (fn-wildmat-pattern-listp
                 (fn-wildmat-result-value
                  (fn-wildmat-parse-one codepoints positivep fuel)))))
  :hints (("Goal"
           :induct (fn-wm-parse-one-induct codepoints positivep fuel)
           :in-theory (e/d (fn-wildmat-parse-one
                               fn-wildmat-result-okp
                               fn-wildmat-result-value
                               fn-wm-scan-end-nil-items-consp
                               fn-wm-scan-end-nil-items-valid
                               fn-wm-scan-more-nil-items-consp
                               fn-wm-scan-more-nil-items-valid
                               fn-wm-scan-more-excludes-end
                               fn-wildmat-parsedp
                               fn-wildmat-pattern-listp
                               fn-wildmat-patternp
                               fn-wildmat-make-pattern)
                           (fn-wildmat-scan-endp
                            fn-wildmat-scan-morep)))
          ("Subgoal *1/3.4''"
           :use (fn-wm-scan-end-nil-items-consp
                 fn-wm-scan-end-nil-items-valid))
          ("Subgoal *1/3.3''"
           :use (fn-wm-scan-end-nil-items-valid))
          ("Subgoal *1/3.2''"
           :use (fn-wm-scan-end-nil-items-consp))
          ("Subgoal *1/3.1''"
           :use (fn-wm-scan-end-nil-items-valid))
          ("Subgoal *1/2.8''"
           :use (fn-wm-scan-more-nil-items-consp))
          ("Subgoal *1/2.7''"
           :use (fn-wm-scan-more-nil-items-valid))
          ("Subgoal *1/2.6''"
           :use (fn-wm-scan-more-nil-items-consp))
          ("Subgoal *1/2.5''"
           :use (fn-wm-scan-more-nil-items-valid))
          ("Subgoal *1/2.4''"
           :use (fn-wm-scan-more-nil-items-consp))
          ("Subgoal *1/2.3''"
           :use (fn-wm-scan-more-nil-items-valid))
          ("Subgoal *1/2.2''"
           :use (fn-wm-scan-more-nil-items-consp))
          ("Subgoal *1/2.1''"
           :use (fn-wm-scan-more-nil-items-valid))))

(defthm fn-wildmat-successful-parse-parsedp
  (implies (fn-wildmat-result-okp (fn-wildmat-parse octets))
           (fn-wildmat-parsedp
            (fn-wildmat-result-value (fn-wildmat-parse octets))))
  :hints (("Goal"
           :use ((:instance fn-wm-parse-one-success-pattern-listp
                            (codepoints
                             (fn-wildmat-result-value
                              (fn-wildmat-decode octets)))
                            (positivep t)
                            (fuel *fn-wildmat-max-octets*)))
           :in-theory (e/d (fn-wildmat-parse
                             fn-wildmat-parse-codepoints
                             fn-wildmat-result-okp
                             fn-wildmat-result-value
                             fn-wildmat-parsedp)
                           (fn-wildmat-parse-one)))))
