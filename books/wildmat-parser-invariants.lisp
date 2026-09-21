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
                (fn-wildmat-text-items-p
                 (fn-wildmat-scan-items
                  (fn-wildmat-scan-pattern codepoints nil)))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-scan-end-success-items
                            (items-rev nil)))
           :in-theory (enable fn-wildmat-scan-endp fn-wildmat-text-items-p))))

(defthm fn-wm-scan-more-nil-items
  (implies (fn-wildmat-scan-morep (fn-wildmat-scan-pattern codepoints nil))
           (and (consp (fn-wildmat-scan-items
                        (fn-wildmat-scan-pattern codepoints nil)))
                (fn-wildmat-text-items-p
                 (fn-wildmat-scan-items
                  (fn-wildmat-scan-pattern codepoints nil)))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-scan-more-success-items
                            (items-rev nil)))
           :in-theory (enable fn-wildmat-scan-morep fn-wildmat-text-items-p))))

(defthm fn-wm-scan-end-nil-items-consp
  (implies (fn-wildmat-scan-endp (fn-wildmat-scan-pattern codepoints nil))
           (consp (fn-wildmat-scan-items
                   (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal" :use fn-wm-scan-end-nil-items))
  :rule-classes :forward-chaining)

(defthm fn-wm-scan-end-nil-items-valid
  (implies (fn-wildmat-scan-endp (fn-wildmat-scan-pattern codepoints nil))
           (fn-wildmat-text-items-p
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
           (fn-wildmat-text-items-p
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

; -----------------------------------------------------------------------------
; The RFC 3977 section 4.1 profile, preserved (decision D19)
;
; The scanner above collects the header-value item set, so the shape theorem
; it feeds carries that set.  This section says what `fn-wildmat-parse' --- the
; newsgroup-name entry, the one `newsgroup-name = 1*wildmat-exact' reads ---
; still produces: patterns every one of whose items is a section 4.1
; `<wildmat-item>'.  That is the statement this book had before D19, and it is
; recovered here rather than weakened.

(defthm fn-wm-rfc3977-codepointsp-cdr
  (implies (fn-wildmat-rfc3977-codepointsp codepoints)
           (fn-wildmat-rfc3977-codepointsp (cdr codepoints)))
  :hints (("Goal" :in-theory (enable fn-wildmat-rfc3977-codepointsp))))

; The suffix the scanner leaves after a separating comma is a suffix of its
; input, so the section 4.1 restriction travels with it.
(defthm fn-wm-scan-rest-rfc3977
  (implies (and (fn-wildmat-rfc3977-codepointsp codepoints)
                (fn-wildmat-scan-morep
                 (fn-wildmat-scan-pattern codepoints items-rev)))
           (fn-wildmat-rfc3977-codepointsp
            (fn-wildmat-scan-rest
             (fn-wildmat-scan-pattern codepoints items-rev))))
  :hints (("Goal"
           :induct (fn-wildmat-scan-pattern codepoints items-rev)
           :in-theory (enable fn-wildmat-scan-pattern
                               fn-wildmat-scan-morep
                               fn-wildmat-scan-rest
                               fn-wildmat-rfc3977-codepointsp))))

; Every item the scanner collects is a code point of its input, so under the
; section 4.1 restriction every collected item is a section 4.1 item.
(defthm fn-wm-scan-end-rfc3977-items
  (implies (and (fn-wildmat-items-p items-rev)
                (fn-wildmat-rfc3977-codepointsp codepoints)
                (fn-wildmat-scan-endp
                 (fn-wildmat-scan-pattern codepoints items-rev)))
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints items-rev))))
  :hints (("Goal"
           :induct (fn-wildmat-scan-pattern codepoints items-rev)
           :in-theory (enable fn-wildmat-scan-pattern
                               fn-wildmat-scan-endp
                               fn-wildmat-scan-items
                               fn-wildmat-items-p
                               fn-wildmat-rfc3977-codepointsp
                               fn-wildmat-rfc3977-codepointp))))

(defthm fn-wm-scan-more-rfc3977-items
  (implies (and (fn-wildmat-items-p items-rev)
                (fn-wildmat-rfc3977-codepointsp codepoints)
                (fn-wildmat-scan-morep
                 (fn-wildmat-scan-pattern codepoints items-rev)))
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints items-rev))))
  :hints (("Goal"
           :induct (fn-wildmat-scan-pattern codepoints items-rev)
           :in-theory (enable fn-wildmat-scan-pattern
                               fn-wildmat-scan-morep
                               fn-wildmat-scan-items
                               fn-wildmat-items-p
                               fn-wildmat-rfc3977-codepointsp
                               fn-wildmat-rfc3977-codepointp))))

(defthm fn-wm-scan-nil-end-rfc3977-items
  (implies (and (fn-wildmat-rfc3977-codepointsp codepoints)
                (fn-wildmat-scan-endp
                 (fn-wildmat-scan-pattern codepoints nil)))
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal" :use ((:instance fn-wm-scan-end-rfc3977-items
                                   (items-rev nil)))
           :in-theory (enable fn-wildmat-items-p)))
  :rule-classes :forward-chaining)

(defthm fn-wm-scan-nil-more-rfc3977-items
  (implies (and (fn-wildmat-rfc3977-codepointsp codepoints)
                (fn-wildmat-scan-morep
                 (fn-wildmat-scan-pattern codepoints nil)))
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal" :use ((:instance fn-wm-scan-more-rfc3977-items
                                   (items-rev nil)))
           :in-theory (enable fn-wildmat-items-p)))
  :rule-classes :forward-chaining)

(defthm fn-wm-parse-one-rfc3977-pattern-listp
  (implies (and (fn-wildmat-rfc3977-codepointsp codepoints)
                (fn-wildmat-result-okp
                 (fn-wildmat-parse-one codepoints positivep fuel)))
           (fn-wildmat-rfc3977-pattern-listp
            (fn-wildmat-result-value
             (fn-wildmat-parse-one codepoints positivep fuel))))
  ; Cited by `:use' below.  As a :REWRITE it would conclude a recognizer
  ; call and rewrite away the very hypothesis the `:use' supplies.
  :rule-classes nil
  :hints (("Goal"
           :induct (fn-wm-parse-one-induct codepoints positivep fuel)
           ; The scanner stays CLOSED here.  Opened, every fact about it
           ; arrives as `(cadr (fn-wildmat-scan-pattern ...))' and the
           ; forward-chaining shape rules -- which conclude about
           ; `fn-wildmat-scan-items' -- stop matching at the leaves; that is
           ; what made the sibling theorem above need twelve subgoal hints.
           :in-theory (e/d (fn-wildmat-parse-one
                               fn-wildmat-result-okp
                               fn-wildmat-result-value
                               fn-wm-scan-end-nil-items-consp
                               fn-wm-scan-end-nil-items-valid
                               fn-wm-scan-more-nil-items-consp
                               fn-wm-scan-more-nil-items-valid
                               fn-wm-scan-nil-end-rfc3977-items
                               fn-wm-scan-nil-more-rfc3977-items
                               fn-wm-scan-more-excludes-end
                               fn-wm-scan-rest-rfc3977
                               fn-wm-rfc3977-codepointsp-cdr
                               fn-wildmat-rfc3977-pattern-listp
                               fn-wildmat-rfc3977-patternp
                               fn-wildmat-patternp
                               fn-wildmat-make-pattern)
                           (fn-wildmat-scan-endp
                            fn-wildmat-scan-morep
                            fn-wildmat-scan-pattern
                            fn-wildmat-scan-items
                            fn-wildmat-scan-rest)))))

(defthm fn-wildmat-parse-yields-rfc3977-patterns
  (implies (fn-wildmat-result-okp (fn-wildmat-parse octets))
           (and (consp (fn-wildmat-result-value (fn-wildmat-parse octets)))
                (fn-wildmat-rfc3977-pattern-listp
                 (fn-wildmat-result-value (fn-wildmat-parse octets)))))
  :hints (("Goal"
           :use ((:instance fn-wm-parse-one-rfc3977-pattern-listp
                            (codepoints
                             (fn-wildmat-result-value
                              (fn-wildmat-decode octets)))
                            (positivep t)
                            (fuel *fn-wildmat-max-octets*))
                 (:instance fn-wildmat-successful-parse-parsedp))
           ; `fn-wildmat-parse' is opened here, so the sibling that supplies
           ; the record shape cannot fire as a rewrite and is cited instead;
           ; it is disabled in the same hint so the citation is the only way
           ; it enters (board, w11/owner-config).
           :in-theory (e/d (fn-wildmat-parse
                             fn-wildmat-parse-codepoints
                             fn-wildmat-result-okp
                             fn-wildmat-result-value
                             fn-wildmat-parsedp)
                           (fn-wildmat-parse-one
                            fn-wildmat-successful-parse-parsedp)))))
