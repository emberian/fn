; fn: the header limits are the operator's, and the parser admits exactly
; up to them (lane header-limits-profile, 2026-09-27; D27; PRF-230, STO-030).
;
; `fn-article-parse-under OCTETS LIMITS' (books/article) is the admission
; parser; LIMITS = (FIELDS LINES OCTETS) comes from the store profile's
; fields 15 to 17 (books/byte-store-frame).  This book states what it
; decides, over a census of the input's header taken by the parser's own
; line scanner (`fn-article-header-census': the fields, the physical lines
; and the octets, CRLFs included, before the blank line):
;
;   `fn-article-parse-under-admits-exactly-the-limits' (the keystone): for
;   any limits WIDER under which the input parses, the parse under LIMITS
;   is that same article when the census is within LIMITS, and otherwise a
;   refusal whose code is one of the three limit names.
;
; Its three uses, each by instance: a parse that succeeds has a census
; within its limits (`fn-article-parse-under-within-its-limits'); raising a
; limit never changes an admitted article
; (`fn-article-parse-under-raised-limits-agree': profile evolution and
; representation agree, and a store's articles reparse identically under
; any wider profile); and the default parser is the default limits'
; instance (`fn-article-parse', definitionally).
;
; Host: the injection decision `fn-inj-decide' (books/injection) refuses by
; `fn-article-census-refusal' against `fn-inj-config-header-limits' of the
; configuration the host installs from the opened profile
; (host/owner-host.lisp `fn-owner-served-post-bound' ->
; `fn-bs-profile-header-limits'); by the keystone that is exactly the parse
; under the profile's limits (`fn-article-census-refusal-is-the-parse').

(in-package "ACL2")
(include-book "article-properties")

(defthm fn-ahl-next-line-shortens
  (implies (fn-article-line-okp (fn-article-next-line octets))
           (< (len (fn-article-line-rest (fn-article-next-line octets)))
              (len octets)))
  :hints (("Goal"
           :use ((:instance fn-article-line-scan-partitions-input
                  (line-rev nil) (left *fn-article-max-line-octets*))
                 (:instance fn-ap-length-append
                  (left (fn-article-line-value
                      (fn-article-next-line-aux
                       octets nil *fn-article-max-line-octets*)))
                  (right (append '(13 10)
                             (fn-article-line-rest
                              (fn-article-next-line-aux
                               octets nil *fn-article-max-line-octets*))))))
           :in-theory (e/d (fn-article-next-line)
                           (fn-article-next-line-aux fn-ap-length-append))))
  :rule-classes :linear)

;; The input's header census, read by `fn-article-next-line' over the lines
;; before the first empty one: its fields (lines not starting with WSP),
;; its physical lines, and its octets (each line and its CRLF).
(defmacro fn-ahl-census-step (name each)
  `(defun ,name (octets)
     (declare (xargs :measure (len octets) :guard t :verify-guards nil
                     :hints (("Goal" :use ((:instance fn-ahl-next-line-shortens))
                              :in-theory (disable fn-article-next-line
                                                  fn-ahl-next-line-shortens)))))
     (let ((next (fn-article-next-line octets)))
       (if (or (not (fn-article-line-okp next))
               (null (fn-article-line-value next)))
           0
         (+ (let ((line (fn-article-line-value next))) (declare (ignorable line)) ,each)
            (,name (fn-article-line-rest next)))))))

(fn-ahl-census-step fn-article-header-field-count
                    (if (fn-article-wspp (car line)) 0 1))
(fn-ahl-census-step fn-article-header-line-count 1)
(fn-ahl-census-step fn-article-header-octet-count (+ 2 (len line)))

(defun fn-article-header-census (octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-article-header-field-count octets)
        (fn-article-header-line-count octets)
        (fn-article-header-octet-count octets)))

(defthm fn-ahl-no-lines-no-fields-no-octets
  (implies (equal (fn-article-header-line-count octets) 0)
           (and (equal (fn-article-header-field-count octets) 0)
                (equal (fn-article-header-octet-count octets) 0)))
  :hints (("Goal" :expand ((fn-article-header-line-count octets)
                           (fn-article-header-field-count octets)
                           (fn-article-header-octet-count octets))
           :in-theory (disable fn-article-next-line))))

(defun fn-article-census-fields (c) (declare (xargs :guard t))
  (nfix (if (consp c) (car c) 0)))
(defun fn-article-census-lines (c) (declare (xargs :guard t))
  (nfix (if (and (consp c) (consp (cdr c))) (cadr c) 0)))
(defun fn-article-census-octets (c) (declare (xargs :guard t))
  (nfix (if (and (consp c) (consp (cdr c)) (consp (cddr c))) (caddr c) 0)))

(defun fn-article-census-within (c limits)
  (declare (xargs :guard t))
  (and (<= (fn-article-census-fields c) (fn-article-limit-fields limits))
       (<= (fn-article-census-lines c) (fn-article-limit-lines limits))
       (<= (fn-article-census-octets c) (fn-article-limit-octets limits))))

; The induction: the parse's own recursion, carried under two line fuels.
(defun fn-ahl-ind (octets nl nw hb nf fr cur hr)
  (declare (xargs :measure (nfix nw)))
  (if (zp nw)
      (list octets nl hb nf fr cur hr)
    (let ((next (fn-article-next-line octets)))
      (if (not (fn-article-line-okp next))
          nil
        (let ((line (fn-article-line-value next))
              (rest (fn-article-line-rest next)))
          (if (null line)
              nil
            (if (fn-article-wspp (car line))
                (fn-ahl-ind rest (1- nl) (1- nw) (+ hb (len line) 2) nf fr
                            (fn-article-add-fold cur line)
                            (fn-article-header-rev-add-line hr line))
              (fn-ahl-ind rest (1- nl) (1- nw) (+ hb (len line) 2)
                          (if cur (+ 1 (nfix nf)) nf)
                          (if cur (cons cur fr) fr)
                          (fn-article-line-value (fn-article-new-field line))
                          (fn-article-header-rev-add-line hr line)))))))))

;; The census from a parse state fits LIMITS: lines below the fuel NL, the
;; octets so far plus the census within the octet limit, and the fields so
;; far plus the census within the field limit (each vacuous when the census
;; has no line or no field, where the parse makes no such comparison).
(defun fn-ahl-fits (octets nl hb nf cur limits)
  (declare (xargs :guard t :verify-guards nil))
  (and (< (fn-article-header-line-count octets) (nfix nl))
       (or (zp (fn-article-header-line-count octets))
           (<= (+ (nfix hb) (fn-article-header-octet-count octets))
               (fn-article-limit-octets limits)))
       (or (zp (fn-article-header-field-count octets))
           (<= (+ (nfix nf) (if cur 1 0) (fn-article-header-field-count octets))
               (fn-article-limit-fields limits)))))

(defmacro fn-ahl-theory ()
  '(disable fn-article-next-line fn-article-next-line-aux
            fn-article-new-field fn-article-add-fold
            fn-article-finish-fields fn-article-body-crlfp
            fn-article-header-rev-add-line
            fn-article-line-value fn-article-line-rest
            fn-article-fold-linep fn-article-limit-fields
            fn-article-limit-octets))

;; Two runs that both succeed from one state agree.
(defthm fn-ahl-two-successes-agree
  (implies
   (and (fn-article-result-okp
         (fn-article-parse-lines octets wider nw hb nf fr cur hr))
        (fn-article-result-okp
         (fn-article-parse-lines octets limits nl hb nf fr cur hr)))
   (equal (fn-article-parse-lines octets limits nl hb nf fr cur hr)
          (fn-article-parse-lines octets wider nw hb nf fr cur hr)))
  :rule-classes nil
  :hints (("Goal"
           :induct (fn-ahl-ind octets nl nw hb nf fr cur hr)
           :expand ((fn-article-parse-lines octets wider nw hb nf fr cur hr)
                    (fn-article-parse-lines octets limits nl hb nf fr cur hr))
           :in-theory (fn-ahl-theory))))

;; Under any limits, the parse of an input some limits admit either
;; succeeds or refuses by a limit's name.
(defthm fn-ahl-narrower-refuses-by-name
  (implies
   (fn-article-result-okp
    (fn-article-parse-lines octets wider nw hb nf fr cur hr))
   (or (fn-article-result-okp
        (fn-article-parse-lines octets limits nl hb nf fr cur hr))
       (and (equal (car (fn-article-parse-lines octets limits nl hb nf fr cur hr))
                   :error)
            (fn-article-limit-reasonp
             (cadr (fn-article-parse-lines octets limits nl hb nf fr cur hr))))))
  :rule-classes nil
  :hints (("Goal"
           :induct (fn-ahl-ind octets nl nw hb nf fr cur hr)
           :expand ((fn-article-parse-lines octets wider nw hb nf fr cur hr)
                    (fn-article-parse-lines octets limits nl hb nf fr cur hr))
           :in-theory (fn-ahl-theory))))

;; A success fits its own limits.
(defthm fn-ahl-success-fits
  (implies
   (and (fn-article-result-okp
         (fn-article-parse-lines octets limits nl hb nf fr cur hr))
        (natp hb))
   (fn-ahl-fits octets nl hb nf cur limits))
  :rule-classes nil
  :hints (("Goal"
           :induct (fn-article-parse-lines octets limits nl hb nf fr cur hr)
           :expand ((fn-article-parse-lines octets limits nl hb nf fr cur hr)
                    (fn-article-header-line-count octets)
                    (fn-article-header-field-count octets)
                    (fn-article-header-octet-count octets))
           :in-theory (fn-ahl-theory))))

;; What fits is admitted, given that some limits admit the input.
(defthm fn-ahl-fits-succeeds
  (implies
   (and (fn-article-result-okp
         (fn-article-parse-lines octets wider nw hb nf fr cur hr))
        (fn-ahl-fits octets nl hb nf cur limits)
        (natp hb))
   (fn-article-result-okp
    (fn-article-parse-lines octets limits nl hb nf fr cur hr)))
  :rule-classes nil
  :hints (("Goal"
           :induct (fn-ahl-ind octets nl nw hb nf fr cur hr)
           :expand ((fn-article-parse-lines octets wider nw hb nf fr cur hr)
                    (fn-article-parse-lines octets limits nl hb nf fr cur hr)
                    (fn-article-header-line-count octets)
                    (fn-article-header-field-count octets)
                    (fn-article-header-octet-count octets))
           :in-theory (fn-ahl-theory))))

(defthm fn-ahl-fits-at-entry-is-within
  (equal (fn-ahl-fits octets (1+ (fn-article-limit-lines limits)) 0 0 nil limits)
         (fn-article-census-within (fn-article-header-census octets) limits))
  :hints (("Goal" :in-theory (disable fn-article-limit-lines))))

;; THE KEYSTONE.  Given any limits under which the input parses, the parse
;; under LIMITS is that same article exactly when the input's header census
;; is within LIMITS, and otherwise a refusal by one of the three limit
;; names (`:header-fields-limit', `:header-lines-limit',
;; `:header-octets-limit').
(defthm fn-article-parse-under-admits-exactly-the-limits
  (implies (fn-article-result-okp (fn-article-parse-under octets wider))
           (if (fn-article-census-within (fn-article-header-census octets)
                                         limits)
               (equal (fn-article-parse-under octets limits)
                      (fn-article-parse-under octets wider))
             (and (equal (car (fn-article-parse-under octets limits)) :error)
                  (fn-article-limit-reasonp
                   (cadr (fn-article-parse-under octets limits))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-ahl-two-successes-agree
                  (nw (1+ (fn-article-limit-lines wider)))
                  (nl (1+ (fn-article-limit-lines limits)))
                  (hb 0) (nf 0) (fr nil) (cur nil) (hr nil))
                 (:instance fn-ahl-narrower-refuses-by-name
                  (nw (1+ (fn-article-limit-lines wider)))
                  (nl (1+ (fn-article-limit-lines limits)))
                  (hb 0) (nf 0) (fr nil) (cur nil) (hr nil))
                 (:instance fn-ahl-success-fits
                  (nl (1+ (fn-article-limit-lines limits)))
                  (hb 0) (nf 0) (fr nil) (cur nil) (hr nil))
                 (:instance fn-ahl-fits-succeeds
                  (nw (1+ (fn-article-limit-lines wider)))
                  (nl (1+ (fn-article-limit-lines limits)))
                  (hb 0) (nf 0) (fr nil) (cur nil) (hr nil)))
           :in-theory (e/d (fn-article-parse-under)
                           (fn-ahl-fits fn-article-census-within
                            fn-article-header-census
                            fn-article-parse-lines fn-article-limit-lines
                            fn-article-limit-reasonp)))))

;; A parse that succeeds has a header census within its limits.
(defthm fn-article-parse-under-within-its-limits
  (implies (fn-article-result-okp (fn-article-parse-under octets limits))
           (fn-article-census-within (fn-article-header-census octets) limits))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-article-parse-under-admits-exactly-the-limits
                  (wider limits)))
           :in-theory (disable fn-article-parse-under fn-article-census-within
                               fn-article-header-census))))

;; Raising the limits never changes an admitted article: the profile may
;; widen, and a store's articles reparse identically under any wider
;; profile (profile evolution and representation agree, D27).
(defthm fn-article-parse-under-raised-limits-agree
  (implies (and (fn-article-result-okp (fn-article-parse-under octets limits))
                (fn-article-limits-within limits wider))
           (equal (fn-article-parse-under octets wider)
                  (fn-article-parse-under octets limits)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-article-parse-under-within-its-limits
                 (:instance fn-article-parse-under-admits-exactly-the-limits
                  (wider limits) (limits wider)))
           :in-theory (e/d (fn-article-census-within fn-article-limits-within)
                           (fn-article-parse-under fn-article-header-census
                            fn-article-census-fields fn-article-census-lines
                            fn-article-census-octets fn-article-limit-fields
                            fn-article-limit-lines fn-article-limit-octets
                            fn-article-limit-reasonp fn-article-result-okp)))))

;; The reading parser is the ceiling limits' instance.
(defthm fn-article-parse-is-the-ceiling-limits-by-definition
  (equal (fn-article-parse octets)
         (fn-article-parse-under octets *fn-article-ceiling-limits*))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-article-parse))))

(verify-guards fn-article-header-field-count
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp))
           :in-theory (e/d (fn-article-line-okp)
                           (fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-line-count
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp))
           :in-theory (e/d (fn-article-line-okp)
                           (fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-octet-count
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp))
           :in-theory (e/d (fn-article-line-okp)
                           (fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-census)

;; The admission's refusal by the census: the first limit the census
;; passes, by name, in the order fields, lines, octets; NIL within.
(defun fn-article-census-refusal (c limits)
  (declare (xargs :guard t))
  (cond ((< (fn-article-limit-fields limits) (fn-article-census-fields c))
         :header-fields-limit)
        ((< (fn-article-limit-lines limits) (fn-article-census-lines c))
         :header-lines-limit)
        ((< (fn-article-limit-octets limits) (fn-article-census-octets c))
         :header-octets-limit)
        (t nil)))

;; KEYSTONE (the admission's subject).  For an input the reading parser
;; admits, the census refusal is NIL exactly when the parse under LIMITS
;; admits it (and then that parse is the reading parse), and otherwise a
;; limit's name while the parse under LIMITS refuses by a limit's name.
(defthm fn-article-census-refusal-is-the-parse
  (implies (fn-article-result-okp (fn-article-parse octets))
           (let ((refusal (fn-article-census-refusal
                           (fn-article-header-census octets) limits)))
             (if refusal
                 (and (fn-article-limit-reasonp refusal)
                      (not (fn-article-result-okp
                            (fn-article-parse-under octets limits)))
                      (fn-article-limit-reasonp
                       (cadr (fn-article-parse-under octets limits))))
               (equal (fn-article-parse-under octets limits)
                      (fn-article-parse octets)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-article-parse-under-admits-exactly-the-limits
                  (wider *fn-article-ceiling-limits*)))
           :in-theory (e/d (fn-article-parse fn-article-census-within
                            fn-article-census-refusal fn-article-result-okp)
                           (fn-article-parse-under fn-article-header-census
                            fn-article-census-fields fn-article-census-lines
                            fn-article-census-octets fn-article-limit-fields
                            fn-article-limit-lines fn-article-limit-octets)))))
