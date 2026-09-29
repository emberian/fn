; Teeth for books/article-buffer.lisp: the received article parsed from the
; octet buffer (D27 boundary 9, PRF-935).
;
; 1. The host's entries are guard-verified with guard T.
; 2. KEYSTONE fn-ars-parse-under-is-article-parse-under, positive witness:
;    a two-field article with a body in the live buffer parses to the
;    reference parse with its body located (offset 28), and the located
;    suffix is the reference's body (fn-ars-body-is-located).  Every error
;    arm agrees too: a bare LF, a missing separator, a line past 998
;    octets, the header-lines limit.
; 3. Hypothesis removal: a cell that is not an octet (300).  The retained
;    antecedent is none; the omitted one, fn-octets-p, fails; and the
;    conclusion fails: the reference refuses (:error :invalid-header) where
;    the twin, which cannot see a non-octet, parses on.  A corrupted-value
;    witness: no live buffer holds it.
; 4. The consumers: over the same article the gate, the filing plan, the
;    carrier form and the current plan answer what their references answer
;    (the -is-reference theorems' positive witnesses).

(in-package "ACL2")
(include-book "../../books/article-buffer")

(assert-event
 (and (eq (symbol-class 'fn-ars-parse-under (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ars-lb-ocfg-gate (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ars-filing-plan (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ars-carrier-form (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ars-current-plan (w state)) :common-lisp-compliant)))

(defun arbt-octets (s) (fn-record-string-octets s))

; "From: a@b\r\nNewsgroups: g\r\n\r\nbody line\r\n": the body at offset 28
; ("From: a@b" and CRLF, 11; "Newsgroups: g" and CRLF, 15; the separator, 2).
(defconst *arbt-article*
  (append (arbt-octets "From: a@b") '(13 10)
          (arbt-octets "Newsgroups: g") '(13 10)
          '(13 10)
          (arbt-octets "body line") '(13 10)))

(defconst *arbt-body* (append (arbt-octets "body line") '(13 10)))

; 2. The positive witness, in the live buffer.
(assert-event
 (let* ((fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list *arbt-article* fn-octets))
        (twin (fn-ars-parse-under *fn-article-default-limits* fn-octets))
        (ref (fn-article-parse-under *arbt-article* *fn-article-default-limits*)))
   (mv (and (fn-article-result-okp twin)
            (fn-article-result-okp ref)
            (equal twin (fn-ars-of ref (len *arbt-article*)))
            (equal (fn-article-body (fn-article-result-article twin)) 28)
            (equal (fn-article-body (fn-article-result-article ref)) *arbt-body*)
            (equal (nthcdr 28 *arbt-article*) *arbt-body*)
            (equal (fn-article-fields (fn-article-result-article twin))
                   (fn-article-fields (fn-article-result-article ref))))
       fn-octets))
 :stobjs-out '(nil fn-octets))

; The error arms, each in the live buffer against the reference.
(defun arbt-agreesp (xs limits fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-list xs fn-octets))
         (twin (fn-ars-parse-under limits fn-octets))
         (ref (fn-article-parse-under xs limits)))
    (mv (and (equal twin (fn-ars-of ref (len xs)))
             (not (fn-article-result-okp ref)))
        fn-octets)))

(assert-event
 (mv-let (a fn-octets) (arbt-agreesp (append (arbt-octets "From: a") '(10)) *fn-article-default-limits* fn-octets)
   (mv-let (b fn-octets) (arbt-agreesp (arbt-octets "From: a") *fn-article-default-limits* fn-octets)
     (mv-let (c fn-octets) (arbt-agreesp (append (arbt-octets "X: ") (make-list 999 :initial-element 97) '(13 10 13 10))
                                         *fn-article-default-limits* fn-octets)
       (mv-let (d fn-octets) (arbt-agreesp *arbt-article* (fn-article-limits 64 1 16384) fn-octets)
         (mv (and a b c d) fn-octets)))))
 :stobjs-out '(nil fn-octets))

; 3. Hypothesis removal: the omitted antecedent fails and the conclusion
; fails, on the logical definitions (no live buffer holds 300).
(defconst *arbt-bad* (append '(300) (cdr *arbt-article*)))

(defthm arbt-hypothesis-removal-witness
  (and (not (fn-octets-p *arbt-bad*))
       (equal (fn-article-parse-under *arbt-bad* *fn-article-default-limits*)
              '(:error :invalid-header))
       (not (equal (fn-ars-parse-under *fn-article-default-limits* *arbt-bad*)
                   (fn-ars-of (fn-article-parse-under *arbt-bad* *fn-article-default-limits*)
                              (len *arbt-bad*)))))
  :rule-classes nil)

; 4. The consumers over the article in the live buffer.
(assert-event
 (let* ((fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list *arbt-article* fn-octets)))
   (mv (and (equal (fn-ars-carrier-kind fn-octets) :absent)
            (equal (fn-ars-carrier-form fn-octets) (fn-pa-carrier-form *arbt-article*))
            (equal (fn-ars-carrier-form fn-octets) :absent)
            (equal (fn-ars-filing-plan '((103)) '("g") fn-octets)
                   (fn-pa-filing-plan *arbt-article* '((103)) '("g")))
            (equal (fn-ars-filing-plan '((103)) '("g") fn-octets) '(:file ((103))))
            (equal (fn-ars-current-plan nil nil nil fn-octets)
                   (fn-pa-current-plan *arbt-article* nil nil nil))
            ; The gate: a bound login without a carrier is refused by name;
            ; an unbound one passes without reading the article.
            (equal (fn-ars-lb-gate '(97) '(((97) . (1 2 3))) t fn-octets)
                   (fn-lb-gate *arbt-article* '(97) '(((97) . (1 2 3))) t))
            (equal (fn-ars-lb-gate '(97) '(((97) . (1 2 3))) t fn-octets)
                   '(:refused :login-unsigned (97)))
            (equal (fn-ars-lb-gate '(97) nil t fn-octets) '(:pass (97) nil)))
       fn-octets))
 :stobjs-out '(nil fn-octets))
