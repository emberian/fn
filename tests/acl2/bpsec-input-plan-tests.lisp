; Canonical command metadata only; every reference here is explicitly unissued.
(in-package "ACL2")
(include-book "../../books/bpsec-input-plan")
(defconst *fn-bpsip-primary* '(:bp-primary-source (:bps-ref 9 1) 1 24 0 0 nil))
(defconst *fn-bpsip-target* '(:bp-canonical-source (:bps-ref 9 1) 24 33 1 1 255 0 (:bps-span (:bps-ref 9 1) 30 3) nil))
(defconst *fn-bpsip-security* '(:bp-canonical-source (:bps-ref 9 1) 33 50 11 7 128 0 (:bps-span (:bps-ref 9 1) 39 11) nil))
(defun fn-bpsip-descriptor (action scope tail)
 (declare (xargs :guard t))
 (fn-bps-op-make action '(:bps-ref 1 1) '(:bps-ref 2 1) '(:bps-ref 3 1) '(:bps-ref 4 1)
  7 1 (if (eq action :verify-bib) 1 2)
  (if (eq action :verify-bib) (list :bps-bib-params 5 scope nil)
   (list :bps-bcb-params 3 scope '(:bytes-span 9 0 12) nil
         (if tail :tag-in-ciphertext :separate-tag)))
  '(:bps-ref 5 1) (if (eq action :verify-bib) '(:bytes-span 9 256 32)
                       (if tail nil '(:bytes-span 9 256 16)))))
; Exact RFC9173 3.7 ordering and reserved extension flag mask.
(assert-event
 (let* ((d (fn-bpsip-descriptor :verify-bib 7 nil))
        (result (fn-bps-input-plan d *fn-bpsip-primary* *fn-bpsip-target* *fn-bpsip-security*)))
  (and (fn-bps-opp d)
       (equal result (list :planned (list :bps-input-plan d
        '((:bps-literal (7)) (:bps-span (:bps-ref 9 1) 1 23)
          (:bps-literal (1 1 23)) (:bps-literal (11 7 0))
          (:bps-literal (67)) (:bps-span (:bps-ref 9 1) 30 3)) nil nil))))))
; Primary target: direct canonical primary exactly once, no bstr framing and
; no duplicate optional primary/target header, even when scope bits are all1.
(assert-event
 (let ((d (fn-bps-op-make :verify-bib '(:bps-ref 1 1) '(:bps-ref 2 1) '(:bps-ref 3 1) '(:bps-ref 4 1)
          7 0 1 '(:bps-bib-params 5 7 nil) '(:bps-ref 5 1) '(:bytes-span 9 256 32))))
  (equal (fn-bps-input-plan d *fn-bpsip-primary* *fn-bpsip-primary* *fn-bpsip-security*)
   (list :planned (list :bps-input-plan d
    '((:bps-literal (7)) (:bps-literal (11 7 0)) (:bps-span (:bps-ref 9 1) 1 23)) nil nil)))))
; BCB AAD uses actual BCB header; ciphertext is raw target bytes.
(assert-event
 (let* ((d (fn-bpsip-descriptor :decrypt-bcb 7 nil))
        (s '(:bp-canonical-source (:bps-ref 9 1) 33 50 12 7 128 0 (:bps-span (:bps-ref 9 1) 39 11) nil)))
  (equal (fn-bps-input-plan d *fn-bpsip-primary* *fn-bpsip-target* s)
   (list :planned (list :bps-input-plan d
    '((:bps-literal (7)) (:bps-span (:bps-ref 9 1) 1 23)
      (:bps-literal (1 1 23)) (:bps-literal (12 7 0)))
    '(:bps-span (:bps-ref 9 1) 30 3) '(:bytes-span 9 256 16))))))
; Tail-tag extraction is metadata derivation only; no second pass grant.
(assert-event
 (let* ((d (fn-bpsip-descriptor :decrypt-bcb 0 t))
        (s '(:bp-canonical-source (:bps-ref 9 1) 50 67 12 7 0 0 (:bps-span (:bps-ref 9 1) 56 11) nil))
        (target '(:bp-canonical-source (:bps-ref 9 1) 24 49 1 1 0 0 (:bps-span (:bps-ref 9 1) 30 19) nil)))
  (and (equal (fn-bps-input-plan d *fn-bpsip-primary* target s)
        (list :planned (list :bps-input-plan d '((:bps-literal (0)))
          '(:bps-span (:bps-ref 9 1) 30 3) '(:bps-span (:bps-ref 9 1) 33 16))))
       (equal (fn-bps-input-plan d *fn-bpsip-primary* *fn-bpsip-target* s) '(:refused :short-ciphertext-tag)))))
; Captured source/number/mask/extent mutations: no guessed mapping.
(assert-event
 (let ((d (fn-bpsip-descriptor :verify-bib 0 nil)))
  (and (equal (fn-bps-input-plan d nil *fn-bpsip-target* *fn-bpsip-security*) '(:refused :invalid-source-metadata))
       (equal (fn-bps-input-plan d *fn-bpsip-primary* *fn-bpsip-target*
        '(:bp-canonical-source (:bps-ref 9 2) 33 50 11 7 0 0 (:bps-span (:bps-ref 9 2) 39 11) nil)) '(:refused :foreign-source-metadata))
       (equal (fn-bps-input-plan d *fn-bpsip-primary*
        '(:bp-canonical-source (:bps-ref 9 1) 24 33 1 2 0 0 (:bps-span (:bps-ref 9 1) 30 3) nil) *fn-bpsip-security*) '(:refused :foreign-target-metadata))
       (not (fn-bps-input-blockp '(:bp-canonical-source (:bps-ref 9 1) 24 33 1 1 0 0 (:bps-span (:bps-ref 9 1) 30 4) nil))))))
; Protocol uint64 extent, not an arbitrary stored-object ceiling.
(assert-event
 (let* ((d (fn-bpsip-descriptor :verify-bib 0 nil))
        (target '(:bp-canonical-source (:bps-ref 9 1) 24 1099511627816 1 1 0 0
                  (:bps-span (:bps-ref 9 1) 40 1099511627776) nil))
        (commands (fn-bps-field 2 (fn-bps-field 1 (fn-bps-input-plan d *fn-bpsip-primary* target *fn-bpsip-security*)))))
  (equal commands '((:bps-literal (0)) (:bps-literal (91 0 0 1 0 0 0 0 0))
                   (:bps-span (:bps-ref 9 1) 40 1099511627776)))))
(assert-event
 (and (eq (symbol-class 'fn-bps-input-spanp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-input-primaryp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-input-blockp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-input-primary-span (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-input-header (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-input-header-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-input-plan (w state)) :common-lisp-compliant)))

; Algorithm total limits: literal metadata checks, with no physical giant
; allocation or authenticated source claim. Each immediate boundary matters.
(assert-event
 (let* ((s '(:bp-canonical-source (:bps-ref 9 1) 33 50 12 7 0 0 (:bps-span (:bps-ref 9 1) 39 11) nil))
        (d (fn-bpsip-descriptor :decrypt-bcb 0 nil))
        (maximum '(:bp-canonical-source (:bps-ref 9 1) 24 68719476744 1 1 0 0 (:bps-span (:bps-ref 9 1) 40 68719476704) nil))
        (over '(:bp-canonical-source (:bps-ref 9 1) 24 68719476745 1 1 0 0 (:bps-span (:bps-ref 9 1) 40 68719476705) nil)))
  (and (fn-bps-opp d) (fn-bps-input-blockp maximum) (fn-bps-input-blockp over)
       (eq (car (fn-bps-input-plan d *fn-bpsip-primary* maximum s)) :planned)
       (equal (fn-bps-input-plan d *fn-bpsip-primary* over s) '(:refused :gcm-ciphertext-limit)))))
(assert-event
 (let* ((s '(:bp-canonical-source (:bps-ref 9 1) 33 50 12 7 0 0 (:bps-span (:bps-ref 9 1) 39 11) nil))
        (d (fn-bpsip-descriptor :decrypt-bcb 1 nil))
        (maximum '(:bp-primary-source (:bps-ref 9 1) 0 2305843009213693950 0 0 nil))
        (over '(:bp-primary-source (:bps-ref 9 1) 0 2305843009213693951 0 0 nil)))
  (and (fn-bps-input-primaryp maximum) (fn-bps-input-primaryp over)
       (eq (car (fn-bps-input-plan d maximum *fn-bpsip-target* s)) :planned)
       (equal (fn-bps-input-plan d over *fn-bpsip-target* s) '(:refused :gcm-aad-limit)))))
(assert-event
 (let* ((d (fn-bps-op-make :verify-bib '(:bps-ref 1 1) '(:bps-ref 2 1) '(:bps-ref 3 1) '(:bps-ref 4 1)
          7 0 1 '(:bps-bib-params 5 0 nil) '(:bps-ref 5 1) '(:bytes-span 9 256 32)))
        (maximum '(:bp-primary-source (:bps-ref 9 1) 0 2305843009213693886 0 0 nil))
        (over '(:bp-primary-source (:bps-ref 9 1) 0 2305843009213693887 0 0 nil)))
  (and (fn-bps-opp d) (fn-bps-input-primaryp maximum) (fn-bps-input-primaryp over)
       (eq (car (fn-bps-input-plan d maximum maximum *fn-bpsip-security*)) :planned)
       (equal (fn-bps-input-plan d over over *fn-bpsip-security*) '(:refused :sha256-input-limit)))))
