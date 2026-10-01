; Supplied descriptor/observation component teeth, never an issued grant.
(in-package "ACL2")
(include-book "../../books/bpsec-primitive-plan")

(defconst *fn-bpspt-bib*
  (fn-bps-op-make :verify-bib '(:bps-ref 1 2) '(:bps-ref 10 3)
                 '(:bps-ref 20 4) '(:bps-ref 30 5) 7 1 1
                 '(:bps-bib-params 5 7 nil) '(:bps-ref 50 6)
                 '(:bytes-span 40 200 32)))
(defconst *fn-bpspt-bcb*
  (fn-bps-op-make :decrypt-bcb '(:bps-ref 2 2) '(:bps-ref 10 3)
                 '(:bps-ref 20 4) '(:bps-ref 31 5) 8 1 2
                 '(:bps-bcb-params 3 7 (:bytes-span 40 300 12) nil :separate-tag)
                 '(:bps-ref 51 6) '(:bytes-span 40 400 16)))
(defconst *fn-bpspt-tag* (make-list 32 :initial-element 42))

; Complete antecedent/conclusion for the sole matching/byte keystone.
(assert-event
 (let* ((descriptor *fn-bpspt-bib*)
        (observation (list :bps-primitive-observation descriptor :hmac-bytes *fn-bpspt-tag*))
        (expected *fn-bpspt-tag*)
        (answer (fn-bps-primitive-answer descriptor observation expected)))
   (and (eq (fn-bps-field 1 answer) :verified)
        (fn-bps-opp descriptor) (fn-bps-fixed-recordp 4 observation)
        (eq (fn-bps-field 0 observation) :bps-primitive-observation)
        (equal (fn-bps-field 1 observation) descriptor)
        (eq (fn-bps-field 1 descriptor) :verify-bib)
        (eq (fn-bps-field 2 observation) :hmac-bytes)
        (equal (fn-bps-field 3 observation) expected)
        (fn-bps-exact-octetsp (fn-bps-hmac-width (fn-bps-field 1 (fn-bps-field 9 descriptor))) expected)
        (equal answer (list :bps-primitive-status :verified :ok
                            (list :bps-completion descriptor :verified nil :ok))))))

; Omit sole verified-status premise: all matching/shape/word/length fields
; retained, but unequal full bytes make the literal conclusion false.
(assert-event
 (let* ((descriptor *fn-bpspt-bib*) (expected *fn-bpspt-tag*)
        (actual (cons 43 (cdr expected)))
        (observation (list :bps-primitive-observation descriptor :hmac-bytes actual)))
   (and (fn-bps-opp descriptor) (fn-bps-fixed-recordp 4 observation)
        (eq (car observation) :bps-primitive-observation)
        (equal (fn-bps-field 1 observation) descriptor)
        (eq (fn-bps-field 1 descriptor) :verify-bib)
        (eq (fn-bps-field 2 observation) :hmac-bytes)
        (fn-bps-exact-octetsp 32 actual) (fn-bps-exact-octetsp 32 expected)
        (not (eq (fn-bps-field 1 (fn-bps-primitive-answer descriptor observation expected)) :verified))
        (not (equal actual expected))
        (equal (fn-bps-primitive-answer descriptor observation expected)
               (list :bps-primitive-status :failed :authentication-failed
                     (list :bps-completion descriptor :failed nil :authentication-failed))))))

(assert-event
 (and (equal (fn-bps-primitive-select *fn-bpspt-bib* 32)
             (list :bps-primitive-plan *fn-bpspt-bib* :sha256 32 32 0))
      (equal (fn-bps-primitive-select *fn-bpspt-bib* 16) '(:refused :key-width))
      (equal (fn-bps-primitive-select *fn-bpspt-bcb* 32)
             (list :bps-primitive-plan *fn-bpspt-bcb* :aes256-gcm 32 16 12))
      (equal (fn-bps-primitive-select *fn-bpspt-bcb* 16) '(:refused :key-width))))
(assert-event
 (and (equal (fn-bps-primitive-select nil 32) '(:refused :invalid-descriptor))
      (equal (fn-bps-primitive-select
              (fn-bps-op-make :verify-bib '(:bps-ref 1 2) '(:bps-ref 10 3)
               '(:bps-ref 20 4) '(:bps-ref 30 5) 7 1 99
               '(:bps-bib-params 5 7 nil) '(:bps-ref 50 6) '(:bytes-span 40 200 32)) 32)
             '(:unsupported :unsupported-profile))))

(assert-event
 (let* ((bib384 (fn-bps-op-make :verify-bib '(:bps-ref 1 2) '(:bps-ref 10 3)
                 '(:bps-ref 20 4) '(:bps-ref 30 5) 7 1 1
                 '(:bps-bib-params 6 7 nil) '(:bps-ref 50 6) '(:bytes-span 40 200 48)))
        (bib512 (fn-bps-op-make :verify-bib '(:bps-ref 1 2) '(:bps-ref 10 3)
                 '(:bps-ref 20 4) '(:bps-ref 30 5) 7 1 1
                 '(:bps-bib-params 7 7 nil) '(:bps-ref 50 6) '(:bytes-span 40 200 64)))
        (bcb128 (fn-bps-op-make :decrypt-bcb '(:bps-ref 2 2) '(:bps-ref 10 3)
                 '(:bps-ref 20 4) '(:bps-ref 31 5) 8 1 2
                 '(:bps-bcb-params 1 0 (:bytes-span 40 300 12) nil :tag-in-ciphertext)
                 '(:bps-ref 51 6) nil)))
   (and (fn-bps-opp bib384) (fn-bps-opp bib512) (fn-bps-opp bcb128)
        (equal (fn-bps-primitive-select bib384 48)
               (list :bps-primitive-plan bib384 :sha384 48 48 0))
        (equal (fn-bps-primitive-select bib512 64)
               (list :bps-primitive-plan bib512 :sha512 64 64 0))
        (equal (fn-bps-primitive-select bcb128 16)
               (list :bps-primitive-plan bcb128 :aes128-gcm 16 16 12))
        (equal (fn-bps-primitive-select bib384 16) '(:refused :key-width))
        (equal (fn-bps-primitive-select bib512 16) '(:refused :key-width)))))

; First GCM authentication cannot fabricate a verified BCB completion/ref.
(assert-event
 (let* ((descriptor *fn-bpspt-bcb*)
        (observation (list :bps-primitive-observation descriptor :authenticated nil))
        (answer (fn-bps-primitive-answer descriptor observation nil)))
   (and (fn-bps-opp descriptor) (eq (fn-bps-field 1 descriptor) :decrypt-bcb)
        (fn-bps-fixed-recordp 4 observation)
        (eq (car observation) :bps-primitive-observation)
        (equal (fn-bps-field 1 observation) descriptor)
        (eq (fn-bps-field 2 observation) :authenticated) (null (fn-bps-field 3 observation))
        (equal answer (list :bps-primitive-status :authenticated :pending-plaintext
                            (list :bps-authenticated descriptor (fn-bps-field 10 descriptor))))
        (not (fn-bps-completionp (fn-bps-field 3 answer))))))
(assert-event
 (let ((descriptor *fn-bpspt-bcb*))
   (and (equal (fn-bps-primitive-answer descriptor
                 (list :bps-primitive-observation descriptor :bad-tag nil) nil)
               (list :bps-primitive-status :failed :authentication-failed
                     (list :bps-completion descriptor :failed nil :authentication-failed)))
        (equal (fn-bps-primitive-answer descriptor
                 (list :bps-primitive-observation descriptor :primitive-unavailable nil) nil)
               (list :bps-primitive-status :uncertain :primitive-unavailable
                     (list :bps-completion descriptor :uncertain nil :primitive-unavailable)))
        (equal (fn-bps-primitive-answer descriptor
                 (list :bps-primitive-observation descriptor :unsupported nil) nil)
               (list :bps-primitive-status :unsupported :unsupported-profile
                     (list :bps-completion descriptor :unsupported nil :unsupported-profile))))))

; Input mutations: foreign descriptor, malformed HMAC bytes, wrong word.
(assert-event
 (and (eq (fn-bps-field 1 (fn-bps-primitive-answer *fn-bpspt-bib*
              (list :bps-primitive-observation *fn-bpspt-bcb* :hmac-bytes *fn-bpspt-tag*) *fn-bpspt-tag*)) :ignored)
      (eq (fn-bps-field 1 (fn-bps-primitive-answer *fn-bpspt-bib*
              (list :bps-primitive-observation *fn-bpspt-bib* :hmac-bytes (cdr *fn-bpspt-tag*)) *fn-bpspt-tag*)) :uncertain)
      (eq (fn-bps-field 1 (fn-bps-primitive-answer *fn-bpspt-bib*
              (list :bps-primitive-observation *fn-bpspt-bib* :authenticated nil) *fn-bpspt-tag*)) :uncertain)))

; Actual existing current matcher revokes even a matched supplied BIB result.
(assert-event
 (let* ((descriptor *fn-bpspt-bib*)
        (completion (fn-bps-field 3 (fn-bps-primitive-answer descriptor
                      (list :bps-primitive-observation descriptor :hmac-bytes *fn-bpspt-tag*) *fn-bpspt-tag*)))
        (operation (list :bps-operation :issued descriptor)))
   (and (fn-bps-completionp completion)
        (eq (fn-bps-field 1 (fn-bps-op-complete operation (fn-bps-op-current descriptor) completion)) :verified)
        (null (fn-bps-field 4 (fn-bps-op-complete operation nil completion)))
        (eq (fn-bps-field 2 (fn-bps-op-complete operation nil completion)) :stale-current))))

(assert-event
 (and (eq (symbol-class 'fn-bps-primitive-select (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-primitive-answer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-hmac-width (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-exact-octetsp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-tag-difference (w state)) :common-lisp-compliant)))

; Full-width traversal teeth: last-byte mismatch, maximum accumulated value,
; and a nonzero starting accumulator all preclude a zero difference.
(assert-event
 (let ((zeros (make-list 64 :initial-element 0))
       (maximum (make-list 64 :initial-element 255)))
   (and (fn-bps-exact-octetsp 64 zeros) (fn-bps-exact-octetsp 64 maximum)
        (equal (fn-bps-tag-difference 64 zeros zeros 0) 0)
        (equal (fn-bps-tag-difference 64 maximum zeros 0) 4161600)
        (equal (fn-bps-tag-difference 64 zeros maximum 0) 4161600)
        (equal (fn-bps-tag-difference 64 zeros zeros 1) 1)
        (equal (fn-bps-tag-difference 64 zeros (append (make-list 63 :initial-element 0) '(1)) 0) 1))))
