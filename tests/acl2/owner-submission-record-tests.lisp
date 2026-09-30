; Actual canonical seven-field constructors and the fields the queue carries.
; No ingress-authority, durable-acceptance, or whole-owner claim.
(in-package "ACL2")
(include-book "../../books/owner-submission-record")

(defconst *osrt-decision*
  '(:transit "peer" :ihave (60 97 62) (65 13 10)))
(defconst *osrt-sub*
  (fn-own-sub-make-author 3 11 nil *osrt-decision* '(97) '(1 2)
                          :native-source))
(defconst *osrt-packed* (fn-psub-pack-sub *osrt-sub*))
(defconst *osrt-unpacked* (fn-psub-unpack-sub *osrt-packed*))

; The complete unconditional constructor/context equations, with nonempty
; decision, login/account and context. The no-login path preserves context.
(assert-event
 (and (equal (fn-own-sub-source-context
              (fn-own-sub-make 3 11 nil *osrt-decision* :relay-v1)) :relay-v1)
      (equal (fn-own-sub-source-context *osrt-sub*) :native-source)
      (equal (fn-own-sub-source-context
              (fn-own-sub-make-author 3 11 nil *osrt-decision* nil '(1 2)
                                      :post-d25)) :post-d25)
      (fn-own-sub-shapep *osrt-sub*)
      (equal (len *osrt-sub*) 7)
      (consp (fn-own-sub-decision *osrt-sub*))))

; Every conjunct of fn-own-sub-fields-of-pack on the actual packed record.
(assert-event
 (and (equal (fn-own-sub-id *osrt-packed*) (fn-own-sub-id *osrt-sub*))
      (equal (fn-own-sub-version *osrt-packed*) (fn-own-sub-version *osrt-sub*))
      (equal (fn-own-sub-mark *osrt-packed*) (fn-own-sub-mark *osrt-sub*))
      (equal (fn-own-sub-login *osrt-packed*) (fn-own-sub-login *osrt-sub*))
      (equal (fn-own-sub-account *osrt-packed*) (fn-own-sub-account *osrt-sub*))
      (equal (fn-own-sub-source-context *osrt-packed*)
             (fn-own-sub-source-context *osrt-sub*))
      (equal (fn-own-sub-decision *osrt-packed*)
             (fn-psub-pack-decision (fn-own-sub-decision *osrt-sub*)))
      (equal (fn-own-sub-shapep *osrt-packed*) (fn-own-sub-shapep *osrt-sub*))
      (equal (consp *osrt-packed*) (consp *osrt-sub*))
      (not (equal *osrt-packed* *osrt-sub*))))

; Every conjunct of fn-own-sub-fields-of-unpack, plus exact roundtrip.
(assert-event
 (and (equal (fn-own-sub-id *osrt-unpacked*) (fn-own-sub-id *osrt-packed*))
      (equal (fn-own-sub-version *osrt-unpacked*) (fn-own-sub-version *osrt-packed*))
      (equal (fn-own-sub-mark *osrt-unpacked*) (fn-own-sub-mark *osrt-packed*))
      (equal (fn-own-sub-login *osrt-unpacked*) (fn-own-sub-login *osrt-packed*))
      (equal (fn-own-sub-account *osrt-unpacked*) (fn-own-sub-account *osrt-packed*))
      (equal (fn-own-sub-source-context *osrt-unpacked*)
             (fn-own-sub-source-context *osrt-packed*))
      (equal (fn-own-sub-decision *osrt-unpacked*)
             (fn-psub-unpack-decision (fn-own-sub-decision *osrt-packed*)))
      (equal (consp *osrt-unpacked*) (consp *osrt-packed*))
      (equal *osrt-unpacked* *osrt-sub*)))

; Mutation witness: erasing only field 6 leaves all earlier coordinates
; intact and a canonical shape, but destroys the full context conclusion.
(defconst *osrt-erased* (update-nth 6 nil *osrt-packed*))
(assert-event
 (and (fn-own-sub-shapep *osrt-erased*)
      (equal (take 6 *osrt-erased*) (take 6 *osrt-packed*))
      (not (equal (fn-own-sub-source-context *osrt-erased*)
                  (fn-own-sub-source-context *osrt-sub*)))
      (not (equal (fn-own-sub-source-context
                   (fn-psub-unpack-sub *osrt-erased*))
                  (fn-own-sub-source-context *osrt-sub*)))))

; Verify the actual world's executable classification for every moved entry.
(make-event
 (value
  (list 'assert-event
        (and
         (equal (getpropc 'fn-own-sub-shapep 'symbol-class nil (w state)) :common-lisp-compliant)
         (equal (getpropc 'fn-own-sub-id 'symbol-class nil (w state)) :common-lisp-compliant)
         (equal (getpropc 'fn-own-sub-version 'symbol-class nil (w state)) :common-lisp-compliant)
         (equal (getpropc 'fn-own-sub-mark 'symbol-class nil (w state)) :common-lisp-compliant)
         (equal (getpropc 'fn-own-sub-decision 'symbol-class nil (w state)) :common-lisp-compliant)
         (equal (getpropc 'fn-own-sub-source-context 'symbol-class nil (w state)) :common-lisp-compliant)
         (equal (getpropc 'fn-own-sub-make 'symbol-class nil (w state)) :common-lisp-compliant)
         (equal (getpropc 'fn-own-sub-login 'symbol-class nil (w state)) :common-lisp-compliant)
         (equal (getpropc 'fn-own-sub-account 'symbol-class nil (w state)) :common-lisp-compliant)
         (equal (getpropc 'fn-own-sub-make-author 'symbol-class nil (w state)) :common-lisp-compliant)))))
