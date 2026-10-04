; Teeth for books/store-host-boundary.lisp (PRF-961, PRF-962): each keystone
; witnessed with its complete antecedent, each hypothesis removed once with
; the conclusion's failure shown, over the development profile the store's
; own codec decodes.
(in-package "ACL2")
(include-book "../../books/store-host-boundary")

(defconst *shbt-profile* (fn-bs-config-for-profile :development))
(defconst *shbt-t* (fn-bs-profile-max-transactions *shbt-profile*))
(defconst *shbt-ceiling* (fn-bs-profile-record-ceiling *shbt-profile*))

; The three entries are guard-verified.
(assert-event (eq (symbol-class 'fn-store-charge (w state)) :common-lisp-compliant))
(assert-event (eq (symbol-class 'fn-store-publication-admissibility (w state))
                  :common-lisp-compliant))
(assert-event (eq (symbol-class 'fn-store-profile-read-bound (w state))
                  :common-lisp-compliant))

; ---------------------------------------------------------------------------
; fn-store-publication-admissibility-admits-exactly-within-the-profile:
; the complete antecedent, then each conjunct of it removed.
(assert-event (and (fn-bs-profile-admittedp *shbt-profile*)
                   (natp *shbt-t*) (natp *shbt-ceiling*)
                   (< 0 *shbt-t*) (< 0 *shbt-ceiling*)))
(assert-event (equal (fn-store-publication-admissibility *shbt-profile* 0 0)
                     :admissible))
(assert-event (equal (fn-store-publication-admissibility
                      *shbt-profile* (1- *shbt-t*) *shbt-ceiling*)
                     :admissible))
; committed count at T
(assert-event (equal (fn-store-publication-admissibility *shbt-profile* *shbt-t* 0)
                     :refused))
; payload one past the ceiling
(assert-event (equal (fn-store-publication-admissibility
                      *shbt-profile* 0 (1+ *shbt-ceiling*))
                     :refused))
; not a natural
(assert-event (equal (fn-store-publication-admissibility *shbt-profile* -1 0)
                     :refused))
(assert-event (equal (fn-store-publication-admissibility *shbt-profile* 0 nil)
                     :refused))
; no admitted profile
(assert-event (not (fn-bs-profile-admittedp nil)))
(assert-event (equal (fn-store-publication-admissibility nil 0 0) :refused))

; fn-store-profile-read-bound-covers-every-admitted-publication: the bound
; holds the overhead plus the largest admitted payload, and one more octet
; is past it.
(assert-event (equal (fn-store-profile-read-bound *shbt-profile*)
                     (+ *fn-frame-overhead-octets* *shbt-ceiling*)))
(assert-event (<= (+ *fn-frame-overhead-octets* *shbt-ceiling*)
                  (fn-store-profile-read-bound *shbt-profile*)))
(assert-event (< (fn-store-profile-read-bound *shbt-profile*)
                 (+ *fn-frame-overhead-octets* (1+ *shbt-ceiling*))))
; an invalid profile: the overhead alone
(assert-event (equal (fn-store-profile-read-bound nil) *fn-frame-overhead-octets*))

; ---------------------------------------------------------------------------
; fn-store-charge-is-positive-exactly-for-a-length-and-is-the-receipt-charge
(assert-event (equal (fn-store-charge 0) 1))
(assert-event (equal (fn-store-charge 4096) (fn-charge-for-payload 4096)))
(assert-event (posp (fn-store-charge 100000)))
(assert-event (equal (fn-store-charge nil) 0))
(assert-event (equal (fn-store-charge -1) 0))
(assert-event (equal (fn-store-charge 1/2) 0))
(defconst *shbt-article*
  (fn-ct-make-article '(60 97 62) '(1 2 3) '(104 101 108 108 111) nil))
(assert-event (equal (fn-store-charge (len (fn-ct-article-octets *shbt-article*)))
                     (fn-ct-charge *shbt-article*)))

; ---------------------------------------------------------------------------
; fn-spo-refusal-text-refuses-exactly-the-foreign-format
(assert-event (stringp (fn-spo-refusal-text '(:refused :store-format))))
(assert-event (null (fn-spo-refusal-text '(:refused :other))))
(assert-event (null (fn-spo-refusal-text '(:rejected))))
(assert-event (null (fn-spo-refusal-text (list :opened *shbt-profile*))))
; the open's own verdicts: a saved profile opens, no frame is rejected
(assert-event (null (fn-spo-refusal-text
                     (fn-spo-config-open
                      (fn-bs-config-frame-for-profile :development)))))
(assert-event (equal (fn-spo-config-open nil) '(:rejected)))
(assert-event (null (fn-spo-refusal-text (fn-spo-config-open nil))))

; fn-gen-refusal-text-refuses-exactly-a-refused-open
(assert-event (stringp (fn-gen-refusal-text '(:refused :genesis-damaged))))
(assert-event (stringp (fn-gen-refusal-text '(:refused :genesis-format))))
(assert-event (stringp (fn-gen-refusal-text '(:refused :schema-digest))))
(assert-event (stringp (fn-gen-refusal-text '(:refused :profile-digest))))
(assert-event (null (fn-gen-refusal-text '(:refused :other))))
(assert-event (null (fn-gen-refusal-text '(:genesis nil nil))))
; the open's own verdict for no octets is the damaged refusal, with its line
(assert-event (equal (fn-gen-open nil *shbt-profile*) '(:refused :genesis-damaged)))
(assert-event (stringp (fn-gen-refusal-text (fn-gen-open nil *shbt-profile*))))

; fn-bs-profile-report-names-the-format-exactly-for-a-valid-profile
(assert-event (fn-bs-profile-validp *shbt-profile*))
(assert-event (alistp (fn-bs-profile-report *shbt-profile*)))
(assert-event (equal (cdr (assoc-equal "format" (fn-bs-profile-report *shbt-profile*)))
                     10))
(assert-event (not (fn-bs-profile-validp nil)))
(assert-event (equal (cdr (assoc-equal "format" (fn-bs-profile-report nil))) 0))

; fn-bs-config-frame-for-profile-is-what-the-open-opens: each preset's frame
; opens as that preset; a word that names no preset has no frame (init
; refuses it).
(assert-event (equal (fn-spo-config-open (fn-bs-config-frame-for-profile :development))
                     (list :opened (fn-bs-config-for-profile :development))))
(assert-event (equal (fn-spo-config-open (fn-bs-config-frame-for-profile :scale))
                     (list :opened (fn-bs-config-for-profile :scale))))
(assert-event (equal (fn-spo-config-open (fn-bs-config-frame-for-profile :default))
                     (list :opened (fn-bs-config-for-profile :default))))
(assert-event (null (fn-bs-config-frame-for-profile :no-such-preset)))
(assert-event (equal (car (fn-bs-profile-init-verdict :no-such-preset)) :refused))

; fn-bs-profile-logp-holds-exactly-for-a-valid-profile
(assert-event (and (fn-bs-profile-validp *shbt-profile*) (fn-bs-profile-logp *shbt-profile*)))
(assert-event (and (not (fn-bs-profile-validp nil)) (not (fn-bs-profile-logp nil))))
(assert-event (and (not (fn-bs-profile-validp '(1 2 3))) (not (fn-bs-profile-logp '(1 2 3)))))

; fn-store-charge-of-profile-article-is-representable (lane caps, D27):
; witness at the development profile's largest article; the hypothesis
; removed (a length past every profile's A, the codec ceiling) and the
; conclusion's failure shown far past it.
(assert-event
 (let ((a (fn-bs-profile-max-article-octets *shbt-profile*)))
   (and (fn-bs-profile-admittedp *shbt-profile*)
        (posp (fn-store-charge a))
        (fn-record-uint32p (fn-store-charge a)))))
(assert-event (fn-record-uint32p (fn-store-charge *fn-record-max-payload*)))
(assert-event
 (not (fn-record-uint32p (fn-store-charge (* 4096 (+ 1 *fn-cbor-max-uint*))))))
(assert-event (equal (fn-store-charge -1) 0))
