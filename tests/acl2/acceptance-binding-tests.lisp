; PRF-1108 representation teeth. These do not claim durable integration.
(in-package "ACL2")
(include-book "../../books/acceptance-binding")
(include-book "../../books/crypto-attach")

(defconst *abt-subject* (append *fn-ab-subject-head* (make-list 32 :initial-element 0)))
(defconst *abt-post* (fn-ab-make :post-d25 *abt-subject*))
(defconst *abt-relay* (fn-ab-make :relay-v1 *abt-subject*))
(defconst *abt-native* (fn-ab-make :native-source *abt-subject*))

(assert-event
 (and (eq (symbol-class 'fn-ab-encode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ab-decode (w state)) :common-lisp-compliant)))

; Profile coding's complete positive and sole-hypothesis removal.
(assert-event
 (and (fn-ab-profilep :relay-v1)
      (equal (fn-ab-code-profile (fn-ab-profile-code :relay-v1)) :relay-v1)
      (not (fn-ab-profilep :unknown))
      (not (equal (fn-ab-code-profile (fn-ab-profile-code :unknown)) :unknown))))

; Complete positive antecedent/conclusion for each literal codec theorem.
(assert-event
 (and (fn-ab-p *abt-post*) (fn-ab-p *abt-relay*) (fn-ab-p *abt-native*)
      (equal (fn-ab-decode (fn-ab-encode *abt-post*)) (list :ok *abt-post*))
      (equal (fn-ab-decode (fn-ab-encode *abt-relay*)) (list :ok *abt-relay*))
      (equal (fn-ab-decode (fn-ab-encode *abt-native*)) (list :ok *abt-native*))
      (equal (len (fn-ab-encode *abt-post*)) *fn-ab-octets*)
      (equal (car (fn-ab-decode (fn-ab-encode *abt-relay*))) :ok)
      (fn-ab-p (cadr (fn-ab-decode (fn-ab-encode *abt-relay*))))))

; Sole fn-ab-p hypothesis absent: nil is not a binding and neither the
; roundtrip nor fixed encoded length conclusion holds. No default profile.
(assert-event
 (and (not (fn-ab-p nil))
      (not (equal (fn-ab-decode (fn-ab-encode nil)) (list :ok nil)))
      (not (equal (len (fn-ab-encode nil)) *fn-ab-octets*))))

; Sole successful-decode hypothesis absent; its decoded value is no binding.
(assert-event
 (and (not (equal (car (fn-ab-decode nil)) :ok))
      (not (fn-ab-p (cadr (fn-ab-decode nil))))))

; Corrupt/current-format data: unknown profile, wrong magic, old digest
; algorithm, truncated typed identity, a trailing octet and an improper tail.
(assert-event
 (and (equal (fn-ab-decode nil) '(:error :invalid-binding))
      (equal (fn-ab-decode (update-nth 7 0 (fn-ab-encode *abt-post*)))
             '(:error :invalid-binding))
      (equal (fn-ab-decode (update-nth 6 48 (fn-ab-encode *abt-post*)))
             '(:error :invalid-binding))
      (equal (fn-ab-decode (update-nth 23 1 (fn-ab-encode *abt-post*)))
             '(:error :invalid-binding))
      (equal (fn-ab-decode (take 55 (fn-ab-encode *abt-post*)))
             '(:error :invalid-binding))
      (equal (fn-ab-decode (append (fn-ab-encode *abt-post*) '(0)))
             '(:error :invalid-binding))
      (equal (fn-ab-decode (append (fn-ab-encode *abt-post*) 7))
             '(:error :invalid-binding))))

; Generated commitments retain their received-byte meaning, independently of
; the profile. Removing the sole profile hypothesis really breaks the type.
(assert-event
 (and (fn-ab-profilep :relay-v1)
      (fn-ab-p (fn-ab-of-received :relay-v1 '(65)))
      (equal (fn-ab-received-subject (fn-ab-of-received :relay-v1 '(65)))
             (fn-id-subject-of-payload '(65)))
      (not (equal (fn-ab-received-subject (fn-ab-of-received :relay-v1 '(65)))
                  (fn-ab-received-subject (fn-ab-of-received :relay-v1 '(66)))))
      (not (fn-ab-profilep nil))
      (not (fn-ab-p (fn-ab-of-received nil '(65))))))
