(in-package "ACL2")
(include-book "../../books/hybrid-carrier")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(local (in-theory (enable fn-hybrid-carrier-vocabulary
                          fn-hybrid-signature-vocabulary)))

(defconst *hc-ed-key* (make-list 32 :initial-element 17))
(defconst *hc-ml-key* (make-list 1952 :initial-element 34))
(defconst *hc-ed-sig* (make-list 64 :initial-element 51))
(defconst *hc-ml-sig* (make-list 3309 :initial-element 68))
(defconst *hc-principal* (make-list 32 :initial-element 85))
(defconst *hc-keys* (list (cons :ed25519 *hc-ed-key*)
                          (cons :ml-dsa-65 *hc-ml-key*)))
(defconst *hc-sigs* (list (cons :ed25519 *hc-ed-sig*)
                          (cons :ml-dsa-65 *hc-ml-sig*)))
(defconst *hc-source*
  '(70 114 111 109 58 32 97 13 10
    83 117 98 106 101 99 116 58 32 115 13 10
    68 97 116 101 58 32 83 117 110 44 32 48 49 32 74 97 110 32 50 48 50 51 32 48 48 58 48 48 58 48 48 32 43 48 48 48 48 13 10
    88 45 85 110 107 110 111 119 110 58 32 32 65 9 66 13 10
    9 67 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 116 101 115 116 13 10
    77 101 115 115 97 103 101 45 73 68 58 32 60 104 99 64 101 120 97 109 112 108 101 62 13 10
    13 10 0 255 13 10))

(assert-event
 (equal (len (fn-hc-encode *hc-principal* *hc-keys* *hc-sigs*)) 5405))
(assert-event
 (equal (len (fn-hc-field-encode *hc-principal* *hc-keys* *hc-sigs*)) 7208))
(assert-event
 (equal (fn-hc-decode (fn-hc-encode *hc-principal* *hc-keys* *hc-sigs*))
        (fn-hc-ok (list *hc-principal* *hc-keys* *hc-sigs*))))
(assert-event
 (equal (fn-hc-field-decode
         (fn-hc-field-encode *hc-principal* *hc-keys* *hc-sigs*))
        (fn-hc-ok (list *hc-principal* *hc-keys* *hc-sigs*))))
(assert-event
 (equal (car (fn-hc-native-plan *hc-source* *hc-principal*
                                *hc-keys* *hc-sigs*)) :ok))
(assert-event
 (equal (car (fn-hc-value
              (fn-hc-native-plan *hc-source* *hc-principal*
                                 *hc-keys* *hc-sigs*))) *hc-source*))
(assert-event
 (let* ((wire (fn-hc-render *hc-source* *hc-principal* *hc-keys* *hc-sigs*))
        (received (fn-hc-received-plan wire)))
   (and (equal (car received) :ok)
        (equal (car (fn-hc-value received)) *hc-source*)
        (equal (cadr (fn-hc-value received))
               (list *hc-principal* *hc-keys* *hc-sigs*)))))

; The complete transport article, including the carrier expansion, is the
; bound's subject.  A source-sized cap refuses the otherwise valid artifact.
(assert-event
 (let ((wire (fn-hc-render *hc-source* *hc-principal* *hc-keys* *hc-sigs*)))
   (and (< (len *hc-source*) (len wire))
        (null (fn-hc-render-at-most
               (len *hc-source*) *hc-source* *hc-principal* *hc-keys* *hc-sigs*))
        (equal (fn-hc-render-at-most
                (len wire) *hc-source* *hc-principal* *hc-keys* *hc-sigs*)
               wire))))

; Relay and gateway fields are a separate projection.  They can change
; without changing the exact bytes passed to signature verification.
(assert-event
 (let* ((wire (fn-hc-render *hc-source* *hc-principal* *hc-keys* *hc-sigs*))
        (received (fn-hc-received-plan
                   (append '(80 97 116 104 58 32 114 101 108 97 121 13 10
                             88 114 101 102 58 32 102 110 46 116 101 115 116 13 10
                             73 110 106 101 99 116 105 111 110 45 73 110 102 111 58 32 103 119 13 10)
                           wire))))
   (and (fn-hc-okp received)
        (equal (car (fn-hc-value received)) *hc-source*))))

; Changing either exact source bytes or the enrolled key set changes the
; signed preimage.  The primitive negative verdict is tested at the native
; boundary; framing itself is ACL2-owned.
(assert-event
 (not (equal (fn-hsig-signed-preimage *hc-principal* *hc-keys* *hc-source*)
             (fn-hsig-signed-preimage *hc-principal* *hc-keys*
                                      (append *hc-source* '(0))))))
(defconst *hc-other-keys*
  (list (cons :ed25519 (make-list 32 :initial-element 18))
        (cons :ml-dsa-65 *hc-ml-key*)))
(assert-event
 (not (equal (fn-hsig-signed-preimage *hc-principal* *hc-keys* *hc-source*)
             (fn-hsig-signed-preimage *hc-principal* *hc-other-keys* *hc-source*))))
(assert-event
 (and (not (fn-hsig-authorize *hc-principal* *hc-keys* *hc-source*
                              *hc-sigs* *hc-ml-key* :verified :refused))
      (not (fn-hsig-authorize *hc-principal* *hc-keys* *hc-source*
                              (list (car *hc-sigs*)) *hc-ml-key*
                              :verified :verified))))

; Unknown versions and non-minimal CBOR are malformed for this selected
; profile, rather than silently treated as v1.
(assert-event
 (equal (car (fn-hc-decode (cons 2 (cdr (fn-hc-encode
                                              *hc-principal* *hc-keys* *hc-sigs*)))))
        :unverified))
(assert-event
 (equal (car (fn-hc-decode (append '(24 1)
                                   (cdr (fn-hc-encode
                                         *hc-principal* *hc-keys* *hc-sigs*)))))
        :unverified))
(assert-event
 (equal (car (fn-hc-decode (make-list (1+ *fn-hc-max-binary-octets*)
                                       :initial-element 0)))
        :unverified))

; Native construction refuses every generated/mutable namespace.
(assert-event
 (equal (car (fn-hc-native-plan
              (append '(80 97 116 104 58 32 102 110 13 10) *hc-source*)
              *hc-principal* *hc-keys* *hc-sigs*)) :unverified))

; A source without Date is not portable v1 and is never silently repaired.
(defconst *hc-no-date*
  '(70 114 111 109 58 32 97 13 10
    83 117 98 106 101 99 116 58 32 115 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 116 101 115 116 13 10
    77 101 115 115 97 103 101 45 73 68 58 32 60 110 100 64 101 120 97 109 112 108 101 62 13 10
    13 10 120 13 10))
(assert-event
 (and (equal (car (fn-hc-native-plan *hc-no-date* *hc-principal*
                                     *hc-keys* *hc-sigs*)) :unverified)
      (equal (cadr (fn-hc-native-plan *hc-no-date* *hc-principal*
                                      *hc-keys* *hc-sigs*)) :source-profile)
      (equal (nth 2 (fn-hc-native-plan *hc-no-date* *hc-principal*
                                       *hc-keys* *hc-sigs*)) *hc-no-date*)))
(assert-event
 (equal (car (fn-hc-native-plan
              (append '(70 78 45 83 116 97 116 101 109 101 110 116 58 32 65 13 10)
                      *hc-source*)
              *hc-principal* *hc-keys* *hc-sigs*)) :unverified))

; Malformed and ambiguous inbound carriers return their original bytes.
(defconst *hc-bad-received*
  '(70 78 45 65 117 116 104 111 114 115 104 105 112 58 32 33 13 10
    70 114 111 109 58 32 97 13 10 13 10 120 13 10))
(assert-event
 (and (equal (car (fn-hc-received-plan *hc-bad-received*)) :unverified)
      (equal (nth 2 (fn-hc-received-plan *hc-bad-received*))
             *hc-bad-received*)))

; Packet A does not infer a source through mutable relay fields.  Later NNTP
; composition must validate their existing grammars before enabling removal.
(defconst *hc-ambiguous-received*
  (append '(80 97 116 104 58 32 102 110 13 10) *hc-bad-received*))
(assert-event
 (and (equal (car (fn-hc-received-plan *hc-ambiguous-received*)) :unverified)
      (equal (nth 2 (fn-hc-received-plan *hc-ambiguous-received*))
             *hc-ambiguous-received*)))

; Cross-profile dispatch cannot parse an ordinary FN-Statement field as this
; fixed hybrid profile.
(assert-event
 (equal (car (fn-hc-field-decode '(81 85 74 68 82 65 61 61))) :unverified))

; Teeth: source preservation needs successful native admission.
(must-fail
 (defthm hc-source-without-success
   (equal (car (fn-hc-value
                (fn-hc-native-plan source principal keys signatures)))
          source)))

;; ---------------------------------------------------------------- carrier v2
;; Item 1 says the version; everything else keeps the v1 shape and widths.
(assert-event
 (let ((v1 (fn-hc-encode-at 1 *hc-principal* *hc-keys* *hc-sigs*))
       (v2 (fn-hc-encode-at 2 *hc-principal* *hc-keys* *hc-sigs*)))
   (and (equal v1 (fn-hc-encode *hc-principal* *hc-keys* *hc-sigs*))
        (equal (len v2) 5405)
        (equal (nth 1 v2) 2)
        (equal (update-nth 1 1 v2) v1)
        (null (fn-hc-encode-at 3 *hc-principal* *hc-keys* *hc-sigs*)))))

;; Round trip at v2, and the version item binds in both directions.
(assert-event
 (let ((v1 (fn-hc-encode-at 1 *hc-principal* *hc-keys* *hc-sigs*))
       (v2 (fn-hc-encode-at 2 *hc-principal* *hc-keys* *hc-sigs*)))
   (and (equal (fn-hc-decode-at 2 v2)
               (fn-hc-ok (list *hc-principal* *hc-keys* *hc-sigs*)))
        (equal (fn-hc-decode-at 1 v2) (fn-hc-error :profile v2))
        (equal (fn-hc-decode v2) (fn-hc-error :profile v2))
        (equal (fn-hc-decode-at 2 v1) (fn-hc-error :profile v1))
        (equal (fn-hc-decode-at 3 v2) (fn-hc-error :profile v2))
        (equal (fn-hc-field-decode-at
                2 (fn-hc-field-encode-at 2 *hc-principal* *hc-keys* *hc-sigs*))
               (fn-hc-ok (list *hc-principal* *hc-keys* *hc-sigs*))))))

;; A v1-sized source must carry a v1 carrier: the native plan emits v1, and
;; the same article with a v2 carrier (item 1 flipped to 2) is refused
;; :carrier by the received plan, which decodes at the source's version.
(assert-event
 (let* ((v2-field (fn-hc-field-encode-at 2 *hc-principal* *hc-keys* *hc-sigs*))
        (forged (append (fn-hc-field-lines v2-field) *hc-source*))
        (plan (fn-hc-native-plan *hc-source* *hc-principal* *hc-keys* *hc-sigs*)))
   (and (equal (cadr (fn-hc-value plan))
               (fn-hc-field-encode *hc-principal* *hc-keys* *hc-sigs*))
        (equal (fn-hc-received-plan forged)
               (fn-hc-error :carrier forged)))))

;; Teeth: the round trip needs the emission premise (an unemittable
;; version, key set or signature pair has no carrier to decode) ...
(must-fail
 (defthm hc-decode-at-of-encode-at-without-emission
   (equal (fn-hc-decode-at version
                           (fn-hc-encode-at version principal keys signatures))
          (fn-hc-ok (list principal keys signatures)))))
;; ... and version binding needs both premises: another version, and a
;; carrier that was emitted.
(must-fail
 (defthm hc-decode-at-refuses-without-other-version
   (implies (fn-hc-encode-at version principal keys signatures)
            (not (fn-hc-okp (fn-hc-decode-at other
                                             (fn-hc-encode-at version principal
                                                              keys signatures)))))))
(must-fail
 (defthm hc-decode-at-refuses-without-emission
   (implies (not (equal other version))
            (not (fn-hc-okp (fn-hc-decode-at other
                                             (fn-hc-encode-at version principal
                                                              keys signatures)))))))
