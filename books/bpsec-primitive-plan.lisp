; Core receiver suite/key-width planning and bounded primitive observations.
; RFC 9173 sections3.5,3.6,4.4; no installed key policy or crypto assumption.
; Exact primitive provenance and expected-tag/source-span binding are caller
; obligations. This leaf never manufactures an immutable plaintext ref or
; actual replay grant. A shaped descriptor/observation is not authority.
(in-package "ACL2")
(include-book "bpsec-operation")

(defun fn-bps-hmac-width (variant)
  (declare (xargs :guard t))
  (case variant (5 32) (6 48) (7 64) (otherwise 0)))

(defun fn-bps-primitive-select (descriptor key-octets)
  (declare (xargs :guard t))
  (let* ((action (fn-bps-field 1 descriptor))
         (context (fn-bps-field 8 descriptor))
         (params (fn-bps-field 9 descriptor))
         (variant (fn-bps-field 1 params))
         (bib (eq action :verify-bib))
         (width (if bib (fn-bps-hmac-width variant)
                  (case variant (1 16) (3 32) (otherwise 0)))))
    (cond
     ((not (fn-bps-fixed-recordp 12 descriptor)) (list :refused :invalid-descriptor))
     ((not (or (equal context 1) (equal context 2))) (list :unsupported :unsupported-profile))
     ((not (or bib (eq action :decrypt-bcb))) (list :refused :invalid-descriptor))
     ((equal width 0) (list :unsupported :unsupported-profile))
     ((not (fn-bps-opp descriptor)) (list :refused :invalid-descriptor))
     ; RFC9173 3.5: HMAC key is output-sized. AES key is variant-sized.
     ; This count must come from the actual held key entry, not a native claim.
     ((not (equal key-octets width)) (list :refused :key-width))
     (t (list :bps-primitive-plan descriptor
              (if bib (case variant (5 :sha256) (6 :sha384) (otherwise :sha512))
                (if (equal variant 1) :aes128-gcm :aes256-gcm))
              width (if bib width 16)
              (if bib 0 (fn-bps-field 3 (fn-bps-field 3 params))))))))

(defun fn-bps-exact-octetsp (count bytes)
  (declare (xargs :guard (natp count) :measure (nfix count)))
  (if (zp count) (null bytes)
    (and (consp bytes) (fn-cbor-octetp (car bytes))
         (fn-bps-exact-octetsp (1- count) (cdr bytes)))))

; All fixed-width bytes participate. There is no equality/prefix branch
; on their values: the sum of squared byte differences is zero exactly for
; equal octets. For a supported MAC, <=64 terms of <=65025 fit a fixnum on
; the supported runtime. This is source-level fixed traversal, not a proof
; of compiler/CPU constant time or of actual native expected-span custody.
(defun fn-bps-tag-difference (count actual expected accumulator)
  (declare (xargs :guard (and (natp count) (<= count 64)
                             (fn-bps-exact-octetsp count actual)
                             (fn-bps-exact-octetsp count expected)
                             (integerp accumulator))
                  :measure (nfix count)))
  (if (zp count) accumulator
    (let ((difference (- (car actual) (car expected))))
      (fn-bps-tag-difference (1- count) (cdr actual) (cdr expected)
                            (+ accumulator (* difference difference))))))

(defthm fn-bps-tag-difference-nonnegative
  (implies (and (natp count) (fn-bps-exact-octetsp count actual)
                (fn-bps-exact-octetsp count expected) (natp accumulator))
           (<= 0 (fn-bps-tag-difference count actual expected accumulator)))
  :hints (("Goal" :induct (fn-bps-tag-difference count actual expected accumulator)
           :in-theory (disable distributivity) :nonlinearp t)))

; Arithmetic helper only; no cryptographic assumption.
(local (defthm fn-bps-square-zero
  (implies (acl2-numberp x)
           (equal (equal (* x x) 0) (equal x 0)))
  :hints (("Goal" :cases ((equal x 0))
           :use ((:instance associativity-of-* (x (/ x)) (y x) (z x)))
           :in-theory (disable associativity-of-*)))))

(defthm fn-bps-tag-difference-zero-is-exact-equality
  (implies (and (natp count) (fn-bps-exact-octetsp count actual)
                (fn-bps-exact-octetsp count expected) (natp accumulator))
           (equal (equal (fn-bps-tag-difference count actual expected accumulator) 0)
                  (and (equal accumulator 0) (equal actual expected))))
  :hints (("Goal" :induct (fn-bps-tag-difference count actual expected accumulator)
           :in-theory (disable distributivity) :nonlinearp t)))

(defun fn-bps-primitive-answer (descriptor observation expected)
  (declare (xargs :guard t))
  (let* ((observed (fn-bps-field 1 observation))
         (word (fn-bps-field 2 observation))
         (actual (fn-bps-field 3 observation))
         (bib (eq (fn-bps-field 1 descriptor) :verify-bib))
         (width (fn-bps-hmac-width (fn-bps-field 1 (fn-bps-field 9 descriptor)))))
    (cond
     ((or (not (fn-bps-opp descriptor))
          (not (fn-bps-fixed-recordp 4 observation))
          (not (eq (fn-bps-field 0 observation) :bps-primitive-observation)))
      (list :bps-primitive-status :ignored :malformed-completion nil))
     ((not (equal descriptor observed))
      (list :bps-primitive-status :ignored :foreign-completion nil))
     ((and (eq word :unsupported) (null actual))
      (list :bps-primitive-status :unsupported :unsupported-profile
            (list :bps-completion descriptor :unsupported nil :unsupported-profile)))
     ((and (or (eq word :primitive-unavailable) (eq word :primitive-fault)) (null actual))
      (list :bps-primitive-status :uncertain word
            (list :bps-completion descriptor :uncertain nil word)))
     ((and bib (eq word :hmac-bytes)
           (fn-bps-exact-octetsp width actual) (fn-bps-exact-octetsp width expected))
      (if (equal (fn-bps-tag-difference width actual expected 0) 0)
          (list :bps-primitive-status :verified :ok
                (list :bps-completion descriptor :verified nil :ok))
        (list :bps-primitive-status :failed :authentication-failed
              (list :bps-completion descriptor :failed nil :authentication-failed))))
     ((and (not bib) (eq word :bad-tag) (null actual))
      (list :bps-primitive-status :failed :authentication-failed
            (list :bps-completion descriptor :failed nil :authentication-failed)))
     ((and (not bib) (eq word :authenticated) (null actual))
      ; Only an authentication-stage observation. Same immutable ciphertext
      ; replay and current authority must later produce a genuine output ref.
      (list :bps-primitive-status :authenticated :pending-plaintext
            (list :bps-authenticated descriptor (fn-bps-field 10 descriptor))))
     (t (list :bps-primitive-status :uncertain :primitive-fault
              (list :bps-completion descriptor :uncertain nil :primitive-fault))))))

; These are component metadata/byte relations, not real crypto statements.
(defthm fn-bps-primitive-verified-requires-exact-bib-observation
  (implies (eq (fn-bps-field 1 (fn-bps-primitive-answer descriptor observation expected)) :verified)
           (and (fn-bps-opp descriptor)
                (fn-bps-fixed-recordp 4 observation)
                (eq (fn-bps-field 0 observation) :bps-primitive-observation)
                (equal (fn-bps-field 1 observation) descriptor)
                (eq (fn-bps-field 1 descriptor) :verify-bib)
                (eq (fn-bps-field 2 observation) :hmac-bytes)
                (equal (fn-bps-field 3 observation) expected)
                (fn-bps-exact-octetsp (fn-bps-hmac-width (fn-bps-field 1 (fn-bps-field 9 descriptor))) expected)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bps-opp fn-bps-fixed-recordp fn-bps-exact-octetsp fn-bps-hmac-width fn-bps-tag-difference))))

(defthm fn-bps-primitive-gcm-authentication-is-only-pending-by-definition
  (implies (and (fn-bps-opp descriptor)
                (eq (fn-bps-field 1 descriptor) :decrypt-bcb)
                (fn-bps-fixed-recordp 4 observation)
                (eq (fn-bps-field 0 observation) :bps-primitive-observation)
                (equal (fn-bps-field 1 observation) descriptor)
                (eq (fn-bps-field 2 observation) :authenticated)
                (null (fn-bps-field 3 observation)))
           (equal (fn-bps-primitive-answer descriptor observation expected)
                  (list :bps-primitive-status :authenticated :pending-plaintext
                        (list :bps-authenticated descriptor (fn-bps-field 10 descriptor)))))
  :hints (("Goal" :in-theory (disable fn-bps-opp fn-bps-fixed-recordp fn-bps-exact-octetsp fn-bps-hmac-width fn-bps-tag-difference))))
