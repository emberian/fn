; Immutable first-acceptance binding, PRF-1108 representation increment.
; This is a distinct current-format field, never release-evidence metadata.
; Installing it in durable article records and the served comparison remains
; a separate integration obligation. A validated profile is not authority.
(in-package "ACL2")
(include-book "identity")

(defconst *fn-ab-magic* '(0 70 78 45 65 66 49)) ; NUL FN-AB1
(defconst *fn-ab-octets* 56) ; magic7 + profile1 + received subject48
(defconst *fn-ab-subject-head* '(102 110 47 115 117 98 106 101 99 116 47 118 49 0 1 2))

(defun fn-ab-profilep (x)
  (declare (xargs :guard t))
  (and (member-eq x '(:post-d25 :relay-v1 :native-source)) t))
(defun fn-ab-profile-code (x)
  (declare (xargs :guard t))
  (case x (:post-d25 1) (:relay-v1 2) (:native-source 3) (otherwise 0)))
(defun fn-ab-code-profile (x)
  (declare (xargs :guard t))
  (case x (1 :post-d25) (2 :relay-v1) (3 :native-source) (otherwise nil)))

; Exact typed incoming-byte subject, independently of the stored payload's
; content-subject. No caller-supplied text or decoded provenance selects it.
(defun fn-ab-received-subjectp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-at-mostp x 48)
       (equal (len x) 48)
       (fn-cbor-octet-listp x)
       (equal (take 16 x) *fn-ab-subject-head*)))
(defun fn-ab-make (profile received-subject)
  (declare (xargs :guard t))
  (list profile received-subject))
(defun fn-ab-profile (x)
  (declare (xargs :guard t))
  (fn-cbor-ag-car x))
(defun fn-ab-received-subject (x)
  (declare (xargs :guard t))
  (fn-cbor-ag-car (fn-cbor-ag-cdr x)))
(defun fn-ab-p (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)
       (fn-ab-profilep (fn-ab-profile x))
       (fn-ab-received-subjectp (fn-ab-received-subject x))))

(defun fn-ab-encode (x)
  (declare (xargs :guard t))
  (if (fn-ab-p x)
      (append *fn-ab-magic*
              (cons (fn-ab-profile-code (fn-ab-profile x))
                    (fn-ab-received-subject x)))
    nil))
(defun fn-ab-decode (w)
  (declare (xargs :guard t))
  ; Reject length before walking the octet domain. All work is bounded by
  ; this field's fixed grammar, independently of the article's size.
  (if (and (fn-cbor-at-mostp w *fn-ab-octets*)
           (equal (len w) *fn-ab-octets*)
           (fn-cbor-octet-listp w)
           (equal (take 7 w) *fn-ab-magic*))
      (let ((x (fn-ab-make (fn-ab-code-profile (nth 7 w)) (nthcdr 8 w))))
        (if (fn-ab-p x) (list :ok x) (list :error :invalid-binding)))
    (list :error :invalid-binding)))

(defthm fn-ab-profile-code-roundtrip
  (implies (fn-ab-profilep x)
           (equal (fn-ab-code-profile (fn-ab-profile-code x)) x)))
(defthm fn-ab-decode-validates
  (implies (equal (car (fn-ab-decode w)) :ok)
           (fn-ab-p (cadr (fn-ab-decode w)))))

(local (defthm fn-ab-octets-are-true-list
  (implies (fn-cbor-octet-listp x) (true-listp x))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local (defthm fn-ab-at-mostp-from-length
  (implies (and (true-listp x) (natp n) (<= (len x) n))
           (fn-cbor-at-mostp x n))
  :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))

(defthm fn-ab-encode-length
  (implies (fn-ab-p x) (equal (len (fn-ab-encode x)) *fn-ab-octets*)))
(local (defthm fn-ab-two-fields
  (implies (and (true-listp x) (equal (len x) 2))
           (equal (list (car x) (cadr x)) x))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x)))
                  :in-theory (enable true-listp)))))
(defthm fn-ab-decode-of-encode
  (implies (fn-ab-p x)
           (equal (fn-ab-decode (fn-ab-encode x)) (list :ok x)))
  :hints (("Goal" :use fn-ab-two-fields :in-theory (disable fn-ab-two-fields))))

(defun fn-ab-of-received (profile received)
  (declare (xargs :guard (and (fn-cbor-octet-listp received)
                              (<= (len received) *fn-cbor-max-uint*))))
  (fn-ab-make profile (fn-id-subject-of-payload received)))

(defthm fn-ab-of-received-is-binding
  (implies (fn-ab-profilep profile)
           (fn-ab-p (fn-ab-of-received profile received)))
  :hints (("Goal" :in-theory
           (e/d (fn-ab-of-received fn-ab-p fn-ab-make fn-ab-profile
                 fn-ab-received-subject fn-ab-received-subjectp
                 fn-id-subject-of-payload fn-id-subject fn-id-render
                 fn-frame-digest-length fn-frame-digest-octet-listp)
                (fn-id-subject-preimage fn-ab-profilep)))))

; No host integration is claimed by these representation theorems.
(in-theory (disable fn-ab-profilep fn-ab-profile-code fn-ab-code-profile
                    fn-ab-received-subjectp fn-ab-make fn-ab-profile
                    fn-ab-received-subject fn-ab-p fn-ab-encode fn-ab-decode fn-ab-of-received))
