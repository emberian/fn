; RFC9172 section4; RFC9173 sections3.7 and4.7.
; Finite canonical literal/span commands, not canonical-source authority.
; Primary spans require the caller's deterministic/valid primary relation;
; source refs require actual immutable registry/pin establishment. No MAC,
; plaintext completion, endpoint validity or acceptance follows from :planned.
(in-package "ACL2")
(include-book "bpsec-operation")

(defun fn-bps-input-spanp (span)
 (declare (xargs :guard t))
 (and (fn-bps-fixed-recordp 4 span) (eq (fn-bps-field 0 span) :bps-span)
      (fn-bps-refp (fn-bps-field 1 span))
      (fn-bps-uintp (fn-bps-field 2 span)) (fn-bps-uintp (fn-bps-field 3 span))
      (<= (+ (fn-bps-field 2 span) (fn-bps-field 3 span)) *fn-bpc-max-uint*)))

(defun fn-bps-input-primaryp (event)
 (declare (xargs :guard t))
 (and (fn-bps-fixed-recordp 7 event) (eq (fn-bps-field 0 event) :bp-primary-source)
      (fn-bps-refp (fn-bps-field 1 event))
      (fn-bps-uintp (fn-bps-field 2 event)) (fn-bps-uintp (fn-bps-field 3 event))
      (< (fn-bps-field 2 event) (fn-bps-field 3 event))
      (fn-bps-uintp (fn-bps-field 4 event))
      (member-equal (fn-bps-field 5 event) '(0 1 2))))

(defun fn-bps-input-blockp (event)
 (declare (xargs :guard t))
 (let ((span (fn-bps-field 8 event)))
  (and (fn-bps-fixed-recordp 10 event) (eq (fn-bps-field 0 event) :bp-canonical-source)
       (fn-bps-refp (fn-bps-field 1 event))
       (fn-bps-uintp (fn-bps-field 2 event)) (fn-bps-uintp (fn-bps-field 3 event))
       (< (fn-bps-field 2 event) (fn-bps-field 3 event))
       (fn-bps-uintp (fn-bps-field 4 event))
       (fn-bps-uintp (fn-bps-field 5 event)) (< 0 (fn-bps-field 5 event))
       (fn-bps-uintp (fn-bps-field 6 event))
       (member-equal (fn-bps-field 7 event) '(0 1 2))
       (fn-bps-input-spanp span)
       (equal (fn-bps-field 1 event) (fn-bps-field 1 span))
       (<= (fn-bps-field 2 event) (fn-bps-field 2 span))
       (<= (+ (fn-bps-field 2 span) (fn-bps-field 3 span)) (fn-bps-field 3 event)))))

(defun fn-bps-input-primary-span (event)
 (declare (xargs :guard (fn-bps-input-primaryp event)))
 (list :bps-span (fn-bps-field 1 event) (fn-bps-field 2 event)
       (- (fn-bps-field 3 event) (fn-bps-field 2 event))))

(defun fn-bps-input-header (event)
 (declare (xargs :guard (fn-bps-input-blockp event)))
 ; RFC9171 assigned extension bits are1,2,4,16. RFC9172 section4 clears
 ; all reserved/unassigned bits in canonical nonprimary control flags.
 (list :bps-literal
  (append (fn-bpc-argument 0 (fn-bps-field 4 event))
          (fn-bpc-argument 0 (fn-bps-field 5 event))
          (fn-bpc-argument 0 (logand 23 (fn-bps-field 6 event))))))

(defun fn-bps-input-header-count (event)
 (declare (xargs :guard (fn-bps-input-blockp event)
  :guard-hints (("Goal" :in-theory (enable fn-bps-input-header fn-bps-field)))))
 ; Count only the bounded <=27-octet literal header, never source data.
 (len (fn-bps-field 1 (fn-bps-input-header event))))

; Proof-only field facts keep the fixed-record predicates closed at the
; composed guard boundary; no whole-state/source revalidation is introduced.
(local (defthm fn-bps-input-scope-natural
 (implies (fn-bps-opp descriptor)
          (natp (fn-bps-field 2 (fn-bps-field 9 descriptor))))
 :hints (("Goal" :in-theory (disable fn-bps-field)))
 :rule-classes :forward-chaining))
(local (defthm fn-bps-input-block-data-numbers
 (implies (fn-bps-input-blockp event)
  (and (integerp (fn-bps-field 2 (fn-bps-field 8 event)))
       (integerp (fn-bps-field 3 (fn-bps-field 8 event)))))
 :hints (("Goal" :in-theory (disable fn-bps-field)))
 :rule-classes :forward-chaining))
(local (defthm fn-bps-input-primary-span-numbers
 (implies (fn-bps-input-primaryp event)
  (and (integerp (fn-bps-field 2 (fn-bps-input-primary-span event)))
       (integerp (fn-bps-field 3 (fn-bps-input-primary-span event)))))
 :hints (("Goal" :in-theory (enable fn-bps-field)))
 :rule-classes :forward-chaining))

(defun fn-bps-input-plan (descriptor primary target security)
 (declare (xargs :guard t
  :guard-hints (("Goal" :in-theory (disable fn-bps-field fn-bps-input-header
                              fn-bps-input-primary-span fn-bpc-argument fn-bps-opp
                              fn-bps-input-primaryp fn-bps-input-blockp
                              fn-bps-input-spanp fn-bps-input-header-count)))))
 (let* ((bib (eq (fn-bps-field 1 descriptor) :verify-bib))
        (target-number (fn-bps-field 7 descriptor))
        (primary-target (equal target-number 0))
        (params (fn-bps-field 9 descriptor))
        (scope (fn-bps-field 2 params)))
  (cond
   ((not (fn-bps-opp descriptor)) (list :refused :invalid-descriptor))
   ((or (not (fn-bps-input-primaryp primary)) (not (fn-bps-input-blockp security)))
    (list :refused :invalid-source-metadata))
   ((or (not (equal (fn-bps-field 1 primary) (fn-bps-field 1 security)))
        (not (equal (fn-bps-field 5 security) (fn-bps-field 6 descriptor)))
        (not (equal (fn-bps-field 4 security) (if bib 11 12))))
    (list :refused :foreign-source-metadata))
   ((if primary-target
      (or (not (fn-bps-input-primaryp target))
          (not (equal (fn-bps-field 1 target) (fn-bps-field 1 primary)))
          (not (equal (fn-bps-field 2 target) (fn-bps-field 2 primary)))
          (not (equal (fn-bps-field 3 target) (fn-bps-field 3 primary)))
          (not (equal (fn-bps-field 4 target) (fn-bps-field 4 primary)))
          (not (equal (fn-bps-field 5 target) (fn-bps-field 5 primary))))
      (or (not (fn-bps-input-blockp target))
          (not (equal (fn-bps-field 1 target) (fn-bps-field 1 primary)))
          (not (equal (fn-bps-field 5 target) target-number))))
    (list :refused :foreign-target-metadata))
   ((or (and (not bib) (or primary-target (equal (fn-bps-field 4 target) 12)))
        (and bib (not primary-target) (member-equal (fn-bps-field 4 target) '(11 12))))
    (list :refused :forbidden-target))
   (t
    (let* ((data (if primary-target (fn-bps-input-primary-span primary) (fn-bps-field 8 target)))
           (tail (and (not bib) (eq (fn-bps-field 5 params) :tag-in-ciphertext))))
     (if (and tail (< (fn-bps-field 3 data) 16))
      (list :refused :short-ciphertext-tag)
      (let* ((transcript
              (append (list (list :bps-literal (fn-bpc-argument 0 scope)))
               (if (and (not primary-target) (not (equal (logand scope 1) 0)))
                (list (fn-bps-input-primary-span primary)) nil)
               (if (and (not primary-target) (not (equal (logand scope 2) 0)))
                (list (fn-bps-input-header target)) nil)
               (if (not (equal (logand scope 4) 0)) (list (fn-bps-input-header security)) nil)
               (if bib
                (if primary-target (list data)
                 (list (list :bps-literal (fn-bpc-argument 2 (fn-bps-field 3 data))) data)) nil)))
             (transcript-count
              (+ 1
               (if (and (not primary-target) (not (equal (logand scope 1) 0)))
                (fn-bps-field 3 (fn-bps-input-primary-span primary)) 0)
               (if (and (not primary-target) (not (equal (logand scope 2) 0)))
                (fn-bps-input-header-count target) 0)
               (if (not (equal (logand scope 4) 0)) (fn-bps-input-header-count security) 0)
               (if bib (if primary-target (fn-bps-field 3 data)
                        (+ (len (fn-bpc-argument 2 (fn-bps-field 3 data))) (fn-bps-field 3 data))) 0)))
             (cipher-count (if bib 0 (- (fn-bps-field 3 data) (if tail 16 0))))
             (cipher (and (not bib)
                      (if tail (list :bps-span (fn-bps-field 1 data) (fn-bps-field 2 data)
                                    (- (fn-bps-field 3 data) 16)) data)))
             (tag (and (not bib)
                   (if tail (list :bps-span (fn-bps-field 1 data)
                                 (+ (fn-bps-field 2 data) (- (fn-bps-field 3 data) 16)) 16)
                    (fn-bps-field 11 descriptor)))))
       ; :planned is an unauthoritative command description. The input-ref
       ; registry must bind these exact commands to the issued descriptor.
       ; NIST SP800-38D5.2.1.1/5.2.2 restrict total input lengths;
       ; these are algorithm limits, not arbitrary stored-object ceilings.
       ; SHA256 has a <2^64-bit domain (FIPS180-4); the HMAC inner
       ; hash also consumes its64-octet ipad block (RFC2104section2).
       (cond
        ((and (not bib) (> cipher-count 68719476704)) (list :refused :gcm-ciphertext-limit))
        ((and (not bib) (> transcript-count 2305843009213693951)) (list :refused :gcm-aad-limit))
        ((and bib (equal (fn-bps-field 1 params) 5) (> transcript-count 2305843009213693887))
         (list :refused :sha256-input-limit))
        (t (list :planned (list :bps-input-plan descriptor transcript cipher tag)))))))))))
