; The store bounds the host reads -- the charge for a payload, the admission
; of a publication and the open's per-file read bound -- as guard-verified
; functions with their keystones (lane decision-keystones-2, K4: the three
; were :ideal in host/store-host.lisp, each with a branch of its own and no
; theorem about it; host/native/io.lisp calls them through the host file).
; The other ten fn-store-* decision entries of that host file are each
; exactly a call of one book function and delegate to it by declaration
; (host/interfaces.lisp :delegates, checked against the world); this book
; proves the theorems three of those callees lacked: the two refusal-text
; renderers and the profile report.
(in-package "ACL2")
(include-book "byte-store-frame")
(include-book "store-profile-open")
(include-book "store-genesis")
(include-book "identity-invariants")
(include-book "container")
(include-book "frame-octets")

; -----------------------------------------------------------------------------
; The three entries, exactly as the host file defined them (the read bound
; fixes its summand, which changes no value: `+' fixes its arguments).

(defun fn-store-charge (length)
  (declare (xargs :guard t))
  (if (natp length) (fn-charge-for-payload length) 0))

(defun fn-store-publication-admissibility (profile committed-count
                                                   prospective-payload-octets)
  (declare (xargs :guard t))
  (if (fn-bs-publication-admissiblep profile committed-count
                                     prospective-payload-octets)
      :admissible
    :refused))

;; The open's per-file read bound under the persisted PROFILE: one FNST frame
;; whose payload is at most the profile's per-record ceiling.  A profile that
;; is not valid yields the frame overhead alone, and the open refuses every
;; file.
(defun fn-store-profile-read-bound (profile)
  (declare (xargs :guard t))
  (+ *fn-frame-overhead-octets* (fix (fn-bs-profile-record-ceiling profile))))

; -----------------------------------------------------------------------------
; KEYSTONE (PRF-961).  The admission the host reads is :admissible exactly
; when the profile is admitted, both counts are naturals, the committed
; count is below the profile's T and the prospective payload is within its
; record ceiling; everything else is :refused, and nothing else is answered.

(defthm fn-store-publication-admissibility-admits-exactly-within-the-profile
  (let ((a (fn-store-publication-admissibility profile committed-count
                                               prospective-payload-octets)))
    (and (member-equal a '(:admissible :refused))
         (iff (equal a :admissible)
              (and (fn-bs-profile-admittedp profile)
                   (natp committed-count)
                   (natp prospective-payload-octets)
                   (< committed-count (fn-bs-profile-max-transactions profile))
                   (<= prospective-payload-octets
                       (fn-bs-profile-record-ceiling profile))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-store-publication-admissibility
                                   fn-bs-publication-admissiblep)
                                  (fn-bs-profile-admittedp
                                   fn-bs-profile-max-transactions
                                   fn-bs-profile-record-ceiling)))))

; KEYSTONE (PRF-961), the composition of two host entries: the open's read
; bound covers every publication the store admitted under the same profile
; -- the frame overhead plus the admitted payload never exceeds it.  This
; is the claim host/native/io.lisp's open relies on when it reads each
; committed file under fn-store-profile-read-bound.

(defthm fn-store-profile-read-bound-covers-every-admitted-publication
  (implies (equal (fn-store-publication-admissibility profile committed-count
                                                      prospective-payload-octets)
                  :admissible)
           (<= (+ *fn-frame-overhead-octets* prospective-payload-octets)
               (fn-store-profile-read-bound profile)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-store-publication-admissibility
                                   fn-store-profile-read-bound
                                   fn-bs-publication-admissiblep)
                                  (fn-bs-profile-admittedp
                                   fn-bs-profile-max-transactions
                                   fn-bs-profile-record-ceiling)))))

; KEYSTONE (PRF-961).  The charge the host quotes is positive exactly for a
; length, is the identity book's page charge for that length, and for an
; article's octets is the charge the container's receipt records.

(defthm fn-store-charge-is-positive-exactly-for-a-length-and-is-the-receipt-charge
  (and (iff (posp (fn-store-charge length)) (natp length))
       (implies (natp length)
                (equal (fn-store-charge length) (fn-charge-for-payload length)))
       (equal (fn-store-charge (len (fn-ct-article-octets a))) (fn-ct-charge a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-store-charge fn-ct-charge)
                                  (fn-charge-for-payload fn-ct-article-octets))
           :use ((:instance fn-charge-for-payload-posp)
                 (:instance fn-charge-for-payload-posp
                            (length (len (fn-ct-article-octets a))))))))

; -----------------------------------------------------------------------------
; The callees of the delegating wrappers (PRF-962).

; fn-store-metadata-config-refusal-text is fn-spo-refusal-text: a line
; exactly for the foreign-format refusal, and for the open's own verdict
; exactly when the frame is no profile of this format but names another.

(defthm fn-spo-refusal-text-refuses-exactly-the-foreign-format
  (and (iff (fn-spo-refusal-text verdict)
            (equal verdict (list :refused :store-format)))
       (iff (fn-spo-refusal-text (fn-spo-config-open octets))
            (and (not (fn-bs-config-decode octets))
                 (fn-spo-foreign-formatp octets))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-spo-refusal-text fn-spo-config-open)
                                  (fn-bs-config-decode fn-spo-foreign-formatp)))))

; fn-store-genesis-refusal-text is fn-gen-refusal-text: a line exactly for
; the four refusals of the genesis open, and for the open's own verdict
; exactly when it is not the accepted genesis.

(defthm fn-gen-refusal-text-refuses-exactly-a-refused-open
  (and (iff (fn-gen-refusal-text verdict)
            (member-equal verdict '((:refused :genesis-damaged)
                                    (:refused :genesis-format)
                                    (:refused :schema-digest)
                                    (:refused :profile-digest))))
       (iff (fn-gen-refusal-text (fn-gen-open octets profile))
            (not (equal (car (fn-gen-open octets profile)) :genesis))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-gen-refusal-text fn-gen-open)
                                  (fn-gen-decode fn-gen-format fn-gen-schema
                                   fn-gen-image-schema-digest
                                   fn-gen-profile-digest
                                   fn-gen-profile-digest-of fn-gen-trailer)))))

; fn-store-profile-report is fn-bs-profile-report: an alist whose "format"
; is this release's format word exactly for a valid profile and 0 otherwise.

(local
 (defthm fn-shb-profile-report-fields-alistp
   (alistp (fn-bs-profile-report-fields names values))
   :hints (("Goal" :in-theory (enable fn-bs-profile-report-fields)))))

(defthm fn-bs-profile-report-names-the-format-exactly-for-a-valid-profile
  (and (alistp (fn-bs-profile-report values))
       (equal (cdr (assoc-equal "format" (fn-bs-profile-report values)))
              (if (fn-bs-profile-validp values) 10 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-report)
                                  (fn-bs-profile-validp
                                   fn-bs-profile-report-fields)))))
