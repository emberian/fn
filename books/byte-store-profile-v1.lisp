;; fn: the store profile relation as the image before packet P6 checked it,
;; frozen, and the keystone that a profile it admitted is still admitted
;; (D27, design 2026-09-25-bounds 2.3, packet P6).
;;
;; Packet P6 widened the record's integer fields to u64.  Its first cut raised
;; the record overhead a profile's R must hold from 1 083 to 1 111 octets, so
;; a format-8 profile saved with the development or scale preset (R =
;; 17 138 486, the article record of A = 32 768 and G = 65 535 at 1 083) failed
;; `fn-bs-profile-validp' at open, and the store would not have opened.  The
;; relation now reads the ceiling at the widths the runtime produces
;; (records-shape `fn-record-encoded-octets-ceiling', u32 heads), and the
;; theorem below says every profile the old relation admitted is admitted by
;; `fn-bs-profile-admittedp', the function host/store-host.lisp
;; `fn-store-profile-admittedp' calls, and is the profile the store runs under
;; (`fn-bs-profile-of', which every accessor the host reads goes through).
;;
;; The frozen definition is the text of books/byte-store-frame.lisp
;; `fn-bs-profile-invalid-reason' at dev 56eb33ee with the record-ceiling call
;; written out at its 1 083-octet overhead, (+ A (* 261 G) 1083); every other
;; constant it names is unchanged by P6.  No host line calls it.
(in-package "ACL2")
(include-book "byte-store-frame")

(defun fn-bs-profile-v1-invalid-reason (values)
  (declare (xargs :guard t))
  (let ((tx (fn-bs-pf 2 values)) (h (fn-bs-pf 3 values))
        (r (fn-bs-pf 4 values)) (a (fn-bs-pf 5 values))
        (g (fn-bs-pf 6 values)) (n (fn-bs-pf 7 values))
        (k (fn-bs-pf 8 values)))
    (cond ((not (fn-frame-values-okp *fn-bs-meta-profile-spec* values))
           :layout)
          ((not (equal (fn-bs-meta-nth 0 values) *fn-bs-meta-format-8*))
           :format)
          ((not (equal (fn-bs-meta-nth 1 values) *fn-bs-meta-frontier-format*))
           :frontier-format)
          ((or (< tx 1) (< *fn-bs-profile-transaction-ceiling* tx))
           :max-transactions-outside-txid-width)
          ((< h r) :max-history-octets-below-max-record-octets)
          ((< r *fn-bs-profile-min-record-octets*)
           :max-record-octets-below-an-event-kind)
          ((< *fn-bs-profile-record-ceiling-codec* r)
           :max-record-octets-above-codec)
          ((or (< a 1) (< *fn-bs-profile-article-ceiling-codec* a))
           :max-article-octets-outside-codec)
          ((or (< g 1) (< *fn-bs-profile-groups-ceiling-codec* g))
           :max-groups-per-article-outside-codec)
          ((or (< n 1) (< *fn-bs-profile-group-name-ceiling-codec* n))
           :max-group-name-octets-outside-codec)
          ((< r (+ a (* 261 g) 1083))
           :max-record-octets-below-the-article-record)
          ((or (< k 1) (< tx k)) :max-open-suffix-outside-transactions)
          ((not (and (fn-bs-profile-countp (fn-bs-pf 9 values))
                     (fn-bs-profile-countp (fn-bs-pf 10 values))
                     (fn-bs-profile-countp (fn-bs-pf 11 values))
                     (fn-bs-profile-countp (fn-bs-pf 12 values))
                     (fn-bs-profile-countp (fn-bs-pf 13 values))))
           :namespace-count-outside-width)
          ((< 1 (fn-bs-pf 14 values)) :history-marker-not-a-word)
          (t nil))))

;  The relation's half: the old relation's acceptance is the new one's, for
; every R within the kind-6 poll reply's report ceiling.  PKT-467 (the
; coordinator's ruling, D27: profile validation and representation agree)
; refuses the 355 octets of R above *fn-stxa-max-octets*, which the old
; relation admitted and no poll reply can carry; that window is refused BY
; NAME (`fn-bs-profile-v1-valid-above-the-poll-reply-is-refused-by-name'), so
; the two theorems together say exactly which saved profiles still open.
(defthm fn-bs-profile-v1-valid-is-valid
  (implies (and (not (fn-bs-profile-v1-invalid-reason values))
                (<= (fn-bs-pf 4 values) *fn-stxa-max-octets*))
           (fn-bs-profile-validp values))
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-validp
                                   fn-bs-profile-invalid-reason
                                   fn-record-encoded-octets-ceiling)
                                  (fn-bs-pf fn-frame-values-okp)))))

;  KEYSTONE (a saved profile stays admitted).  A format-8 profile the image
; before P6 admitted is admitted by this one and is, unchanged, the profile
; the store runs under, so a store saved under it opens with the same bounds.
(defthm fn-bs-profile-v1-valid-stays-valid
  (implies (and (not (fn-bs-profile-v1-invalid-reason values))
                (<= (fn-bs-pf 4 values) *fn-stxa-max-octets*))
           (and (fn-bs-profile-admittedp values)
                (equal (fn-bs-profile-of values) values)))
  :rule-classes nil
  :hints (("Goal" :use fn-bs-profile-v1-valid-is-valid
           :in-theory (e/d (fn-bs-profile-admittedp)
                           (fn-bs-profile-v1-invalid-reason fn-bs-pf
                            fn-bs-profile-v1-valid-is-valid
                            fn-bs-profile-validp fn-bs-profile-of)))))

;  The window PKT-467 closes: a profile the old relation admitted whose R lies
; above the poll reply's report ceiling fails the new relation by its own
; name for it, which `init' and `store upgrade-profile' print.  An open of a
; store saved in that window is refused by the host's generic configuration
; fault, not by this name (PKT-471: no such store is known).
(defthm fn-bs-profile-v1-valid-above-the-poll-reply-is-refused-by-name
  (implies (and (not (fn-bs-profile-v1-invalid-reason values))
                (< *fn-stxa-max-octets* (fn-bs-pf 4 values)))
           (equal (fn-bs-profile-invalid-reason values)
                  :max-record-octets-above-the-poll-reply))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-invalid-reason)
                                  (fn-bs-pf fn-frame-values-okp
                                   fn-record-encoded-octets-ceiling)))))
