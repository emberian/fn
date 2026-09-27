; fn: the open's recovery input bound, derived from the profile so that every
; history the profile admits reopens (lane compact-arena, 2026-09-27; the
; coordinator's addition to PKT-686).
;
; The defect.  Every open sums the committed transaction files' record octets
; and refuses the store past a bound (host/native/io.lisp
; `fnn-durable-records', `fnn-read-suffix-records': "transaction recovery
; input exceeds configured bound").  The bound was H, the profile's history
; bound (books/store-profile-facts.lisp `fn-profile-replay-within-boundp').
; Since the records flip a retained article row costs its PAYLOAD's octets in
; the history budget (books/store-budget-stored.lisp: the stored octets),
; while its transaction file holds the whole encoded record: payload,
; Message-ID, groups, the fixed fields.  So a store the budget admitted up to
; H holds more than H octets of records, and the open refused it at every
; heap size (a small-preset store of 3,500 x 2 KiB posts, lane
; reservation-after-flip; the post-alloc capacity vector's full store).
;
; The bound.  A record the runtime produces for an article of P payload
; octets and G groups encodes within `fn-record-encoded-octets-ceiling' P G =
; P + (5 + 256) G + 1,083 (books/records-shape.lisp; the narrow length bound
; of records-seam).  With at most T records (max-transactions) of at most G
; groups (max-groups-per-article), each costing at least its payload in the
; budget, the records' encoded octets are within
;
;     B = H + T x (fn-record-encoded-octets-ceiling 0 G)
;
; `fn-srb-replay-input-bound'.  KEYSTONE fn-srb-admitted-history-is-within-
; the-bound: for any history of records (ENCODED their encoded lengths,
; STORED their budget octets, pointwise) of at most T records with STORED
; summing to at most H and each encoding within its stored octets plus the
; per-record overhead, the encoded octets sum to at most B.  The host-called
; subject is `fn-srb-replay-within-boundp' (host/store-host.lisp
; `fn-store-profile-replay-within-bound', from io.lisp `fnn-durable-records'
; and `fnn-read-suffix-records'); `fn-srb-within-h-is-within-the-bound':
; everything the old bound accepted, this one accepts.
;
; Scope: that a committed article's encoding is within its payload plus the
; overhead is records-seam's narrow length bound for the records the POST
; path produces (`fn-sbud-article-figure-bounds-the-record'); every other
; row's budget octets are its whole encoding (store-budget
; `fn-sbud-row-octets'), so its overhead term is 0.  The bound is a
; validity bound on the input, not a data ceiling: a store within it is
; opened, one past it was not written by this profile.
(in-package "ACL2")
(include-book "store-profile-facts")
(include-book "records-shape")

(local
 (defthm fn-srb-profile-fields-natp
   (and (natp (fn-bs-profile-max-history-octets profile))
        (natp (fn-bs-profile-max-transactions profile))
        (natp (fn-bs-profile-max-groups-per-article profile)))
   :rule-classes ((:type-prescription :corollary (natp (fn-bs-profile-max-history-octets profile)))
                  (:type-prescription :corollary (natp (fn-bs-profile-max-transactions profile)))
                  (:type-prescription :corollary
                                      (natp (fn-bs-profile-max-groups-per-article profile))))
   :hints (("Goal" :in-theory (disable fn-bs-profile-of)))))

(local (in-theory (disable fn-bs-profile-admittedp fn-bs-profile-max-history-octets
                           fn-bs-profile-max-transactions
                           fn-bs-profile-max-groups-per-article)))

(defun fn-srb-record-overhead (profile)
  (declare (xargs :guard t))
  (fn-record-encoded-octets-ceiling
   0 (nfix (fn-bs-profile-max-groups-per-article profile))))

(defthm fn-srb-record-overhead-natp
  (natp (fn-srb-record-overhead profile))
  :rule-classes :type-prescription)

(defun fn-srb-replay-input-bound (profile)
  (declare (xargs :guard t))
  (+ (nfix (fn-bs-profile-max-history-octets profile))
     (* (nfix (fn-bs-profile-max-transactions profile))
        (fn-srb-record-overhead profile))))

(defthm fn-srb-replay-input-bound-natp
  (natp (fn-srb-replay-input-bound profile))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn-bs-profile-max-history-octets
                                      fn-bs-profile-max-transactions
                                      fn-bs-profile-max-groups-per-article))))

(defthm fn-srb-h-within-the-bound
  (<= (nfix (fn-bs-profile-max-history-octets profile))
      (fn-srb-replay-input-bound profile))
  :rule-classes :linear)

(in-theory (disable fn-srb-replay-input-bound))

(defun fn-srb-replay-within-boundp (profile aggregate)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-bs-profile-admittedp
                                                            fn-srb-replay-input-bound)))))
  (and (fn-bs-profile-admittedp profile)
       (natp aggregate)
       (<= aggregate (fn-srb-replay-input-bound profile))))

; Everything the bound H accepted, the derived bound accepts.
(defthm fn-srb-within-h-is-within-the-bound
  (implies (fn-profile-replay-within-boundp profile aggregate)
           (fn-srb-replay-within-boundp profile aggregate))
  :hints (("Goal" :in-theory (enable fn-profile-replay-within-boundp))
          ("Goal'" :use fn-srb-h-within-the-bound)))

; -----------------------------------------------------------------------------
; Every admitted history is within the bound.

(defun fn-srb-sum (xs)
  (declare (xargs :guard t))
  (if (consp xs) (+ (nfix (car xs)) (fn-srb-sum (cdr xs))) 0))

; Each encoding within its stored octets plus the per-record overhead O.
(defun fn-srb-pointwise-within (encoded stored o)
  (declare (xargs :guard t))
  (if (consp encoded)
      (and (consp stored)
           (<= (nfix (car encoded)) (+ (nfix (car stored)) (nfix o)))
           (fn-srb-pointwise-within (cdr encoded) (cdr stored) o))
    t))

(local
 (defthm fn-srb-sum-within
   (implies (fn-srb-pointwise-within encoded stored o)
            (<= (fn-srb-sum encoded)
                (+ (fn-srb-sum stored) (* (len encoded) (nfix o)))))
   :rule-classes :linear))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-srb-times-monotone
   (implies (and (natp a) (natp b) (natp c) (<= a b))
            (<= (* a c) (* b c)))
   :rule-classes nil))

; KEYSTONE.
(defthm fn-srb-admitted-history-is-within-the-bound
  (implies (and (fn-bs-profile-admittedp profile)
                (<= (len encoded) (fn-bs-profile-max-transactions profile))
                (<= (fn-srb-sum stored) (fn-bs-profile-max-history-octets profile))
                (fn-srb-pointwise-within encoded stored (fn-srb-record-overhead profile)))
           (fn-srb-replay-within-boundp profile (fn-srb-sum encoded)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-srb-sum-within (o (fn-srb-record-overhead profile)))
                 (:instance fn-srb-times-monotone (a (len encoded))
                            (b (fn-bs-profile-max-transactions profile))
                            (c (fn-srb-record-overhead profile))))
           :in-theory (e/d (fn-srb-replay-input-bound)
                           (fn-srb-sum-within fn-srb-record-overhead)))))
