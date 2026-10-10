; fn: the history gate charges an article at its own worst case (packet 1 of
; the Fable mandate section 12, decided 2026-09-25).
;
; Before this book the owner's history gate charged every article the fixed
; pre-reservation figure 65 538 (`*fn-store-article-publication-figure*'),
; and the served prepare (`fn-sbud-prepare') charged it nothing; an article
; past that figure could be admitted and push the committed history past H,
; after which every open refuses the store (`fn-profile-replay-within-boundp',
; host/native/io.lisp `fnn-durable-records').  Here an article is charged the
; record ceiling of its own payload length and group count at the widths the
; runtime produces, `fn-record-encoded-octets-ceiling' (records-shape): the
; bound on its real record (`fn-record-encode-narrow-length-bound'), and
; independent of the profile.
;
; Host calls: host/store-node-host.lisp `fn-store-sn-article-verdict' (the
; developer `store post', before the allocator reservation) and
; host/owner-host.lisp `fn-owner-prepare' / the buffered prepare, which pass
; `fn-sbud-article-budget' of the record to `fn-pcar-sbud-prepare' (equal to
; `fn-sbud-prepare', `fn-pcar-sbud-prepare-is-sbud-prepare').
(in-package "ACL2")
(include-book "owner-store-budget")
(include-book "store-profile-facts")

(local (in-theory (disable fn-sbud-budget-is-the-profile-admissibility
                           fn-bs-publication-admissiblep fn-bs-profile-validp
                           fn-bs-profile-of fn-bs-profile-admittedp
                           fn-bs-profile-max-history-octets)))

;; The record figure of one article of PAYLOAD-LENGTH octets in
;; GROUP-COUNT groups: its encoding's ceiling at the produced widths
;; (books/records-shape.lisp; the narrow length bound of records-seam).
(defun fn-sbud-article-figure (payload-length group-count)
  (declare (xargs :guard t))
  (fn-record-encoded-octets-ceiling (nfix payload-length) (nfix group-count)))

; The history octets one article is charged at the gate: its payload's, the
; charge of the held row it becomes.
(defun fn-sbud-article-gate-figure (payload-length group-count)
  (declare (xargs :guard t) (ignore group-count))
  (nfix payload-length))

(defun fn-sbud-article-verdict-at (profile used bytes-used payload-length
                                           group-count)
  "The publication verdict for one article: the count gate and the history
gate at the article's own figure."
  (declare (xargs :guard t))
  (if (and (fn-sbud-admitp (fn-sbud-budget profile :article) used)
           (fn-bs-history-admissiblep
            profile bytes-used
            (fn-sbud-article-gate-figure payload-length group-count)))
      :admissible
    :unaffordable))

(defun fn-sbud-article-budget (profile bytes-used payload-length group-count)
  "The transaction budget the served prepare is handed for one article: the
profile's article budget when the article's figure fits the history bound,
else 0 (so `fn-sbud-prepare' refuses and the owner answers :unaffordable)."
  (declare (xargs :guard t))
  (if (fn-bs-history-admissiblep
       profile bytes-used (fn-sbud-article-gate-figure payload-length group-count))
      (fn-sbud-budget profile :article)
    0))

(defun fn-sbud-article-budget-for (profile bytes-used record)
  (declare (xargs :guard t))
  (fn-sbud-article-budget profile bytes-used
                          (len (fn-record-payload record))
                          (len (fn-record-groups record))))

; The figure bounds every narrow record with at most those counts.
(defthm fn-sbud-article-figure-bounds-the-record
  (implies (and (not (fn-record-widep record))
                (<= (len (fn-record-payload record)) (nfix payload-length))
                (<= (len (fn-record-groups record)) (nfix group-count)))
           (<= (len (fn-record-encode record))
               (fn-sbud-article-figure payload-length group-count)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-record-encode-narrow-length-bound))
           :in-theory (e/d (fn-sbud-article-figure
                            fn-record-encoded-octets-ceiling)
                           (fn-record-encode-narrow-length-bound)))))

; KEYSTONE (an admitted article never pushes history past H).  If the article
; verdict at BYTES-USED committed octets admits an article of those counts,
; the committed octets plus its payload, the charge of the held row it
; becomes, are within H, whatever the record's width.
(defthm fn-sbud-article-verdict-keeps-history
  (implies (and (equal (fn-sbud-article-verdict-at profile used bytes-used
                                                   payload-length group-count)
                       :admissible)
                (<= (len (fn-record-payload record)) (nfix payload-length)))
           (fn-profile-replay-within-boundp
            profile (+ bytes-used (len (fn-record-payload record)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sbud-article-verdict-at
                                   fn-sbud-article-gate-figure
                                   fn-bs-history-admissiblep
                                   fn-profile-replay-within-boundp)
                                  (fn-sbud-admitp fn-sbud-budget
                                   fn-bs-profile-admittedp
                                   fn-bs-profile-max-history-octets)))))

; KEYSTONE for the served prepare (host/owner-host.lisp `fn-owner-prepare'):
; a prepare that staged under the article budget of the record it stages
; kept the history within H.
(defthm fn-sbud-prepare-under-article-budget-keeps-history
  (implies (not (equal (fn-sbud-prepare
                        oc record
                        (fn-sbud-article-budget-for profile bytes-used record))
                       oc))
           (fn-profile-replay-within-boundp
            profile (+ bytes-used (len (fn-record-payload record)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sbud-prepare fn-sbud-article-budget-for
                                   fn-sbud-article-budget fn-sbud-admitp
                                   fn-sbud-article-gate-figure
                                   fn-bs-history-admissiblep
                                   fn-profile-replay-within-boundp)
                                  (fn-opc-prepare fn-sbud-budget fn-sbud-used
                                   fn-bs-profile-admittedp
                                   fn-bs-profile-max-history-octets)))))

; PRF-126: the figure at the widths the producers now reach.  A record whose
; charge fits u32 is within the figure whatever the width of its sequence,
; txid, generation and stamp (`fn-record-encode-producer-length-bound',
; records-seam).
(defthm fn-sbud-article-figure-bounds-the-producer-record
  (implies (and (fn-record-uint32p (fn-record-charge record))
                (<= (len (fn-record-payload record)) (nfix payload-length))
                (<= (len (fn-record-groups record)) (nfix group-count)))
           (<= (len (fn-record-encode record))
               (fn-sbud-article-figure payload-length group-count)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-record-encode-producer-length-bound))
           :in-theory (e/d (fn-sbud-article-figure
                            fn-record-encoded-octets-ceiling)
                           (fn-record-uint32p)))))
