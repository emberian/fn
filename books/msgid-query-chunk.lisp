; Internal compiled page reader. The operational provider selects the exact
; borrowed child with stobj-let; this helper is never a host dispatch export.
(in-package "ACL2")
(include-book "index-backing-chunks")
(include-book "msgid-query-page")
(include-book "msgid-query-state")

(defun fn-miq-chunk-next (tag cursor fuel pages page-index fn-ibp-table-page)
  (declare (xargs :stobjs fn-ibp-table-page :measure (nfix fuel)
                  :guard (and (natp tag) (fn-mpr-cursorp cursor pages)
                              (natp page-index) (< page-index pages)
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (cond ((equal (nth 1 cursor) 0) (mv :done cursor nil fuel))
        ((zp fuel) (mv :yield cursor nil 0))
        ((not (equal (nth 0 cursor) page-index)) (mv :next-page cursor nil fuel))
        (t
         (let* ((slot (nth 2 cursor))
                (found-tag (fn-ibp-table-word slot fn-ibp-table-page))
                (next (fn-mpr-advance cursor pages)))
           (cond ((equal found-tag 0) (mv :done cursor nil (- fuel 1)))
                 ((equal found-tag tag)
                  (let ((encoded-seq (fn-ibp-table-word (+ 1024 slot) fn-ibp-table-page)))
                    (if (zp encoded-seq)
                        (mv :recovery-required cursor nil (- fuel 1))
                      (mv :candidate next (- encoded-seq 1) (- fuel 1)))))
                 (t (fn-miq-chunk-next tag next (- fuel 1) pages page-index fn-ibp-table-page)))))))

(verify-guards fn-miq-chunk-next
  :hints (("Goal" :use ((:instance fn-ibp-table-word-u64
                                   (slot (+ 1024 (nth 2 cursor)))))
           :in-theory (e/d (fn-mpr-cursorp)
                            (fn-ibp-table-pagep fn-ibp-table-word
                             fn-ibp-table-wordsi fn-ibp-table-word-u64)))))

(defthm fn-miq-chunk-word-is-flat
  (implies (and (fn-ibp-table-pagep fn-ibp-table-page)
                (natp slot) (< slot 2048))
           (equal (fn-ibp-table-word slot fn-ibp-table-page)
                  (nfix (nth slot (nth 0 fn-ibp-table-page)))))
  :hints (("Goal" :use ((:instance fn-ibp-table-word-u64))
           :in-theory (e/d (fn-ibp-table-word fn-ibp-table-wordsi)
                            (fn-ibp-table-pagep fn-ibp-table-word-u64)))))

(defthm fn-miq-chunk-tag-is-page-tag
  (implies (and (fn-ibp-table-pagep fn-ibp-table-page)
                (natp slot) (< slot 1024))
           (equal (fn-ibp-table-word slot fn-ibp-table-page)
                  (fn-mpl-tag-at 0 slot (nth 0 fn-ibp-table-page))))
  :hints (("Goal" :in-theory (e/d (fn-mpl-tag-at fn-mpxt-slot)
                            (fn-ibp-table-word fn-ibp-table-wordsi fn-ibp-table-pagep)))))

(defthm fn-miq-chunk-seq-is-page-seq
  (implies (and (fn-ibp-table-pagep fn-ibp-table-page)
                (natp slot) (< slot 1024))
           (equal (fn-ibp-table-word (+ 1024 slot) fn-ibp-table-page)
                  (fn-mpl-seq-at 0 slot (nth 0 fn-ibp-table-page))))
  :hints (("Goal" :in-theory (e/d (fn-mpl-seq-at fn-mpxt-slot)
                            (fn-ibp-table-word fn-ibp-table-wordsi fn-ibp-table-pagep)))))

(defthm fn-miq-chunk-next-is-page-layout-step
  (implies (and (fn-ibp-table-pagep fn-ibp-table-page)
                (fn-mpr-cursorp cursor pages))
           (equal (fn-miq-chunk-next tag cursor fuel pages page-index fn-ibp-table-page)
                  (fn-mpl-page-next tag cursor fuel pages page-index
                                    (nth 0 fn-ibp-table-page))))
  :hints (("Goal" :induct (fn-miq-chunk-next tag cursor fuel pages page-index fn-ibp-table-page)
           :in-theory (e/d (fn-miq-chunk-next fn-mpl-page-next)
                            (fn-mpl-tag-at fn-mpl-seq-at fn-mpr-cursorp fn-mpr-advance
                             fn-ibp-table-word fn-ibp-table-wordsi fn-ibp-table-pagep)))))

(defun fn-miq-page-next (query fuel page-index fn-ibp-table-page)
  (declare (xargs :stobjs fn-ibp-table-page
                  :guard (and (equal (fn-miq-phase query) :probing)
                              (null (fn-miq-pending query))
                              (equal (fn-ibp-table-sealed fn-ibp-table-page) 1)
                              (posp (fn-ibp-table-id fn-ibp-table-page))
                              (natp (fn-miq-tag query))
                              (fn-mpr-cursorp (fn-miq-cursor query) (fn-miq-pages query))
                              (natp page-index) (< page-index (fn-miq-pages query))
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))))
  (mv-let (status cursor candidate fuel-left)
    (fn-miq-chunk-next (fn-miq-tag query) (fn-miq-cursor query) fuel
                       (fn-miq-pages query) page-index fn-ibp-table-page)
    (let ((phase (cond ((equal status :candidate) :candidate)
                       ((equal status :done) :done)
                       ((equal status :recovery-required) :recovery-required)
                       (t :probing))))
      (mv status (fn-miq-with-progress query cursor candidate (fn-miq-best query) phase)
          candidate fuel-left))))

(in-theory (disable fn-miq-chunk-next fn-miq-page-next))

(defun fn-miw-chunk-place (tag seq cursor fuel pages page-index fn-ibp-table-page)
  (declare (xargs :stobjs fn-ibp-table-page :measure (nfix fuel)
                  :guard (and (posp tag) (unsigned-byte-p 64 tag)
                              (natp seq) (unsigned-byte-p 64 (+ 1 seq))
                              (fn-mpr-cursorp cursor pages)
                              (natp page-index) (< page-index pages)
                              (equal (fn-ibp-table-sealed fn-ibp-table-page) 0)
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (cond ((equal (nth 1 cursor) 0) (mv :full cursor fuel fn-ibp-table-page))
        ((zp fuel) (mv :yield cursor 0 fn-ibp-table-page))
        ((not (equal (nth 0 cursor) page-index)) (mv :next-page cursor fuel fn-ibp-table-page))
        (t
         (let* ((slot (nth 2 cursor)) (next (fn-mpr-advance cursor pages)))
           (if (equal (fn-ibp-table-word slot fn-ibp-table-page) 0)
               (let* ((fn-ibp-table-page (fn-ibp-table-set slot tag fn-ibp-table-page))
                      (fn-ibp-table-page (fn-ibp-table-set (+ 1024 slot) (+ 1 seq) fn-ibp-table-page)))
                 (mv :placed next (- fuel 1) fn-ibp-table-page))
             (fn-miw-chunk-place tag seq next (- fuel 1) pages page-index fn-ibp-table-page))))))

(verify-guards fn-miw-chunk-place
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp fn-ibp-table-set
                                    fn-ibp-table-sealed update-fn-ibp-table-wordsi))))

(defthm fn-miw-chunk-place-is-page-layout-step
  (implies (and (fn-ibp-table-pagep fn-ibp-table-page)
                (fn-mpr-cursorp cursor pages))
           (let ((physical (fn-miw-chunk-place tag seq cursor fuel pages page-index fn-ibp-table-page))
                 (logical (fn-mpl-page-place tag seq cursor fuel pages page-index (nth 0 fn-ibp-table-page))))
             (and (equal (nth 0 physical) (nth 0 logical))
                  (equal (nth 1 physical) (nth 1 logical))
                  (equal (nth 2 physical) (nth 2 logical))
                  (equal (nth 0 (nth 3 physical)) (nth 3 logical)))))
  :hints (("Goal" :induct (fn-miw-chunk-place tag seq cursor fuel pages page-index fn-ibp-table-page)
           :in-theory (enable fn-miw-chunk-place fn-mpl-page-place fn-mpl-tag-at
                              fn-mpl-write-slot fn-mpxt-slot fn-ibp-table-word
                              fn-ibp-table-wordsi fn-ibp-table-pagep fn-ibp-table-set
                              update-fn-ibp-table-wordsi))))

(in-theory (disable fn-miw-chunk-place))

; Internal confirmation obtains both observations from this one provider-
; selected immutable row child. Neither observation crosses the host ABI.
(defun fn-miq-row-confirm (query ordinal fn-ibp-row-page)
  (declare (xargs :stobjs fn-ibp-row-page
                  :guard-hints (("Goal" :use ((:instance mod-bounded-by-modulus (x ordinal) (y 256)))
                                  :in-theory (disable mod fn-ibp-row-pagep)))
                  :guard (and (natp ordinal)
                              (equal (fn-ibp-row-sealed fn-ibp-row-page) 1)
                              (posp (fn-ibp-row-id fn-ibp-row-page)))))
  (let ((held (fn-ibp-row (mod ordinal 256) fn-ibp-row-page)))
    (fn-miq-confirm query ordinal (fn-record-sequence held) (fn-record-msgid held))))

(defthm fn-miq-row-confirm-same-retained-row-by-definition
  (implies (natp ordinal)
           (equal (fn-miq-row-confirm query ordinal fn-ibp-row-page)
                  (let ((held (nth (mod ordinal 256) (nth 0 fn-ibp-row-page))))
                    (fn-miq-confirm query ordinal (fn-record-sequence held)
                                    (fn-record-msgid held)))))
  :hints (("Goal" :in-theory (enable fn-miq-row-confirm fn-ibp-row fn-ibp-row-cellsi))))
(in-theory (disable fn-miq-row-confirm))
