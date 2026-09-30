; Internal chunk effects. Registered page-owner/join/fresh-ID authority is
; supplied only by the provider's token-only transition, not these scalars.
; Recycled capacity remains charged U; no GC or allocation refund occurs.
(in-package "ACL2")
(include-book "index-backing-chunks")
(defun fn-ibp-table-restamp (old-id old-incarnation new-id new-incarnation fn-ibp-table-page)
  (declare (xargs :stobjs fn-ibp-table-page
                  :guard (and (posp old-id) (natp old-incarnation)
                              (posp new-id) (natp new-incarnation))))
  (if (not (and (equal (fn-ibp-table-id fn-ibp-table-page) old-id)
                (equal (fn-ibp-table-incarnation fn-ibp-table-page) old-incarnation)
                (not (equal old-id new-id))))
      (mv :stale-chunk fn-ibp-table-page)
    (let* ((fn-ibp-table-page (update-fn-ibp-table-sealed 0 fn-ibp-table-page))
           (fn-ibp-table-page (update-fn-ibp-table-id new-id fn-ibp-table-page))
           (fn-ibp-table-page (update-fn-ibp-table-incarnation new-incarnation fn-ibp-table-page)))
      (mv :restamped fn-ibp-table-page))))
(defun fn-ibp-row-restamp (old-id old-incarnation new-id new-incarnation fn-ibp-row-page)
  (declare (xargs :stobjs fn-ibp-row-page
                  :guard (and (posp old-id) (natp old-incarnation)
                              (posp new-id) (natp new-incarnation))))
  (if (not (and (equal (fn-ibp-row-id fn-ibp-row-page) old-id)
                (equal (fn-ibp-row-incarnation fn-ibp-row-page) old-incarnation)
                (not (equal old-id new-id))))
      (mv :stale-chunk fn-ibp-row-page)
    (let* ((fn-ibp-row-page (update-fn-ibp-row-sealed 0 fn-ibp-row-page))
           (fn-ibp-row-page (update-fn-ibp-row-id new-id fn-ibp-row-page))
           (fn-ibp-row-page (update-fn-ibp-row-incarnation new-incarnation fn-ibp-row-page)))
      (mv :restamped fn-ibp-row-page))))
(defun fn-ibp-table-clear-span (start count fn-ibp-table-page)
  (declare (xargs :stobjs fn-ibp-table-page :measure (nfix count)
                  :guard (and (natp start) (natp count) (<= start 2048)
                              (<= count (- 2048 start))
                              (equal (fn-ibp-table-sealed fn-ibp-table-page) 0))))
  (if (zp count) fn-ibp-table-page
    (let ((fn-ibp-table-page (fn-ibp-table-set start 0 fn-ibp-table-page)))
      (fn-ibp-table-clear-span (+ 1 start) (- count 1) fn-ibp-table-page))))
(defun fn-ibp-row-clear-span (start count fn-ibp-row-page)
  (declare (xargs :stobjs fn-ibp-row-page :measure (nfix count)
                  :guard (and (natp start) (natp count) (<= start 256)
                              (<= count (- 256 start))
                              (equal (fn-ibp-row-sealed fn-ibp-row-page) 0))))
  (if (zp count) fn-ibp-row-page
    (let ((fn-ibp-row-page (fn-ibp-row-set start nil fn-ibp-row-page)))
      (fn-ibp-row-clear-span (+ 1 start) (- count 1) fn-ibp-row-page))))
(verify-guards fn-ibp-table-restamp)
(verify-guards fn-ibp-row-restamp)
(verify-guards fn-ibp-table-clear-span)
(verify-guards fn-ibp-row-clear-span)

(defun fn-ibp-clear-span-model (start count blank cells)
  (declare (xargs :guard (and (natp start) (natp count) (true-listp cells))
                  :measure (nfix count)))
  (if (zp count) cells
    (fn-ibp-clear-span-model (+ 1 start) (- count 1) blank
                             (update-nth start blank cells))))
(defthm fn-ibp-table-clear-span-refines-complete-chunk
  (equal (fn-ibp-table-clear-span start count fn-ibp-table-page)
         (if (zp count) fn-ibp-table-page
           (update-nth 0 (fn-ibp-clear-span-model start count 0 (nth 0 fn-ibp-table-page))
                       fn-ibp-table-page)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ibp-table-clear-span start count fn-ibp-table-page)
           :in-theory (enable fn-ibp-table-clear-span fn-ibp-table-set
                              update-fn-ibp-table-wordsi fn-ibp-clear-span-model))))
(defthm fn-ibp-row-clear-span-refines-complete-chunk
  (equal (fn-ibp-row-clear-span start count fn-ibp-row-page)
         (if (zp count) fn-ibp-row-page
           (update-nth 0 (fn-ibp-clear-span-model start count nil (nth 0 fn-ibp-row-page))
                       fn-ibp-row-page)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ibp-row-clear-span start count fn-ibp-row-page)
           :in-theory (enable fn-ibp-row-clear-span fn-ibp-row-set
                              update-fn-ibp-row-cellsi fn-ibp-clear-span-model))))
