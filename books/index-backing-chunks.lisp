; Fixed physical chunks for leased index generations. PRF-1139.
; Tables use the existing page-store2048-u64 format. Catalog pages retain
;256 immutable row references. These are page sizes, never data limits.
; Directory/root ownership, funding and actual native registry correspondence
; are separate provider obligations. Copies target unpublished distinct chunks.
(in-package "ACL2")

(defstobj fn-ibp-table-page
  (fn-ibp-table-words :type (array (unsigned-byte 64) (2048)) :initially 0)
  (fn-ibp-table-id :type (integer 0 *) :initially 0)
  (fn-ibp-table-incarnation :type (integer 0 *) :initially 0)
  (fn-ibp-table-sealed :type (integer 0 1) :initially 0)
  :inline t)
(defstobj fn-ibp-table-page2
  (fn-ibp-table-words2 :type (array (unsigned-byte 64) (2048)) :initially 0)
  (fn-ibp-table2-id :type (integer 0 *) :initially 0)
  (fn-ibp-table2-incarnation :type (integer 0 *) :initially 0)
  (fn-ibp-table2-sealed :type (integer 0 1) :initially 0)
  :congruent-to fn-ibp-table-page :inline t)
(defstobj fn-ibp-row-page
  (fn-ibp-row-cells :type (array t (256)) :initially nil)
  (fn-ibp-row-id :type (integer 0 *) :initially 0)
  (fn-ibp-row-incarnation :type (integer 0 *) :initially 0)
  (fn-ibp-row-sealed :type (integer 0 1) :initially 0)
  :inline t)
(defstobj fn-ibp-row-page2
  (fn-ibp-row-cells2 :type (array t (256)) :initially nil)
  (fn-ibp-row2-id :type (integer 0 *) :initially 0)
  (fn-ibp-row2-incarnation :type (integer 0 *) :initially 0)
  (fn-ibp-row2-sealed :type (integer 0 1) :initially 0)
  :congruent-to fn-ibp-row-page :inline t)

(defun fn-ibp-table-initialize (id incarnation fn-ibp-table-page)
  (declare (xargs :stobjs fn-ibp-table-page :guard (and (posp id) (natp incarnation))))
  (if (not (and (equal (fn-ibp-table-id fn-ibp-table-page) 0)
                (equal (fn-ibp-table-incarnation fn-ibp-table-page) 0)
                (equal (fn-ibp-table-sealed fn-ibp-table-page) 0)))
      (mv :already-initialized fn-ibp-table-page)
    (let* ((fn-ibp-table-page (update-fn-ibp-table-id id fn-ibp-table-page))
           (fn-ibp-table-page (update-fn-ibp-table-incarnation incarnation fn-ibp-table-page)))
      (mv :initialized fn-ibp-table-page))))
(defun fn-ibp-table-seal (id incarnation fn-ibp-table-page)
  (declare (xargs :stobjs fn-ibp-table-page :guard (and (posp id) (natp incarnation))))
  (if (not (and (equal (fn-ibp-table-id fn-ibp-table-page) id)
                (equal (fn-ibp-table-incarnation fn-ibp-table-page) incarnation)
                (equal (fn-ibp-table-sealed fn-ibp-table-page) 0)))
      (mv :stale-chunk fn-ibp-table-page)
    (let ((fn-ibp-table-page (update-fn-ibp-table-sealed 1 fn-ibp-table-page)))
      (mv :sealed fn-ibp-table-page))))

(defun fn-ibp-row-initialize (id incarnation fn-ibp-row-page)
  (declare (xargs :stobjs fn-ibp-row-page :guard (and (posp id) (natp incarnation))))
  (if (not (and (equal (fn-ibp-row-id fn-ibp-row-page) 0)
                (equal (fn-ibp-row-incarnation fn-ibp-row-page) 0)
                (equal (fn-ibp-row-sealed fn-ibp-row-page) 0)))
      (mv :already-initialized fn-ibp-row-page)
    (let* ((fn-ibp-row-page (update-fn-ibp-row-id id fn-ibp-row-page))
           (fn-ibp-row-page (update-fn-ibp-row-incarnation incarnation fn-ibp-row-page)))
      (mv :initialized fn-ibp-row-page))))
(defun fn-ibp-row-seal (id incarnation fn-ibp-row-page)
  (declare (xargs :stobjs fn-ibp-row-page :guard (and (posp id) (natp incarnation))))
  (if (not (and (equal (fn-ibp-row-id fn-ibp-row-page) id)
                (equal (fn-ibp-row-incarnation fn-ibp-row-page) incarnation)
                (equal (fn-ibp-row-sealed fn-ibp-row-page) 0)))
      (mv :stale-chunk fn-ibp-row-page)
    (let ((fn-ibp-row-page (update-fn-ibp-row-sealed 1 fn-ibp-row-page)))
      (mv :sealed fn-ibp-row-page))))

(defun fn-ibp-table-word (slot fn-ibp-table-page)
  (declare (xargs :stobjs fn-ibp-table-page :guard (and (natp slot) (< slot 2048))))
  (fn-ibp-table-wordsi slot fn-ibp-table-page))
(defun fn-ibp-table-set (slot value fn-ibp-table-page)
  (declare (xargs :stobjs fn-ibp-table-page
                  :guard (and (natp slot) (< slot 2048) (unsigned-byte-p 64 value)
                              (equal (fn-ibp-table-sealed fn-ibp-table-page) 0))))
  (update-fn-ibp-table-wordsi slot value fn-ibp-table-page))
(defun fn-ibp-row (slot fn-ibp-row-page)
  (declare (xargs :stobjs fn-ibp-row-page :guard (and (natp slot) (< slot 256))))
  (fn-ibp-row-cellsi slot fn-ibp-row-page))
(defun fn-ibp-row-set (slot row fn-ibp-row-page)
  (declare (xargs :stobjs fn-ibp-row-page :guard (and (natp slot) (< slot 256)
                              (equal (fn-ibp-row-sealed fn-ibp-row-page) 0))))
  (update-fn-ibp-row-cellsi slot row fn-ibp-row-page))

(local (defthm fn-ibp-table-wordsp-nth
  (implies (and (fn-ibp-table-wordsp xs) (natp i) (< i (len xs)))
           (unsigned-byte-p 64 (nth i xs)))
  :hints (("Goal" :induct (nth i xs) :in-theory (enable fn-ibp-table-wordsp)))))

(defthm fn-ibp-table-word-u64
  (implies (and (fn-ibp-table-pagep fn-ibp-table-page)
                (natp slot) (< slot 2048))
           (unsigned-byte-p 64 (fn-ibp-table-word slot fn-ibp-table-page)))
  :hints (("Goal" :in-theory (enable fn-ibp-table-pagep fn-ibp-table-wordsi))))

(defun fn-ibp-table-copy-span (start count fn-ibp-table-page fn-ibp-table-page2)
  (declare (xargs :stobjs (fn-ibp-table-page fn-ibp-table-page2)
                  :measure (nfix count)
                  :guard-hints (("Goal" :use ((:instance fn-ibp-table-word-u64 (slot start)))
                    :in-theory (disable fn-ibp-table-word-u64 fn-ibp-table-word fn-ibp-table-wordsi fn-ibp-table-pagep)))
                  :guard (and (natp start) (natp count) (<= count 64)
                              (<= (+ start count) 2048)
                              (equal (fn-ibp-table2-sealed fn-ibp-table-page2) 0))))
  (if (zp count) fn-ibp-table-page2
    (let ((fn-ibp-table-page2
           (update-fn-ibp-table-wordsi start
             (fn-ibp-table-word start fn-ibp-table-page) fn-ibp-table-page2)))
      (fn-ibp-table-copy-span (+ 1 start) (- count 1)
                              fn-ibp-table-page fn-ibp-table-page2))))
(defun fn-ibp-row-copy-span (start count fn-ibp-row-page fn-ibp-row-page2)
  (declare (xargs :stobjs (fn-ibp-row-page fn-ibp-row-page2)
                  :measure (nfix count)
                  :guard (and (natp start) (natp count) (<= count 32)
                              (<= (+ start count) 256)
                              (equal (fn-ibp-row2-sealed fn-ibp-row-page2) 0))))
  (if (zp count) fn-ibp-row-page2
    (let ((fn-ibp-row-page2
           (update-fn-ibp-row-cellsi start
             (fn-ibp-row start fn-ibp-row-page) fn-ibp-row-page2)))
      (fn-ibp-row-copy-span (+ 1 start) (- count 1)
                            fn-ibp-row-page fn-ibp-row-page2))))

(local (defthm fn-ibp-nth-update
  (implies (and (natp i) (natp j))
           (equal (nth j (update-nth i v xs))
                  (if (equal i j) v (nth j xs))))))

; Whole output/effect boundary: precisely this span changes; source and
;every other destination cell retain their original values. No list of words
;or rows is built by the executable copy.
(defthm fn-ibp-table-copy-span-exact-output
  (implies (and (natp start) (natp count) (natp j))
    (equal (nth j (nth 0 (fn-ibp-table-copy-span start count
                           fn-ibp-table-page fn-ibp-table-page2)))
           (if (and (<= start j) (< j (+ start count)))
               (nth j (nth 0 fn-ibp-table-page))
             (nth j (nth 0 fn-ibp-table-page2)))))
  :hints (("Goal" :induct (fn-ibp-table-copy-span start count fn-ibp-table-page fn-ibp-table-page2)
           :in-theory (enable update-fn-ibp-table-wordsi))))
(defthm fn-ibp-row-copy-span-exact-output
  (implies (and (natp start) (natp count) (natp j))
    (equal (nth j (nth 0 (fn-ibp-row-copy-span start count
                           fn-ibp-row-page fn-ibp-row-page2)))
           (if (and (<= start j) (< j (+ start count)))
               (nth j (nth 0 fn-ibp-row-page))
             (nth j (nth 0 fn-ibp-row-page2)))))
  :hints (("Goal" :induct (fn-ibp-row-copy-span start count fn-ibp-row-page fn-ibp-row-page2)
           :in-theory (enable update-fn-ibp-row-cellsi))))
