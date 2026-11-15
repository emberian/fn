; Shared actual source-manifest packing and decoders. The D upload/cursor
; and recovery path and the C checkpoint retention walker use these same
; format codecs. Article admission/packing profile remains with D.
(in-package "ACL2")
(include-book "commit-format")
(fn2-book-layer :b)

(defconst *fn2-am-block-bytes* *fn2-commit-unit-bytes*)

(defconst *fn2-upload-payload-units* 3)
(defconst *fn2-upload-payload-bytes* (* *fn2-upload-payload-units* *fn2-commit-unit-bytes*))

(defun fn2-am-manifestp (total)
  (declare (xargs :guard t))
  (< *fn2-upload-payload-bytes* (nfix total)))
(in-theory (disable fn2-am-manifestp))

(defconst *fn2-am-header-max* (fn2-layout-max-size *fn2-format-source-manifest-header*))

(defconst *fn2-am-entry-max* (fn2-layout-max-size *fn2-format-source-manifest-entry*))

(defconst *fn2-am-entries-per-unit*
  (floor (- *fn2-commit-unit-bytes* *fn2-am-header-max*) *fn2-am-entry-max*))

(defconst *fn2-am-header-fields* *fn2-format-source-manifest-header-num-fields*)
(defconst *fn2-am-entry-fields* *fn2-format-source-manifest-entry-num-fields*)

(defun fn2-am-blocks (total)
  (declare (xargs :guard t))
  (ceiling (nfix total) *fn2-am-block-bytes*))
(defun fn2-am-units (total)
  (declare (xargs :guard t))
  (ceiling (fn2-am-blocks total) *fn2-am-entries-per-unit*))
(defthm fn2-am-units-natp (natp (fn2-am-units total)) :rule-classes :type-prescription)

(defun fn2-am-entry-at (off)
  (declare (xargs :guard t))
  (let* ((off (nfix off)) (room (- *fn2-commit-unit-bytes* (mod off *fn2-commit-unit-bytes*))))
    (if (< room *fn2-am-entry-max*) (+ off room) off)))
(defthm fn2-am-entry-at-natp (natp (fn2-am-entry-at off)) :rule-classes :type-prescription)
(defthm fn2-am-entry-at-bound (<= (nfix off) (fn2-am-entry-at off)) :rule-classes :linear)
(in-theory (disable fn2-am-blocks fn2-am-units fn2-am-entry-at))


;; The entry at OFF of SLOT GEN (at most END): (mv code next logical-offset
;; length unit epoch alloc fn2-fields), NEXT the octet after it. Fields at BASE.
(defun fn2-am-get-entry (base slot gen off end okind oslot ogen fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (if (not (and (natp base) (<= (+ base *fn2-am-entry-fields*) (fn2-fields-rows fn2-fields))))
      (mv :bounds 0 0 0 0 0 0 fn2-fields)
    (mv-let (code next fn2-fields)
      (fn2-format-source-manifest-entry-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool)
      (if (not (eq code :ok)) (mv (if (eq code :more) :bounds code) 0 0 0 0 0 0 fn2-fields)
        (mv :ok (nfix next)
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-logical-offset*) fn2-fields))
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-length*) fn2-fields))
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-block-physical-unit*) fn2-fields))
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-block-writer-epoch*) fn2-fields))
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-block-allocation*) fn2-fields))
            fn2-fields)))))
(fn2-fc-shape fn2-am-get-entry-shape
  (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 7)))
(defthm fn2-am-get-entry-naturals
  (and (natp (mv-nth 1 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 2 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 3 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 4 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 5 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 6 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))))
(in-theory (disable fn2-am-get-entry))

;; The header's length at OFF of SLOT GEN (its stored length checked against
;; TOTAL): (mv code next fn2-fields).
(defun fn2-am-get-header (base total slot gen off end okind oslot ogen fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (if (not (and (natp base) (<= (+ base *fn2-am-header-fields*) (fn2-fields-rows fn2-fields))))
      (mv :bounds 0 fn2-fields)
    (mv-let (code next fn2-fields)
      (fn2-format-source-manifest-header-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool)
      (cond ((not (eq code :ok)) (mv (if (eq code :more) :bounds code) 0 fn2-fields))
            ((not (and (equal (fn2-fields-value (+ base *fn2-format-source-manifest-header-field-source-length*) fn2-fields) total)
                       (equal (fn2-fields-value (+ base *fn2-format-source-manifest-header-field-block-size*) fn2-fields)
                              *fn2-am-block-bytes*)))
             (mv :bounds 0 fn2-fields))
            (t (mv :ok (nfix next) fn2-fields))))))
(fn2-fc-shape fn2-am-get-header-shape
  (fn2-am-get-header base total slot gen off end okind oslot ogen fn2-fields fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 2)))
(defthm fn2-am-get-header-natp
  (natp (mv-nth 1 (fn2-am-get-header base total slot gen off end okind oslot ogen fn2-fields fn2-pool)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-am-get-header))
