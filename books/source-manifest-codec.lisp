; Actual ROOT source-manifest geometry and readers, shared below C and D.
; The physical 64KiB manifest threshold is unchanged.
(in-package "ACL2")
(include-book "commit-format")
(fn2-book-layer :b)

(defconst *fn2-am-block-bytes* *fn2-commit-unit-bytes*)

(defconst *fn2-am-header-max* (fn2-layout-max-size *fn2-format-source-manifest-header*))

(defconst *fn2-am-entry-max* (fn2-layout-max-size *fn2-format-source-manifest-entry*))

(defconst *fn2-am-entries-per-unit*
  (floor (- *fn2-commit-unit-bytes* *fn2-am-header-max*) *fn2-am-entry-max*))

(defconst *fn2-am-stored-max*
  (* *fn2-am-block-bytes* *fn2-am-entries-per-unit* *fn2-commit-write-resources*))

(assert-event (equal *fn2-am-stored-max* 380928))

(defconst *fn2-am-header-fields* *fn2-format-source-manifest-header-num-fields*)

(defconst *fn2-am-entry-fields* *fn2-format-source-manifest-entry-num-fields*)

(assert-event (equal *fn2-am-entries-per-unit* 31))

(assert-event (<= *fn2-am-entry-max* *fn2-commit-unit-bytes*))

(defun fn2-am-blocks (total)
  (declare (xargs :guard t))
  (ceiling (nfix total) *fn2-am-block-bytes*))

(defun fn2-am-units (total)
  (declare (xargs :guard t))
  (ceiling (fn2-am-blocks total) *fn2-am-entries-per-unit*))

(defthm fn2-am-units-natp (natp (fn2-am-units total)) :rule-classes :type-prescription)

(defun fn2-am-manifestp (total)
  (declare (xargs :guard t))
  (< *fn2-commit-extent-bytes* (nfix total)))

(defun fn2-am-fits (total)
  (declare (xargs :guard t))
  (<= (fn2-am-units total) *fn2-commit-write-resources*))

(assert-event (and (fn2-am-fits *fn2-am-stored-max*) (not (fn2-am-fits (+ 1 *fn2-am-stored-max*)))))

(defun fn2-am-entry-at (off)
  (declare (xargs :guard t))
  (let* ((off (nfix off)) (room (- *fn2-commit-unit-bytes* (mod off *fn2-commit-unit-bytes*))))
    (if (< room *fn2-am-entry-max*) (+ off room) off)))

(defthm fn2-am-entry-at-natp (natp (fn2-am-entry-at off)) :rule-classes :type-prescription)

(defthm fn2-am-entry-at-bound (<= (nfix off) (fn2-am-entry-at off)) :rule-classes :linear)

(in-theory (disable fn2-am-blocks fn2-am-units fn2-am-manifestp fn2-am-fits fn2-am-entry-at))

(local (in-theory (disable fn2-fields-rows fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-pool-rows)))

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
