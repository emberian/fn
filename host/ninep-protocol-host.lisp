; Additive guarded native dispatch boundary, not listener/runtime activation.
(in-package "ACL2")
(include-book "../books/ninep-header")

(defun fn-ninep-frame-prefix (begin end msize fn-octets state)
 (declare (xargs :stobjs (fn-octets state)
                 :guard (and (natp begin) (natp end) (<= begin end)
                             (<= end (fn-octets-len fn-octets)))))
 (let ((header (fn-9p-header-at begin end msize fn-octets)))
  (mv header (fn-9p-prefix-action header end) state)))

(defthm fn-ninep-frame-prefix-is-core-wire-boundary
 (and (equal (mv-nth 0 (fn-ninep-frame-prefix begin end msize fn-octets state))
             (fn-9p-header-reference begin end msize fn-octets))
      (equal (mv-nth 1 (fn-ninep-frame-prefix begin end msize fn-octets state))
             (fn-9p-prefix-action
              (fn-9p-header-reference begin end msize fn-octets) end))
      (equal (mv-nth 2 (fn-ninep-frame-prefix begin end msize fn-octets state)) state))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-ninep-frame-prefix)
               (fn-9p-header-at fn-9p-header-reference fn-9p-prefix-action)))))

(include-book "../books/ninep-fields")

(defun fn-ninep-request-step (cursor fn-octets state)
 (declare (xargs :stobjs (fn-octets state)
                 :guard (and (fn-9p-fields-ready-p cursor)
                             (<= (nth 4 cursor) (fn-octets-len fn-octets)))))
 (mv-let (word next) (fn-9p-fields-step cursor fn-octets)
  (mv word next state)))

(defthm fn-ninep-request-step-is-core-wire-boundary
 (and (equal (mv-nth 0 (fn-ninep-request-step cursor fn-octets state))
             (mv-nth 0 (fn-9p-fields-step cursor fn-octets)))
      (equal (mv-nth 1 (fn-ninep-request-step cursor fn-octets state))
             (mv-nth 1 (fn-9p-fields-step cursor fn-octets)))
      (equal (mv-nth 2 (fn-ninep-request-step cursor fn-octets state)) state))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-ninep-request-step) (fn-9p-fields-step)))))
