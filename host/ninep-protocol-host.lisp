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

(include-book "../books/ninep-version")

(defun fn-ninep-version-reply (server-msize cursor fn-octets state)
 (declare (xargs :stobjs (fn-octets state) :guard t))
 (mv (fn-9p-version-at server-msize cursor fn-octets) state))

(defthm fn-ninep-version-reply-is-core-wire-boundary
 (and (equal (mv-nth 0 (fn-ninep-version-reply server cursor fn-octets state))
             (fn-9p-version-at server cursor fn-octets))
      (equal (mv-nth 1 (fn-ninep-version-reply server cursor fn-octets state)) state))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-ninep-version-reply) (fn-9p-version-at)))))

(include-book "../books/ninep-group-directory-source")

; Internal borrowed cursor only. This does not issue a mounted source or
; expose a supplied root as an authenticated publication.
(defun fn-ninep-group-directory-step (tasks state)
 (declare (xargs :stobjs state :guard t))
 (mv-let (word entry next) (fn-9p-ge-step tasks)
  (mv word entry next state)))

(defthm fn-ninep-group-directory-step-preserves-source
 (and (equal (fn-9p-ge-remaining tasks)
             (append
              (if (equal (mv-nth 0 (fn-ninep-group-directory-step tasks state)) :group)
                  (list (mv-nth 1 (fn-ninep-group-directory-step tasks state))) nil)
              (fn-9p-ge-remaining
               (mv-nth 2 (fn-ninep-group-directory-step tasks state)))))
      (equal (mv-nth 3 (fn-ninep-group-directory-step tasks state)) state))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-ninep-group-directory-step)
               (fn-9p-ge-step fn-9p-ge-remaining))
          :use fn-9p-ge-step-preserves-ordered-directory)))

(include-book "../books/ninep-refusal")

(defun fn-ninep-refusal-reply (msize tag reason state)
 (declare (xargs :stobjs state :guard t))
 (mv (fn-9p-refusal-reply msize tag reason) state))

(defthm fn-ninep-refusal-reply-is-core-and-preserves-state
 (and (equal (mv-nth 0 (fn-ninep-refusal-reply msize tag reason state))
             (fn-9p-refusal-reply msize tag reason))
      (equal (mv-nth 1 (fn-ninep-refusal-reply msize tag reason state)) state)))
