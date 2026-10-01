; Registered-token caller for the first bounded full-report fold. Internal
; source-specific BODY owns each quantum; this is not an installed callback.
(in-package "ACL2")
(include-book "owner-report-capture")
(include-book "owner-report-count")

(defun fn-owner-report-count-tick (token fuel state)
  (declare (xargs :stobjs state :guard (natp fuel)
                  :guard-hints (("Goal" :in-theory
                    (disable fn-orc-current fn-orc-keep-progress-internal
                             fn-orc-count-run fn-orc-count-one)))))
  (mv-let (word job) (fn-orc-current token state)
    (if (not (and (eq word :report-current)
                  (true-listp job) (fn-orc-countp (nth 6 job))))
        (mv (if (eq word :report-current) :report-stage-unavailable word) nil state)
      (mv-let (count-word cursor) (fn-orc-count-run fuel (nth 6 job))
        (mv-let (kept state) (fn-orc-keep-progress-internal token cursor state)
          (if (not (eq kept :report-progress)) (mv kept nil state)
            (mv (if (eq count-word :counted) :report-counted :yield)
                (if (eq count-word :counted) (nth 2 cursor) nil) state)))))))
