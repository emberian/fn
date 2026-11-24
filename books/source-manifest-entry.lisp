;; One authenticated manifest unit, decoded at a caller-owned field stripe.
;; This helper grants no authenticity: callers verify the complete location
;; unit against the retained location commitment before invoking it.
(in-package "ACL2")
(include-book "article-manifest")
(fn2-book-layer :d)

;; Keep offset normalization and field accessors opaque. The field row
;; count is already natural, so its NFIX does not need a case split.
(local (defthm fn2-source-manifest-entry-nfix-natp
  (implies (natp x) (equal (nfix x) x))))
(local (in-theory (disable floor nfix fn2-fields-rows fn2-fields-ref-slot
                            fn2-fields-ref-len fn2-fields-ref-off
                            fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp)))

(defun fn2-source-manifest-entry (base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
                 :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* ((prefix (nfix prefix))
       (mpos (nfix mpos))
       (u0 (* *fn2-commit-unit-bytes* (floor mpos *fn2-commit-unit-bytes*)))
       ((mv c at fn2-fields)
        (if (equal mpos 0)
            (mv-let (c h fn2-fields)
              (fn2-am-get-header base total lslot lgen prefix (+ prefix *fn2-commit-unit-bytes*) okind oslot ogen fn2-fields fn2-pool)
              (mv c (fn2-am-entry-at (nfix (- h prefix))) fn2-fields))
          (mv :ok mpos fn2-fields)))
       ((unless (and (eq c :ok) (<= u0 at) (< (- at u0) *fn2-commit-unit-bytes*))) (mv :bounds 0 0 0 0 0 0 0 0 fn2-fields))
       ((mv c next lo len unit epoch alloc fn2-fields)
        (fn2-am-get-entry base lslot lgen (+ prefix (- at u0)) (+ prefix *fn2-commit-unit-bytes*) okind oslot ogen fn2-fields fn2-pool))
       (h (+ (nfix base) *fn2-format-source-manifest-entry-field-block-expected-hash*))
       (cv (+ (nfix base) *fn2-format-source-manifest-entry-field-subtree-cv*))
       ((unless (and (eq c :ok) (< h (nfix (fn2-fields-rows fn2-fields))) (< cv (nfix (fn2-fields-rows fn2-fields)))
                     (equal (fn2-fields-ref-slot h fn2-fields) lslot) (equal (fn2-fields-ref-len h fn2-fields) 32)
                     (equal (fn2-fields-ref-slot cv fn2-fields) lslot) (equal (fn2-fields-ref-len cv fn2-fields) 32)))
        (mv :bounds 0 0 0 0 0 0 0 0 fn2-fields)))
    (mv :ok (fn2-am-entry-at (+ u0 (nfix (- next prefix)))) lo len unit epoch alloc
        (nfix (fn2-fields-ref-off h fn2-fields)) (nfix (fn2-fields-ref-off cv fn2-fields)) fn2-fields)))

(defthm fn2-source-manifest-entry-shape
 (implies (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  (let ((after (mv-nth 9 (fn2-source-manifest-entry base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool))))
   (and (fn2-fieldsp after) (fn2-fields-wfp after)
        (equal (fn2-fields-rows after) (fn2-fields-rows fn2-fields))))))
(defthm fn2-source-manifest-entry-naturals
 (and
  (natp (mv-nth 1 (fn2-source-manifest-entry base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool)))
  (natp (mv-nth 2 (fn2-source-manifest-entry base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool)))
  (natp (mv-nth 3 (fn2-source-manifest-entry base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool)))
  (natp (mv-nth 4 (fn2-source-manifest-entry base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool)))
  (natp (mv-nth 5 (fn2-source-manifest-entry base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool)))
  (natp (mv-nth 6 (fn2-source-manifest-entry base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool)))
  (natp (mv-nth 7 (fn2-source-manifest-entry base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool)))
  (natp (mv-nth 8 (fn2-source-manifest-entry base prefix lslot lgen mpos total okind oslot ogen fn2-fields fn2-pool)))
))
(in-theory (disable fn2-source-manifest-entry))
