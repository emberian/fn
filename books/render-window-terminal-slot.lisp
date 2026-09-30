; Guarded internal CURRENT-slot source component. Unhooked pending actual context10,
; operation allowance, complete binding publisher cohort and epilogue fence.
(in-package "ACL2")
(include-book "index-backing-provider")
(include-book "render-window-terminal-cursor")
(include-book "page-read-binding-revision")

(defun fn-prwt-root-query (root)
  (declare (xargs :guard t))
  (if (eq (fn-prl-nth 0 root) :window-terminal)
      (fn-prl-nth 4 (fn-prl-nth 9 root))
    (fn-prl-nth 4 root)))

(defthm fn-prwt-fixed-width-is-proper-list
  (implies (fn-omk-widthp x n) (true-listp x))
  :hints (("Goal" :induct (fn-omk-widthp x n)
                  :in-theory (enable fn-omk-widthp))))

; No supplied snapshot row/root/cursor. The full query token is an internal
; parameter selected by the RH parent; actual child registration checks it.
(defun fn-prwt-slot-step (token fuel fn-ibp-query-segment fn-page-read-pool)
  (declare (xargs :stobjs (fn-ibp-query-segment fn-page-read-pool)
                  :guard (natp fuel)
                  :guard-hints
                  (("Goal" :in-theory
                    (e/d (fn-ibp-query-slot-livep fn-ibp-query-tokenp)
                         (fn-page-read-poolp fn-ibp-query-segmentp
                          fn-ibp-qs-inputsi fn-ibp-qs-controlsi
                          fn-owner-page-read-binding-revision
                          fn-prwt-root-query fn-prwt-run fn-omk-widthp))))))
  (cond
   ((not (fn-ibp-query-slot-livep token fn-ibp-query-segment))
    (mv :stale nil fuel fn-ibp-query-segment fn-page-read-pool))
   ((zp fuel)
    (mv :yield nil fuel fn-ibp-query-segment fn-page-read-pool))
   (t
    (let* ((slot (nth 3 token))
           (context (fn-ibp-qs-inputsi slot fn-ibp-query-segment))
           (control (fn-ibp-qs-controlsi slot fn-ibp-query-segment))
           (custody (fn-prl-nth 9 context))
           (root (fn-prl-nth 11 custody)))
      (cond
       ((not (and (fn-omk-widthp context 10)
                  (member-eq (fn-prl-nth 0 context)
                             '(:reader-context :incoming-query-context))
                  (eq (fn-prl-nth 0 control) :fn-ibr)
                  (equal (fn-prl-nth 1 control) (fn-prl-nth 1 token))
                  (equal (fn-prl-nth 2 control) (fn-prl-nth 4 token))
                  (fn-omk-widthp custody 12)
                  (eq (fn-prl-nth 0 custody) :receiver-custody)))
        (mv :unavailable nil fuel fn-ibp-query-segment fn-page-read-pool))
       ((not (equal (fn-prwt-root-query root) token))
        (mv :stale nil fuel fn-ibp-query-segment fn-page-read-pool))
       ((not (and (fn-omk-widthp root 12)
                  (eq (fn-prl-nth 0 root) :window-terminal)))
        ; Only the actual epilogue constructor may install a scan cursor from
        ; root7. The scan entry never manufactures that observation itself.
        (mv :unavailable nil fuel fn-ibp-query-segment fn-page-read-pool))
       ((not (equal (fn-prl-nth 2 root)
                    (fn-owner-page-read-binding-revision fn-page-read-pool)))
        (mv :stale nil fuel fn-ibp-query-segment fn-page-read-pool))
       ((eq (fn-prl-nth 8 root) :commit-ready)
        (mv :commit-unavailable nil fuel fn-ibp-query-segment fn-page-read-pool))
       ((not (member-eq (fn-prl-nth 8 root) '(:scan :rebuild)))
        (mv :unavailable nil fuel fn-ibp-query-segment fn-page-read-pool))
       (t
        (mv-let (cursor left) (fn-prwt-run root (- fuel 1))
          (let* ((custody1 (update-nth 11 cursor custody))
                 (context1 (update-nth 9 custody1 context))
                 (fn-ibp-query-segment
                  (update-fn-ibp-qs-inputsi slot context1 fn-ibp-query-segment)))
            (mv (if (eq (fn-prl-nth 8 cursor) :commit-ready)
                    :commit-unavailable :yield)
                nil left fn-ibp-query-segment fn-page-read-pool)))))))))

; No pool mutation, refund, input clearing or terminal receipt occurs here.
; Original and partial reconstruction roots persist in actual CURRENT input.
; Allocation authority is the installed source BODY of the actual caller,
; not FUEL, :active mode, receipt shape, or the query's retained grant.
