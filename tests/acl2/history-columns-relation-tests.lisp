; Teeth for books/history-columns-relation.lisp (lane history-columns-3):
; R (fn-hist-of-storep) and the host's refresh before a read
; (KEYSTONE fn-hist-refresh-is-the-history; host/store-node-host.lisp
; fn-host-hist-sync calls fn-hist-refresh).  The stobj's logical value is a
; history list, so the witnesses are ground theorems over lists.
(in-package "ACL2")
(include-book "history-columns-tests")
(include-book "../../books/history-columns-relation")
(include-book "must-fail-checked")

; A files record holding the history (a, b, c) (history-columns-tests'
; events), and the snoc-list's count and rows the sync reads.
(defconst *hcr-hist* (list *hct-a* *hct-b* *hct-c*))
(defconst *hcr-files* (fn-sf-make :ready 3 nil *hcr-hist* nil nil nil 0))
(assert-event (equal (fn-sf-records *hcr-files*) *hcr-hist*))

; fn-hist-refresh-is-the-history, positive, both arms: a reload over a stobj
; holding another history, and a sync over a proper prefix.
(defthm hcr-refresh-reload-witness
  (let ((other (list *hct-c*)))
    (and (true-listp (fn-sf-records *hcr-files*))
         (not (fn-sf-prefixp other (fn-sf-records *hcr-files*)))
         (equal (fn-hist-refresh *hcr-files* t other) *hcr-hist*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist-refresh fn-hist-load fn-hist-load-events
                                     fn-hist-sync fn-hist-sync-aux fn-sf-prefixp))))
(defthm hcr-refresh-sync-witness
  (let ((prefix (list *hct-a*)))
    (and (true-listp (fn-sf-records *hcr-files*))
         (fn-sf-prefixp prefix (fn-sf-records *hcr-files*))
         (equal (fn-hist-refresh *hcr-files* nil prefix) *hcr-hist*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist-refresh fn-hist-sync fn-hist-sync-aux
                                     fn-sf-prefixp fn-sf-records-count))))
; Removal of the disjunction (no reload, not a prefix): the stobj holds a
; different history of the same length, the sync appends nothing, and the
; answer is not the history.
(defthm hcr-refresh-without-reload-or-prefix
  (let ((other (list *hct-c* *hct-b* *hct-a*)))
    (and (true-listp (fn-sf-records *hcr-files*))
         (not (fn-sf-prefixp other (fn-sf-records *hcr-files*)))
         (not (equal (fn-hist-refresh *hcr-files* nil other) *hcr-hist*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist-refresh fn-hist-sync fn-hist-sync-aux
                                     fn-sf-prefixp fn-sf-records-count))))
(must-fail-checked
 (defthm hcr-refresh-must-fail
   (equal (fn-hist-refresh *hcr-files* nil (list *hct-c* *hct-b* *hct-a*)) *hcr-hist*)
   :hints (("Goal" :in-theory (enable fn-hist-refresh fn-hist-sync fn-hist-sync-aux
                                      fn-sf-records-count)))))

; R's three answers, positive, and without R (a stobj holding another history).
(defconst *hcr-store* (list nil nil *hcr-files* nil nil nil nil nil nil nil nil nil nil nil))
(assert-event (equal (fn-sf-records (fn-sn-files *hcr-store*)) *hcr-hist*))
(defthm hcr-r-witness
  (and (fn-hist-of-storep *hcr-hist* *hcr-store*)
       (equal (fn-hist-count *hcr-hist*) 3)
       (equal (fn-hist-at 1 *hcr-hist*) *hct-b*))
  :rule-classes nil)
(defthm hcr-without-r
  (let ((other (list *hct-c*)))
    (and (not (fn-hist-of-storep other *hcr-store*))
         (not (equal (fn-hist-count other)
                     (len (fn-sf-records (fn-sn-files *hcr-store*)))))))
  :rule-classes nil)
