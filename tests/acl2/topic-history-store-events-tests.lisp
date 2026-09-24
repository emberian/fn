(in-package "ACL2")
(include-book "../../books/topic-history-store-events")
(include-book "topic-history-admission-tests")
(include-book "topic-history-local-admin-tests")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (fn-th-topic-eventp *thad-anchor-event*))
(assert-event (fn-th-topic-eventp *thad-report-event*))
(assert-event (fn-th-topic-eventp *thla-install*))
(assert-event (fn-th-topic-eventp (fn-stmt-value *thla-anchor*)))
(make-event `(defconst *thae-admin-octets*
               ',(fn-th-topic-event-encode *thla-install*)))
(make-event `(defconst *thae-anchor-octets*
               ',(fn-th-topic-event-encode *thad-anchor-event*)))
(make-event `(defconst *thae-anchor-v2-octets*
               ',(fn-th-topic-event-encode (fn-stmt-value *thla-anchor*))))
(make-event `(defconst *thae-report-octets*
               ',(fn-th-topic-event-encode *thad-report-event*)))
(assert-event (and *thae-anchor-octets* *thae-report-octets*))
(assert-event (and *thae-admin-octets*
                   (<= (len *thae-admin-octets*) *fn-th-topic-max-octets*)))
(assert-event
 (equal (fn-th-topic-event-decode-exact *thae-admin-octets*)
        (fn-stmt-ok *thla-install*)))
(assert-event (<= (len *thae-anchor-octets*) *fn-th-topic-max-octets*))
(assert-event (<= (len *thae-report-octets*) *fn-th-topic-max-octets*))
(assert-event
 (equal (fn-th-topic-event-decode-exact *thae-anchor-octets*)
        (fn-stmt-ok *thad-anchor-event*)))
(assert-event
 (equal (fn-th-topic-event-decode-exact *thae-anchor-v2-octets*)
        *thla-anchor*))
(assert-event
 (equal (fn-th-at 1 (fn-th-topic-event-items *thad-anchor-event*))
        (cons :uint *fn-th-topic-version*)))
(assert-event
 (equal (fn-th-at 1
                  (fn-th-topic-event-items (fn-stmt-value *thla-anchor*)))
        (cons :uint *fn-th-topic-anchor-v2-version*)))
(assert-event
 (equal (fn-th-topic-event-from-items
         (update-nth 1 (cons :uint 3)
                     (fn-th-topic-event-items (fn-stmt-value *thla-anchor*))))
        (fn-stmt-error :version)))
(assert-event
 (not (fn-stmt-okp
       (fn-th-topic-event-decode-exact
        (fn-stxe-encode-items
         (update-nth 1 (cons :uint *fn-th-topic-version*)
                     (fn-th-topic-event-items
                      (fn-stmt-value *thla-anchor*))))))))
(assert-event
 (not (fn-stmt-okp
       (fn-th-topic-event-decode-exact
        (fn-stxe-encode-items
         (update-nth 1 (cons :uint *fn-th-topic-anchor-v2-version*)
                     (fn-th-topic-event-items *thad-anchor-event*)))))))
(assert-event
 (not (fn-stmt-okp
       (fn-th-topic-event-from-items
        (update-nth 1 (cons :uint *fn-th-topic-anchor-v2-version*)
                    (fn-th-topic-event-items *thad-report-event*))))))
(assert-event
 (equal (fn-th-topic-event-decode-exact *thae-report-octets*)
        (fn-stmt-ok *thad-report-event*)))
(assert-event
 (equal (fn-th-topic-event-decode-exact
         (append *thae-report-octets* '(0)))
        (fn-stmt-error :canonical)))
(assert-event
 (not (fn-stmt-okp
       (fn-th-topic-event-decode-exact
        (cons 0 (cdr *thae-anchor-octets*))))))
(assert-event
 (equal (fn-th-topic-event-decode-exact
         (make-list 1025 :initial-element 0))
        (fn-stmt-error :octet-limit)))
(assert-event
 (not (fn-th-topic-eventp
       (list :topic-admit 11 12 13 *thad-topic*
             (fn-stxa-authored-id *thad-event*) *thad-topic*
             (fn-th-auth-ref-of *thad-event*)
             (list *thad-topic* *thad-topic*)))))
(assert-event
 (not (fn-th-topic-eventp
       (list :topic-anchor 8 9 10 *thad-topic*
             (fn-th-auth-ref-of *tha-event*) 65 *tha-principal*))))
(must-fail
 (defthm thae-duplicate-parent-can-encode
   (fn-th-topic-event-encode
    (list :topic-admit 11 12 13 *thad-topic*
          (fn-stxa-authored-id *thad-event*) *thad-topic*
          (fn-th-auth-ref-of *thad-event*)
          (list *thad-topic* *thad-topic*)))))
