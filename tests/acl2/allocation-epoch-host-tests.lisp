(in-package "ACL2")
; These checks use the actual loaded declarations and actual guarded entries.
(assert-event
 (equal (cdr (assoc-eq 'fn-aec-pool-collection-request-internal
                       (table-alist 'fn-interfaces (w state))))
        '(:class :common-lisp-compliant
          :raw-with (fn-aech-request-preserves-carried-state fn-aech-request-preserves-existing-roots))))
(assert-event
 (equal (cdr (assoc-eq 'fn-aec-pool-collect-observed-internal
                       (table-alist 'fn-interfaces (w state))))
        '(:class :common-lisp-compliant
          :raw-with (fn-aech-observed-preserves-carried-state fn-aech-observed-preserves-existing-roots))))
(assert-event
 (equal (cdr (assoc-eq 'fn-aec-pool-uncertain-internal
                       (table-alist 'fn-interfaces (w state))))
        '(:class :common-lisp-compliant
          :raw-with (fn-aech-uncertain-preserves-carried-state fn-aec-pool-uncertainty-retains-charge-and-identities))))
(assert-event
 (and (not (fn-di-raw-with-problem 'fn-aec-pool-collection-request-internal
            (cdr (assoc-eq 'fn-aec-pool-collection-request-internal (table-alist 'fn-interfaces (w state)))) (w state)))
      (not (fn-di-raw-with-problem 'fn-aec-pool-collect-observed-internal
            (cdr (assoc-eq 'fn-aec-pool-collect-observed-internal (table-alist 'fn-interfaces (w state)))) (w state)))
      (not (fn-di-raw-with-problem 'fn-aec-pool-uncertain-internal
            (cdr (assoc-eq 'fn-aec-pool-uncertain-internal (table-alist 'fn-interfaces (w state)))) (w state)))))
; Removing the actual preservation theorem must fail the declaration check;
; a root-frame theorem alone does not establish the skipped carried guard.
(assert-event
 (fn-di-raw-with-problem 'fn-aec-pool-collection-request-internal
  '(:class :common-lisp-compliant :raw-with (fn-aech-request-preserves-existing-roots)) (w state)))
(assert-event
 (fn-di-raw-with-problem 'fn-aec-pool-collect-observed-internal
  '(:class :common-lisp-compliant :raw-with (fn-aech-observed-preserves-existing-roots)) (w state)))
(assert-event
 (fn-di-raw-with-problem 'fn-aec-pool-uncertain-internal
  '(:class :common-lisp-compliant :raw-with (fn-aec-pool-uncertainty-retains-charge-and-identities)) (w state)))
; A preservation theorem about another entry cannot substitute.
(assert-event
 (fn-di-raw-with-problem 'fn-aec-pool-collection-request-internal
  '(:class :common-lisp-compliant :raw-with (fn-aech-uncertain-preserves-carried-state)) (w state)))
(assert-event
 (and (equal (getpropc 'fn-aec-pool-collection-request-internal 'symbol-class nil (w state)) :common-lisp-compliant)
      (equal (getpropc 'fn-aec-pool-collect-observed-internal 'symbol-class nil (w state)) :common-lisp-compliant)
      (equal (getpropc 'fn-aec-pool-uncertain-internal 'symbol-class nil (w state)) :common-lisp-compliant)))
(assert-event
 (and (equal (getpropc 'fn-aec-pool-collection-request-internal 'stobjs-out nil (w state))
             '(nil nil nil nil fn-page-read-pool))
      (equal (getpropc 'fn-aec-pool-collect-observed-internal 'stobjs-out nil (w state))
             '(nil fn-page-read-pool))
      (equal (getpropc 'fn-aec-pool-uncertain-internal 'stobjs-out nil (w state))
             '(fn-page-read-pool))))
