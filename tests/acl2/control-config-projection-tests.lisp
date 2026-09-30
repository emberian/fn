(in-package "ACL2")
(include-book "../../books/control-config-projection")

; Actual values intentionally differ; no invented default answers pre-seed.
(defconst *ccpxt-seed* (fn-ccpx-entry (fn-cfg-make 1 :genesis) 0 0 3 :origin nil))
(defconst *ccpxt-old* (fn-ccpx-entry (fn-cfg-make 7 :before) 6 9 3 :old *ccpxt-seed*))
(defconst *ccpxt-tie* (fn-ccpx-entry (fn-cfg-make 8 :typed) 7 9 4 :commit *ccpxt-old*))
(defconst *ccpxt-new* (fn-ccpx-entry (fn-cfg-make 9 :later) 8 15 4 :later *ccpxt-tie*))
(defconst *ccpxt-start* (fn-cp-nth 1 (fn-ccpx-begin *ccpxt-new* 9 :captured-origin)))
;@positive-witness fn-ccpx-yield-preserves-complete-lookup
(assert-event
 (let* ((one (fn-ccpx-tick *ccpxt-start*)) (next (fn-cp-nth 1 one)))
  (and (equal (fn-cp-nth 0 one) :yield)
       (equal (fn-ccpx-at (fn-cp-nth 3 next) (fn-cp-nth 1 next))
              (fn-ccpx-at (fn-cp-nth 3 *ccpxt-start*) (fn-cp-nth 1 *ccpxt-start*)))
       (equal (fn-cp-nth 2 next) *ccpxt-new*)
       (equal (fn-cp-nth 4 next) :captured-origin))))
;@hyp-removal-witness fn-ccpx-yield-preserves-complete-lookup omitted=yield
(assert-event
 (let* ((bad (list :control-config-lookup 'bad *ccpxt-new* *ccpxt-new* :captured-origin))
        (one (fn-ccpx-tick bad)))
  (and (not (equal (fn-cp-nth 0 one) :yield))
       (not (equal (fn-ccpx-at (fn-cp-nth 3 (fn-cp-nth 1 one))
                              (fn-cp-nth 1 (fn-cp-nth 1 one)))
                   (fn-ccpx-at (fn-cp-nth 3 bad) (fn-cp-nth 1 bad)))))))
;@positive-witness fn-ccpx-selected-complete-result
(assert-event
 (let* ((cursor (fn-cp-nth 1 (fn-ccpx-tick *ccpxt-start*)))
        (one (fn-ccpx-tick cursor)))
  (and (equal (fn-cp-nth 0 one) :configuration)
       (equal one (fn-ccpx-at (fn-cp-nth 3 cursor) (fn-cp-nth 1 cursor)))
       (equal (fn-cp-nth 1 one) (fn-cfg-make 8 :typed))
       (equal (fn-cp-nth 6 one) :commit))))
;@hyp-removal-witness fn-ccpx-selected-complete-result omitted=selected
(assert-event
 (let* ((bad (list :control-config-lookup 'bad *ccpxt-new* *ccpxt-new* :captured-origin))
        (one (fn-ccpx-tick bad)))
  (and (not (equal (fn-cp-nth 0 one) :configuration))
       (not (equal one (fn-ccpx-at (fn-cp-nth 3 bad) (fn-cp-nth 1 bad)))))))
;@mutation-witness latest-same-txid-and-actual-seed-only
(assert-event
 (and (equal (fn-cp-nth 1 (fn-ccpx-at *ccpxt-new* 9)) (fn-cfg-make 8 :typed))
      (equal (fn-cp-nth 1 (fn-ccpx-at *ccpxt-new* 0)) (fn-cfg-make 1 :genesis))
      (equal (fn-ccpx-at nil 0) '(:unavailable :historical-config-prefix))
      (equal (fn-ccpx-at (fn-ccpx-entry (fn-cfg-make 7 :before) 6 9 3 :old nil) 0)
             '(:unavailable :historical-config-prefix))))
