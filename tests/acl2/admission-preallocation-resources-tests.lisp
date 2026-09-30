(in-package "ACL2")
(include-book "../../books/admission-preallocation-resources")
(defmacro aprt3 (n call) `(mv-let (a b c) ,call (nth ,n (list a b c))))
(defmacro aprt2 (n call) `(mv-let (a b) ,call (nth ,n (list a b))))
(defconst *aprt-ledger* (fn-prl-make '(10000 10000 100 100 100)))
(defconst *aprt-identity* '(7 5 9 17 :article))
(defconst *aprt-demand* '(100 200 0 0 1))
(defconst *aprt-rescue* '(10 20 0 0 0))
(defconst *aprt-row*
 (mv-let (word row ledger)
   (fn-apr-issue *aprt-identity* *aprt-demand* *aprt-rescue* nil *aprt-ledger*)
  (declare (ignore word ledger)) row))
(defconst *aprt-issued*
 (mv-let (word row ledger)
   (fn-apr-issue *aprt-identity* *aprt-demand* *aprt-rescue* nil *aprt-ledger*)
  (declare (ignore word row)) ledger))
(assert-event
 (and (equal (aprt3 0 (fn-apr-issue *aprt-identity* *aprt-demand*
                                    *aprt-rescue* nil *aprt-ledger*)) :reserved)
      (equal (fn-prl-nth 0 *aprt-row*) '(:admission-grant 0 7 5 9 17 :article))
      (equal (fn-prl-nth 1 *aprt-issued*) *aprt-demand*)
      (equal (fn-prl-nth 2 *aprt-issued*) 1)
      (fn-prs-fundedp (fn-prl-nth 0 *aprt-issued*) (fn-prl-baseline *aprt-issued*)
                      *aprt-rescue* (fn-prl-nth 1 *aprt-issued*))))
; A second predecessor cannot replace the current grant or consume a nonce.
(assert-event
 (and (equal (aprt3 0 (fn-apr-issue '(7 6 10 18 :identity) *aprt-demand*
                                     *aprt-rescue* *aprt-row* *aprt-issued*)) :admission-busy)
      (equal (aprt3 1 (fn-apr-issue '(7 6 10 18 :identity) *aprt-demand*
                                     *aprt-rescue* *aprt-row* *aprt-issued*)) *aprt-row*)
      (equal (aprt3 2 (fn-apr-issue '(7 6 10 18 :identity) *aprt-demand*
                                     *aprt-rescue* *aprt-row* *aprt-issued*)) *aprt-issued*)))
; Same seq/txid in another process epoch is a stale callback.
(assert-event
 (equal (aprt3 2 (fn-apr-release '(:admission-grant 0 8 5 9 17 :article)
                                  :joined *aprt-row* *aprt-issued*)) *aprt-issued*))
; Uncertainty retains charges and repeated observation retains the same row.
(assert-event
 (let* ((token (fn-prl-nth 0 *aprt-row*))
        (row (aprt2 1 (fn-apr-uncertain token *aprt-row*))))
   (and (eq (fn-prl-nth 2 row) :uncertain)
        (equal (aprt2 1 (fn-apr-uncertain token row)) row)
        (equal (aprt3 2 (fn-apr-release token :uncertain row *aprt-issued*)) *aprt-issued*))))
; Actual join algebra refunds only reusable coordinates; the nonce stays spent.
(assert-event
 (let ((settled (aprt3 2 (fn-apr-release (fn-prl-nth 0 *aprt-row*) :joined
                                         *aprt-row* *aprt-issued*))))
  (and (equal (fn-prl-nth 1 settled) '(0 0 0 0 1))
       (equal (fn-prl-nth 2 settled) 1)
       (equal (fn-prl-nth 3 settled) (fn-prl-nth 3 *aprt-issued*)))))
; Corrupted charged carry must not be silently clamped into a successful refund.
(assert-event
 (eq (aprt3 0 (fn-apr-release (fn-prl-nth 0 *aprt-row*) :joined *aprt-row*
               (fn-prl-build '(10000 10000 100 100 100) '(99 200 0 0 1)
                              1 nil '(0 0 0 0 0)))) :invalid-resource-state))
