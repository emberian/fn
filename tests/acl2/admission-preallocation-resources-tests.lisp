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
   (fn-apr-issue *aprt-identity* *aprt-demand* *aprt-rescue* '(:captured-old-owner) nil *aprt-ledger*)
  (declare (ignore word ledger)) row))
(defconst *aprt-issued*
 (mv-let (word row ledger)
   (fn-apr-issue *aprt-identity* *aprt-demand* *aprt-rescue* '(:captured-old-owner) nil *aprt-ledger*)
  (declare (ignore word row)) ledger))
(assert-event
 (and (equal (aprt3 0 (fn-apr-issue *aprt-identity* *aprt-demand*
                                    *aprt-rescue* '(:captured-old-owner) nil *aprt-ledger*)) :reserved)
      (equal (fn-prl-nth 0 *aprt-row*) '(:admission-grant 0 7 5 9 17 :article))
      (equal (fn-prl-nth 1 *aprt-issued*) *aprt-demand*)
      (equal (fn-prl-nth 2 *aprt-issued*) 1)
      (fn-prs-fundedp (fn-prl-nth 0 *aprt-issued*) (fn-prl-baseline *aprt-issued*)
                      *aprt-rescue* (fn-prl-nth 1 *aprt-issued*))))
; A second predecessor cannot replace the current grant or consume a nonce.
(assert-event
 (and (equal (aprt3 0 (fn-apr-issue '(7 6 10 18 :identity) *aprt-demand*
                                     *aprt-rescue* '(:another-base) *aprt-row* *aprt-issued*)) :admission-busy)
      (equal (aprt3 1 (fn-apr-issue '(7 6 10 18 :identity) *aprt-demand*
                                     *aprt-rescue* '(:another-base) *aprt-row* *aprt-issued*)) *aprt-row*)
      (equal (aprt3 2 (fn-apr-issue '(7 6 10 18 :identity) *aprt-demand*
                                     *aprt-rescue* '(:another-base) *aprt-row* *aprt-issued*)) *aprt-issued*)))
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
; The same operation retains its borrowed BASE and produced NEXTready across
; uncertainty; changing the current publication pointer does not settle it.
(assert-event
 (let* ((token (fn-prl-nth 0 *aprt-row*))
        (next '(:ready 7 6 original-context field-carries consumer-context
                       consumer-carries pool rows source))
        (produced (aprt2 1 (fn-apr-produced token next *aprt-row*)))
        (uncertain (aprt2 1 (fn-apr-uncertain token produced))))
  (and (eq (fn-prl-nth 2 produced) :produced)
       (equal (fn-prl-nth 3 produced) '(:captured-old-owner))
       (equal (fn-prl-nth 4 produced) next)
       (eq (fn-prl-nth 2 uncertain) :uncertain)
       (equal (fn-prl-nth 3 uncertain) (fn-prl-nth 3 produced))
       (equal (fn-prl-nth 4 uncertain) next)
       (equal (aprt3 2 (fn-apr-release token :uncertain uncertain *aprt-issued*))
              *aprt-issued*))))
; Malformed token nesting cannot enter stored token equality or release charge.
(assert-event
 (and (not (fn-apr-tokenp '(:admission-grant (nested old row) 7 5 9 17 :article)))
      (eq (aprt3 0 (fn-apr-release '(:admission-grant (nested old row) 7 5 9 17 :article)
                                  :joined *aprt-row* *aprt-issued*)) :stale)))
; Installed backing transfers once from C to U while reducing the SAME stored
; remaining claim. Final release cannot refund that permanent transfer.
(assert-event
 (let* ((token (fn-prl-nth 0 *aprt-row*))
        (produced (aprt2 1 (fn-apr-produced token '(:next-ready) *aprt-row*)))
        (row (aprt3 1 (fn-apr-promote token '(40 80 0 0 0) produced *aprt-issued*)))
        (ledger (aprt3 2 (fn-apr-promote token '(40 80 0 0 0) produced *aprt-issued*)))
        (settled (aprt3 2 (fn-apr-release token :joined row ledger))))
  (and (fn-apr-promotablep token '(40 80 0 0 0) produced *aprt-issued*)
       (eq (aprt3 0 (fn-apr-promote token '(40 80 0 0 0) produced *aprt-issued*)) :promoted)
       (equal (fn-prl-nth 1 row) '(60 120 0 0 1))
       (equal (fn-prl-baseline ledger) '(40 80 0 0 0))
       (equal (fn-prl-nth 1 ledger) '(60 120 0 0 1))
       (equal (fn-iqr-resident-total ledger) (fn-iqr-resident-total *aprt-issued*))
       (equal (aprt3 1 (fn-apr-promote token '(40 80 0 0 0) row ledger)) row)
       (equal (aprt3 2 (fn-apr-promote token '(40 80 0 0 0) row ledger)) ledger)
       (equal (fn-prl-baseline settled) '(40 80 0 0 0))
       (equal (fn-prl-nth 1 settled) '(0 0 0 0 1))
       (equal (fn-prl-nth 2 settled) 1))))
; Promotion underflow/corrupt current resource cannot become installed U.
(assert-event
 (let ((token (fn-prl-nth 0 *aprt-row*)))
  (and (eq (aprt3 0 (fn-apr-promote token '(101 0 0 0 0)
          (aprt2 1 (fn-apr-produced token '(:next-ready) *aprt-row*)) *aprt-issued*)) :refused)
       (eq (aprt3 0 (fn-apr-promote token '(40 80 0 0 1)
          (aprt2 1 (fn-apr-produced token '(:next-ready) *aprt-row*)) *aprt-issued*)) :refused))))
