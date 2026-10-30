;; Evidence for the principal ledger (fn2/books/accounts.lisp; layer D, D7
;; 2/n): the admission rule's refusals by name, protected reservations under
;; exhausted shared capacity (positive-size acquisitions), monotone charges,
;; attribution as a net change, configuration checks, and the teeth of the
;; owed fn2-account-ops-conserve.
(in-package "ACL2")
(include-book "../books/accounts")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-accounts-test-profile*
  (put-assoc-equal
   :accounts
   '((0 :state :anonymous :limits ((:connection-row . 6) (:principal-reservation . 6)))
     (1 :state :configured :weight 2
        :limits ((:connection-row . 3) (:principal-reservation . 3))
        :reserves ((:connection-row . 2) (:principal-reservation . 1)))
     (:system :limits ((:connection-row . 8) (:principal-reservation . 8))
              :reserves ((:connection-row . 1))))
   (put-assoc-equal :c 8 *fn2-profile-tiny*)))

(defmacro fn2-acc-cr () '(fn2-account-holding :connection-row))
(defmacro fn2-acc-pr () '(fn2-account-holding :principal-reservation))

(assert-event (and (fn2-accounts-profilep *fn2-profile-tiny*)
                   (fn2-accounts-profilep *fn2-profile-concrete*)
                   (fn2-accounts-profilep *fn2-accounts-test-profile*)))
;; Refused configurations: reserves over capacity; a reserve over its limit;
;; an unknown dimension; a slot outside P; a duplicate slot.
(assert-event
 (let ((base (put-assoc-equal :c 8 *fn2-profile-tiny*)))
   (and (not (fn2-accounts-profilep
              (put-assoc-equal :accounts '((1 :state :configured :limits ((:connection-row . 9))
                                               :reserves ((:connection-row . 9)))) base)))
        (not (fn2-accounts-profilep
              (put-assoc-equal :accounts '((1 :state :configured :limits ((:connection-row . 1))
                                               :reserves ((:connection-row . 2)))) base)))
        (not (fn2-accounts-profilep
              (put-assoc-equal :accounts '((1 :state :configured :limits ((:upload-row . 1)))) base)))
        (not (fn2-accounts-profilep (put-assoc-equal :accounts '((4 :state :configured)) base)))
        (not (fn2-accounts-profilep
              (put-assoc-equal :accounts '((1 :state :configured) (1 :state :configured)) base))))))

;; The default ledger: slot 0 anonymous with every limit the capacity, the
;; other slots free with limit 0, the system row P.
(defun fn2-accounts-test-default ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-accounts
    (mv-let (result fn2-accounts)
      (let ((fn2-accounts (fn2-accounts-init *fn2-profile-tiny* fn2-accounts)))
        (mv (and (fn2-accounts-conservedp fn2-accounts)
                 (equal (fn2-accounts-rows fn2-accounts) 5)
                 (equal (fn2-accounts-state 0 fn2-accounts) *fn2-account-state-anonymous*)
                 (equal (fn2-accounts-state 1 fn2-accounts) *fn2-account-state-free*)
                 (equal (fn2-accounts-state 4 fn2-accounts) *fn2-account-state-system*)
                 (equal (fn2-account-limit 0 (fn2-acc-cr) fn2-accounts) 4)
                 (equal (fn2-account-limit 1 (fn2-acc-cr) fn2-accounts) 0)
                 (equal (fn2-account-limit 4 (fn2-acc-pr) fn2-accounts) 4)
                 (equal (fn2-account-committed (fn2-acc-cr) fn2-accounts) 0))
            fn2-accounts))
      result)))
(assert-event (fn2-accounts-test-default))

;; The admission rule over the configured ledger (C = 8; reserves: slot 1
;; holds 2 connection rows, the system 1; slot 0 may hold 6).
(defun fn2-accounts-test-rule-run (fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :verify-guards nil))
  (b* ((fn2-accounts (fn2-accounts-init *fn2-accounts-test-profile* fn2-accounts))
       (c0 (fn2-account-committed (fn2-acc-cr) fn2-accounts))
       ;; the anonymous flood: five fit the shared remainder 8 - 3, the sixth does not
       ((mv a1 fn2-accounts) (fn2-account-acquire 0 (fn2-acc-cr) 1 fn2-accounts))
       ((mv a2 fn2-accounts) (fn2-account-acquire 0 (fn2-acc-cr) 1 fn2-accounts))
       ((mv a3 fn2-accounts) (fn2-account-acquire 0 (fn2-acc-cr) 1 fn2-accounts))
       ((mv a4 fn2-accounts) (fn2-account-acquire 0 (fn2-acc-cr) 1 fn2-accounts))
       ((mv a5 fn2-accounts) (fn2-account-acquire 0 (fn2-acc-cr) 1 fn2-accounts))
       ((mv a6 fn2-accounts) (fn2-account-acquire 0 (fn2-acc-cr) 1 fn2-accounts))
       (ok1 (fn2-accounts-conservedp fn2-accounts))
       ;; the protected principal under exhausted shared capacity: its two
       ;; reserved rows are admitted, the third is not
       ((mv b1 fn2-accounts) (fn2-account-acquire 1 (fn2-acc-cr) 1 fn2-accounts))
       ((mv b2 fn2-accounts) (fn2-account-acquire 1 (fn2-acc-cr) 1 fn2-accounts))
       ((mv b3 fn2-accounts) (fn2-account-acquire 1 (fn2-acc-cr) 1 fn2-accounts))
       ;; the system row: its one reserved row, then nothing
       ((mv s1 fn2-accounts) (fn2-account-acquire 4 (fn2-acc-cr) 1 fn2-accounts))
       ((mv s2 fn2-accounts) (fn2-account-acquire 4 (fn2-acc-cr) 1 fn2-accounts))
       (ok2 (fn2-accounts-conservedp fn2-accounts))
       ;; a free slot has limit 0
       ((mv f1 fn2-accounts) (fn2-account-acquire 2 (fn2-acc-cr) 1 fn2-accounts))
       ;; charges, then a disconnect: the holdings go, the charge stays
       ((mv k1 fn2-accounts) (fn2-account-charge 0 (fn2-account-charge-dim :rx-octets) 100 fn2-accounts))
       ((mv r1 fn2-accounts) (fn2-account-release 0 (fn2-acc-cr) 1 fn2-accounts))
       (rx (fn2-account-charged 0 (fn2-account-charge-dim :rx-octets) fn2-accounts))
       ;; the released row is shared again: principal 1's third fits, its fourth is over its limit
       ((mv b4 fn2-accounts) (fn2-account-acquire 1 (fn2-acc-cr) 1 fn2-accounts))
       ((mv b5 fn2-accounts) (fn2-account-acquire 1 (fn2-acc-cr) 1 fn2-accounts))
       (ok3 (fn2-accounts-conservedp fn2-accounts))
       ;; attribution 0 -> 1 refused by 1's limit: the ledger is unchanged
       (before (list (fn2-account-hold 0 (fn2-acc-cr) fn2-accounts) (fn2-account-hold 1 (fn2-acc-cr) fn2-accounts)
                     (fn2-account-committed (fn2-acc-cr) fn2-accounts)))
       ((mv t1 fn2-accounts) (fn2-account-attribute 0 1 (fn2-acc-cr) 1 (fn2-acc-pr) 0 fn2-accounts))
       (after (list (fn2-account-hold 0 (fn2-acc-cr) fn2-accounts) (fn2-account-hold 1 (fn2-acc-cr) fn2-accounts)
                    (fn2-account-committed (fn2-acc-cr) fn2-accounts)))
       ;; release 1's row above its reserve, then attribution 0 -> 1 is a net change:
       ;; with shared capacity full it is still admitted (acquire-first would refuse it)
       ((mv r2 fn2-accounts) (fn2-account-release 1 (fn2-acc-cr) 1 fn2-accounts))
       ((mv a7 fn2-accounts) (fn2-account-acquire 0 (fn2-acc-cr) 1 fn2-accounts))
       (full (equal (fn2-account-committed (fn2-acc-cr) fn2-accounts) 8))
       ((mv t2 fn2-accounts) (fn2-account-attribute 0 1 (fn2-acc-cr) 1 (fn2-acc-pr) 0 fn2-accounts))
       (rx2 (fn2-account-charged 0 (fn2-account-charge-dim :rx-octets) fn2-accounts))
       (rx1 (fn2-account-charged 1 (fn2-account-charge-dim :rx-octets) fn2-accounts))
       (ok4 (fn2-accounts-conservedp fn2-accounts))
       ;; a release the ledger does not hold
       ((mv u1 fn2-accounts) (fn2-account-release 2 (fn2-acc-cr) 1 fn2-accounts))
       ;; the request bundle: whole or not at all
       ((mv w1 fn2-accounts) (fn2-account-acquire2 2 (fn2-acc-cr) 0 (fn2-acc-pr) 1 fn2-accounts))
       (ok5 (fn2-accounts-conservedp fn2-accounts)))
    (mv (and (equal c0 3)
             (equal (list a1 a2 a3 a4 a5 a6) '(:ok :ok :ok :ok :ok :shared))
             (equal (list b1 b2 b3) '(:ok :ok :shared))
             (equal (list s1 s2) '(:ok :shared))
             (eq f1 :limit) (eq k1 :ok) (eq r1 :ok) (equal rx 100)
             (equal (list b4 b5) '(:ok :limit))
             (eq t1 :limit) (equal before after)
             (eq r2 :ok) (eq a7 :ok) full (eq t2 :ok) (equal rx2 100) (equal rx1 0)
             (eq u1 :underflow) (eq w1 :limit)
             ok1 ok2 ok3 ok4 ok5)
        fn2-accounts)))
(defun fn2-accounts-test-rule ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-accounts
    (mv-let (result fn2-accounts) (fn2-accounts-test-rule-run fn2-accounts) result)))
(assert-event (fn2-accounts-test-rule))

;; Teeth of fn2-account-ops-conserve. Positive: 600 pseudo-random
;; operations of every kind (rows 0..4, both dimensions, amounts 0..3) from
;; the configured ledger, conserved after each. Negative: the predicate
;; refuses a committed count off by one and a holding over its limit (what
;; an acquisition skipping either check would leave).
(defun fn2-accounts-test-step (x fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :verify-guards nil))
  (let* ((op (mod x 6)) (p (mod (floor x 6) 5)) (q (mod (floor x 30) 5))
         (d1 (mod (floor x 150) 2)) (a1 (mod (floor x 300) 4))
         (d2 (- 1 d1)) (a2 (mod (floor x 1200) 2)))
    (case op
      (0 (mv-let (c fn2-accounts) (fn2-account-acquire p d1 a1 fn2-accounts) (declare (ignore c)) fn2-accounts))
      (1 (mv-let (c fn2-accounts) (fn2-account-release p d1 a1 fn2-accounts) (declare (ignore c)) fn2-accounts))
      (2 (mv-let (c fn2-accounts) (fn2-account-charge p (mod a1 3) a1 fn2-accounts) (declare (ignore c)) fn2-accounts))
      (3 (mv-let (c fn2-accounts) (fn2-account-acquire2 p d1 a1 d2 a2 fn2-accounts) (declare (ignore c)) fn2-accounts))
      (4 (mv-let (c fn2-accounts) (fn2-account-release2 p d1 a1 d2 a2 fn2-accounts) (declare (ignore c)) fn2-accounts))
      (otherwise (mv-let (c fn2-accounts) (fn2-account-attribute p q d1 a1 d2 a2 fn2-accounts)
                   (declare (ignore c)) fn2-accounts)))))
(defun fn2-accounts-test-walk (n x fn2-accounts)
  (declare (xargs :stobjs fn2-accounts :verify-guards nil :measure (nfix n)))
  (if (zp n) (mv t fn2-accounts)
    (let* ((fn2-accounts (fn2-accounts-test-step x fn2-accounts))
           (ok (fn2-accounts-conservedp fn2-accounts)))
      (mv-let (rest fn2-accounts)
        (fn2-accounts-test-walk (- n 1) (mod (+ (* x 1103515245) 12345) 2147483648) fn2-accounts)
        (mv (and ok rest) fn2-accounts)))))
(defun fn2-accounts-test-conserve ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-accounts
    (mv-let (result fn2-accounts)
      (let ((fn2-accounts (fn2-accounts-init *fn2-accounts-test-profile* fn2-accounts)))
        (if (fn2-accounts-conservedp fn2-accounts) (fn2-accounts-test-walk 600 7 fn2-accounts)
          (mv nil fn2-accounts)))
      result)))
(assert-event (fn2-accounts-test-conserve))

(defun fn2-accounts-test-conserve-negative ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-accounts
    (mv-let (result fn2-accounts)
      (b* ((fn2-accounts (fn2-accounts-init *fn2-accounts-test-profile* fn2-accounts))
           (good (fn2-accounts-conservedp fn2-accounts))
           (c (fn2-accounts-committedi 0 fn2-accounts))
           (fn2-accounts (update-fn2-accounts-committedi 0 (+ 1 c) fn2-accounts))
           (off-by-one (fn2-accounts-conservedp fn2-accounts))
           (fn2-accounts (update-fn2-accounts-committedi 0 c fn2-accounts))
           (restored (fn2-accounts-conservedp fn2-accounts))
           ;; slot 2 (limit 0) made to hold a row: committed kept in step, the limit is broken
           (fn2-accounts (update-fn2-accounts-holdi (+ 2 (* 0 (fn2-accounts-rows fn2-accounts))) 1 fn2-accounts))
           (fn2-accounts (update-fn2-accounts-committedi 0 (+ 1 c) fn2-accounts))
           (over-limit (fn2-accounts-conservedp fn2-accounts)))
        (mv (and good (not off-by-one) restored (not over-limit)) fn2-accounts))
      result)))
(assert-event (fn2-accounts-test-conserve-negative))
