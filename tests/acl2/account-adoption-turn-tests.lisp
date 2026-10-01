(in-package "ACL2")
(include-book "../../books/account-adoption-turn")

; SYNTHETIC UNFUNDED ledger fixture; this is the internal algebra, never an
; installed allowance/native grant/whole-operation or lifecycle witness.
(defconst *fn-act-test-ledger*
 (fn-prl-build '(200 0 0 0 100) '(0 0 0 0 0) 7
               '(:original-binding-root) '(20 0 0 0 0)))
(defconst *fn-act-test-reserved*
 (mv-let (word current ledger)
  (fn-act-reserve 3 4 :begin nil '(:old-request) '(:old-job)
                  '(30 0 0 0 1) '(0 0 0 0 0) nil *fn-act-test-ledger*)
  (list word current ledger)))

; Complete output/custody/counter positive, not just success or token shape.
(assert-event
 (equal *fn-act-test-reserved*
        (list :account-turn-reserved
              '(:account-turn (:account-preparation-turn 7 3 4) :reserved
                (30 0 0 0 1) :begin nil (:old-request) (:old-job) nil nil)
              (fn-prl-build '(200 0 0 0 100) '(30 0 0 0 1) 8
                            '(:original-binding-root) '(20 0 0 0 0)))))

(defconst *fn-act-test-produced*
 (mv-let (word current)
  (fn-act-produced '(:account-preparation-turn 7 3 4)
    '((:new-request) (:new-job) :yield) (fn-cp-nth 1 *fn-act-test-reserved*))
  (declare (ignore word)) current))
(assert-event
 (equal *fn-act-test-produced*
        '(:account-turn (:account-preparation-turn 7 3 4) :produced
          (30 0 0 0 1) :begin nil (:old-request) (:old-job)
          ((:new-request) (:new-job) :yield) nil)))

(defconst *fn-act-test-promoting*
 (mv-let (word current)
  (fn-act-promotion-intent '(:account-preparation-turn 7 3 4)
    '(20 0 0 0 0) *fn-act-test-produced* (fn-cp-nth 2 *fn-act-test-reserved*))
  (declare (ignore word)) current))
(assert-event
 (and (eq (fn-cp-nth 2 *fn-act-test-promoting*) :promoting)
      (equal (fn-cp-nth 6 *fn-act-test-promoting*) '(:old-request))
      (equal (fn-cp-nth 7 *fn-act-test-promoting*) '(:old-job))
      (equal (fn-cp-nth 2 (fn-cp-nth 9 *fn-act-test-promoting*))
             (fn-prl-build '(200 0 0 0 100) '(10 0 0 0 1) 8
                           '(:original-binding-root) '(40 0 0 0 0)))))
(assert-event
 (equal (mv-let (word current) (fn-act-promotion-published
                   '(:account-preparation-turn 7 3 4) *fn-act-test-promoting*) (declare (ignore word)) current)
        (fn-act-row '(:account-preparation-turn 7 3 4) :promoted
                    '(10 0 0 0 1) :begin nil '(:old-request) '(:old-job)
                    '((:new-request) (:new-job) :yield)
                    (fn-cp-nth 9 *fn-act-test-promoting*))))

; CORRUPTED STATE: an excessive retained projection cannot hide subtraction
; with NFIX. Complete original current survives; no pool mutation is proposed.
(assert-event
 (equal (mv-let (word current) (fn-act-promotion-intent '(:account-preparation-turn 7 3 4)
                  '(31 0 0 0 0) *fn-act-test-produced*
                  (fn-cp-nth 2 *fn-act-test-reserved*)) (declare (ignore word)) current)
        *fn-act-test-produced*))

; STALE CALLBACK: an earlier nonce cannot publish this current source/output.
(assert-event
 (and (eq (mv-let (word current) (fn-act-produced '(:account-preparation-turn 6 3 4)
                         '(:arbitrary-output) *fn-act-test-produced*) (declare (ignore current)) word) :stale)
      (equal (mv-let (word current) (fn-act-produced '(:account-preparation-turn 6 3 4)
                         '(:arbitrary-output) *fn-act-test-produced*) (declare (ignore word)) current)
             *fn-act-test-produced*)))

; Ambiguity keeps original and produced roots and the exact promotion intent.
(assert-event
 (equal (mv-let (word current) (fn-act-uncertain '(:account-preparation-turn 7 3 4)
                                   *fn-act-test-promoting*) (declare (ignore word)) current)
        (fn-act-row '(:account-preparation-turn 7 3 4) :uncertain
                    '(30 0 0 0 1) :begin nil '(:old-request) '(:old-job)
                    '((:new-request) (:new-job) :yield)
                    (fn-cp-nth 9 *fn-act-test-promoting*))))
