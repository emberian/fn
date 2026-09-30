; Concrete child and SAMEpool transitions. Setup is synthetic installation,
; not selected-runtime funding evidence. Positive token is OLD NEXT+1.
(in-package "ACL2")
(include-book "index-connection-issuer-tests")
(include-book "../../books/index-connection-start")

(defun fn-ics-test-start (children fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard (natp fuel)))
 (mv-let (fn-index-backing fn-page-read-pool)
  (fn-icr-test-setup children fn-index-backing fn-page-read-pool)
  (let ((before (fn-owner-page-read-ledger fn-page-read-pool)))
   (mv-let (word token left fn-index-backing fn-page-read-pool)
    (fn-ics-reserve-register 1000000 '(40 0 0 0 1) fuel fn-index-backing fn-page-read-pool)
    (let* ((after (fn-owner-page-read-ledger fn-page-read-pool))
           (pending (fn-ibp-connection-pending fn-index-backing))
           (ok (cond
                ((< fuel 8)
                 (and (eq word :yield) (not token) (equal left fuel)
                      (equal before after) (not pending)))
                (children
                 (and (eq word :reserved) (equal token '(:connection-holder 1 1 0))
                      (equal left (- fuel 1))
                      (equal (fn-prl-nth 1 after) '(40 0 0 0 1))
                      (equal (fn-prl-nth 2 after) 1)
                      (equal (fn-omk-at 1 pending) token)
                      (eq (fn-omk-at 6 pending) :registered)))
                (t (and (eq word :refused) (not token) (not pending)
                        (equal (fn-prl-nth 1 after) '(0 0 0 0 1))
                        (equal (fn-prl-nth 2 after) 1)
                        (equal (fn-ibp-connection-free fn-index-backing) '(0)))))))
     (mv-let (read row ignored) (fn-ibp-connection-read token 1 fn-index-backing)
      (declare (ignore ignored))
      (mv (and ok (if (and children (<= 8 fuel))
                      (and (eq read :present) (equal (fn-omk-at 2 row) 1000000)
                           (eq (fn-omk-at 4 row) :reserved)
                           (equal (fn-omk-at 5 row) '(40 0 0 0 1))) t))
          fn-index-backing fn-page-read-pool)))))))

(defun fn-ics-test-local (children fuel)
 (declare (xargs :guard (natp fuel)))
 (with-local-stobj fn-index-backing
  (mv-let (ok fn-index-backing)
   (with-local-stobj fn-page-read-pool
    (mv-let (ok fn-index-backing fn-page-read-pool)
     (fn-ics-test-start children fuel fn-index-backing fn-page-read-pool)
     (mv ok fn-index-backing)))
   ok)))

(assert-event (fn-ics-test-local t 8))
(assert-event (fn-ics-test-local nil 8))
(assert-event (fn-ics-test-local t 7))
(assert-event (fn-ics-test-local nil 0))

; Raw-uncertainty fixture: interruption at the existing retained registration
; intent. A retry cannot issue a second identity, release or hide the old root.
(defun fn-ics-test-uncertain (fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (mv-let (fn-index-backing fn-page-read-pool)
  (fn-icr-test-setup nil fn-index-backing fn-page-read-pool)
  (mv-let (reserved token fn-index-backing fn-page-read-pool)
   (fn-icr-reserve 42 '(40 0 0 0 1) fn-index-backing fn-page-read-pool)
   (let* ((fn-index-backing
            (update-fn-ibp-connection-pending
             (fn-icr-keep-phase (fn-ibp-connection-pending fn-index-backing)
                                :register-intent nil) fn-index-backing))
          (before (fn-owner-page-read-ledger fn-page-read-pool))
          (pending (fn-ibp-connection-pending fn-index-backing)))
    (mv-let (word new-token left fn-index-backing fn-page-read-pool)
     (fn-ics-reserve-register 43 '(40 0 0 0 1) 8 fn-index-backing fn-page-read-pool)
     (mv (and (eq reserved :reserved) (equal token '(:connection-holder 1 1 0))
              (eq word :recovery-required) (not new-token) (equal left 8)
              (equal before (fn-owner-page-read-ledger fn-page-read-pool))
              (equal pending (fn-ibp-connection-pending fn-index-backing))
              (equal (fn-prl-nth 2 before) 1)
              (equal (fn-omk-at 1 pending) token)
              (eq (fn-omk-at 6 pending) :register-intent))
         fn-index-backing fn-page-read-pool))))))

(defun fn-ics-test-local-uncertain ()
 (declare (xargs :guard t))
 (with-local-stobj fn-index-backing
  (mv-let (ok fn-index-backing)
   (with-local-stobj fn-page-read-pool
    (mv-let (ok fn-index-backing fn-page-read-pool)
     (fn-ics-test-uncertain fn-index-backing fn-page-read-pool)
     (mv ok fn-index-backing)))
   ok)))

(assert-event (fn-ics-test-local-uncertain))
