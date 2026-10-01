(in-package "ACL2")
(include-book "../../books/consumer-remote-source-scan")

; Actual owner/STATE refusal: a shaped token and plan cannot create custody.
(make-event
 (let* ((state (f-put-global 'fn-owner-history-capture nil state))
        (state (f-put-global 'fn-owner-history-read nil state))
        (state (f-put-global 'fn-owner-remote-scan nil state)))
  (mv-let (word state)
   (fn-owner-remote-scan-begin-internal '(:history-capture 1) '(:scan-request) '(key) 1
                                      fn-history-backing state)
   (if (and (equal word '(:unavailable :history-source))
            (null (fn-owner-remote-scan-read state)) (null (fn-owner-history-read-slot state)))
       (value '(value-triple :passed))
    (er soft 'remote-source "A request shape manufactured history custody.")))))

; Corrupted STATE does not turn an unregistered source into a read or skip.
(make-event
 (let* ((token '(:history-capture 2))
        (state (f-put-global 'fn-owner-history-capture nil state))
        (state (f-put-global 'fn-owner-history-read nil state))
        (state (f-put-global 'fn-owner-remote-scan
                 (fn-crt-holder token :active '(scan) nil nil nil '(key) nil) state))
        (before (fn-owner-remote-scan-read state)))
  (mv-let (word left state)
   (fn-owner-remote-scan-step-internal token '(key) 10 fn-history-backing state)
   (let* ((ok (and (equal word '(:unavailable :history-source)) (equal left 10)
                   (equal before (fn-owner-remote-scan-read state))
                   (null (fn-owner-history-read-slot state))))
          (state (f-put-global 'fn-owner-remote-scan nil state)))
    (if ok (value '(value-triple :passed))
     (er soft 'remote-source "An unregistered source advanced the dense cursor."))))))

(make-event
 (let* ((token '(:history-capture 3))
        (state (f-put-global 'fn-owner-remote-scan
                 (fn-crt-holder token :active '(scan) '(reader) '(reply) '(callback) '(key) nil) state))
        (before (fn-owner-remote-scan-read state)))
  (mv-let (word left state)
   (fn-owner-remote-scan-step-internal token '(different-key) 10 fn-history-backing state)
   (let* ((ok (and (equal word '(:refused :consumer-source-changed)) (equal left 10)
                   (equal before (fn-owner-remote-scan-read state))))
          (state (f-put-global 'fn-owner-remote-scan nil state)))
    (if ok (value '(value-triple :passed))
     (er soft 'remote-source "Changed semantic source consumed a retained alias."))))))

; Aggregate release fixture uses actual local backing/pool stobjs. Those
; empty physical containers are not admitted source or allocation authority.
(defun fn-crsst-release-refusal (token state)
 (declare (xargs :stobjs state :guard t))
 (with-local-stobj fn-page-read-pool
  (mv-let (ok fn-page-read-pool state)
   (with-local-stobj fn-history-backing
    (mv-let (ok fn-history-backing fn-page-read-pool state)
     (let ((before (fn-owner-remote-scan-read state))
           (pool-before (fn-prp-data fn-page-read-pool)))
      (mv-let (word fn-history-backing fn-page-read-pool state)
       (fn-owner-remote-scan-release token fn-history-backing fn-page-read-pool state)
       (mv (and (equal word '(:refused :remote-history-token))
                (equal before (fn-owner-remote-scan-read state))
                (equal pool-before (fn-prp-data fn-page-read-pool)))
           fn-history-backing fn-page-read-pool state)))
     (mv ok fn-page-read-pool state)))
   (mv ok state))))

(make-event
 (let* ((token '(:history-capture 4))
        (state (f-put-global 'fn-owner-history-capture nil state))
        (state (f-put-global 'fn-owner-remote-scan
                 (fn-crt-holder token :cancelled nil nil nil nil '(key) nil) state)))
  (mv-let (ok state) (fn-crsst-release-refusal token state)
   (let ((state (f-put-global 'fn-owner-remote-scan nil state)))
    (if ok (value '(value-triple :passed))
     (er soft 'remote-return "Shape-only cancellation released the actual pool."))))))
