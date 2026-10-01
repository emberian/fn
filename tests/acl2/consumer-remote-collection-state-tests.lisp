(in-package "ACL2")
(include-book "../../books/consumer-remote-collection-state")

; Corrupted-state fixture: no shaped holder/candidate may supply history grant.
(defun fn-crcol-state-fixture-refusal (fn-arena fn-history-backing state)
 (declare (xargs :stobjs (fn-arena fn-history-backing state) :guard t
   :guard-hints (("Goal" :in-theory (enable fn-owner-remote-collection-step-internal
                fn-owner-history-recheck fn-owner-history-capture-slot fn-owner-remote-scan-read fn-cp-nth fn-sg-state-p1-of-put-global)))))
 (with-local-stobj fn-octets
  (mv-let (ok state fn-octets)
   (let* ((token '(:history-capture 30))
          (state (f-put-global 'fn-owner-history-capture nil state))
          (state (f-put-global 'fn-owner-history-read nil state))
          (state (f-put-global 'fn-owner-remote-scan
            (fn-crt-holder token :active '(scanner) '(reader) '(:event-before-query row 1)
                           '(callback) '(key) nil) state))
          (before (fn-owner-remote-scan-read state)))
    (mv-let (answer fn-octets state)
     (fn-owner-remote-collection-step-internal token '(key) '(:authenticated) 9 nil nil
                                            2 3 4096 4096 fn-arena fn-history-backing fn-octets state)
     (let* ((ok (and (equal answer '(:unavailable :history-source))
                     (equal before (fn-owner-remote-scan-read state))
                     (equal (fn-octets-list fn-octets) nil)))
            (state (f-put-global 'fn-owner-remote-scan nil state)))
      (mv ok state fn-octets))))
   (mv ok state))))
(make-event
 (mv-let (ok state) (fn-crcol-state-fixture-refusal fn-arena fn-history-backing state)
  (if ok (value '(value-triple :passed))
    (er soft 'remote-collection "Unregistered source consumed event aliases."))))

; Actual STATE bookkeeping keeps OLD cursor and pending reply through encoding,
; publication refusal and cancellation. This is not a native receipt fixture.
(make-event
 (let* ((token '(:history-capture 31))
        (state (f-put-global 'fn-owner-history-read '(actual-reader) state))
        (state (f-put-global 'fn-owner-remote-scan
         (fn-crt-holder token :active '(old-scanner) '(reader) '(:collection-writing child)
                        '(callback) '(key) nil) state)))
  (mv-let (kept state)
    (fn-owner-remote-collection-keep token '(:collection-encoded (:encoded next-scanner) key scope 3 4096) :writing state)
   (let ((before (fn-owner-remote-scan-read state)))
    (mv-let (refusal state) (fn-owner-remote-collection-publication token state)
     (mv-let (cancel state) (fn-owner-remote-scan-cancel token state)
      (let* ((held (fn-owner-remote-scan-read state))
             (ok (and (equal kept '(:held))
                      (equal (fn-cp-nth 3 before) '(old-scanner))
                      (equal refusal '(:unavailable :remote-collection-publication-issuer))
                      (equal cancel '(:cancellation-held))
                      (equal (fn-cp-nth 3 held) '(old-scanner))
                      (equal (fn-cp-nth 4 held) '(actual-reader))
                      (equal (fn-cp-nth 5 held) (fn-cp-nth 5 before))
                      (equal (fn-cp-nth 6 held) '(callback))))
             (state (f-put-global 'fn-owner-remote-scan nil state))
             (state (f-put-global 'fn-owner-history-read nil state)))
       (if ok (value '(value-triple :passed))
        (er soft 'remote-collection "Encoded/cancelled collection released pending aliases.")))))))))
