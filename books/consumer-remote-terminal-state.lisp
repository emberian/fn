; Serialized remote alias holder. This is bookkeeping, never source/grant
; authority. Only the installed endpoint may use the internal hold/update APIs.
; The physical callback-completion issuer is not installed: terminal refuses
; and retains the capture until that actual receipt source exists.
(in-package "ACL2")
(include-book "consumer-remote-fields")
(include-book "state-globals")

; Fixed9: tag, genuine capture token, phase, scanner alias, backing reader
; alias, pending reply alias, callback alias, semantic key, final outcome.
(defun fn-crt-holder (token phase scanner reader reply callback key outcome)
 (declare (xargs :guard t))
 (list :remote-scan-holder token phase scanner reader reply callback key outcome))

(defun fn-owner-remote-scan-read (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-remote-scan state)
      (f-get-global 'fn-owner-remote-scan state)))

(defun fn-owner-remote-scan-hold-internal (token scanner reader reply callback key state)
 (declare (xargs :stobjs state :guard t))
 (if (fn-owner-remote-scan-read state) (mv '(:refused :remote-scan-busy) state)
  (let ((state (f-put-global 'fn-owner-remote-scan
                 (fn-crt-holder token :active scanner reader reply callback key nil) state)))
   (mv '(:held) state))))

(defun fn-owner-remote-scan-update-internal (token scanner reader reply callback outcome state)
 (declare (xargs :stobjs state :guard t))
 (let ((held (fn-owner-remote-scan-read state)))
  (if (not (and (eq (fn-cp-nth 0 held) :remote-scan-holder)
                 (equal token (fn-cp-nth 1 held))
                 (eq (fn-cp-nth 2 held) :active)))
      (mv '(:refused :remote-scan-token-or-phase) state)
   (let ((state (f-put-global 'fn-owner-remote-scan
                  (fn-crt-holder token :active scanner reader reply callback
                                 (fn-cp-nth 7 held) outcome) state)))
    (mv '(:held) state)))))

; Cancellation does not drop an alias or refund a captured source. In-flight
; physical reads/writes still require their actual completion receipt.
(defun fn-owner-remote-scan-cancel (token state)
 (declare (xargs :stobjs state :guard t))
 (let ((held (fn-owner-remote-scan-read state)))
  (if (not (and (eq (fn-cp-nth 0 held) :remote-scan-holder)
                 (equal token (fn-cp-nth 1 held))))
      (mv '(:refused :remote-scan-token) state)
   (let ((state (f-put-global 'fn-owner-remote-scan
                 (fn-crt-holder token :cancelled (fn-cp-nth 3 held)
                                (fn-cp-nth 4 held) (fn-cp-nth 5 held)
                                (fn-cp-nth 6 held) (fn-cp-nth 7 held)
                                (fn-cp-nth 8 held)) state)))
    (mv '(:cancellation-held) state)))))

; Real native operation completion must eventually publish this source. No
; supplied Boolean, user-created receipt, empty cursor or writable global may
; provide it. Until that issuer is installed, all terminals remain held.
(defun fn-owner-remote-callback-completion (token state)
 (declare (xargs :stobjs state :guard t) (ignore token))
 (mv '(:unavailable :remote-native-completion-issuer) state))

; Positive branch is deliberately unreachable with the current genuine source.
; It clears every alias in the actual holder before the caller may splice
; history-quiesce-terminal/release-issued under the same owner span. A return
; of :remote-quiesced alone is not a physical completion or custody theorem.
(defun fn-owner-remote-scan-terminal (token state)
 (declare (xargs :stobjs state :guard t))
 (let ((held (fn-owner-remote-scan-read state)))
  (if (not (and (eq (fn-cp-nth 0 held) :remote-scan-holder)
                 (equal token (fn-cp-nth 1 held))))
      (mv '(:refused :remote-scan-token) state)
   (mv-let (completion state) (fn-owner-remote-callback-completion token state)
    (if (not (eq (fn-cp-nth 0 completion) :completion-available))
        (mv completion state)
     (let ((state (f-put-global 'fn-owner-remote-scan nil state)))
      (mv (list :remote-quiesced token (fn-cp-nth 8 held)) state)))))))

(in-theory (disable fn-crt-holder fn-owner-remote-scan-read
 fn-owner-remote-scan-hold-internal fn-owner-remote-scan-update-internal
 fn-owner-remote-scan-cancel fn-owner-remote-callback-completion
 fn-owner-remote-scan-terminal))
