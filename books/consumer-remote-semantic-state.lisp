; Internal serialized endpoint join. Current ingress/config/view must be read
; from the installed owner in one genuine retained source span. The outer
; caller also validates the selected CEP/current CP source before invoking it.
; These internal arguments cannot act as public source/funding authority.
(in-package "ACL2")
(include-book "consumer-remote-terminal-return")
(include-book "consumer-remote-semantic-scan")

; Report input remains an alias in STATE. There is no supplied writer-done
; Boolean and no completion from a socket write. The actual bounded writer
; must eventually consume this projection and its continuation; its genuine
; installed profile/operation producer is still unavailable.
(defun fn-owner-remote-semantic-keep (token answer state)
 (declare (xargs :stobjs state :guard t))
 (let* ((held (fn-owner-remote-scan-read state)) (word (fn-cp-nth 0 answer))
        (scanner (if (eq word :event-complete) (fn-cp-nth 1 answer) (fn-cp-nth 3 held)))
        (reply (cond ((eq word :event-complete) nil)
                     ((eq word :yield) (list :semantic (fn-cp-nth 1 answer)))
                     ((eq word :report-input) (list :semantic-report answer))
                     (t (list :semantic-result answer)))))
  (if (not (member-eq word '(:event-complete :yield :report-input))) (mv answer state)
   (mv-let (status state)
   (fn-owner-remote-scan-update-internal token scanner (fn-owner-history-read-slot state)
    reply (fn-cp-nth 6 held) (if (eq word :event-complete) nil word) state)
   (mv (if (eq (fn-cp-nth 0 status) :held)
           (cond ((eq word :report-input) '(:report-input-held))
                 ((eq word :event-complete) '(:yield))
                 ((eq word :yield) '(:yield)) (t answer)) status) state)))))

; ONE pure semantic step, or begin of its saved continuation, after genuine
; capture recheck. Every refusal leaves scanner/read/reply/callback aliases
; intact. A pending report cannot be resumed or dropped by this entry point.
(defun fn-owner-remote-semantic-step-internal
 (token current-key ingress generation posting-config current-view query-limit fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :guard t))
 (let* ((held (fn-owner-remote-scan-read state)) (pending (fn-cp-nth 5 held))
        (scanner (fn-cp-nth 3 held))
        (source (fn-hhc-at 3 (fn-owner-history-capture-slot state))))
  (cond
   ((not (and (eq (fn-cp-nth 0 held) :remote-scan-holder)
               (equal token (fn-cp-nth 1 held)) (eq (fn-cp-nth 2 held) :active)))
    (mv '(:refused :remote-scan-token-or-phase) state))
   ((not (equal current-key (fn-cp-nth 7 held)))
    (mv '(:refused :consumer-source-changed) state))
   ((not (and (eq (fn-owner-history-recheck token state) :history-source-current)
               (fn-hep-capture-livep source token fn-history-backing)))
    (mv '(:unavailable :history-source) state))
   ((not (eq (fn-cp-nth 0 ingress) :authenticated)) (mv ingress state))
   ((not (and (posp query-limit) (fn-cp-uintp query-limit)))
    (mv '(:refused :consumer-query-count) state))
   ((eq (fn-cp-nth 0 pending) :semantic-report)
    (mv '(:unavailable :remote-report-producer) state))
   ((eq (fn-cp-nth 0 pending) :event-before-query)
    (if (not (equal (fn-cp-nth 2 pending) (fn-cp-nth 5 scanner)))
        (mv '(:refused :semantic-history-coordinate) state)
     (fn-owner-remote-semantic-keep token
       (fn-crm-begin scanner (fn-cp-nth 1 pending) ingress generation posting-config current-view) state)))
   ((eq (fn-cp-nth 0 pending) :semantic)
    (fn-owner-remote-semantic-keep token
      (fn-crm-tick (fn-cp-nth 1 pending) current-key (fn-crs-key ingress generation) query-limit) state))
   (t (mv '(:refused :remote-semantic-pending-kind) state)))))

(in-theory (disable fn-owner-remote-semantic-keep fn-owner-remote-semantic-step-internal))
