; Real APPEND -> persisted device -> FETCH of 6144 exact octets through the
; ordinary selected actors. No source descriptor, phase or result is seeded.
; Source-only until the paired application gate executes this assertion.
(in-package "ACL2")
(include-book "consumer-session-support")
(defconst *fn2-csf-mid* "<stream-fetch@example.invalid>")
(defconst *fn2-csf-mid-bytes* (fn2-cw-chars (coerce *fn2-csf-mid* 'list)))
(defconst *fn2-csf-head*
 (fn2-cw-crlf-octets '("From: stream@example.invalid" "Subject: streamed bytes"
   "Newsgroups: local.test" "Message-ID: <stream-fetch@example.invalid>" "")))
(defconst *fn2-csf-article*
 (append *fn2-csf-head* (repeat (- 6144 (+ 2 (len *fn2-csf-head*))) 120) '(13 10)))
(defun fn2-csf-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (b* ((fn2-core (fn2-init-executor *fn2-ccu-profile* :echo nil fn2-core))
        ((mv epoch fn2-core)
         (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
          (code fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
        ; Coalesced client bytes retain their original wire framing. CTL,
        ; not this fixture, decides each admitted receive extent.
        ((mv posted wire store fn2-core)
         (fn2-ccu-session 0 (list (fn2-ccu-cat (list (fnc-append 17 *fn2-csf-article*) (fnc-control 5)))) fn2-core))
        (reply (car (fnc-replies '(append) wire)))
        (position (car (nth 2 reply)))
        ((unless (and (eq epoch :ok) (eq posted :quiet) (consp store)
                      (equal (fn2-core-stop-reason fn2-core) 0)
                      (eq (car reply) :accepted) (equal (cadr reply) "")
                      (posp position) (equal (cadr (nth 2 reply)) 1)))
         (mv (list :producer epoch posted reply (fn2-core-stop-reason fn2-core)) fn2-core))
        ((mv fetched wire & fn2-core)
         (fn2-ccu-session-store 1
          (list (fn2-ccu-cat (list (fnc-fetch *fn2-csf-mid-bytes* position) (fnc-control 5))))
          store fn2-core))
        (released (stobj-let ((fn2-cns-sources (fn2-core-cns-sources fn2-core)))
                   (yes) (and (equal (fn2-cns-sources-rows fn2-cns-sources) 1)
                              (equal (fn2-cns-sources-phase 0 fn2-cns-sources) *fn2-cns-source-phase-free*)) yes)))
    (mv (list fetched (fnc-replies '(fetch) wire) released (fn2-core-stop-reason fn2-core)) fn2-core))
   answer)))
(assert-event (equal (len *fn2-csf-article*) 6144))
(assert-event
 (equal (fn2-csf-run) (list :quiet (list (list :accepted "" *fn2-csf-article*)) t 0)))
