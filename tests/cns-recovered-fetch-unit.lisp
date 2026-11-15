; Served-machine APPEND -> discarded core -> fresh-core recovery -> FETCH.
; Simulator persistence model; native process-death cuts are a separate gate.
; Only the adapter's persisted device and the accepted occurrence position
; cross the death boundary. No live article/directory/phase state is copied.
; Source-only until the shared application world executes these assertions.
(in-package "ACL2")
(include-book "consumer-session-support")

(defconst *fn2-crf-mid* "<recovered-fetch@example.invalid>")
(defconst *fn2-crf-mid-bytes* (fn2-cw-chars (coerce *fn2-crf-mid* 'list)))
(defconst *fn2-crf-article*
  (fn2-cw-crlf-octets
    '("From: recovery@example.invalid" "Subject: recovered bytes"
      "Newsgroups: local.test" "Message-ID: <recovered-fetch@example.invalid>"
      "" "persistent body AAA")))

(defun fn2-crf-produce ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-ccu-profile* :echo nil fn2-core))
           ((mv epoch fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
              (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv status wire store fn2-core)
            (fn2-ccu-session 0 (list (fnc-append 9 *fn2-crf-article*)
                                       (fnc-control 5)) fn2-core))
           (reply (car (fnc-replies '(append) wire))))
        (mv (list epoch status reply store (fn2-core-stop-reason fn2-core))
            fn2-core))
      result)))

(defun fn2-crf-recover-fetch (store position)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-ccu-profile* :echo nil fn2-core))
           (rid (fn2-machine-global-id *fn2-recovery-machine-kind* 0 *fn2-ccu-profile*))
           ; Same named persistence-fence assumption as consumer-commit/M2.
           ((mv start fn2-core) (fn2-recovery-start rid 2 0 fn2-core))
           ((mv status & store fn2-core)
            (fn2-cw-loop 400000 0 0 nil store fn2-core))
           (done (equal (fn2-machine-phase rid fn2-core) *fn2-recovery-machine-state-done*))
           (class (nth (fn2-machine-rc-class rid fn2-core) *fn2-rec-classes*))
           ((unless (and (eq start :ok) (eq status :quiet) done
                         (eq class :intact) (equal (fn2-core-stop-reason fn2-core) 0)))
            (mv (list :recovery start status done class
                      (fn2-core-stop-reason fn2-core)) fn2-core))
           ((mv fetched wire & fn2-core)
            (fn2-ccu-session-store 0
              (list (fnc-fetch *fn2-crf-mid-bytes* position) (fnc-control 5))
              store fn2-core)))
        (mv (list :fetched fetched (fnc-replies '(fetch) wire)
                  (fn2-core-stop-reason fn2-core)) fn2-core))
      result)))

(defun fn2-crf-run ()
  (declare (xargs :verify-guards nil))
  (let* ((live (fn2-crf-produce)) (reply (nth 2 live))
         (position (car (nth 2 reply))) (store (nth 3 live)))
    (if (and (eq (nth 0 live) :ok) (eq (nth 1 live) :quiet)
             (equal (nth 4 live) 0) (consp store)
             (eq (car reply) :accepted) (equal (cadr reply) "")
             (posp position) (equal (cadr (nth 2 reply)) 1))
        (fn2-crf-recover-fetch store position)
      (list :producer (take 3 live) (nth 4 live)))))

; Exact octets, not an accepted reply alone or a reconstructed shadow model.
(assert-event
 (equal (fn2-crf-run)
        (list :fetched :quiet (list (list :accepted "" *fn2-crf-article*)) 0)))
