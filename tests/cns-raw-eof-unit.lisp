; Actual APPEND callback -> upload discard -> transaction/publication -> reply.
; Source-only until qualified. These are finite served controls, not a theorem
; about all fragment schedules, crashes, or resource lifetimes.
(in-package "ACL2")
(include-book "consumer-session-support")

(defun fn2-cre-article (n)
  (declare (xargs :verify-guards nil))
  (let ((head (fn2-cw-crlf-octets
               '("From: eof@example.invalid" "Subject: eof"
                 "Newsgroups: local.test" "Message-ID: <eof@example.invalid>" ""))))
    (append head (repeat (nfix (- (nfix n) (+ 2 (len head)))) 120)
            '(13 10))))

; The session helper interprets each list element as one receive size. Splitting
; the wire, rather than the article passed to a twin parser, exercises actual
; control-frame buffering before the actual CNS callback consumes it.
(defun fn2-cre-fragments (frames split)
  (declare (xargs :verify-guards nil))
  (let* ((wire (fn2-ccu-cat frames))
         (split (cond ((eq split :bad-final-byte)
                       (- (+ (len (nth 0 frames)) (len (nth 1 frames))) 1))
                      ((eq split :good-crlf)
                       (- (len (fn2-ccu-cat (take 4 frames))) 1))
                      (t (nfix split)))))
    (if (zp split) frames
      (list (take (min split (len wire)) wire)
            (nthcdr (min split (len wire)) wire)))))

(defun fn2-cre-after-frames (n wire)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) wire
    (fn2-cre-after-frames (- n 1) (nthcdr (len (fnc-frame-extent wire)) wire))))

(defun fn2-cre-append-mid-p (wire expected)
  (declare (xargs :verify-guards nil))
  (let ((r (fnc-parse (cadr (assoc-eq 'append *fn2-fnct-results*)) (fnc-k28-result wire))))
    (and r (not (equal expected "")) (equal (fnc-chars-string (car (cadr r))) expected))))

(defun fn2-cre-run (n split)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-ccu-profile* :echo nil fn2-core))
           ((mv epoch fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
              (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           (article (fn2-cre-article n))
           ; Same Message-ID on retry: a malformed frame must not have claimed
           ; its identity or published the otherwise valid CRLF prefix.
           (frames (list (fnc-register 1 1)
                         (fnc-append 9 (append article '(13)))
                         (fnc-status 1)
                         (fnc-append 10 article)
                         (fnc-status 1) (fnc-control 5)))
           ((mv status wire & fn2-core)
            (fn2-ccu-session 0 (fn2-cre-fragments frames split) fn2-core)))
        (mv (list epoch status
                  (fnc-replies '(register append status append status) wire)
                  (fn2-core-stop-reason fn2-core) wire) fn2-core))
      answer)))

(defun fn2-cre-ok (n split)
  (declare (xargs :verify-guards nil))
  (let* ((r (fn2-cre-run n split)) (replies (nth 2 r))
         (accepted (nth 3 replies)) (position (car (nth 2 accepted)))
         (wire (nth 4 r))
         (refusal-wire (fn2-cre-after-frames 1 wire))
         (accept-wire (fn2-cre-after-frames 3 wire))
         (mid "<eof@example.invalid>"))
    ; :quiet alone also means a fatal core stop in fn2-cw-loop. Require
    ; both its idle termination and zero stop reason, plus real epoch setup.
    (and (eq (nth 0 r) :ok)
         (eq (nth 1 r) :quiet)
         (equal (nth 3 r) 0)
         (equal (len replies) 5)
         (equal (nth 0 replies) '(:accepted "" 0))
         (equal (nth 1 replies) '(:refused "framing" nil))
         (equal (nth 2 replies) '(:accepted "" (0 0 0)))
         (eq (car accepted) :accepted) (equal (cadr accepted) "")
         (posp position) (equal (cadr (nth 2 accepted)) 1)
         (fn2-cre-append-mid-p accept-wire mid)
         (not (fn2-cre-append-mid-p accept-wire ""))
         (not (fn2-cre-append-mid-p accept-wire "<other@example.invalid>"))
         (not (fn2-cre-append-mid-p refusal-wire mid))
         (equal (nth 4 replies) (list :accepted "" (list 0 position position))))))

; Bad article lengths 1024/1025/1026 straddle the real feed quantum. The
; trailing CR can be the last octet of a quantum or follow a yielded step.
(assert-event (fn2-cre-ok 1023 0))
(assert-event (fn2-cre-ok 1024 0))
(assert-event (fn2-cre-ok 1025 0))
; Transport split inside the first frame and around the feed quantum.
(assert-event (fn2-cre-ok 1024 1))
(assert-event (fn2-cre-ok 1024 1024))

; Separate the malformed terminal CR, then the valid retry's CR/LF.
(assert-event (fn2-cre-ok 1024 :bad-final-byte))
(assert-event (fn2-cre-ok 1024 :good-crlf))

; Capture the malformed request's real storage handle, before its upload can
; drain. A different free page in this size class could admit another upload
; even if this one leaked. Check the old generation itself.
(defun fn2-cre-owned-page (cns fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let* ((u (fn2-cns-row-upload cns fn2-core))
         (ug (fn2-cns-row-upload-gen cns fn2-core)))
    (and (equal (fn2-cns-row-verb cns fn2-core) *fn2-cns-verb-append*)
         (equal (fn2-cns-row-op cns fn2-core) 9)
         (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
         (equal (fn2-machine-generation u fn2-core) ug)
         (equal (fn2-upload-row-conn u fn2-core) cns)
         (equal (fn2-upload-row-conn-gen u fn2-core) (fn2-machine-generation cns fn2-core))
         (equal (fn2-upload-row-request u fn2-core) (fn2-cns-row-request cns fn2-core))
         (equal (fn2-upload-row-lease u fn2-core) *fn2-upload-lease-held*)
         (list (fn2-upload-row-lslot u fn2-core) (fn2-upload-row-lgen u fn2-core)
               *fn2-upload-kind* u ug))))

(defun fn2-cre-page-view (handle fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((list slot gen kind owner ogen) handle))
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (view)
      (and (natp slot) (< slot (fn2-pool-rows fn2-pool))
           (list (fn2-pool-handle-code slot gen fn2-pool)
                 (fn2-pool-workspace-code slot gen kind owner ogen fn2-pool)
                 (fn2-pool-state slot fn2-pool)
                 (fn2-pool-gen slot fn2-pool)
                 (fn2-pool-reservable-count (fn2-pool-class slot fn2-pool) fn2-pool)))
      view)))

(defun fn2-cre-page-returned-p (handle view)
  (declare (xargs :verify-guards nil))
  ; A released slot may already serve another owner. At the generation limit
  ; release retires the slot permanently without incrementing its generation.
  (or (and (equal (take 2 view) '(:stale :stale))
           (< (nth 1 handle) (nth 3 view)))
      (and (equal (take 2 view) '(:ok :state))
           (equal (nth 2 view) *fn2-pool-state-retired*)
           (equal (nth 1 handle) (nth 3 view)))))

(defun fn2-cre-to-drain (fuel cns captured clients store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (b* ((handle (or captured (fn2-cre-owned-page cns fn2-core)))
       (u (nth 3 handle))
       ((when (and handle (equal (fn2-machine-generation u fn2-core) (nth 4 handle))
                   (equal (fn2-machine-phase u fn2-core) *fn2-upload-state-draining*)
                   (equal (fn2-upload-row-lease u fn2-core) *fn2-upload-lease-held*)))
        (mv handle clients store fn2-core))
       ((when (or (zp fuel) (fn2-core-stopped-p fn2-core)))
        (mv nil clients store fn2-core))
       ((mv & & & & & fn2-core) (fn2-transition t 4 fn2-core))
       ((mv & & clients store fn2-core) (fn2-cw-adapter-one 1 clients store fn2-core)))
    (fn2-cre-to-drain (- fuel 1) cns handle clients store fn2-core)))

(defun fn2-cre-lease-case (hold)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-ccu-profile* :echo nil fn2-core))
           ((mv epoch fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           (article (fn2-cre-article 256))
           (frames (list (fnc-register 1 1) (fnc-append 9 (take 254 article))
                         (fnc-status 1) (fnc-control 5)))
           (fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
           ((mv admit fn2-core) (fn2-machine-admit-fn2-ctl 0 77 3 0 fn2-core))
           ((unless (and (eq epoch :ok) (eq admit :ok))) (mv (list :init epoch admit) fn2-core))
           ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
           (fn2-core (fn2-exec-wake wake fn2-core))
           (cns (fn2-machine-kind-base *fn2-cns-kind* fn2-core))
           ((mv handle clients store fn2-core)
            (fn2-cre-to-drain 40000 cns nil (list (fn2-ccu-client frames)) nil fn2-core))
           ((unless handle) (mv :missed-owner fn2-core))
           ((list slot gen kind owner ogen) handle)
           (before (fn2-cre-page-view handle fn2-core))
           ((unless (and (equal (take 2 before) '(:ok :ok)) (posp (nth 4 before))))
            (mv (list :no-owned-page-with-spare handle before) fn2-core))
           ; A test-only independent reader holds the same taking at the real
           ; drain cut. Its zero-length query is valid on the unfilled page.
           ((mv retained fn2-core)
            (if hold
                (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (code fn2-pool)
                  (fn2-pool-query-acquire slot gen 0 0 kind owner ogen fn2-pool)
                  (mv code fn2-core))
              (mv :ok fn2-core)))
           ((mv quiet clients store fn2-core) (fn2-cw-loop 40000 0 1 clients store fn2-core))
           (wire (caar (fn2-cw-results clients)))
           (replies (fnc-replies '(register append status) wire))
           (view (fn2-cre-page-view handle fn2-core))
           (returned (fn2-cre-page-returned-p handle view))
           ((unless (and (eq retained :ok) (eq quiet :quiet) (not (fn2-core-stopped-p fn2-core))
                         (equal replies '((:accepted "" 0) (:refused "framing" nil) (:accepted "" (0 0 0))))))
            (mv (list :refusal retained quiet replies view) fn2-core))
           ((when hold)
            (mv (if (and (not returned) (equal (take 2 view) '(:ok :held))
                         (equal (nth 2 view) *fn2-pool-state-workspace*)
                         (equal (fn2-machine-generation owner fn2-core) ogen)
                         (equal (fn2-machine-phase owner fn2-core) *fn2-upload-state-draining*))
                    :owned-after-refusal (list :missing-held-control handle view)) fn2-core))
           ((unless (and returned (equal (fn2-machine-phase owner fn2-core) *fn2-upload-state-free*)
                         (< ogen (fn2-machine-generation owner fn2-core))))
            (mv (list :leaked handle view) fn2-core))
           ; Only now supply the valid file, on the same live core and store.
           ((mv done wire & fn2-core)
            (fn2-ccu-session-store 1 (list (fnc-append 10 article) (fnc-status 1) (fnc-control 5)) store fn2-core))
           (answers (fnc-replies '(append status) wire))
           (position (car (caddr (car answers)))))
        (mv (if (and (eq done :quiet) (not (fn2-core-stopped-p fn2-core)) (posp position)
                     (equal answers (list (list :accepted "" (list position 1))
                                          (list :accepted "" (list 0 position position))))
                     (fn2-cre-append-mid-p wire "<eof@example.invalid>"))
                :returned-then-accepted (list :retry answers)) fn2-core))
      answer)))

(assert-event (equal (fn2-cre-lease-case nil) :returned-then-accepted))
(assert-event (equal (fn2-cre-lease-case t) :owned-after-refusal))
