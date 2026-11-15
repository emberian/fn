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
                  (fn2-core-stop-reason fn2-core)) fn2-core))
      answer)))

(defun fn2-cre-ok (n split)
  (declare (xargs :verify-guards nil))
  (let* ((r (fn2-cre-run n split)) (replies (nth 2 r))
         (accepted (nth 3 replies)) (position (car (nth 2 accepted))))
    (and (equal (len replies) 5)
         (equal (nth 0 replies) '(:accepted "" 0))
         (equal (nth 1 replies) '(:refused "framing" nil))
         (equal (nth 2 replies) '(:accepted "" (0 0 0)))
         (eq (car accepted) :accepted) (equal (cadr accepted) "")
         (posp position) (equal (cadr (nth 2 accepted)) 1)
         (equal (nth 4 replies) (list :accepted "" (list 0 position 1))))))

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
