; A5r's host-boundary units (layer doc 4.1.1, 4.1.6): the peer record of an
; Accept result, its validation, and the harvest latch.
(in-package "ACL2")
(include-book "../books/owed-host")

; 127.0.0.1:119, [::1]:8119 and a Unix-domain peer reach the listener row.
(defun fn2-host-test-peer-delivered ()
  (declare (xargs :verify-guards nil))
  (and (equal (fn2-accept-peer-run *fn2-peer-family-inet* 119 #x7f000001 0 0 0)
              (list 0 5 9 *fn2-peer-family-inet* 119 #x7f000001 0 0 0))
       (equal (fn2-accept-peer-run *fn2-peer-family-inet6* 8119 0 0 0 1)
              (list 0 5 9 *fn2-peer-family-inet6* 8119 0 0 0 1))
       (equal (fn2-accept-peer-run *fn2-peer-family-local* 0 0 0 0 0)
              (list 0 5 9 *fn2-peer-family-local* 0 0 0 0 0))))
; An :inet record with a nonzero second word, a :local record with a port,
; and an unnamed family are strays: the Accept stays unposted and the
; listener row keeps its initial record (capability 0, family :none).
(defun fn2-host-test-peer-delivered-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-peer-recordp *fn2-outcome-done* *fn2-peer-family-inet* 119 #x7f000001 5 0 0))
       (equal (fn2-accept-peer-run *fn2-peer-family-inet* 119 #x7f000001 5 0 0)
              (list 1 0 0 *fn2-peer-family-none* 0 0 0 0 0))
       (equal (fn2-accept-peer-run *fn2-peer-family-local* 22 0 0 0 0)
              (list 1 0 0 *fn2-peer-family-none* 0 0 0 0 0))
       (equal (fn2-accept-peer-run 7 119 #x7f000001 0 0 0)
              (list 1 0 0 *fn2-peer-family-none* 0 0 0 0 0))))
(assert-event (and (fn2-host-test-peer-delivered) (fn2-host-test-peer-delivered-negative)))

; The latch describes the observation being delivered: after an Accept's
; harvest it holds that Accept's record; after the next harvest of any
; other cell it is :none again. And a failed Accept may carry only :none.
(defun fn2-host-latch-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
           ((mv & op1 gen1 & fn2-core) (fn2-ah-take-accept 8 fn2-core))
           ((mv & op2 gen2 & fn2-core) (fn2-ah-take-accept 8 fn2-core))
           (fn2-core (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops)
                       (fn2-post-accept-result op1 gen1 *fn2-outcome-done* *fn2-reason-none* 5 9
                                               *fn2-peer-family-inet* 119 #x7f000001 0 0 0 fn2-ops)
                       fn2-core))
           ((mv & & & & & & & & & & fn2-core) (fn2-harvest-one fn2-core))
           ((mv f1 & a1 & & &) (fn2-core-observed-peer fn2-core))
           ; a failed Accept with a record is a stray; with :none it posts
           (s0 (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-stray fn2-ops) n))
           (fn2-core (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops)
                       (fn2-post-accept-result op2 gen2 *fn2-outcome-failed* *fn2-reason-aborted* 0 0
                                               *fn2-peer-family-inet* 119 #x7f000001 0 0 0 fn2-ops)
                       fn2-core))
           (s1 (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-stray fn2-ops) n))
           (fn2-core (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops)
                       (fn2-post-accept-result op2 gen2 *fn2-outcome-failed* *fn2-reason-aborted* 0 0
                                               *fn2-peer-family-none* 0 0 0 0 0 fn2-ops)
                       fn2-core))
           (s2 (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-stray fn2-ops) n))
           ((mv & & & & & & & & & & fn2-core) (fn2-harvest-one fn2-core))
           ((mv f2 & a2 & & &) (fn2-core-observed-peer fn2-core)))
        (mv (and (equal f1 *fn2-peer-family-inet*) (equal a1 #x7f000001)
                 (equal (- s1 s0) 1) (equal s2 s1)
                 (equal f2 *fn2-peer-family-none*) (equal a2 0))
            fn2-core))
      result)))
(assert-event (fn2-host-latch-control))
;; The configured listener (layer doc 4.1.4): defaults, explicit values, and
;; the named refusals for a value outside its width.
(include-book "../books/host-boundary")
(defun fn2-host-listener-control ()
  (declare (xargs :verify-guards nil))
  (and (equal (mv-list 3 (fn2-host-listener-bind *fn2-profile-tiny*)) (list :ok #x7f000001 0))
       (equal (mv-list 3 (fn2-host-listener-bind (list* '(:listener-port . 1119) '(:listener-address . #x0a000001)
                                                        *fn2-profile-tiny*)))
              (list :ok #x0a000001 1119))
       (equal (car (mv-list 3 (fn2-host-listener-bind (cons '(:listener-port . 65536) *fn2-profile-tiny*))))
              :listener-port)
       (equal (car (mv-list 3 (fn2-host-listener-bind (cons '(:listener-port . -1) *fn2-profile-tiny*))))
              :listener-port)
       (equal (car (mv-list 3 (fn2-host-listener-bind (cons '(:listener-address . 4294967296) *fn2-profile-tiny*))))
              :listener-address)))
(assert-event (fn2-host-listener-control))
(value-triple (cw "HOST UNIT: peer record delivered (inet, inet6, local), refused records stray, latch per observation, configured listener and its refusals PASS~%"))
