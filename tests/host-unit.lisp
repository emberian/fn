; A5r's host-boundary units (layer doc 4.1.1, 4.1.6): the peer record of an
; Accept result, its validation, and the harvest latch.
(in-package "ACL2")
(include-book "../books/owed-host")

; 127.0.0.1:119, [::1]:8119 and Unix-domain peers (uid 501 gid 20, and
; root's 0 0) reach the listener row.
(defun fn2-host-test-peer-delivered ()
  (declare (xargs :verify-guards nil))
  (and (equal (fn2-accept-peer-run *fn2-peer-family-inet* 119 #x7f000001 0 0 0)
              (list 0 5 9 *fn2-peer-family-inet* 119 #x7f000001 0 0 0))
       (equal (fn2-accept-peer-run *fn2-peer-family-inet6* 8119 0 0 0 1)
              (list 0 5 9 *fn2-peer-family-inet6* 8119 0 0 0 1))
       (equal (fn2-accept-peer-run *fn2-peer-family-local* 0 501 20 0 0)
              (list 0 5 9 *fn2-peer-family-local* 0 501 20 0 0))
       (equal (fn2-accept-peer-run *fn2-peer-family-local* 0 0 0 0 0)
              (list 0 5 9 *fn2-peer-family-local* 0 0 0 0 0))))
; An :inet record with a nonzero second word, a :local record with a port
; or a third word, a :none record with credentials, and an unnamed family
; are strays: the Accept stays unposted and the listener row keeps its
; initial record (capability 0, family :none).
(defun fn2-host-test-peer-delivered-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-peer-recordp *fn2-outcome-done* *fn2-peer-family-inet* 119 #x7f000001 5 0 0))
       (equal (fn2-accept-peer-run *fn2-peer-family-inet* 119 #x7f000001 5 0 0)
              (list 1 0 0 *fn2-peer-family-none* 0 0 0 0 0))
       (equal (fn2-accept-peer-run *fn2-peer-family-local* 22 501 20 0 0)
              (list 1 0 0 *fn2-peer-family-none* 0 0 0 0 0))
       (equal (fn2-accept-peer-run *fn2-peer-family-local* 0 501 20 7 0)
              (list 1 0 0 *fn2-peer-family-none* 0 0 0 0 0))
       (equal (fn2-accept-peer-run *fn2-peer-family-none* 0 501 20 0 0)
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
(include-book "../books/host-boundary")
;; The first sim row holding an active Accept, scanning from INDEX.
(defun fn2-host-sim-find-accept (left index fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (nfix left)))
  (cond ((zp left) (mv nil 0))
        ((and (= (fn2-sim-active index fn2-sim) 1) (= (fn2-sim-kind index fn2-sim) *fn2-action-accept*))
         (mv t index))
        (t (fn2-host-sim-find-accept (- left 1) (+ 1 index) fn2-sim))))
;; The simulated host's peers (sim/network.lisp): a capability configured
;; :local with credentials hands them to the Accept that lands on it, through
;; the same boundary entry the native adapter posts with, so the listener row
;; observes uid and gid exactly; an unconfigured capability's Accept carries
;; :none; a record the boundary would refuse cannot be configured.
(defun fn2-host-sim-accept-loop (fuel fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv nil 0 fn2-core fn2-sim fn2-own)
    (b* (((mv & & & & fn2-core) (fn2-turn fn2-core))
         ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 8 0 fn2-core fn2-sim fn2-own))
         ((mv found slot) (fn2-host-sim-find-accept (fn2-sim-rows fn2-sim) 0 fn2-sim)))
      (if found (mv t slot fn2-core fn2-sim fn2-own)
        (fn2-host-sim-accept-loop (- fuel 1) fn2-core fn2-sim fn2-own)))))
(defun fn2-host-sim-local-run (configured family uid gid)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (result fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (result fn2-core fn2-sim fn2-own)
              (b* ((profile *fn2-profile-tiny*)
                   (fn2-core (fn2-init-executor profile :echo nil fn2-core))
                   (fn2-sim (fn2-sim-init 7 :none "host-unit" profile fn2-sim))
                   (fn2-own (fn2-own-init profile fn2-own))
                   ((mv set fn2-sim)
                    (if configured
                        (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim)))
                          (code fn2-sim-network) (fn2-network-set-peer 1 family uid gid fn2-sim-network)
                          (mv code fn2-sim))
                      (mv :ok fn2-sim)))
                   ((unless (eq set :ok)) (mv set fn2-core fn2-sim fn2-own))
                   ((mv found slot fn2-core fn2-sim fn2-own) (fn2-host-sim-accept-loop 8 fn2-core fn2-sim fn2-own))
                   ((unless found) (mv :no-accept fn2-core fn2-sim fn2-own))
                   (oslot (fn2-sim-owner-slot slot fn2-sim))
                   ;; word 1 lands the Accept on network capability 1
                   ((mv & fn2-core fn2-sim fn2-own)
                    (fn2-sim-echo-accept slot *fn2-fault-none* 1 t fn2-core fn2-sim fn2-own))
                   ((mv & & & & fn2-core) (fn2-turn fn2-core)))
                (mv (cddr (fn2-ah-listener-view oslot fn2-core)) fn2-core fn2-sim fn2-own))
              (mv result fn2-core fn2-sim)))
          (mv result fn2-core)))
      result)))
(defun fn2-host-sim-local-peer-control ()
  (declare (xargs :verify-guards nil))
  (and (equal (fn2-host-sim-local-run t *fn2-peer-family-local* 501 20)
              (list *fn2-peer-family-local* 0 501 20 0 0))
       (equal (fn2-host-sim-local-run nil 0 0 0)
              (list *fn2-peer-family-none* 0 0 0 0 0))
       (equal (fn2-host-sim-local-run t *fn2-peer-family-inet* 501 20) :peer)
       (equal (fn2-host-sim-local-run t *fn2-peer-family-local* 501 (expt 2 32)) :peer)))
(assert-event (fn2-host-sim-local-peer-control))

;; The configured listeners (layer doc 4.1.4): defaults, explicit values, the
;; owner-only Unix socket's path, and the named refusals for a value outside
;; its width.
(defun fn2-host-listener-control ()
  (declare (xargs :verify-guards nil))
  (let ((long (concatenate 'string "/" (coerce (make-list 103 :initial-element #\a) 'string))))
    (and (equal (mv-list 4 (fn2-host-listener-bind *fn2-profile-tiny*)) (list :ok #x7f000001 0 nil))
         (equal (mv-list 4 (fn2-host-listener-bind (list* '(:listener-port . 1119) '(:listener-address . #x0a000001)
                                                          *fn2-profile-tiny*)))
                (list :ok #x0a000001 1119 nil))
         (equal (mv-list 4 (fn2-host-listener-bind (cons '(:listener-path . "/run/fn/consumer.sock") *fn2-profile-tiny*)))
                (list :ok #x7f000001 0 "/run/fn/consumer.sock"))
         (equal (car (mv-list 4 (fn2-host-listener-bind (cons '(:listener-port . 65536) *fn2-profile-tiny*))))
                :listener-port)
         (equal (car (mv-list 4 (fn2-host-listener-bind (cons '(:listener-port . -1) *fn2-profile-tiny*))))
                :listener-port)
         (equal (car (mv-list 4 (fn2-host-listener-bind (cons '(:listener-address . 4294967296) *fn2-profile-tiny*))))
                :listener-address)
         ;; relative, empty, too long for sun_path, a NUL inside, not a string
         (equal (car (mv-list 4 (fn2-host-listener-bind (cons '(:listener-path . "fn.sock") *fn2-profile-tiny*))))
                :listener-path)
         (equal (car (mv-list 4 (fn2-host-listener-bind (cons '(:listener-path . "") *fn2-profile-tiny*))))
                :listener-path)
         (equal (car (mv-list 4 (fn2-host-listener-bind (cons (cons :listener-path long) *fn2-profile-tiny*))))
                :listener-path)
         (equal (car (mv-list 4 (fn2-host-listener-bind
                                 (cons (cons :listener-path (coerce (list #\/ #\a (code-char 0) #\b) 'string))
                                       *fn2-profile-tiny*))))
                :listener-path)
         (equal (car (mv-list 4 (fn2-host-listener-bind (cons '(:listener-path . 7) *fn2-profile-tiny*))))
                :listener-path))))
(assert-event (fn2-host-listener-control))
(value-triple (cw "HOST UNIT: peer record delivered (inet, inet6, local with uid/gid), refused records stray, latch per observation, configured listeners (TCP and the Unix path) and their refusals, the simulated host's :local peers PASS~%"))
