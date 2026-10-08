; Ground witnesses and teeth for books/owner-reconfig-phased.lisp (ruling 19,
; LIVE-RECONFIGURE).
(in-package "ACL2")
(include-book "../../books/owner-reconfig-phased")

; An accepted reconfiguration naming two new peers: START and the
; authorization under the owner, the observation and the publication off it,
; COMPLETE and the refresh under it, both journals' I/O off it, their replays,
; the install and the answer under it.
(assert-event
 (equal (fn-orp-run nil :staged t :ok :durable :durable '(("a" . :ok) ("b" . :ok)))
        '((:owner . :stage) (:owner . :authorize) (:off . :observe) (:off . :publish)
          (:owner . :complete) (:owner . :refresh)
          (:off :feed-io . "a") (:off :feed-io . "b")
          (:owner :feed-replay . "a") (:owner :feed-replay . "b")
          (:owner . :install) (:owner . :continue) (:owner . :accept))))
(assert-event
 (equal (fn-orp-inline :staged t :ok :durable :durable '(("a" . :ok) ("b" . :ok)))
        '(:stage :authorize :observe :publish :complete :refresh
          (:feed-io . "a") (:feed-replay . "a") (:feed-io . "b") (:feed-replay . "b")
          :install :continue :accept)))
; R1 is not vacuous: an accepted run's durable effects are the publication
; and each journal, in order.
(assert-event
 (equal (fn-orp-durable (strip-cdrs (fn-orp-run nil :staged t :ok :durable :durable
                                                '(("a" . :ok) ("b" . :ok)))))
        '(:publish (:feed-io . "a") (:feed-io . "b"))))

; R2/R5: a refused publication unstages, then refuses; an uncertain one
; fences and keeps the stage; an unauthorized record never leaves quantum 1.
(assert-event
 (equal (fn-orp-run nil :staged t :ok :refused nil nil)
        '((:owner . :stage) (:owner . :authorize) (:off . :observe) (:off . :publish)
          (:owner . :unstage) (:owner . :continue) (:owner . :refuse))))
(assert-event
 (equal (fn-orp-run nil :staged t :ok :uncertain nil nil)
        '((:owner . :stage) (:owner . :authorize) (:off . :observe) (:off . :publish)
          (:owner . :fence))))
(assert-event
 (equal (fn-orp-run nil :staged nil :ok :durable :durable nil)
        '((:owner . :stage) (:owner . :authorize) (:owner . :unstage) (:owner . :continue)
          (:owner . :refuse))))
; A completion that is not :durable after a durable publication fences, and
; no journal is opened.
(assert-event
 (equal (fn-orp-run nil :staged t :ok :durable :recovery-required '(("a" . :ok)))
        '((:owner . :stage) (:owner . :authorize) (:off . :observe) (:off . :publish)
          (:owner . :complete) (:owner . :fence))))

; R3 teeth: the :accept hypothesis is needed.  When the second journal faults,
; inline has already replayed the first under the owner, but the phased run
; replays nothing.  The owner effects differ, while the durable effects and
; the answer (:fault) agree.
(defconst *orp-feed-fault* '(("a" . :ok) ("b" . :eio)))
(assert-event
 (not (equal (fn-orp-owner (strip-cdrs (fn-orp-run nil :staged t :ok :durable :durable *orp-feed-fault*)))
             (fn-orp-owner (fn-orp-inline :staged t :ok :durable :durable *orp-feed-fault*)))))
(assert-event
 (equal (fn-orp-answer (strip-cdrs (fn-orp-run nil :staged t :ok :durable :durable *orp-feed-fault*)))
        :fault))

; R4 teeth: a run that publishes under the owner, or labels an owner effect
; :off, is not labelled.
(assert-event (not (fn-orp-labelsp '((:owner . :stage) (:owner . :publish)))))
(assert-event (not (fn-orp-labelsp '((:owner . :stage) (:off . :complete)))))

; R5 teeth: a refusal that skipped the unstage, or a fence that unstaged, is
; what the statement excludes.
(assert-event (not (member-equal :unstage (fn-orp-before :refuse '(:stage :authorize :refuse)))))
(assert-event (member-equal :unstage '(:stage :unstage :fence)))

; R6 witnesses: the store-limit caller reserves in quantum 1, before the
; observation, converts on acceptance and releases on a refused publication.
(assert-event
 (equal (fn-orp-run t :staged t :ok :durable :durable '(("a" . :ok)))
        '((:owner . :stage) (:owner . :authorize) (:owner . :reserve)
          (:off . :observe) (:off . :publish)
          (:owner . :complete) (:owner . :refresh) (:off :feed-io . "a")
          (:owner :feed-replay . "a") (:owner . :install) (:owner . :convert)
          (:owner . :continue) (:owner . :accept))))
(assert-event
 (equal (fn-orp-run t :staged t :ok :refused nil nil)
        '((:owner . :stage) (:owner . :authorize) (:owner . :reserve)
          (:off . :observe) (:off . :publish)
          (:owner . :release) (:owner . :unstage) (:owner . :continue) (:owner . :refuse))))
; R6 teeth: an uncertain publication keeps the reservation (neither converted
; nor released: the service fences), and a caller without RESERVE never
; reserves.
(assert-event
 (let ((e (strip-cdrs (fn-orp-run t :staged t :ok :uncertain nil nil))))
   (and (member-equal :reserve e) (not (member-equal :convert e)) (not (member-equal :release e)))))
(assert-event
 (not (member-equal :reserve (strip-cdrs (fn-orp-run nil :staged t :ok :durable :durable nil)))))
