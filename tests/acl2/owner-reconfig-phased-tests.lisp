; Ground witnesses and teeth for books/owner-reconfig-phased.lisp (ruling 19,
; LIVE-RECONFIGURE).
(in-package "ACL2")
(include-book "../../books/owner-reconfig-phased")
(include-book "../../books/defkeystone")

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

; R0 witnesses: the host's loop over fn-orp-step on a ground stream of
; observations.
(assert-event
 (equal (fn-orp-trace :start t (fn-orp-events :staged t :ok :durable :durable '(("a" . :ok))))
        (fn-orp-run t :staged t :ok :durable :durable '(("a" . :ok)))))
(assert-event
 (equal (fn-orp-trace :start nil '(:go :staged :authorized :ok :durable :durable
                                   (:feed "a") :ok (:feed "b") :ok :feeds-done))
        (fn-orp-run nil :staged t :ok :durable :durable '(("a" . :ok) ("b" . :ok)))))
; R0 teeth: the step answers only the stream it expects.  A :feeds-done
; while a journal's word is still owed faults rather than installing, and a
; completion word sent while the publication is still running faults too.
(assert-event
 (equal (fn-orp-trace :start nil '(:go :staged :authorized :ok :durable :durable
                                   (:feed "a") :feeds-done))
        '((:owner . :stage) (:owner . :authorize) (:off . :observe) (:off . :publish)
          (:owner . :complete) (:owner . :refresh) (:off :feed-io . "a") (:owner . :fault))))
(assert-event
 (mv-let (effects next) (fn-orp-step :observing nil :durable)
   (and (equal effects '((:owner . :fault))) (equal next :done))))

; RULING19-MODEL-AWAITS-HOST: these teeth cover the model, not host locking.
; R0/R1/R2/R4/R5/R6 have no top-level hypotheses.  The implications inside
; R5/R6 are part of their conclusions, not removable assumptions.
(defteeth fn-orp-step-runs-the-phased-run
  :claim (()
          (equal (fn-orp-trace :start reserve (fn-orp-events stage auth observe publish verdict feeds))
                 (fn-orp-run reserve stage auth observe publish verdict feeds)))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))))
  :breaks ()
  :mutations ((skip-start
               (:conclusion
                (equal (fn-orp-trace :start reserve (cdr (fn-orp-events stage auth observe publish verdict feeds)))
                       (fn-orp-run reserve stage auth observe publish verdict feeds)))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))))
               :fault "the event driver drops the initial :go")))

(defteeth fn-orp-phased-keeps-the-durable-effects
  :claim (()
          (equal (fn-orp-durable (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))
                 (fn-orp-durable (fn-orp-inline stage auth observe publish verdict feeds))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))))
  :breaks ()
  :mutations ((reverse-durable-order
               (:conclusion
                (equal (fn-orp-durable (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))
                       (reverse (fn-orp-durable (fn-orp-inline stage auth observe publish verdict feeds)))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))))
               :fault "durable effects are replayed in reverse order")))

(defteeth fn-orp-phased-answers-as-inline
  :claim (()
          (let ((answer (fn-orp-answer (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))))
            (and (equal answer (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds)))
                 (member-equal answer '(:accept :refuse :fence :fault)))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :uncertain) (verdict nil) (feeds nil))
  :breaks ()
  :mutations ((uncertain-is-refusal
               (:conclusion
                (equal (fn-orp-answer (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))
                       :refuse))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :uncertain) (verdict nil) (feeds nil))
               :fault "an uncertain publication is reported as a definite refusal")))

(defteeth fn-orp-accepted-keeps-the-owner-effects
  :claim (((accepted (equal (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds)) :accept)))
          (equal (fn-orp-owner (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))
                 (fn-orp-owner (fn-orp-inline stage auth observe publish verdict feeds))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))))
  :breaks ((accepted ((feeds *orp-feed-fault*))))
  :mutations ((skip-first-owner-effect
               (:conclusion
                (equal (cdr (fn-orp-owner (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds))))
                       (fn-orp-owner (fn-orp-inline stage auth observe publish verdict feeds))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))))
               :fault "the owner omits staging from an accepted run")))

(defteeth fn-orp-phased-holds-the-owner-only-in-quanta
  :claim (() (fn-orp-labelsp (fn-orp-run reserve stage auth observe publish verdict feeds)))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))))
  :breaks ()
  :mutations ((io-under-owner
               (:conclusion
                (fn-orp-labelsp
                 (subst :owner :off
                        (fn-orp-run reserve stage auth observe publish verdict feeds))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))))
               :fault "off-owner I/O, including publication, is labelled as holding the owner")))

(defteeth fn-orp-refusal-unstages-and-fence-keeps-the-stage
  :claim (()
          (let ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds))))
            (and (implies (and (equal (fn-orp-answer effects) :refuse) (equal stage :staged))
                          (member-equal :unstage (fn-orp-before :refuse effects)))
                 (implies (member-equal (fn-orp-answer effects) '(:fence :fault))
                          (not (member-equal :unstage effects))))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :refused) (verdict nil) (feeds nil))
  :breaks ()
  :mutations ((refusal-keeps-stage
               (:conclusion
                (not (member-equal :unstage (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :refused) (verdict nil) (feeds nil))
               :fault "a definite publication refusal leaks the staged record")
              (fence-unstages
               (:conclusion
                (member-equal :unstage (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :uncertain) (verdict nil) (feeds nil))
               :fault "an uncertain publication discards its recovery stage")))

(defteeth fn-orp-reservation-is-converted-or-released
  :claim (()
          (let* ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))
                 (answer (fn-orp-answer effects)))
            (and (iff (member-equal :reserve effects) (and reserve (equal stage :staged) auth))
                 (implies (member-equal :reserve effects)
                          (member-equal :reserve (fn-orp-before :observe effects)))
                 (implies (equal answer :accept) (iff (member-equal :convert effects) reserve))
                 (implies (member-equal :convert effects) (equal answer :accept))
                 (implies (and (equal answer :refuse) (member-equal :reserve effects))
                          (member-equal :release (fn-orp-before :unstage effects)))
                 (not (and (member-equal :convert effects) (member-equal :release effects))))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok))))
  :breaks ()
  :mutations ((accepted-releases
               (:conclusion
                (member-equal :release (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok))))
               :fault "acceptance releases credit instead of converting it")
              (refused-converts
               (:conclusion
                (member-equal :convert (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :refused) (verdict nil) (feeds nil))
               :fault "refusal converts a reservation for data never accepted")))

; Exercise the alternate R5/R6 branches with their premises true, alongside
; the complete conclusions checked above by defteeth.
(assert-event
 (let ((effects (strip-cdrs (fn-orp-run t :staged t :ok :uncertain nil nil))))
   (and (member-equal (fn-orp-answer effects) '(:fence :fault))
        (not (member-equal :unstage effects)))))
(assert-event
 (let ((effects (strip-cdrs (fn-orp-run t :staged t :ok :refused nil nil))))
   (and (equal (fn-orp-answer effects) :refuse)
        (member-equal :reserve effects)
        (member-equal :release (fn-orp-before :unstage effects))
        (not (member-equal :convert effects)))))

(defteeth-check)
