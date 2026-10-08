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
 (equal (fn-orp-run nil :staged t :ok :durable :durable '(("a" . :ok) ("b" . :ok)) :converted)
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
                                                '(("a" . :ok) ("b" . :ok)) :converted)))
        '(:publish (:feed-io . "a") (:feed-io . "b"))))

; R2/R5: a refused publication unstages, then refuses; an uncertain one
; fences and keeps the stage; an unauthorized record never leaves quantum 1.
(assert-event
 (equal (fn-orp-run nil :staged t :ok :refused nil nil :converted)
        '((:owner . :stage) (:owner . :authorize) (:off . :observe) (:off . :publish)
          (:owner . :unstage) (:owner . :continue) (:owner . :refuse))))
(assert-event
 (equal (fn-orp-run nil :staged t :ok :uncertain nil nil :converted)
        '((:owner . :stage) (:owner . :authorize) (:off . :observe) (:off . :publish)
          (:owner . :fence))))
(assert-event
 (equal (fn-orp-run nil :staged nil :ok :durable :durable nil :converted)
        '((:owner . :stage) (:owner . :authorize) (:owner . :unstage) (:owner . :continue)
          (:owner . :refuse))))
; A completion that is not :durable after a durable publication fences, and
; no journal is opened.
(assert-event
 (equal (fn-orp-run nil :staged t :ok :durable :recovery-required '(("a" . :ok)) :converted)
        '((:owner . :stage) (:owner . :authorize) (:off . :observe) (:off . :publish)
          (:owner . :complete) (:owner . :fence))))

; R3 teeth: the :accept hypothesis is needed.  When the second journal faults,
; inline has already replayed the first under the owner, but the phased run
; replays nothing.  The owner effects differ, while the durable effects and
; the answer (:fault) agree.
(defconst *orp-feed-fault* '(("a" . :ok) ("b" . :eio)))
(assert-event
 (not (equal (fn-orp-owner (strip-cdrs (fn-orp-run nil :staged t :ok :durable :durable *orp-feed-fault* :converted)))
             (fn-orp-owner (fn-orp-inline :staged t :ok :durable :durable *orp-feed-fault*)))))
(assert-event
 (equal (fn-orp-answer (strip-cdrs (fn-orp-run nil :staged t :ok :durable :durable *orp-feed-fault* :converted)))
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
 (equal (fn-orp-run t :staged t :ok :durable :durable '(("a" . :ok)) :converted)
        '((:owner . :stage) (:owner . :authorize) (:owner . :reserve)
          (:off . :observe) (:off . :publish)
          (:owner . :complete) (:owner . :refresh) (:off :feed-io . "a")
          (:owner :feed-replay . "a") (:owner . :install) (:owner . :convert)
          (:owner . :continue) (:owner . :accept))))
(assert-event
 (equal (fn-orp-run t :staged t :ok :refused nil nil :converted)
        '((:owner . :stage) (:owner . :authorize) (:owner . :reserve)
          (:off . :observe) (:off . :publish)
          (:owner . :release) (:owner . :unstage) (:owner . :continue) (:owner . :refuse))))
; R6 teeth: an uncertain publication keeps the reservation (neither converted
; nor released: the service fences), and a caller without RESERVE never
; reserves.
(assert-event
 (let ((e (strip-cdrs (fn-orp-run t :staged t :ok :uncertain nil nil :converted))))
   (and (member-equal :reserve e) (not (member-equal :convert e)) (not (member-equal :release e)))))
(assert-event
 (not (member-equal :reserve (strip-cdrs (fn-orp-run nil :staged t :ok :durable :durable nil :converted)))))

; R0 witnesses: the host's loop over fn-orp-step on a ground stream of
; observations.
(assert-event
 (equal (fn-orp-trace :start t (fn-orp-events t :staged t :ok :durable :durable '(("a" . :ok)) :converted))
        (fn-orp-run t :staged t :ok :durable :durable '(("a" . :ok)) :converted)))
(assert-event
 (equal (fn-orp-trace :start nil '(:go :staged :authorized :ok :durable :durable
                                   (:feed "a") :ok (:feed "b") :ok :feeds-done))
        (fn-orp-run nil :staged t :ok :durable :durable '(("a" . :ok) ("b" . :ok)) :converted)))
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
; R0/R1/R4/R5/R6 have no top-level hypotheses; R2/R3 carry the convert-succeeded
; hypothesis (PRL-ROW-SUM-INVARIANT discharges it) with a hypothesis-removal
; witness (converted); R7 names each of its hypotheses and breaks each.  The
; implications inside R5/R6 are part of their conclusions, not removable
; assumptions.
(defteeth fn-orp-step-runs-the-phased-run
  :claim (()
          (equal (fn-orp-trace :start reserve (fn-orp-events reserve stage auth observe publish verdict feeds convert))
                 (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))) (convert :converted))
  :breaks ()
  :mutations ((skip-start
               (:conclusion
                (equal (fn-orp-trace :start reserve (cdr (fn-orp-events reserve stage auth observe publish verdict feeds convert)))
                       (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))) (convert :converted))
               :fault "the event driver drops the initial :go")))

(defteeth fn-orp-phased-keeps-the-durable-effects
  :claim (()
          (equal (fn-orp-durable (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
                 (fn-orp-durable (fn-orp-inline stage auth observe publish verdict feeds))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))) (convert :converted))
  :breaks ()
  :mutations ((reverse-durable-order
               (:conclusion
                (equal (fn-orp-durable (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
                       (reverse (fn-orp-durable (fn-orp-inline stage auth observe publish verdict feeds)))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))) (convert :converted))
               :fault "durable effects are replayed in reverse order")))

(defteeth fn-orp-phased-answers-as-inline
  :claim (((converted (or (not reserve) (equal convert :converted))))
          (let ((answer (fn-orp-answer (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))))
            (and (equal answer (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds)))
                 (member-equal answer '(:accept :refuse :fence :fault)))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :uncertain) (verdict nil) (feeds nil) (convert :converted))
  :breaks ((converted ((publish :durable) (verdict :durable) (feeds '(("a" . :ok))) (convert :eio))))
  :mutations ((uncertain-is-refusal
               (:conclusion
                (equal (fn-orp-answer (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
                       :refuse))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :uncertain) (verdict nil) (feeds nil) (convert :converted))
               :fault "an uncertain publication is reported as a definite refusal")))

(defteeth fn-orp-accepted-keeps-the-owner-effects
  :claim (((converted (or (not reserve) (equal convert :converted)))
           (accepted (equal (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds)) :accept)))
          (equal (fn-orp-owner (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
                 (fn-orp-owner (fn-orp-inline stage auth observe publish verdict feeds))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))) (convert :converted))
  :breaks ((accepted ((feeds *orp-feed-fault*)))
           (converted ((convert :eio))))
  :mutations ((skip-first-owner-effect
               (:conclusion
                (equal (cdr (fn-orp-owner (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
                       (fn-orp-owner (fn-orp-inline stage auth observe publish verdict feeds))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))) (convert :converted))
               :fault "the owner omits staging from an accepted run")))

(defteeth fn-orp-phased-holds-the-owner-only-in-quanta
  :claim (() (fn-orp-labelsp (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))) (convert :converted))
  :breaks ()
  :mutations ((io-under-owner
               (:conclusion
                (fn-orp-labelsp
                 (subst :owner :off
                        (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok) ("b" . :ok))) (convert :converted))
               :fault "off-owner I/O, including publication, is labelled as holding the owner")))

(defteeth fn-orp-refusal-unstages-and-fence-keeps-the-stage
  :claim (()
          (let ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
            (and (implies (and (equal (fn-orp-answer effects) :refuse) (equal stage :staged))
                          (member-equal :unstage (fn-orp-before :refuse effects)))
                 (implies (member-equal (fn-orp-answer effects) '(:fence :fault))
                          (not (member-equal :unstage effects))))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :refused) (verdict nil) (feeds nil) (convert :converted))
  :breaks ()
  :mutations ((refusal-keeps-stage
               (:conclusion
                (not (member-equal :unstage (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :refused) (verdict nil) (feeds nil) (convert :converted))
               :fault "a definite publication refusal leaks the staged record")
              (fence-unstages
               (:conclusion
                (member-equal :unstage (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :uncertain) (verdict nil) (feeds nil) (convert :converted))
               :fault "an uncertain publication discards its recovery stage")))

(defteeth fn-orp-reservation-is-converted-or-released
  :claim (()
          (let* ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
                 (answer (fn-orp-answer effects)))
            (and (iff (member-equal :reserve effects) (and reserve (equal stage :staged) auth))
                 (implies (member-equal :reserve effects)
                          (member-equal :reserve (fn-orp-before :observe effects)))
                 (implies (equal answer :accept) (iff (member-equal :convert effects) reserve))
                 (implies (member-equal :convert effects)
                          (or (equal answer :accept)
                              (and (equal answer :fault)
                                   (member-equal :release (fn-orp-before :fault effects)))))
                 (implies (and (equal answer :refuse) (member-equal :reserve effects))
                          (member-equal :release (fn-orp-before :unstage effects)))
                 (implies (equal answer :accept) (not (member-equal :release effects)))
                 (implies (member-equal :release effects) (member-equal :reserve effects))
                 (implies (and (member-equal :convert effects) (member-equal :release effects))
                          (equal answer :fault)))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok))) (convert :converted))
  :breaks ()
  :mutations ((accepted-releases
               (:conclusion
                (member-equal :release (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok))) (convert :converted))
               :fault "acceptance releases credit instead of converting it")
              (refused-converts
               (:conclusion
                (member-equal :convert (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :refused) (verdict nil) (feeds nil) (convert :converted))
               :fault "refusal converts a reservation for data never accepted")
              (refused-convert-accepts
               (:conclusion
                (equal (fn-orp-answer (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
                       :accept))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok))) (convert :eio))
               :fault "a refused convert still accepts")))

; R6/R7 witnesses: a refused convert word.  The convert is attempted, the
; reservation is released, the service faults; nothing accepts or continues.
(assert-event
 (equal (fn-orp-run t :staged t :ok :durable :durable '(("a" . :ok)) :eio)
        '((:owner . :stage) (:owner . :authorize) (:owner . :reserve)
          (:off . :observe) (:off . :publish)
          (:owner . :complete) (:owner . :refresh) (:off :feed-io . "a")
          (:owner :feed-replay . "a") (:owner . :install) (:owner . :convert)
          (:owner . :release) (:owner . :fault))))
; Without RESERVE the convert word is never read.
(assert-event
 (equal (fn-orp-run nil :staged t :ok :durable :durable '(("a" . :ok)) :eio)
        (fn-orp-run nil :staged t :ok :durable :durable '(("a" . :ok)) :converted)))
; R0 for the refused convert: the host's step loop ends in :fault after the release.
(assert-event
 (equal (fn-orp-trace :start t (fn-orp-events t :staged t :ok :durable :durable '(("a" . :ok)) :eio))
        (fn-orp-run t :staged t :ok :durable :durable '(("a" . :ok)) :eio)))
(assert-event
 (mv-let (effects next) (fn-orp-step '(:feeding "a") t :feeds-done)
   (and (equal effects '((:owner :feed-replay . "a") (:owner . :install) (:owner . :convert)))
        (equal next :converting))))
(assert-event
 (mv-let (effects next) (fn-orp-step :converting t :converted)
   (and (equal effects '((:owner . :continue) (:owner . :accept))) (equal next :done))))
(assert-event
 (mv-let (effects next) (fn-orp-step :converting t :eio)
   (and (equal effects '((:owner . :release) (:owner . :fault))) (equal next :done))))

; KEYSTONE R7 teeth.
(defteeth fn-orp-refused-convert-faults-after-release
  :claim (((reserved reserve) (staged (equal stage :staged)) (authorized auth)
           (observed (equal observe :ok)) (published (equal publish :durable))
           (completed (equal verdict :durable))
           (feeds-ok (equal (fn-orp-feeds-final feeds) :ok))
           (refused (not (equal convert :converted))))
          (let ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
            (and (equal (fn-orp-answer effects) :fault)
                 (member-equal :convert (fn-orp-before :release effects))
                 (member-equal :release (fn-orp-before :fault effects))
                 (not (member-equal :accept effects))
                 (not (member-equal :continue effects)))))
  :witness ((reserve t) (stage :staged) (auth t) (observe :ok)
            (publish :durable) (verdict :durable) (feeds '(("a" . :ok))) (convert :eio))
  :breaks ((reserved ((reserve nil)))
           (staged ((stage :refused)))
           (authorized ((auth nil)))
           (observed ((observe :refused)))
           (published ((publish :uncertain)))
           (completed ((verdict :recovery-required)))
           (feeds-ok ((feeds '(("a" . :uncertain)))))
           (refused ((convert :converted))))
  :mutations ((fence-not-fault
               (:conclusion
                (equal (fn-orp-answer (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
                       :fence))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok))) (convert :eio))
               :fault "a refused convert fences instead of faulting")
              (no-release
               (:conclusion
                (not (member-equal :release (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok))) (convert :eio))
               :fault "the reservation is never released")
              (accepts-anyway
               (:conclusion
                (member-equal :accept (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
               ((reserve t) (stage :staged) (auth t) (observe :ok)
                (publish :durable) (verdict :durable) (feeds '(("a" . :ok))) (convert :eio))
               :fault "a refused convert accepts")))

; Exercise the alternate R5/R6 branches with their premises true, alongside
; the complete conclusions checked above by defteeth.
(assert-event
 (let ((effects (strip-cdrs (fn-orp-run t :staged t :ok :uncertain nil nil :converted))))
   (and (member-equal (fn-orp-answer effects) '(:fence :fault))
        (not (member-equal :unstage effects)))))
(assert-event
 (let ((effects (strip-cdrs (fn-orp-run t :staged t :ok :refused nil nil :converted))))
   (and (equal (fn-orp-answer effects) :refuse)
        (member-equal :reserve effects)
        (member-equal :release (fn-orp-before :unstage effects))
        (not (member-equal :convert effects)))))

(defteeth fn-orp-step-holds-the-owner-only-in-quanta
  :claim (() (fn-orp-labelsp (mv-nth 0 (fn-orp-step phase reserve event))))
  :witness ((phase :authorizing) (reserve t) (event :authorized))
  :breaks ()
  :mutations ((observe-under-owner
               (:conclusion
                (fn-orp-labelsp (subst :owner :off (mv-nth 0 (fn-orp-step phase reserve event)))))
               ((phase :authorizing) (reserve t) (event :authorized))
               :fault "the next name's observation (an lstat) run while the owner is held")))

(defteeth-check)
