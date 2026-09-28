; Witnesses and teeth for books/owner-stop-drain.lisp (lane health-truth-stop,
; 2026-09-28; PKT-875, PRF-357).  Every scheduler value is REACHED from
; fn-otm-init through the host's calls: the committer's :commit pick and its
; START event (fnn-owner-gate-pick, fnn-owner-commit-event), and the clock
; events the drain appends before each observation (fnn-owner-sched-snapshot
; -> fnn-owner-disk-event :clock).
(in-package "ACL2")
(include-book "../../books/owner-stop-drain")
(include-book "must-fail-checked")

(defun osdt-pick (s w) (mv-let (c s2) (fn-otm-next s w) (declare (ignore c)) s2))
(defun osdt-event (s e) (mv-let (a s2) (fn-otm-commit-event s e) (declare (ignore a)) s2))
(defun osdt-clock (s now) (mv-let (w s2) (fn-otm-disk-event s :clock now nil) (declare (ignore w)) s2))

; Idle: the drain starts at 1,000 ms with nothing in flight.
(defconst *osdt-idle0* (osdt-clock (fn-otm-init) 1000))
(defconst *osdt-idle1* (osdt-clock *osdt-idle0* 1100))
; In flight: the committer's START sealed a batch (phase :staged); the
; drain started at 1,000 ms and observes at 1,000 + X.
(defconst *osdt-f0* (osdt-clock (osdt-event (osdt-pick (fn-otm-init) '(0 0 0 0 1 0)) :started)
                                1000))
(defun osdt-at (x) (osdt-clock *osdt-f0* (+ 1000 x)))

(assert-event (not (fn-osd-in-flight-p *osdt-idle1*)))
(assert-event (fn-osd-in-flight-p *osdt-f0*))
(assert-event (fn-osd-in-flight-p (osdt-at 7000)))
(assert-event (equal (fn-osd-elapsed *osdt-f0* (osdt-at 7000)) 7000))

; A stalled barrier: issued at 1,000 ms with H 6,000, a clock event at
; 7,100 ms enters :stalled (its members are told uncertain by the
; committer); the drain began at 1,500 ms.
(defun osdt-issue (s now l) (mv-let (w s2) (fn-otm-disk-event s :issue now l) (declare (ignore w)) s2))
(defconst *osdt-st-issued* (osdt-issue (osdt-event (osdt-pick (fn-otm-init) '(0 0 0 0 1 0)) :started)
                                       1000 '(2000 6000 250)))
(defconst *osdt-st0* (osdt-clock *osdt-st-issued* 1500))
(defconst *osdt-st* (osdt-clock *osdt-st0* 7100))
(assert-event (not (fn-osd-stall-told-p *osdt-st0*)))
(assert-event (fn-osd-stall-told-p *osdt-st*))
(assert-event (fn-osd-in-flight-p *osdt-st*))

; The limits the native case sets (D 2,000, H 6,000, cadence 250) and none
; (the defaults: H 30,000).
(defconst *osdt-l* '(2000 6000 250))
(assert-event (equal (fn-osd-deadline *osdt-l*) 6000))
(assert-event (equal (fn-osd-deadline nil) 30000))
; H is raised to D when a profile sets it below.
(assert-event (equal (fn-osd-deadline '(9000 6000 250)) 9000))

; --- fn-osd-stops-only-when-nothing-is-owed.
; Positive (first disjunct): idle, nothing awaits or is unsent: :stop at once.
(assert-event (equal (fn-osd-drain-step *osdt-idle0* *osdt-idle1* *osdt-l* 0 0 nil) :stop))
(assert-event (fn-osd-quiet-p *osdt-idle1* 0 0 nil))
; Positive (second disjunct): released, past H + grace, a member still
; awaiting (its client did not read): :stop, not quiet, and the bound holds.
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 16000) *osdt-l* 1 1 t) :stop))
(assert-event (not (fn-osd-quiet-p (osdt-at 16000) 1 1 t)))
(assert-event (<= (+ (fn-osd-deadline *osdt-l*) *fn-osd-grace-ms*)
                  (fn-osd-elapsed *osdt-f0* (osdt-at 16000))))
; Released and quiet while the barrier is still in flight: the told members
; are gone, :stop (the in-flight batch was released).
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 6500) *osdt-l* 0 0 t) :stop))
; Hypothesis removal: a member awaiting its batch in flight before H: the
; step is not :stop, and the conclusion fails (nothing quiet, not released).
(assert-event (not (equal (fn-osd-drain-step *osdt-f0* (osdt-at 500) *osdt-l* 1 0 nil) :stop)))
(assert-event (not (or (fn-osd-quiet-p (osdt-at 500) 1 0 nil) nil)))
; In flight with nobody awaiting and nothing unsent is still owed its
; COMPLETE (a member whose connection has not registered yet): not quiet.
(assert-event (not (fn-osd-quiet-p (osdt-at 500) 0 0 nil)))
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 500) *osdt-l* 0 0 nil) :wait))
(must-fail-checked
 (defthm osdt-stop-without-its-hypothesis
   (or (fn-osd-quiet-p s awaiting unsent released)
       (and released
            (<= (+ (fn-osd-deadline limits) *fn-osd-grace-ms*)
                (fn-osd-elapsed s0 s))))
   :hints (("Goal" :in-theory (enable fn-osd-quiet-p)))))

; --- fn-osd-releases-only-at-the-deadline.
; Positive: in flight, one member awaiting, at H exactly, not released.
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 6000) *osdt-l* 1 0 nil) :release))
(assert-event (<= (fn-osd-deadline *osdt-l*) (fn-osd-elapsed *osdt-f0* (osdt-at 6000))))
(assert-event (not (fn-osd-quiet-p (osdt-at 6000) 1 0 nil)))
; Hypothesis removal: one millisecond before H the step is :wait and the
; conclusion's deadline conjunct fails.
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 5999) *osdt-l* 1 0 nil) :wait))
(assert-event (not (<= (fn-osd-deadline *osdt-l*) (fn-osd-elapsed *osdt-f0* (osdt-at 5999)))))
(must-fail-checked
 (defthm osdt-release-without-its-hypothesis
   (<= (fn-osd-deadline limits) (fn-osd-elapsed s0 s))))

; --- fn-osd-drain-ends-by-the-deadline, first conjunct (:release).
; Positive: all three hypotheses (above, at 6,000).  Removal of each:
;   released: :wait (the grace), not :release;
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 6000) *osdt-l* 1 0 t) :wait))
;   the deadline: :wait;
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 5999) *osdt-l* 1 0 nil) :wait))
;   not quiet (idle, nothing owed, past H): :stop.
(assert-event (equal (fn-osd-drain-step *osdt-idle0* (osdt-clock *osdt-idle0* 8000) *osdt-l* 0 0 nil)
                     :stop))
; --- second conjunct (:stop at H + grace after the release).
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 16000) *osdt-l* 1 0 t) :stop))
;   released removed: :release, not :stop;
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 16000) *osdt-l* 1 0 nil) :release))
; The stall told the members of the barrier in flight: once each was
; handed its reply the drain stops, before its own deadline (5,600 ms in).
(assert-event (equal (fn-osd-drain-step *osdt-st0* *osdt-st* '(2000 6000 250) 0 0 nil) :stop))
(assert-event (equal (fn-osd-drain-step *osdt-st0* *osdt-st* '(2000 6000 250) 1 0 nil) :wait))
(assert-event (equal (fn-osd-drain-step *osdt-st0* *osdt-st0* '(2000 6000 250) 0 0 nil) :wait))
;   the grace removed (one millisecond short): :wait.
(assert-event (equal (fn-osd-drain-step *osdt-f0* (osdt-at 15999) *osdt-l* 1 0 t) :wait))
(must-fail-checked
 (defthm osdt-ends-without-released
   (implies (<= (+ (fn-osd-deadline limits) *fn-osd-grace-ms*) (fn-osd-elapsed s0 s))
            (equal (fn-osd-drain-step s0 s limits awaiting unsent released) :stop))))

; The members the release tells (the committer's fn-otm-stall-releases): an
; accepted member (:durable, renderable) and an own-uncertain one: both
; uncertain, neither :rendered; the same members at a fenced COMPLETE are
; told their own words (fn-ocs-member-releases :complete).
(assert-event (equal (fn-otm-stall-releases '((:durable t) (:uncertain t)))
                     '(:uncertain-reply :own-uncertain)))
(assert-event (equal (fn-ocs-member-releases :complete '((:durable t) (:uncertain t)))
                     '(:rendered :own-uncertain)))

; The service log's lines.
(assert-event (equal (fn-osd-log-line :release *osdt-f0* (osdt-at 6000) *osdt-l* 1)
                     (fn-osch-text "stopping: the drain deadline passed after 6000 ms; the posts in flight are told the outcome is uncertain")))
