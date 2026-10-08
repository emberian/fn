; fn: the gate's hold for a phased live reconfiguration (ruling 19, item
; LOCK-R2-LIVE-RECONFIGURE-IO; books/owner-reconfig-phased.lisp, C7's asks
; (a) and (b), 2026-10-08).
;
; THE HOLD.  From the reconfiguration's first effect off O to the step's
; :done, the configuration it is installing is half there: the record may be
; durable and the configuration live while the new peers' journals are not.
; The gate keeps the hold in the scheduler value's HELD slot at an idle
; commit phase -- a combination the held commit never makes (it holds only
; in flight, books/owner-time-held.lisp) -- and while it is up:
;   * the gate admits only :inspect, :reader and :commit (the
;     reconfiguration's own re-entry), exactly the in-flight admission
;     (fn-otm-hold-next; no control, poster or transit quantum runs);
;   * the committer may not START and does not wake to collect
;     (fn-otm-committer-may-start, fn-otm-held-committer-wake: held);
;   * any commit event faults (fn-och-step at a held idle phase).
; A second reconfiguration that asks for the hold is answered :busy
; (fn-otm-hold-begin); its staging is refused by name as well, :busy, by the
; owner (books/owner-config.lisp fn-ocfg-reconfig-refusal), because the
; first record is still staged.
;
; Entries the host calls: fn-otm-hold-begin (quantum 1, before the first
; effect off O), fn-otm-hold-next (the gate's pick in place of fn-otm-next),
; fn-otm-hold-end (the quantum whose step answered :done).
(in-package "ACL2")
(include-book "owner-time-held")

(defun fn-otm-holdp (s)
  (declare (xargs :guard t))
  (and (fn-otm-held s) (not (fn-ocs-in-flight-p (fn-otm-phase-of s)))))

; (mv WORD S'): :held and the hold set, at an idle owner with nothing held;
; :busy and S unchanged otherwise (a batch in flight, a held commit, or a
; reconfiguration already holding).
(defun fn-otm-hold-begin (s)
  (declare (xargs :guard t))
  (if (or (fn-otm-held s) (fn-ocs-in-flight-p (fn-otm-phase-of s)))
      (mv :busy s)
    (mv :held (fn-otm-with-step s :idle nil t))))

; (mv WORD S'): :released and the hold cleared; :fault (S unchanged) when no
; reconfiguration holds.
(defun fn-otm-hold-end (s)
  (declare (xargs :guard t))
  (if (fn-otm-holdp s)
      (mv :released (fn-otm-with-step s :idle nil nil))
    (mv :fault s)))

; The gate's pick.  Under the hold it is the in-flight pick (the pipeline's
; own, on the value seen at an in-flight phase), and the hold is kept;
; otherwise it is fn-otm-next.
(defun fn-otm-hold-next (s w)
  (declare (xargs :guard t))
  (if (fn-otm-holdp s)
      (mv-let (class s2) (fn-otm-next (fn-otm-with-step s :staged nil t) w)
        (mv class (fn-otm-with-step s2 :idle nil t)))
    (fn-otm-next s w)))

; -----------------------------------------------------------------------------
; The value after a step, read back, and the pick's class.
(local (defthm fn-otr-phase-of-with-step
  (equal (fn-otm-phase-of (fn-otm-with-step s ph n h))
         (if (fn-ocs-in-flight-p ph) ph :idle))
  :hints (("Goal" :in-theory (enable fn-otm-with-step)))))
(local (defthm fn-otr-held-of-with-step
  (equal (fn-otm-held (fn-otm-with-step s ph n h)) (if h t nil))
  :hints (("Goal" :in-theory (enable fn-otm-with-step)))))
(local (defthm fn-otr-next-class
  (equal (mv-nth 0 (fn-otm-next x w))
         (mv-nth 0 (fn-ocs-next (fn-ocp-ocs (fn-otm-ocp x)) w)))
  :hints (("Goal" :in-theory (enable fn-otm-next fn-ocp-next)))))
(local (defthm fn-otr-phase-of-by-definition
  (equal (fn-ocs-phase (fn-ocp-ocs (fn-otm-ocp x))) (fn-otm-phase-of x))))
(local (in-theory (disable fn-otm-with-step fn-otm-phase-of fn-otm-next fn-ocs-next (:e fn-ocs-next) fn-otm-ocp fn-ocp-ocs)))

; KEYSTONE H1.  Under the hold the gate admits only :inspect, :commit and
; :reader (or nobody), and the hold stays up.
(defthm fn-otm-hold-admits-only-inspect-commit-and-reader
  (implies (fn-otm-holdp s)
           (and (member-equal (mv-nth 0 (fn-otm-hold-next s w)) '(:inspect :commit :reader nil))
                (fn-otm-holdp (mv-nth 1 (fn-otm-hold-next s w)))))
  :hints (("Goal" :use ((:instance fn-ocs-in-flight-admits-only-inspect-commit-and-reader
                                   (s (fn-ocp-ocs (fn-otm-ocp (fn-otm-with-step s :staged nil t)))))))))

; KEYSTONE H2.  Outside the hold the pick is fn-otm-next's.
(defthm fn-otm-hold-next-without-the-hold-is-next
  (implies (not (fn-otm-holdp s))
           (equal (fn-otm-hold-next s w) (fn-otm-next s w))))

; KEYSTONE H3.  Under the hold the committer neither starts nor collects, and
; every commit event faults.
(defthm fn-otm-hold-stops-the-committer
  (implies (fn-otm-holdp s)
           (and (not (fn-otm-committer-may-start s))
                (equal (fn-otm-held-committer-wake s returned queued w) :wait)
                (equal (mv-nth 0 (fn-otm-held-event s event)) :fault))))

; KEYSTONE H4.  The hold is taken exactly at an idle owner with nothing
; held, and a second request is :busy and changes nothing; the end releases
; exactly a hold.
(defthm fn-otm-hold-begin-and-end
  (and (iff (equal (mv-nth 0 (fn-otm-hold-begin s)) :held)
            (and (not (fn-otm-held s)) (not (fn-ocs-in-flight-p (fn-otm-phase-of s)))))
       (implies (equal (mv-nth 0 (fn-otm-hold-begin s)) :held)
                (fn-otm-holdp (mv-nth 1 (fn-otm-hold-begin s))))
       (implies (not (equal (mv-nth 0 (fn-otm-hold-begin s)) :held))
                (and (equal (mv-nth 0 (fn-otm-hold-begin s)) :busy)
                     (equal (mv-nth 1 (fn-otm-hold-begin s)) s)))
       (implies (fn-otm-holdp s)
                (and (equal (mv-nth 0 (fn-otm-hold-end s)) :released)
                     (not (fn-otm-held (mv-nth 1 (fn-otm-hold-end s))))
                     (not (fn-ocs-in-flight-p (fn-otm-phase-of (mv-nth 1 (fn-otm-hold-end s)))))))))
