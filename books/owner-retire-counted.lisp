; S9 drain over carried counts and explicit producer-fence observations.
; The host must establish both observations; a bare zero is never success.
(in-package "ACL2")
(include-book "owner-feed-counts")
(include-book "owner-stop-drain")

(defun fn-ort-intake-action (retiringp)
  (declare (xargs :guard t))
  (if retiringp :refused :admit))

(defun fn-ort-fenced-input-consumed (received)
  (declare (xargs :guard t))
  (nfix received))

; A physical timeout retains the writer and its descriptor authority. Even
; an absent/joined writer is not settlement while accounted work remains.
(defun fn-ort-log-close-action (join-observation pending-lines pending-octets queuedp)
  (declare (xargs :guard t))
  (if (and (or (equal join-observation :joined)
               (equal join-observation :absent))
           (equal pending-lines 0) (equal pending-octets 0)
           (equal queuedp nil))
      :joined
    :held))

(defthm fn-ort-log-close-joined-requires-settlement
  (implies (equal (fn-ort-log-close-action observation lines octets queuedp) :joined)
           (and (or (equal observation :joined) (equal observation :absent))
                (equal lines 0) (equal octets 0) (equal queuedp nil)))
  :rule-classes nil)

(defun fn-ort-log-close-exit (prior uncertain action)
  (declare (xargs :guard (and (integerp prior) (integerp uncertain))))
  (if (equal action :joined) prior uncertain))

(defthm fn-ort-log-close-held-is-uncertain
  (implies (not (equal action :joined))
           (equal (fn-ort-log-close-exit prior uncertain action) uncertain)))

(defun fn-ort-report-close-action (log-action journal-observation)
  (declare (xargs :guard t))
  (if (and (equal log-action :joined)
           (or (equal journal-observation :closed)
               (equal journal-observation :absent)))
      :joined
    :held))

(defthm fn-ort-report-close-requires-journal-settlement
  (implies (equal (fn-ort-report-close-action log-action observation) :joined)
           (and (equal log-action :joined)
                (or (equal observation :closed) (equal observation :absent))))
  :rule-classes nil)

(defun fn-ort-drain-step-counted (s0 s seconds pending intake-fenced producers-settled)
  (declare (xargs :guard t))
  (cond ((and (equal intake-fenced t) (equal producers-settled t)
              (natp pending) (equal pending 0)) :drained)
        ((<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s)) :deadline)
        (t :wait)))

 ; A clock-only precheck runs before acquiring the semantic owner mutex.
(defun fn-ort-window-step (s0 s seconds)
  (declare (xargs :guard t))
  (if (<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s)) :deadline :wait))

(defthm fn-ort-window-step-never-drained
  (not (equal (fn-ort-window-step s0 s seconds) :drained)))

(defthm fn-ort-window-step-deadline-is-counted-deadline
  (implies (equal (fn-ort-window-step s0 s seconds) :deadline)
           (not (equal (fn-ort-drain-step-counted
                        s0 s seconds pending intake-fenced producers-settled) :wait))))

(defthm fn-ort-drained-requires-zero-and-both-fences
  (implies (equal (fn-ort-drain-step-counted
                  s0 s seconds pending intake-fenced producers-settled) :drained)
           (and (equal pending 0) (equal intake-fenced t)
                (equal producers-settled t)))
  :rule-classes nil)

(defthm fn-ort-deadline-is-independent-of-the-fences
  (implies (<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s))
           (not (equal (fn-ort-drain-step-counted
                        s0 s seconds pending intake-fenced producers-settled) :wait))))

(defthm fn-ort-counted-drain-waits-before-window-without-fenced-zero
  (implies (and (< (fn-osd-elapsed s0 s) (* 1000 (nfix seconds)))
                (not (and (equal intake-fenced t) (equal producers-settled t)
                          (natp pending) (equal pending 0))))
           (equal (fn-ort-drain-step-counted
                   s0 s seconds pending intake-fenced producers-settled) :wait)))

(in-theory (disable fn-ort-drain-step-counted fn-ort-intake-action
                    fn-ort-fenced-input-consumed fn-ort-window-step
                    fn-ort-log-close-action fn-ort-log-close-exit
                    fn-ort-report-close-action))
