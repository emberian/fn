; The scalar physical-result interpretation shared by native I/O and simulation.
; Kept apart from simulator state, replay and process-death machinery.
(in-package "ACL2")
(include-book "vocab")
(include-book "std/util/bstar" :dir :system)

(defun fn2-sim-result-outcome (kind code count len)
  (declare (xargs :guard (and (natp count) (natp len))))
  (cond ((eq code :cancelled) *fn2-outcome-cancelled*)
        ((and (equal kind *fn2-action-write*) (< count len)) *fn2-outcome-failed*)
        ((or (eq code :ok) (eq code :eof)
             (and (< 0 count) (or (equal kind *fn2-action-send*) (equal kind *fn2-action-receive*))))
         (if (and (< count len) (or (equal kind *fn2-action-send*) (equal kind *fn2-action-read*)))
             *fn2-outcome-short* *fn2-outcome-done*))
        (t *fn2-outcome-failed*)))
(defthm fn2-sim-result-outcome-type
  (unsigned-byte-p 8 (fn2-sim-result-outcome kind code count len)))
(in-theory (disable fn2-sim-result-outcome))
(defun fn2-sim-result-reason (kind code outcome)
  (declare (xargs :guard t))
  (if (not (equal outcome *fn2-outcome-failed*)) *fn2-reason-none*
    (cond ((equal kind *fn2-action-accept*) *fn2-reason-exhausted*)
          ((equal kind *fn2-action-connect*) *fn2-reason-refused*)
          ((or (equal kind *fn2-action-receive*) (equal kind *fn2-action-send*))
           (if (eq code :reset) *fn2-reason-reset* *fn2-reason-closed*))
          ((equal kind *fn2-action-tls-start*) *fn2-reason-handshake*)
          ((equal kind *fn2-action-write*)
           (cond ((eq code :no-space) *fn2-reason-no-space*)
                 ((eq code :ok) *fn2-reason-uncertain*)
                 (t *fn2-reason-io*)))
          (t *fn2-reason-io*))))

(defthm fn2-sim-result-reason-type
  (unsigned-byte-p 8 (fn2-sim-result-reason kind code outcome)))
(in-theory (disable fn2-sim-result-reason))

; Scalar interpretation stays opaque in the state-preservation proofs.
(defun fn2-sim-terminal-values (kind code physical-count aux len release cancelled)
  (declare (xargs :guard (natp len)))
  (b* ((count (if (and (unsigned-byte-p 32 physical-count) (<= physical-count len))
                  physical-count 0))
       (outcome (fn2-sim-result-outcome kind code count len))
       (outcome (if (and (equal kind *fn2-action-cancel*) (not (eq code :cancelled)))
                    (if cancelled *fn2-outcome-done* *fn2-outcome-not-found*) outcome))
       (reason (fn2-sim-result-reason kind code outcome))
       (count (if (or (equal kind *fn2-action-accept*) (equal kind *fn2-action-connect*)
                      (and (fn2-op-input-kindp kind)
                           (or (= outcome *fn2-outcome-failed*) (= outcome *fn2-outcome-cancelled*))))
                  0 count))
       (aux0 (cond ((or (equal kind *fn2-action-accept*) (equal kind *fn2-action-connect*))
                    (if (unsigned-byte-p 32 physical-count) physical-count 0))
                   (release 1) (t 0)))
       (aux1 (if (and (or (equal kind *fn2-action-accept*) (equal kind *fn2-action-connect*))
                      (unsigned-byte-p 32 aux)) aux 0)))
    (mv outcome reason count aux0 aux1)))
(in-theory (disable fn2-sim-terminal-values))
(defthm fn2-sim-terminal-values-outcome-type
  (unsigned-byte-p 8
    (car (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))
(defthm fn2-sim-terminal-values-reason-type
  (unsigned-byte-p 8
    (mv-nth 1 (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))
(defthm fn2-sim-terminal-values-count-type
  (unsigned-byte-p 32
    (mv-nth 2 (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))
(defthm fn2-sim-terminal-values-aux0-type
  (unsigned-byte-p 32
    (mv-nth 3 (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))
(defthm fn2-sim-terminal-values-aux1-type
  (unsigned-byte-p 32
    (mv-nth 4 (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))

