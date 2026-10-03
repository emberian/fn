; Resumable pull/catch-up driver. Protocol/session/cursor decisions remain
; the existing session machines'. This book chooses which retained round
; gets one I/O quantum and the order of its already-authored effects/events.
(in-package "ACL2")
(include-book "feed-wire-input")

; Keys are ACL2's pair (kind peer), never a host-derived identity.
(defun fn-prd-key (kind peer)
  (declare (xargs :guard t))
  (list kind peer))

; The remaining sweep is captured, so one trickling round cannot repeatedly
; select itself before healthy pull/catch-up rounds in that same sweep.
(defun fn-prd-select (active remaining)
  (declare (xargs :guard (true-listp active)))
  (if (consp remaining)
      (if (member-equal (car remaining) active)
          (list (car remaining) (cdr remaining))
        (fn-prd-select active (cdr remaining)))
    (list nil nil)))

(defun fn-prd-sweep (active remaining)
  (declare (xargs :guard (true-listp active)))
  (if (consp remaining)
      (if (member-equal (car remaining) active)
          (cons (car remaining) (fn-prd-sweep active (cdr remaining)))
        (fn-prd-sweep active (cdr remaining)))
    nil))

; KEYSTONE PRF-1260: every retained admitted key in a stable sweep is visited,
; in order, without being skipped by driver selection. This
; assumes each physical I/O attempt returns; it is not a resolver/time bound.
(defthm fn-prd-sweep-visits-all-admitted-rounds
  (implies (and (true-listp remaining) (subsetp-equal remaining active))
           (equal (fn-prd-sweep active remaining) remaining)))

; A pending partial write/handshake/local continuation precedes later effects.
; Wait readiness never feeds a lost event or closes the protocol state.
(defun fn-prd-action (done effects events io now deadline)
  (declare (xargs :guard t))
  (cond (io (if (and (natp deadline) (<= deadline (nfix now)))
                (list :lost :timeout)
              (list :io io)))
        ((consp effects) (list :effect (car effects)))
        ((consp events) (list :event (car events)))
        (done (list :finish))
        (t (list :read))))

(defun fn-prd-deadline (now seconds)
  (declare (xargs :guard t))
  (+ (nfix now) (* 1000 (nfix seconds))))

(defun fn-prd-resume-at (now ms)
  (declare (xargs :guard t))
  (+ (nfix now) (nfix ms)))

(defun fn-prd-read-limit (session-limit)
  (declare (xargs :guard t))
  (if (posp session-limit)
      (min session-limit *fn-feed-wire-input-max-chunk-octets*)
    *fn-feed-wire-input-max-chunk-octets*))

(defun fn-prd-write-end (offset total)
  (declare (xargs :guard t))
  (min (nfix total) (+ (nfix offset) *fn-feed-wire-input-max-chunk-octets*)))

(defun fn-prd-idle-ms ()
  (declare (xargs :guard t))
  10)

; These are concrete observations of named transport failure classes.
; A core/store/unknown condition is never silently turned into round loss.
(defun fn-prd-loss-class-ok (stage class)
  (declare (xargs :guard t))
  (if (equal stage :local)
      (equal class "fnn-store-error")
    (if (member-equal class '("fnn-os-error" "fnn-peer-dial-error"
                             "fnn-tls-unavailable" "fnn-tls-config-error"
                             "fnn-tls-handshake-error" "fnn-tls-verify-error"
                             "fnn-tls-io-error")) t nil)))
