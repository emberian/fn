; Native BP contact-window decision.  The host observes time and transports
; effects; this book alone decides whether a named, ready peer may be opened.
; It deliberately does not run the FNWF scheduler's storage-complete shortcut:
; the BP lifecycle has its own durable FNBS publication outcome.

(in-package "ACL2")
(include-book "bp-node-machine")
(include-book "clock")

(defun fn-bpsc-windowp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)
       (equal (car x) :window)
       (fn-bpp-eidp (cadr x))
       (fn-clock-timep (caddr x))
       (fn-clock-timep (cadddr x))
       (<= (caddr x) (cadddr x))))

(defun fn-bpsc-window (peer start end)
  (declare (xargs :guard t))
  (let ((x (list :window peer start end)))
    (if (fn-bpsc-windowp x) x nil)))

(defun fn-bpsc-relative-window (peer obs start-delay end-delay)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-bpp-eidp peer)
           (fn-clock-observationp obs)
           (fn-clock-timep start-delay)
           (fn-clock-timep end-delay))
      (fn-bpsc-window peer
                      (+ (fn-clock-monotonic obs) start-delay)
                      (+ (fn-clock-monotonic obs) end-delay))
    nil))

(defun fn-bpsc-contact-decision (window peer obs ready-peers)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((or (not (fn-bpsc-windowp window))
             (not (fn-bpp-eidp peer))
             (not (fn-clock-observationp obs))) :invalid)
        ((and (equal peer (cadr window))
              (fn-bpn-member peer ready-peers)
              (<= (caddr window) (fn-clock-monotonic obs))
              (<= (fn-clock-monotonic obs) (cadddr window))) :open)
        (t :closed)))

(defun fn-bpsc-contact-event (window peer obs ready-peers)
  (declare (xargs :guard t :verify-guards nil))
  (let ((decision (fn-bpsc-contact-decision window peer obs ready-peers)))
    (if (eq decision :invalid)
        nil
      (list :contact peer (if (eq decision :open) t nil)))))

(defthm fn-bpsc-open-needs-ready-peer-and-window
  (implies (equal (fn-bpsc-contact-decision window peer obs ready-peers)
                  :open)
           (and (fn-bpsc-windowp window)
                (equal peer (cadr window))
                (fn-bpn-member peer ready-peers)
                (fn-clock-observationp obs)
                (<= (caddr window) (fn-clock-monotonic obs))
                (<= (fn-clock-monotonic obs) (cadddr window))))
  :rule-classes nil)

(defthm fn-bpsc-invalid-releases-no-contact-event-by-definition
  (implies (equal (fn-bpsc-contact-decision window peer obs ready-peers)
                  :invalid)
           (equal (fn-bpsc-contact-event window peer obs ready-peers) nil)))

(defthm fn-bpsc-contact-event-open-iff-decision-open-by-definition
  (implies (not (equal (fn-bpsc-contact-decision window peer obs ready-peers)
                       :invalid))
           (equal (equal (fn-bpsc-contact-event window peer obs ready-peers)
                         (list :contact peer t))
                  (equal (fn-bpsc-contact-decision window peer obs ready-peers)
                         :open))))

(verify-guards fn-bpsc-windowp)
(verify-guards fn-bpsc-window)
(verify-guards fn-bpsc-relative-window
  :hints (("Goal" :in-theory (enable fn-clock-vocabulary))))
(verify-guards fn-bpsc-contact-decision
  :hints (("Goal" :in-theory (enable fn-clock-vocabulary))))
(verify-guards fn-bpsc-contact-event)
