; Native BP contact-window decision.  The host observes time and transports
; effects; this book alone decides whether a named, ready peer may be opened.
; It deliberately does not run the FNWF scheduler's storage-complete shortcut:
; the BP lifecycle has its own durable FNBS publication outcome.

(in-package "ACL2")
(include-book "bp-node-machine")
(include-book "clock")
(local (in-theory (enable fn-clock-vocabulary)))

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

(defun fn-bpsc-contact-decision (window peer obs ready-peers)
  (declare (xargs :guard t))
  (cond ((or (not (fn-bpsc-windowp window))
             (not (fn-bpp-eidp peer))
             (not (fn-clock-observationp obs))) :invalid)
        ((and (equal peer (cadr window))
              (fn-bpn-member peer ready-peers)
              (<= (caddr window) (fn-clock-monotonic obs))
              (<= (fn-clock-monotonic obs) (cadddr window))) :open)
        (t :closed)))

(defun fn-bpsc-contact-event (window peer obs ready-peers)
  (declare (xargs :guard t))
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

(defthm fn-bpsc-invalid-releases-no-contact-event
  (implies (equal (fn-bpsc-contact-decision window peer obs ready-peers)
                  :invalid)
           (equal (fn-bpsc-contact-event window peer obs ready-peers) nil)))

(defthm fn-bpsc-contact-event-open-iff-decision-open
  (implies (not (equal (fn-bpsc-contact-decision window peer obs ready-peers)
                       :invalid))
           (equal (equal (fn-bpsc-contact-event window peer obs ready-peers)
                         (list :contact peer t))
                  (equal (fn-bpsc-contact-decision window peer obs ready-peers)
                         :open))))

(verify-guards fn-bpsc-windowp)
(verify-guards fn-bpsc-window)
(verify-guards fn-bpsc-contact-decision)
(verify-guards fn-bpsc-contact-event)
