; Transport observations retained separately from the catch-up refusal.
; Diagnostics do not change session state, effects, cursor or scheduling.
(in-package "ACL2")
(include-book "peer-catchup")

(defun fn-cu-session-loss-detail (s event s2)
  (declare (xargs :guard t))
  (if (and (not (fn-cu-session-done-p s))
           (equal (fn-cu-r-phase (fn-cu-s-round s2)) :failed)
           (consp event) (equal (car event) :lost))
      (list (fn-peer-lost-word (fn-pull-lost-cause event))
            (if (fn-cu-session-readyp s)
                (fn-cu-refusal-name (fn-cu-r-phase (fn-cu-s-round s)))
              "preamble"))
    nil))

(defun fn-cu-session-step-triple (s event)
  (declare (xargs :guard t))
  (let ((pair (fn-cu-session-step-pair s event)))
    (list (car pair) (cadr pair)
          (fn-cu-session-loss-detail s event (car pair)))))

; A representation equality, not a new productive protocol keystone.
(defthm fn-cu-session-step-triple-preserves-the-pair-by-definition
  (equal (take 2 (fn-cu-session-step-triple s event))
         (fn-cu-session-step-pair s event))
  :hints (("Goal" :in-theory
           (e/d (fn-cu-session-step-triple fn-cu-session-step-pair)
                (fn-cu-session-step fn-cu-session-loss-detail)))))

(defun fn-cu-session-loss-words (detail)
  (declare (xargs :guard t))
  (if (and (consp detail) (stringp (car detail))
           (consp (cdr detail)) (stringp (cadr detail)))
      (append (fn-record-string-octets " loss=")
              (fn-record-string-octets (car detail))
              (fn-record-string-octets " loss-phase=")
              (fn-record-string-octets (cadr detail)))
    nil))

(defun fn-cu-session-log-line-detail (s detail)
  (declare (xargs :guard t))
  (append (fn-cu-session-log-line s) (fn-cu-session-loss-words detail)))

(in-theory (disable fn-cu-session-loss-detail fn-cu-session-step-triple
                    fn-cu-session-loss-words fn-cu-session-log-line-detail))
