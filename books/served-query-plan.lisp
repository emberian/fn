; Actual query render facade. Existing OVER/NEWNEWS theorems retain their
; fn-splan subject; LIST adds a distinct residual/availability boundary here.
; Plan representation and cold/output custody remain identical.
(in-package "ACL2")
(include-book "served-plan-cursor")
(include-book "list-metadata-cursor")

(local (in-theory (disable (tau-system))))

(defun fn-qplan-cursor-effectp (effect)
  (declare (xargs :guard t))
  (or (fn-splan-cursor-effectp effect) (fn-lst-effectp effect)))

(defun fn-qplan-rest-donep (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (and (not (fn-qplan-cursor-effectp (car rest)))
           (atom (fn-srb-effect-octets (car rest)))
           (fn-qplan-rest-donep (cdr rest)))
    t))

(defun fn-qplan-donep (plan)
  (declare (xargs :guard t))
  (and (atom (fn-splan-cur plan)) (fn-qplan-rest-donep (fn-splan-rest plan))))

(defun fn-qplan-rest-at-cursorp (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (cond ((fn-qplan-cursor-effectp (car rest)) t)
            ((consp (fn-srb-effect-octets (car rest))) nil)
            (t (fn-qplan-rest-at-cursorp (cdr rest))))
    nil))

(defun fn-qplan-at-cursorp (plan)
  (declare (xargs :guard t))
  (and (atom (fn-splan-cur plan))
       (fn-qplan-rest-at-cursorp (fn-splan-rest plan))))

(defun fn-qplan-rest-head-len (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (cond ((fn-qplan-cursor-effectp (car rest)) 0)
            ((consp (fn-srb-effect-octets (car rest)))
             (len (fn-srb-effect-octets (car rest))))
            (t (fn-qplan-rest-head-len (cdr rest))))
    0))

(defun fn-qplan-window-size (plan)
  (declare (xargs :guard t))
  (if (consp (fn-splan-cur plan)) (len (fn-splan-cur plan))
    (fn-qplan-rest-head-len (fn-splan-rest plan))))

(defun fn-qplan-window (plan w fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp w)))
  (if (fn-qplan-at-cursorp plan)
      (let ((fn-octets (fn-octets-clear fn-octets)))
        (mv :cursor plan fn-octets))
    ; Stop within the current materialized effect. This prevents the legacy
    ; fill loop from passing a new LIST tag and shares its actual buffer code.
    (fn-splan-window plan (min w (fn-qplan-window-size plan)) fn-octets)))

; Exactly one accepted LIST controller call per activation. Empty progress
; retains the cursor and response capture; no warmth-based completion.
(defun fn-qplan-rest-cursor-step (rest w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (natp w)))
  (if (consp rest)
      (cond
       ((fn-lst-effectp (car rest))
        (mv-let (octets next calls state)
          (fn-lst-step (fn-cur-at 1 (car rest)) w w fn-cat)
          (declare (ignore calls state))
          (mv :ok (cons (fn-nntp-reply-effect octets)
                        (if (fn-lst-livep next)
                            (cons (fn-lst-effect next) (cdr rest))
                          (cdr rest))))))
       ((fn-splan-cursor-effectp (car rest))
        (fn-splan-rest-cursor-step rest w fn-arena fn-cat))
       (t (mv-let (status next)
            (fn-qplan-rest-cursor-step (cdr rest) w fn-arena fn-cat)
            (mv status (cons (car rest) next)))))
    (mv :ok rest)))

(defun fn-qplan-cursor-step (plan w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (natp w)))
  (mv-let (status next)
    (fn-qplan-rest-cursor-step (fn-splan-rest plan) w fn-arena fn-cat)
    (mv status (cons (fn-splan-cur plan) next))))

(in-theory (disable fn-qplan-cursor-effectp fn-qplan-rest-donep fn-qplan-donep
                    fn-qplan-rest-at-cursorp fn-qplan-at-cursorp fn-qplan-rest-head-len
                    fn-qplan-window-size fn-qplan-window
                    fn-qplan-rest-cursor-step fn-qplan-cursor-step))
