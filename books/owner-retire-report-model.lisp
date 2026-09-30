; Literal original fn-oret-report and its exact report-only dependency spine.
(in-package "ACL2")
(include-book "owner-report-words")
(include-book "owner-report-drop-count")

(defun fn-oret-undelivered-total (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (+ (len (fn-feed-queue (fn-own-feed-entry-feed (car tbl))))
         (fn-oret-undelivered-total (cdr tbl)))
    0))

(defun fn-oret-peer-line (e)
  (declare (xargs :guard t))
  (let ((queue (fn-feed-queue (fn-own-feed-entry-feed e))))
    (append (fn-nls-text "retire peer=")
            (if (stringp (fn-own-feed-entry-name e))
                (fn-nls-text (fn-own-feed-entry-name e))
              (fn-nls-text "?"))
            (fn-nls-field "undelivered" (len queue))
            (fn-nls-field "dropped" (fn-nh-dropped-count queue))
            *fn-nls-lf*)))

(defun fn-oret-peer-lines (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (append (fn-oret-peer-line (car tbl)) (fn-oret-peer-lines (cdr tbl)))
    nil))

(defun fn-oret-obligation-words (s)
  (declare (xargs :guard t))
  (append (fn-nls-text "obligations=")
          (fn-nls-nat (len (fn-retain-pins (fn-nls-retention s))))
          (fn-nls-field "reserved" (fn-retain-reserved (fn-nls-retention s)))
          *fn-nls-lf*
          (fn-nls-obligation-lines (fn-retain-pins (fn-nls-retention s)))))

(defun fn-oret-outcome-word (step)
  (declare (xargs :guard t))
  (if (equal step :drained) "drained" "deadline"))

(defun fn-oret-report (step oc)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (tbl (fn-own-feeds o))
         (held (len (fn-retain-pins (fn-nls-retention s)))))
    (append (fn-oret-peer-lines tbl)
            (fn-oret-obligation-words s)
            (fn-nls-text "retired state=")
            (fn-nls-text (fn-oret-outcome-word step))
            (fn-nls-field "undelivered" (fn-oret-undelivered-total tbl))
            (fn-nls-field "obligations" held)
            *fn-nls-lf*
            (if (and (zp (fn-oret-undelivered-total tbl)) (zp held))
                nil
              (fn-nls-text
               "retire release: what stays is released only by `carry drop WORK --abandon REASON' on the stopped store
")))))
