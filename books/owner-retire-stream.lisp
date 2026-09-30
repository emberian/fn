; S9 frozen final report. The cursor shares the installed graph after all
; producers join; it does not acquire a concurrent snapshot lease. Scratch
; for a single rendered line and the stage's disk funding remain OPEN.
(in-package "ACL2")
(include-book "owner-retire")
(include-book "owner-feed-counts")

; Cursor = (phase feed-tail pin-tail pins-root undelivered held reserved step).
(defun fn-orr-start (step oc)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (retention (fn-nls-retention (fn-own-store o)))
         (pins (fn-retain-pins retention)))
    (list :count-pins (fn-own-feeds o) pins pins 0 0
          (fn-retain-reserved retention) step)))

(defun fn-orr-peer-line (entry)
  (declare (xargs :guard t))
  (let ((feed (fn-own-feed-entry-feed entry)))
    (append (fn-nls-text "retire peer=")
            (if (stringp (fn-own-feed-entry-name entry))
                (fn-nls-text (fn-own-feed-entry-name entry))
              (fn-nls-text "?"))
            (fn-nls-field "undelivered" (nfix (fn-feed-undelivered feed)))
            (fn-nls-field "dropped" (nfix (fn-feed-retry-dropped feed)))
            *fn-nls-lf*)))

(defun fn-orr-end-line (step undelivered held)
  (declare (xargs :guard t))
  (append (fn-nls-text "retired state=")
          (fn-nls-text (fn-oret-outcome-word step))
          (fn-nls-field "undelivered" (nfix undelivered))
          (fn-nls-field "obligations" (nfix held))
          *fn-nls-lf*
          (if (and (zp undelivered) (zp held)) nil
            (fn-nls-text
             "retire release: what stays is released only by `carry drop WORK --abandon REASON' on the stopped store
"))))

; Result = (next-cursor output-octets done). Empty output is a real yield.
; A turn visits one pin, one feed, or one fixed report phase. No table or
; queue census occurs during a turn; pin count is accumulated before header.
(defun fn-orr-step (cursor)
  (declare (xargs :guard t))
  (let ((phase (nth 0 cursor)) (feeds (nth 1 cursor))
        (pins (nth 2 cursor)) (root (nth 3 cursor))
        (u (nfix (nth 4 cursor))) (held (nfix (nth 5 cursor)))
        (reserved (nth 6 cursor)) (outcome (nth 7 cursor)))
    (case phase
      (:count-pins
       (list (if (consp pins)
                 (list :count-pins feeds (cdr pins) root u (+ 1 held) reserved outcome)
               (list :peers feeds root root u held reserved outcome)) nil nil))
      (:peers
       (if (consp feeds)
           (list (list :peers (cdr feeds) pins root
                       (+ u (nfix (fn-feed-undelivered
                                   (fn-own-feed-entry-feed (car feeds)))))
                       held reserved outcome)
                 (fn-orr-peer-line (car feeds)) nil)
         (list (list :obligations feeds pins root u held reserved outcome)
               (append (fn-nls-text "obligations=") (fn-nls-nat held)
                       (fn-nls-field "reserved" reserved) *fn-nls-lf*) nil)))
      (:obligations
       (if (consp pins)
           (list (list :obligations feeds (cdr pins) root u held reserved outcome)
                 (fn-nls-obligation-line (car pins)) nil)
         (list (list :done feeds pins root u held reserved outcome)
               (fn-orr-end-line outcome u held) t)))
      (otherwise (list cursor nil t)))))

(local
 (defthm fn-orr-retry-count-is-health-count
   (equal (fn-fct-retry-drops-model queue) (fn-nh-dropped-count queue))
   :hints (("Goal" :induct (fn-fct-retry-drops-model queue)
            :in-theory (enable fn-fct-retry-drops-model fn-fct-retry-drop-bit
                               fn-nh-dropped-count)))))

(defthm fn-orr-peer-line-is-reference
  (implies (fn-feed-count-relationp (fn-own-feed-entry-feed entry))
           (equal (fn-orr-peer-line entry) (fn-oret-peer-line entry)))
  :hints (("Goal" :in-theory (enable fn-orr-peer-line fn-oret-peer-line
                                     fn-feed-count-relationp
                                     ))))

(in-theory (disable fn-orr-start fn-orr-step fn-orr-peer-line fn-orr-end-line))
