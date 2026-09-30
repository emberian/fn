; Retiring a node, the owner's side (row S9; books/native-retire.lisp is the
; operator's).
;
; After the retire request the owner observes, at each tick of its accept
; loop (host/native/owner.lisp fnn-owner-maybe-retire), a scheduler snapshot
; S and its feed table, and ACL2 decides from them whether the drain goes on
; (fn-oret-drain-step): :drained once no feed entry is still being tried,
; :deadline once the window SECONDS has passed since the request's snapshot
; S0, :wait otherwise.  At :drained or :deadline the owner renders the report
; (fn-oret-report), writes it beside the store, takes its final checkpoint
; and stops.
;
; The report names, per configured peer, what stays undelivered (the feed
; queue's length: fn-feed-queue-length-is-undelivered) and how much of it the
; feed gave up at its retry bound (dropped); then the obligation ledger,
; word for word the `obligations' report the running owner answers
; (fn-oret-report-carries-the-obligations-report); then one line naming the
; outcome.  Obligations left are released only by the waiver on the stopped
; store (`carry drop WORK --abandon REASON', PRF-950).
(in-package "ACL2")
(include-book "native-retire")
(include-book "native-health")
(include-book "owner-stop-drain")

; An entry the feed still tries: not dropped at its retry bound.
(defun fn-oret-pending (queue)
  (declare (xargs :guard t))
  (nfix (- (len queue) (fn-nh-dropped-count queue))))

(defun fn-oret-pending-total (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (+ (fn-oret-pending (fn-feed-queue (fn-own-feed-entry-feed (car tbl))))
         (fn-oret-pending-total (cdr tbl)))
    0))

(include-book "owner-retire-report-model")

; The drain's decision.  SECONDS is the accepted window (fn-nret-request's).
(defun fn-oret-drain-step (s0 s seconds tbl)
  (declare (xargs :guard t))
  (cond ((zp (fn-oret-pending-total tbl)) :drained)
        ((<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s)) :deadline)
        (t :wait)))

; KEYSTONE (the drain ends by its window).  The subject is fn-oret-drain-step,
; which host/owner-host.lisp fn-owner-retire-step calls for
; host/native/owner.lisp fnn-owner-maybe-retire at each accept-loop tick over
; the owner's feed table.  An observation at or past the window since the
; request never answers :wait, whatever the feeds hold; the host observes at
; least once a second (the accept loop's one-second readiness poll), so the
; stop begins within one second of the window.
(defthm fn-oret-drain-step-ends-by-the-window
  (implies (<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s))
           (not (equal (fn-oret-drain-step s0 s seconds tbl) :wait))))

; KEYSTONE (a drain is never cut short).  The drain answers :drained only
; when no feed entry is still being tried, and it answers :deadline only when
; the window has passed: before the window, with something still being
; tried, it waits.
(defthm fn-oret-drain-step-waits-while-feeds-drain
  (implies (and (< (fn-osd-elapsed s0 s) (* 1000 (nfix seconds)))
                (< 0 (fn-oret-pending-total tbl)))
           (equal (fn-oret-drain-step s0 s seconds tbl) :wait)))

(defthm fn-oret-drain-step-drained-means-nothing-pending
  (implies (equal (fn-oret-drain-step s0 s seconds tbl) :drained)
           (equal (fn-oret-pending-total tbl) 0)))

; One line per configured peer:
;   retire peer=NAME undelivered=N dropped=D
(include-book "owner-retire-report-model")

(include-book "owner-retire-report-model")

; The obligations part: the ledger's count, the reserve and a line per
; obligation, as `obligations' prints them.
(include-book "owner-retire-report-model")

(include-book "owner-retire-report-model")

; The report the owner writes when the drain ends at STEP, over the
; configured owner OC it carries.
(include-book "owner-retire-report-model")

; KEYSTONE (the report's ledger is the `obligations' report).  The subject is
; fn-oret-report, which host/owner-host.lisp fn-owner-retire-report calls for
; host/native/owner.lisp fnn-owner-maybe-retire.  After the peer lines it
; carries, word for word, what `obligations' prints on the same store
; (books/native-live-status.lisp fn-nls-report's :obligations answer), so
; every theorem about that report (fn-nls-obligations-figures-are-the-
; retention-figures) is about the ledger the retire report names.
(defthm fn-oret-report-carries-the-obligations-report
  (equal (fn-oret-report step oc)
         (append (fn-oret-peer-lines (fn-own-feeds (fn-ocfg-owner oc)))
                 (fn-nls-report :obligations profile
                                (fn-own-store (fn-ocfg-owner oc))
                                bytes seen cfg pins obs fn-arena)
                 (fn-nls-text "retired state=")
                 (fn-nls-text (fn-oret-outcome-word step))
                 (fn-nls-field "undelivered"
                               (fn-oret-undelivered-total (fn-own-feeds (fn-ocfg-owner oc))))
                 (fn-nls-field "obligations"
                               (len (fn-retain-pins
                                     (fn-nls-retention (fn-own-store (fn-ocfg-owner oc))))))
                 *fn-nls-lf*
                 (if (and (zp (fn-oret-undelivered-total (fn-own-feeds (fn-ocfg-owner oc))))
                          (zp (len (fn-retain-pins
                                    (fn-nls-retention (fn-own-store (fn-ocfg-owner oc)))))))
                     nil
                   (fn-nls-text
                    "retire release: what stays is released only by `carry drop WORK --abandon REASON' on the stopped store
"))))
  :hints (("Goal" :in-theory '(fn-oret-report fn-oret-obligation-words fn-nls-report))))

(in-theory (disable fn-oret-drain-step fn-oret-report fn-oret-peer-lines
                    fn-oret-pending-total fn-oret-undelivered-total))
