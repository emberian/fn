; Retiring a node, the owner's side (row S9; books/native-retire.lisp is the
; operator's).
;
; After the retire request the owner observes, at each tick of its
; maintenance (host/native/owner.lisp fnn-owner-maybe-retire), a scheduler
; snapshot S, and ACL2 decides whether the drain goes on: host/owner-host.lisp
; fn-owner-retire-step calls books/owner-retire-counted.lisp
; fn-ort-retire-step over the carried feed count and the owner's queue (the
; producer fence, fn-ort-producers-settled).  Its keystones are
; fn-ort-retire-step-ends-by-the-window, -drains-a-settled-zero and
; -waits-while-anything-drains (witnessed in
; tests/acl2/native-retire-tests.lisp).  At :drained or :deadline the owner
; takes its final checkpoint and stops as a SIGTERM stops it; after the
; joins it renders this book's report (fn-oret-report) and writes it beside
; the store.
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

(defun fn-oret-undelivered-total (tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (+ (len (fn-feed-queue (fn-own-feed-entry-feed (car tbl))))
         (fn-oret-undelivered-total (cdr tbl)))
    0))

; One line per configured peer:
;   retire peer=NAME undelivered=N dropped=D
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

; The obligations part: the ledger's count, the reserve and a line per
; obligation, as `obligations' prints them.
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

; The report the owner writes when the drain ends at STEP, over the
; configured owner OC it carries.
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

(in-theory (disable fn-oret-report fn-oret-peer-lines
                    fn-oret-undelivered-total))
