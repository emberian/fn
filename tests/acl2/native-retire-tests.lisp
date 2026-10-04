; Witnesses and teeth for books/native-retire.lisp, books/owner-retire.lisp,
; books/owner-retire-counted.lisp and books/owner-retire-settlement.lisp
; (row S9: `retire [--drain SECONDS]').  Scheduler values are reached from
; fn-otm-init through the clock events the owner appends before each
; observation (fnn-owner-sched-snapshot -> fnn-owner-disk-event :clock), as
; tests/acl2/owner-stop-drain-tests.lisp reaches them.  The feed tables are
; constructed (as tests/acl2/native-health-tests.lisp's are), labelled so.
(in-package "ACL2")
(include-book "../../books/owner-retire")
(include-book "../../books/owner-retire-counted")
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; The command's decision (fn-nret-plan) and the request the owner reads.

(assert-event (equal (fn-nret-plan 0) '(:accepted 0)))
(assert-event (equal (fn-nret-plan 600) '(:accepted 600)))
(assert-event (equal (fn-nret-plan 86400) '(:accepted 86400)))
(assert-event (equal (fn-nret-plan 86401) '(:refused :drain-seconds-over-bound)))
(assert-event (equal (fn-nret-plan :not-a-number) '(:refused :drain-seconds-not-a-number)))

; Positive witness of fn-nret-request-of-request-argv: the antecedent (the
; plan accepts 600) and the conclusion (the owner reads (:begin 600)).
(assert-event (and (equal (car (fn-nret-plan 600)) :accepted)
                   (equal (fn-nret-request (fn-nret-request-argv 600)) '(:begin 600))))
(assert-event (equal (fn-nret-request (fn-nret-request-argv 0)) '(:begin 0)))
(assert-event (equal (fn-nret-request (fn-nret-request-argv 86400)) '(:begin 86400)))
; Hypothesis removal: a window the plan refuses (86401) is not read back as
; itself: the vector carries it and the owner refuses to take it.
(assert-event (and (not (equal (car (fn-nret-plan 86401)) :accepted))
                   (equal (fn-nret-request-argv 86401)
                          (list (fn-record-string-octets "retire")
                                (fn-record-string-octets "begin")
                                '(0 1 81 129)))
                   (equal (fn-nret-request (fn-nret-request-argv 86401)) nil)))
(must-fail-checked
 (thm (equal (fn-nret-request (fn-nret-request-argv seconds)) (list :begin seconds))))
; Every other vector is not a retire request (the administrative plans).
(assert-event (equal (fn-nret-request (list (fn-record-string-octets "compaction")
                                            (fn-record-string-octets "request")))
                     nil))
(assert-event (equal (fn-nret-request (list (fn-record-string-octets "retire")
                                            (fn-record-string-octets "begin")
                                            '(0 0 2)))
                     nil))

(assert-event (equal (fn-nret-begin-answer nil) '(:accepted :draining)))
(assert-event (equal (fn-nret-begin-answer t) '(:refused :already-retiring)))
(assert-event (equal (fn-nret-refusal-line)
                     (fn-record-string-octets
                      (concatenate 'string "502 this node is retiring and accepts no new connections"
                                   (coerce (list (code-char 13) (code-char 10)) 'string)))))
(assert-event (equal (fn-nret-begin-log-line 600)
                     (fn-record-string-octets "retire begin reason=operator drain-seconds=600")))
(assert-event (equal (fn-nret-begin-log-line 0)
                     (fn-record-string-octets "retire begin reason=operator drain-seconds=0")))

; ---------------------------------------------------------------------------
; Reached scheduler snapshots and constructed feed tables (the report's).

(defun nrt-clock (s now) (mv-let (w s2) (fn-otm-disk-event s :clock now nil) (declare (ignore w)) s2))
(defconst *nrt-s0* (nrt-clock (fn-otm-init) 1000))
(defun nrt-at (x) (nrt-clock *nrt-s0* (+ 1000 x)))

(defconst *nrt-limits* (fn-feed-limits 1024 1000 3 t))
; Constructed: peer "silent" never answers (one article queued, still
; tried); peer "gave-up" dropped one at its retry bound.
(defconst *nrt-pending*
  (list (fn-own-feed-entry "silent" nil
                           (fn-feed-make '(115) *nrt-limits*
                                         (list (fn-feed-entry '(60 97 62) :queued 1 0))
                                         nil 0 nil 0))
        (fn-own-feed-entry "gave-up" nil
                           (fn-feed-make '(103) *nrt-limits*
                                         (list (fn-feed-entry '(60 98 62) '(:dropped :retry-bound) 3 0))
                                         nil 0 7 0))))
(defconst *nrt-drained*
  (list (fn-own-feed-entry "gave-up" nil
                           (fn-feed-make '(103) *nrt-limits*
                                         (list (fn-feed-entry '(60 98 62) '(:dropped :retry-bound) 3 0))
                                         nil 0 7 0))))

(assert-event (equal (fn-osd-elapsed *nrt-s0* (nrt-at 59999)) 59999))
(assert-event (equal (fn-oret-undelivered-total *nrt-pending*) 2))

; ---------------------------------------------------------------------------
; The counted drain (fn-ort-drain-step-counted, books/owner-retire-counted)
; the host's step is built on (fn-ort-retire-step below passes intake-fenced
; T and the producer fence).  Reachable witnesses over the same reached
; scheduler snapshots, per literal keystone, with the producer fence both
; unsettled (NIL) and settled (T).

; fn-ort-deadline-is-independent-of-the-fences, positive: the antecedent (at
; the 60 s window) and the conclusion (not :wait), unsettled
; (pending 1, T, NIL) and with both fences settled and nothing pending.
(assert-event (and (<= (* 1000 (nfix 60)) (fn-osd-elapsed *nrt-s0* (nrt-at 60000)))
                   (not (equal (fn-ort-drain-step-counted *nrt-s0* (nrt-at 60000) 60 1 t nil)
                               :wait))
                   (equal (fn-ort-drain-step-counted *nrt-s0* (nrt-at 60000) 60 1 t nil)
                          :deadline)))
; Hypothesis removal: the omitted hypothesis fails (one millisecond before
; the window) and the conclusion fails (it waits).
(assert-event (and (not (<= (* 1000 (nfix 60)) (fn-osd-elapsed *nrt-s0* (nrt-at 59999))))
                   (equal (fn-ort-drain-step-counted *nrt-s0* (nrt-at 59999) 60 1 t nil)
                          :wait)))

; fn-ort-counted-drain-waits-before-window-without-fenced-zero, positive:
; before the window (59,999 ms of 60 s), not (both fences and zero) -- the
; host's own call, pending 0 with producers-settled NIL -- and it waits.
; This is S9's served defect stated as a witness: the host's step cannot
; answer :drained, so the retire runs to its window.
(assert-event (and (< (fn-osd-elapsed *nrt-s0* (nrt-at 59999)) (* 1000 (nfix 60)))
                   (not (and (equal t t) (equal nil t) (natp 0) (equal 0 0)))
                   (equal (fn-ort-drain-step-counted *nrt-s0* (nrt-at 59999) 60 0 t nil)
                          :wait)))
; Hypothesis removal (the window): the retained hypothesis holds (not both
; fences), the omitted one fails (at the window), the conclusion fails.
(assert-event (and (not (and (equal t t) (equal nil t) (natp 0) (equal 0 0)))
                   (not (< (fn-osd-elapsed *nrt-s0* (nrt-at 60000)) (* 1000 (nfix 60))))
                   (not (equal (fn-ort-drain-step-counted *nrt-s0* (nrt-at 60000) 60 0 t nil)
                               :wait))))
; Hypothesis removal (fenced zero): the retained hypothesis holds (before the
; window), the omitted one fails (both fences, zero pending), the conclusion
; fails (:drained).
(assert-event (and (< (fn-osd-elapsed *nrt-s0* (nrt-at 59999)) (* 1000 (nfix 60)))
                   (and (equal t t) (equal t t) (natp 0) (equal 0 0))
                   (equal (fn-ort-drain-step-counted *nrt-s0* (nrt-at 59999) 60 0 t t)
                          :drained)))

; ---------------------------------------------------------------------------
; The drain step the host calls (fn-ort-retire-step, through
; host/owner-host.lisp fn-owner-retire-step): the carried feed count and the
; owner's queue.  Scheduler values reached as above; the queued submission
; is constructed (the step reads only whether the queue is empty).

(defconst *nrt-queued* '((:constructed-submission 7)))

; fn-ort-retire-step-drains-a-settled-zero, positive: nothing pending,
; nothing queued, inside the window: :drained (the regression this repairs
; answered :wait here and then :deadline, after waiting out the window).
(assert-event (and (equal 0 0) (not (consp nil))
                   (< (fn-osd-elapsed *nrt-s0* (nrt-at 1)) (* 1000 600))
                   (equal (fn-ort-retire-step *nrt-s0* (nrt-at 1) 600 0 nil) :drained)))
; ... and past the window too.
(assert-event (and (<= (* 1000 60) (fn-osd-elapsed *nrt-s0* (nrt-at 60000)))
                   (equal (fn-ort-retire-step *nrt-s0* (nrt-at 60000) 60 0 nil) :drained)))
; Hypothesis removal (pending = 0): the queue hypothesis holds, pending is
; 1, and the conclusion fails (it waits).
(assert-event (and (not (consp nil)) (not (equal 1 0))
                   (not (equal (fn-ort-retire-step *nrt-s0* (nrt-at 1) 600 1 nil) :drained))))
; Hypothesis removal (an empty queue): pending is 0, a submission is
; queued, and the conclusion fails (it waits).
(assert-event (and (equal 0 0) (consp *nrt-queued*)
                   (not (equal (fn-ort-retire-step *nrt-s0* (nrt-at 1) 600 0 *nrt-queued*)
                               :drained))))

; fn-ort-retire-step-waits-while-anything-drains, positive: inside the
; window, one feed entry pending -> :wait; one submission queued -> :wait.
(assert-event (and (< (fn-osd-elapsed *nrt-s0* (nrt-at 59999)) (* 1000 60))
                   (not (equal 1 0))
                   (equal (fn-ort-retire-step *nrt-s0* (nrt-at 59999) 60 1 nil) :wait)))
(assert-event (and (< (fn-osd-elapsed *nrt-s0* (nrt-at 59999)) (* 1000 60))
                   (consp *nrt-queued*)
                   (equal (fn-ort-retire-step *nrt-s0* (nrt-at 59999) 60 0 *nrt-queued*) :wait)))
; Hypothesis removal (inside the window): at the window, the other
; hypothesis holds, and it does not wait.
(assert-event (and (not (< (fn-osd-elapsed *nrt-s0* (nrt-at 60000)) (* 1000 60)))
                   (not (equal 1 0))
                   (not (equal (fn-ort-retire-step *nrt-s0* (nrt-at 60000) 60 1 nil) :wait))))
; Hypothesis removal (something drains): inside the window, nothing
; pending or queued, and it does not wait.
(assert-event (and (< (fn-osd-elapsed *nrt-s0* (nrt-at 59999)) (* 1000 60))
                   (not (or (not (equal 0 0)) (consp nil)))
                   (not (equal (fn-ort-retire-step *nrt-s0* (nrt-at 59999) 60 0 nil) :wait))))

; fn-ort-retire-step-ends-by-the-window, positive: at the window with a
; feed entry pending and a submission queued, :deadline.
(assert-event (and (<= (* 1000 60) (fn-osd-elapsed *nrt-s0* (nrt-at 60000)))
                   (equal (fn-ort-retire-step *nrt-s0* (nrt-at 60000) 60 3 *nrt-queued*)
                          :deadline)))
; A window of 0 (no --drain) with something owed ends at once.
(assert-event (equal (fn-ort-retire-step *nrt-s0* *nrt-s0* 0 3 *nrt-queued*) :deadline))
; Hypothesis removal: before the window, it waits.
(assert-event (and (not (<= (* 1000 60) (fn-osd-elapsed *nrt-s0* (nrt-at 59999))))
                   (equal (fn-ort-retire-step *nrt-s0* (nrt-at 59999) 60 3 *nrt-queued*) :wait)))
(must-fail-checked
 (thm (not (equal (fn-ort-retire-step s0 s seconds pending queue) :wait))))
; Mutation: the producer fence hard-coded unsettled (the step dev called
; before this, fn-ort-drain-step-counted with producers-settled NIL) never
; drains.
(must-fail-checked
 (thm (implies (and (equal pending 0) (not (consp queue)))
               (equal (fn-ort-drain-step-counted s0 s seconds pending t nil) :drained))))
(assert-event (equal (fn-ort-drain-step-counted *nrt-s0* (nrt-at 1) 600 0 t nil) :wait))

; ---------------------------------------------------------------------------
; fn-ort-clean-stop-keeps-its-exit: positive witnesses over the observations
; fnn-owner-run's cleanup takes (writer joined, nothing accounted, journal
; closed, Store closed), for each of fnn-owner-store-settlement's branches.

(defun nrt-settle (join lines octets queuedp journal store authority caller-fd)
  (let* ((log (fn-ort-log-close-action join lines octets queuedp))
         (report (fn-ort-report-close-action log journal))
         (action (fn-ort-store-close-action report authority caller-fd)))
    (case action
      (:defer report)
      (:settled (fn-ort-service-settlement-action report :absent))
      (t (fn-ort-service-settlement-action report store)))))

; :close (authority held, no caller descriptor), the ordinary SIGTERM.
(assert-event (and (equal (fn-ort-store-close-action :joined t nil) :close)
                   (equal (nrt-settle :joined 0 0 nil :closed :closed t nil) :joined)
                   (equal (fn-ort-log-close-exit 0 3 (nrt-settle :joined 0 0 nil :closed :closed t nil))
                          0)))
; :defer (the operator caller still holds its descriptor) and :settled.
(assert-event (and (equal (fn-ort-store-close-action :joined t t) :defer)
                   (equal (fn-ort-log-close-exit 0 3 (nrt-settle :absent 0 0 nil :absent :closed t t))
                          0)))
(assert-event (and (equal (fn-ort-store-close-action :joined nil nil) :settled)
                   (equal (fn-ort-log-close-exit 0 3 (nrt-settle :joined 0 0 nil :closed :closed nil nil))
                          0)))
; Hypothesis removal: one accounted log line left, a journal not closed,
; a Store close that failed, a writer that timed out: each is uncertain
; (exit 3).
(assert-event (equal (fn-ort-log-close-exit 0 3 (nrt-settle :joined 1 0 nil :closed :closed t nil)) 3))
(assert-event (equal (fn-ort-log-close-exit 0 3 (nrt-settle :joined 0 0 nil :uncertain :closed t nil)) 3))
(assert-event (equal (fn-ort-log-close-exit 0 3 (nrt-settle :joined 0 0 nil :closed :uncertain t nil)) 3))
(assert-event (equal (fn-ort-log-close-exit 0 3 (nrt-settle :timeout 0 0 nil :closed :closed t nil)) 3))
(must-fail-checked
 (thm (equal (fn-ort-log-close-exit prior uncertain
                                    (fn-ort-service-settlement-action
                                     (fn-ort-report-close-action
                                      (fn-ort-log-close-action join lines octets queuedp)
                                      journal)
                                     store))
             prior)))

; ---------------------------------------------------------------------------
; The report (fn-oret-report).

(assert-event (equal (fn-oret-peer-lines *nrt-pending*)
                     (fn-record-string-octets
                      "retire peer=silent undelivered=1 dropped=0
retire peer=gave-up undelivered=1 dropped=1
")))

; A configured owner with the constructed feed table and a store with no
; obligation (the owner's thirteenth field is its feed table, fn-own-feeds).
(defconst *nrt-owner0*
  (fn-own-configure (fn-own-start (fn-sn-initial '("fn.test") 10) 3)
                    (fn-inj-make-config t '(102 110) (list (fn-nntp-string-octets "fn.test")) 32768)))
(defconst *nrt-oc*
  (fn-ocfg-make (update-nth 12 *nrt-pending* *nrt-owner0*) nil nil nil))
(assert-event (equal (fn-own-feeds (fn-ocfg-owner *nrt-oc*)) *nrt-pending*))

(assert-event
 (equal (fn-oret-report :deadline *nrt-oc*)
        (fn-record-string-octets
         "retire peer=silent undelivered=1 dropped=0
retire peer=gave-up undelivered=1 dropped=1
obligations=0 reserved=0
retired state=deadline undelivered=2 obligations=0
retire release: what stays is released only by `carry drop WORK --abandon REASON' on the stopped store
")))
; The ledger part (fn-oret-report-carries-the-obligations-report equates
; it with fn-nls-report's :obligations answer, which takes the arena stobj).
(assert-event
 (equal (fn-oret-obligation-words (fn-own-store (fn-ocfg-owner *nrt-oc*)))
        (fn-record-string-octets "obligations=0 reserved=0
")))
; Nothing undelivered and nothing held: no release line.
(defconst *nrt-oc-empty*
  (fn-ocfg-make (update-nth 12 nil *nrt-owner0*) nil nil nil))
(assert-event
 (equal (fn-oret-report :drained *nrt-oc-empty*)
        (fn-record-string-octets
         "obligations=0 reserved=0
retired state=drained undelivered=0 obligations=0
")))
