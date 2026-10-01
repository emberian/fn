; Witnesses and teeth for books/native-retire.lisp and books/owner-retire.lisp
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
; The drain's decision (fn-oret-drain-step).

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
(assert-event (equal (fn-oret-pending-total *nrt-pending*) 1))
(assert-event (equal (fn-oret-pending-total *nrt-drained*) 0))
(assert-event (equal (fn-oret-undelivered-total *nrt-pending*) 2))

; fn-oret-drain-step-waits-while-feeds-drain, positive: within the 60 s
; window with one entry still tried, the drain waits.
(assert-event (and (< (fn-osd-elapsed *nrt-s0* (nrt-at 59999)) (* 1000 60))
                   (< 0 (fn-oret-pending-total *nrt-pending*))
                   (equal (fn-oret-drain-step *nrt-s0* (nrt-at 59999) 60 *nrt-pending*) :wait)))
; fn-oret-drain-step-ends-by-the-window, positive: at the window, with the
; silent peer still owed, it answers :deadline.
(assert-event (and (<= (* 1000 60) (fn-osd-elapsed *nrt-s0* (nrt-at 60000)))
                   (equal (fn-oret-drain-step *nrt-s0* (nrt-at 60000) 60 *nrt-pending*) :deadline)))
; A window of 0 (no --drain) ends at once.
(assert-event (equal (fn-oret-drain-step *nrt-s0* *nrt-s0* 0 *nrt-pending*) :deadline))
; fn-oret-drain-step-drained-means-nothing-pending: what gave up at its
; retry bound is not waited for.
(assert-event (and (equal (fn-oret-drain-step *nrt-s0* (nrt-at 1) 60 *nrt-drained*) :drained)
                   (equal (fn-oret-pending-total *nrt-drained*) 0)))
; Teeth: without the window's hypothesis the drain may wait; without
; something pending it does not.
(must-fail-checked
 (thm (not (equal (fn-oret-drain-step s0 s seconds tbl) :wait))))
(assert-event (and (not (<= (* 1000 60) (fn-osd-elapsed *nrt-s0* (nrt-at 59999))))
                   (equal (fn-oret-drain-step *nrt-s0* (nrt-at 59999) 60 *nrt-pending*) :wait)))
(assert-event (and (not (< 0 (fn-oret-pending-total *nrt-drained*)))
                   (not (equal (fn-oret-drain-step *nrt-s0* (nrt-at 59999) 60 *nrt-drained*)
                               :wait))))

; ---------------------------------------------------------------------------
; The HOST-CALLED drain (fn-ort-drain-step-counted, books/owner-retire-counted;
; host/owner-host.lisp fn-owner-retire-step passes the carried pending count,
; intake-fenced T and producers-settled NIL).  Reachable witnesses over the
; same reached scheduler snapshots, per literal keystone.

; fn-ort-deadline-is-independent-of-the-fences, positive: the antecedent (at
; the 60 s window) and the conclusion (not :wait), in the host's own shape
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
