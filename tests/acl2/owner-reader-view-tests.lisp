; Witnesses and teeth for books/owner-reader-view.lisp (lane
; scheduler-2-rebase, 2026-09-27; PKT-828).
(in-package "ACL2")
(include-book "../../books/owner-reader-view")
(include-book "std/testing/must-fail" :dir :system)

; --- fn-ocv-capture: the host's calls, in the committer's order ---------------
; A START captures the working view; a START-NEXT adds the next batch's; the
; COMPLETE makes it current; the next COMPLETE with no next batch releases.
(assert-event (equal (fn-ocv-capture nil :start 'v0) '(v0)))
(assert-event (equal (fn-ocv-capture '(v0) :next 'v1) '(v0 v1)))
(assert-event (equal (fn-ocv-capture '(v0 v1) :complete 'v2) '(v1)))
(assert-event (equal (fn-ocv-capture '(v1) :complete 'v2) nil))
(assert-event (equal (fn-ocv-capture '(v0 v1) :unnext 'v1) '(v0)))
(assert-event (equal (fn-ocv-capture '(v0) :drop 'v0) nil))
; A second START or START-NEXT keeps the older capture (never a later view).
(assert-event (equal (fn-ocv-capture '(v0) :start 'v9) '(v0)))
(assert-event (equal (fn-ocv-capture '(v0 v1) :next 'v9) '(v0 v1)))
; The reader view: the capture while held, the working view otherwise.
(assert-event (equal (fn-ocv-reader-view '(v0 v1) 'w) 'v0))
(assert-event (equal (fn-ocv-reader-view nil 'w) 'w))

; --- KEYSTONE fn-ocvm-reader-view-is-the-completed-prefix --------------------
; Positive witness, a reached run: START of 3, START-NEXT of 2, COMPLETE,
; COMPLETE.  After each event the reader view is C and W = C + A + B.
(defconst *orvt-run* '((:start 3) (:next 2) (:complete) (:complete)))
(assert-event (fn-ocvm-legal-run-p (fn-ocvm-init) *orvt-run*))
(defun orvt-at (n)
  (fn-ocvm-run (fn-ocvm-init) (take n *orvt-run*)))
(defun orvt-reader (m) (fn-ocv-reader-view (fn-ocvm-views m) (fn-ocvm-w m)))
; During A's barrier (3 in flight): the working view counts 3, readers 0.
(assert-event (and (equal (fn-ocvm-w (orvt-at 1)) 3) (equal (orvt-reader (orvt-at 1)) 0)
                   (equal (fn-ocvm-c (orvt-at 1)) 0)))
; B prepared behind it: working 5, readers still 0.
(assert-event (and (equal (fn-ocvm-w (orvt-at 2)) 5) (equal (orvt-reader (orvt-at 2)) 0)))
; A's COMPLETE: readers 3 (A, not B), B in flight.
(assert-event (and (equal (orvt-reader (orvt-at 3)) 3) (equal (fn-ocvm-c (orvt-at 3)) 3)
                   (equal (fn-ocvm-a (orvt-at 3)) 2)))
; B's COMPLETE: readers 5 = the working view, nothing captured.
(assert-event (and (equal (orvt-reader (orvt-at 4)) 5) (null (fn-ocvm-views (orvt-at 4)))))
; A START-NEXT that took nobody gives up its capture (:unnext).
(defconst *orvt-run-unnext* '((:start 3) (:next 0) (:unnext) (:complete)))
(assert-event (fn-ocvm-legal-run-p (fn-ocvm-init) *orvt-run-unnext*))
(assert-event (let ((m (fn-ocvm-run (fn-ocvm-init) *orvt-run-unnext*)))
                (and (null (fn-ocvm-views m)) (equal (orvt-reader m) 3))))
; Hypothesis removal: an illegal run (a second START while a batch is in
; flight) is not a legal run, and along it the conclusion fails -- had the
; capture taken the later view, readers would count a batch in flight.
(defconst *orvt-illegal* '((:start 3) (:start 2)))
(assert-event (not (fn-ocvm-legal-run-p (fn-ocvm-init) *orvt-illegal*)))
; The retained hypothesis holds of the positive run (above); here the
; conclusion's second half still holds but the model's A is the second
; START's, so A + C no longer counts the first batch: W = 5, C + A + B = 2.
(assert-event (let ((m (fn-ocvm-run (fn-ocvm-init) *orvt-illegal*)))
                (not (equal (fn-ocvm-w m) (+ (fn-ocvm-c m) (fn-ocvm-a m) (fn-ocvm-b m))))))
; A COMPLETE with nothing captured (illegal: no batch in flight) is refused.
(assert-event (not (fn-ocvm-legal-run-p (fn-ocvm-init) '((:complete)))))

; --- KEYSTONE fn-olr-take-never-joins-the-batch-in-flight ---------------------
; A kernel with a batch in flight (INFLIGHT (r0)) and an open batch (r1):
; a take joins the open batch, the batch in flight is unchanged.
(defconst *orvt-ks* (fn-lgk-make nil nil 0 7 '((1 2)) '((9 9)) 0 :appended))
(defconst *orvt-take* (fn-olr-take *orvt-ks* '(3 4) 7 1 10 64 1000000 512))
(assert-event (equal (car *orvt-take*) :taken))
(assert-event (equal (fn-lgk-inflight (cadr *orvt-take*)) '((9 9))))
(assert-event (equal (fn-lgk-batch (cadr *orvt-take*)) '((1 2) (3 4))))
; At the operator's bound (count 1 >= bmax 1) the take answers :full and
; changes nothing (the host waits for the barrier, then commits the batch).
(defconst *orvt-full* (fn-olr-take *orvt-ks* '(3 4) 7 1 10 1 1000000 512))
(assert-event (and (equal (car *orvt-full*) :full)
                   (equal (cadr *orvt-full*) *orvt-ks*)))
; Mutation witness (labelled): a take that put the record into INFLIGHT
; would change it -- the keystone's first conjunct refuses that shape.
(must-fail
 (assert-event (equal (fn-lgk-inflight
                       (fn-lgk-make nil nil 0 8 '((1 2)) '((9 9) (3 4)) 0 :appended))
                      (fn-lgk-inflight *orvt-ks*))))

; --- the owner at the reader view -------------------------------------------
; fn-ocfg-at-reader-view reads the capture; with nothing captured it is the
; owner itself.
(defconst *orvt-oc* (fn-ocfg-make (fn-own-make 'st 'working nil 0 1 nil nil nil nil
                                               nil nil nil nil nil nil)
                                  'cfg nil nil))
(assert-event (equal (fn-own-view (fn-ocfg-owner (fn-ocfg-at-reader-view *orvt-oc* '(durable))))
                     'durable))
(assert-event (equal (fn-ocfg-at-reader-view *orvt-oc* nil) *orvt-oc*))
(assert-event (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-at-reader-view *orvt-oc* '(durable))))
                     'st))
; Putting the working view back gives the owner back.
(assert-event (equal (fn-ocfg-with-view (fn-ocfg-at-reader-view *orvt-oc* '(durable)) 'working)
                     *orvt-oc*))
