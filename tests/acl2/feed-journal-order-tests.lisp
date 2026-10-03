; Witnesses and teeth for books/feed-journal-order.lisp (lane owner-offlock,
; 2026-10-03): the OLD batch order of an FNFD journal (intents N, intents
; N+1, resolutions N; written before this lane) and the NEW one (intents N,
; resolutions N, intents N+1) replay to the same unresolved intents and the
; same offerable feed.  The frames are built by the constructors the host's
; START and COMPLETE publish (fn-own-feed-intent-records,
; fn-own-feed-resolution-records) for peer "inn".
(in-package "ACL2")
(include-book "../../books/feed-journal-order")

(defconst *fjot-open*
  (fn-feed-open '(105 110 110) (fn-feed-limits 5 1000 3 t)
                (fn-sched-contact "inn" 0 1000000) 7))
(defun fjot-a (txid) (declare (xargs :guard t))
  (list 60 97 (+ 48 (nfix txid)) 64 120 62))
(defun fjot-intent (txid) (declare (xargs :verify-guards nil))
  (car (fn-own-feed-intent-records '("inn") (fjot-a txid) '(1 2 3) '(4 5) 1 txid txid)))
(defun fjot-commit (txid) (declare (xargs :verify-guards nil))
  (car (fn-own-feed-resolution-records :feed-commit '("inn") (fjot-a txid) '(1 2 3) '(4 5) 1 txid txid)))

; Batch N = members 1 2, batch N+1 = members 3 4; an earlier unresolved
; intent 9 is in the journal before them, and member 5's intent after.
(defconst *fjot-before* (list (fjot-intent 9)))
(defconst *fjot-after* (list (fjot-intent 5)))
(defconst *fjot-old*
  (append *fjot-before*
          (list (fjot-intent 1) (fjot-intent 2)      ; START N
                (fjot-intent 3) (fjot-intent 4)      ; START-NEXT N+1
                (fjot-commit 1) (fjot-commit 2))     ; COMPLETE N
          *fjot-after*))
(defconst *fjot-new*
  (append *fjot-before*
          (list (fjot-intent 1) (fjot-intent 2)      ; job N: intents
                (fjot-commit 1) (fjot-commit 2)      ; job N: resolutions
                (fjot-intent 3) (fjot-intent 4))     ; job N+1: intents
          *fjot-after*))

; Both journals are ones a feed machine could have written, and both differ.
(assert-event (not (equal *fjot-old* *fjot-new*)))
(assert-event (fn-feed-journalp *fjot-old*))
(assert-event (fn-feed-journalp *fjot-new*))
; THE OLD-ORDER REPLAY TEST: the same unresolved intents (5 3 4 9 in the
; fold's order: 3 and 4 unresolved, 9 earlier, 5 later) and the same feed.
(assert-event (equal (fn-fjo-intents-run nil *fjot-old*)
                     (fn-fjo-intents-run nil *fjot-new*)))
(assert-event (equal (len (fn-fjo-intents-run nil *fjot-new*)) 4))
(assert-event (equal (fn-feed-replay *fjot-open* *fjot-old*)
                     (fn-feed-replay *fjot-open* *fjot-new*)))
; The feed is not trivially unchanged: the two commits enqueued two articles.
(assert-event (equal (len (fn-feed-queue (fn-feed-replay *fjot-open* *fjot-new*))) 2))

; KEYSTONE fn-fjo-an-intent-moved-past-another-resolution-replays-alike:
; a reached positive witness, every hypothesis and both conclusions (I the
; intent of member 3, R the commit of member 1, XS and YS the rest).
(defun fjot-k (i r xs ys)
  (declare (xargs :verify-guards nil))
  (list (and (equal (fn-feed-journal-kind i) :feed-intent)
             (member-equal (fn-feed-journal-kind r) '(:feed-commit :feed-abort))
             (not (equal (fn-own-feed-intent-key (fn-feed-journal-values i))
                         (fn-own-feed-intent-key (fn-feed-journal-values r)))))
        (equal (fn-fjo-intents-run nil (append xs (list* i r ys)))
               (fn-fjo-intents-run nil (append xs (list* r i ys))))
        (equal (fn-feed-replay *fjot-open* (append xs (list* i r ys)))
               (fn-feed-replay *fjot-open* (append xs (list* r i ys))))))
(defconst *fjot-xs* (list (fjot-intent 1) (fjot-intent 2)))
(defconst *fjot-ys* (list (fjot-commit 2)))
(assert-event (equal (fjot-k (fjot-intent 3) (fjot-commit 1) *fjot-xs* *fjot-ys*) '(t t t)))
; Removal of "another key": I is member 1's own intent moved past its own
; commit.  The other hypotheses hold, the omitted one fails, and the
; intent conclusion fails: the commit before its intent leaves 1 unresolved.
(defconst *fjot-xs1* nil)
(assert-event (equal (fn-feed-journal-kind (fjot-intent 1)) :feed-intent))
(assert-event (equal (fn-feed-journal-kind (fjot-commit 1)) :feed-commit))
(assert-event (equal (fn-own-feed-intent-key (fn-feed-journal-values (fjot-intent 1)))
                     (fn-own-feed-intent-key (fn-feed-journal-values (fjot-commit 1)))))
(assert-event (equal (fjot-k (fjot-intent 1) (fjot-commit 1) nil nil) '(nil nil t)))
; Removal of "I is an intent": I is member 3's commit moved past member 1's
; commit.  The kind of R holds and the keys differ; the omitted hypothesis
; fails and the feed conclusion fails: the queue order of the two articles
; changes.
(assert-event (equal (fjot-k (fjot-commit 3) (fjot-commit 1) nil nil) '(nil t nil)))
; Removal of "R is a resolution": R is member 1's INTENT; I member 3's
; intent.  Both orders then add both keys, so the intent fold changes order
; and the conclusion fails.
(assert-event (equal (fjot-k (fjot-intent 3) (fjot-intent 1) nil nil) '(nil nil t)))
