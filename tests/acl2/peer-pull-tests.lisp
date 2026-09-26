; Witnesses and teeth for the NEWNEWS pull feed (books/peer-pull.lisp,
; PRF-100) and its schedule (books/scheduler-peers.lisp `fn-sched-pull-*').
;
; The witness is one whole round as the host drives it: the peer's greeting,
; DATE, a NEWNEWS listing two Message-IDs, the local node's greeting on the
; transit connection, a 335 and a forwarded article answered 235, and a 435
; for the second id.  A second round differs from it in one reply only (436
; instead of 435), so every separating case below separates on the one thing
; the keystone is about.
(in-package "ACL2")
(include-book "../../books/peer-pull")
(include-book "std/testing/must-fail" :dir :system)

(defun pp-line (s) (append (fn-record-string-octets s) '(13 10)))
(defun pp-run (r es) (mv-let (a b) (fn-pull-run r es) (list a b)))
(defun pp-step (r e) (mv-let (a b) (fn-pull-step r e) (list a b)))

(defconst *pp-peer* (fn-record-string-octets "innA"))
(defconst *pp-wildmat* (fn-record-string-octets "fn.*"))
(defconst *pp-now* 811000000000)
(defconst *pp-a* (fn-record-string-octets "<a@fn.invalid>"))
(defconst *pp-b* (fn-record-string-octets "<b@fn.invalid>"))
(defconst *pp-fresh* (fn-pull-fresh-cursor *pp-peer*))

(defconst *pp-events-head*
  (list (cons :remote (pp-line "200 innA ready"))
        (cons :remote (pp-line "111 20260925120000"))
        (cons :remote (append (pp-line "230 list follows")
                              (pp-line "<a@fn.invalid>")
                              (pp-line "<b@fn.invalid>")
                              (pp-line "<a@fn.invalid>")
                              (pp-line ".")))
        (cons :local (pp-line "200 transit"))
        (cons :local (pp-line "335 send it"))
        (cons :remote (append (pp-line "220 0 <a@fn.invalid>")
                              (pp-line "Subject: s")
                              (pp-line "")
                              (pp-line "body")
                              (pp-line ".")))
        (cons :local (pp-line "235 accepted"))))

(defconst *pp-good-events*
  (append *pp-events-head* (list (cons :local (pp-line "435 have it")))))
(defconst *pp-held-events*
  (append *pp-events-head* (list (cons :local (pp-line "436 try later")))))

(defconst *pp-bound* 2)
(defconst *pp-r0* (fn-pull-begin *pp-fresh* *pp-wildmat* *pp-now* *pp-bound*))
(defconst *pp-good* (car (pp-run *pp-r0* *pp-good-events*)))
(defconst *pp-good-effects* (cadr (pp-run *pp-r0* *pp-good-events*)))
(defconst *pp-held* (car (pp-run *pp-r0* *pp-held-events*)))

; -----------------------------------------------------------------------------
; The round reaches its end with both ids answered by the local node; the
; repeated listing of <a> is one id.
(assert-event (equal (fn-pull-r-phase *pp-good*) :done))
(assert-event (equal (fn-pull-r-listed *pp-good*) (list *pp-a* *pp-b*)))
(assert-event (equal (fn-pull-answer-of *pp-a* (fn-pull-r-answers *pp-good*)) 235))
(assert-event (equal (fn-pull-answer-of *pp-b* (fn-pull-r-answers *pp-good*)) 435))
; The wire it drives: DATE, one NEWNEWS naming the begin instant, ARTICLE
; for the wanted id only, QUIT.
(assert-event
 (equal (fn-pull-remote-effects *pp-good-effects*)
        (list (pp-line "DATE")
              (fn-pull-newnews-octets *pp-wildmat*
                                      (- *pp-now* *fn-pull-first-window-ms*))
              (append (fn-record-string-octets "ARTICLE ") (pp-line "<a@fn.invalid>"))
              (pp-line "QUIT"))))
(assert-event
 (equal (fn-pull-newnews-octets *pp-wildmat* (- *pp-now* *fn-pull-first-window-ms*))
        (pp-line "NEWNEWS fn.* 20250911 134640 GMT")))
; The article's octets reach the local node as the IHAVE body, unchanged.
(assert-event
 (member-equal (cons :local (append (pp-line "Subject: s") (pp-line "")
                                    (pp-line "body") (pp-line ".")))
               *pp-good-effects*))

; -----------------------------------------------------------------------------
; KEYSTONE fn-pull-close-advances-only-past-a-fully-answered-round.
; Witness: the good round moves the cursor to the peer's DATE less one second.
(defconst *pp-date-ms* (fn-pull-date-ms (fn-record-string-octets "111 20260925120000")))
(assert-event (natp *pp-date-ms*))
(assert-event (not (equal (fn-pull-close *pp-good*) (fn-pull-round-cursor *pp-good*))))
(assert-event (equal (fn-pull-close *pp-good*)
                     (list *pp-peer* (- *pp-date-ms* 1000) 1 nil)))
(assert-event (fn-pull-all-answeredp (fn-pull-r-listed *pp-good*)
                                     (fn-pull-r-answers *pp-good*)))
; Tooth (the one hypothesis, "the cursor moved"): the held round differs by
; one 436, and its ids are not all answered.
(assert-event (equal (fn-pull-r-phase *pp-held*) :done))
(must-fail
 (assert-event (fn-pull-all-answeredp (fn-pull-r-listed *pp-held*)
                                      (fn-pull-r-answers *pp-held*))))
(assert-event (equal (fn-pull-close *pp-held*) (fn-pull-round-cursor *pp-held*)))

; KEYSTONE fn-pull-unanswered-id-holds-the-cursor.
(assert-event (equal (fn-pull-answer-of *pp-b* (fn-pull-r-answers *pp-held*)) 436))
; Tooth (membership): an id the round never listed does not hold the good round.
(must-fail
 (assert-event (equal (fn-pull-close *pp-good*) (fn-pull-round-cursor *pp-good*))))
(assert-event (not (member-equal (fn-record-string-octets "<z@fn.invalid>")
                                 (fn-pull-r-listed *pp-good*))))
; Tooth (no terminal answer): <a> drew 235, and the good round moves.
(assert-event (fn-pull-terminal-codep
               (fn-pull-answer-of *pp-a* (fn-pull-r-answers *pp-good*))))

; A round that fails part-way (the peer's connection is lost after the list)
; holds the cursor, even though nothing it listed drew a 436.
(defconst *pp-lost*
  (car (pp-run *pp-r0* (append (take 4 *pp-good-events*)
                                         (list (list :lost))))))
(assert-event (equal (fn-pull-r-phase *pp-lost*) :failed))
(assert-event (equal (fn-pull-close *pp-lost*) (fn-pull-round-cursor *pp-lost*)))
;; A 430 answer the peer sends while more octets follow it is a protocol
;; error: the round fails and holds the cursor.
(defconst *pp-gone*
  (car (pp-run *pp-r0* (append (take 5 *pp-good-events*)
                               (list (cons :remote (append (pp-line "430 no such article")
                                                           (pp-line "junk"))))))))
(assert-event (equal (fn-pull-r-phase *pp-gone*) :failed))
(assert-event (equal (fn-pull-close *pp-gone*) (fn-pull-round-cursor *pp-gone*)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-pull-step-answers-only-from-the-local-node.
(defconst *pp-offer*
  (car (pp-run *pp-r0* (take 4 *pp-good-events*))))
(assert-event (equal (fn-pull-r-phase *pp-offer*) :offer))
(defconst *pp-after-435*
  (car (pp-step *pp-offer* (cons :local (pp-line "435 have it")))))
; Witness: a local 435 adds exactly (<a> . 435).
(assert-event (equal (fn-pull-r-answers *pp-after-435*)
                     (cons (cons *pp-a* 435) (fn-pull-r-answers *pp-offer*))))
; Tooth (answers changed): the same octets from the PEER record nothing ---
; the conclusion "the event is local" fails for an event that changes nothing.
(defconst *pp-remote-435* (cons :remote (pp-line "435 have it")))
(assert-event (equal (fn-pull-r-answers (car (pp-step *pp-offer* *pp-remote-435*)))
                     (fn-pull-r-answers *pp-offer*)))
(must-fail (assert-event (equal (car *pp-remote-435*) :local)))

; KEYSTONE fn-pull-step-keeps-the-cursor-and-journals-nothing (no
; hypotheses): the whole good round asks with the begin cursor and journals
; nothing.
(assert-event (equal (fn-pull-round-cursor *pp-good*) (fn-pull-round-cursor *pp-r0*)))
(assert-event (null (fn-pull-journal-effects *pp-good-effects*)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-pull-journal-is-the-cursor-at-every-cut.
; Witness: from a fresh cursor, the begin journals the first instant, and
; the replay after begin, after the run, and after the close is each cut's
; cursor.
(defconst *pp-j0* (fn-pull-journal-effects (fn-pull-begin-effects *pp-fresh* *pp-now*)))
(assert-event (equal *pp-j0* (list (list *pp-peer* (- *pp-now* *fn-pull-first-window-ms*) 0 nil))))
(assert-event (equal (fn-pull-replay *pp-fresh* *pp-j0*) (fn-pull-round-cursor *pp-r0*)))
(defconst *pp-j1* (append *pp-j0* (fn-pull-journal-effects (fn-pull-close-effects *pp-good*))))
(assert-event (equal (fn-pull-replay *pp-fresh* *pp-j1*) (fn-pull-close *pp-good*)))
; The FNPL record of that cursor decodes back to it (under a fixed digest:
; the trailer's digest is the A-CRYPTO facility, not evaluable here; the
; sealed frame is exercised by the native run).
(defconst *pp-digest* *fn-pull-zero-digest*)
(defconst *pp-encoded* (fn-pull-encode :pull-cursor (fn-pull-cursor-values (fn-pull-close *pp-good*)) *pp-digest*))
(assert-event (consp *pp-encoded*))
(assert-event (equal (fn-pull-decode *pp-encoded* *pp-digest*)
                     (fn-frame-ok *fn-pull-magic* *fn-frame-version* :pull-cursor
                                  (fn-pull-cursor-values (fn-pull-close *pp-good*)))))
; An empty file is the end; a torn four-octet length is a repair to the
; previous record, never evidence.
(assert-event (equal (car (fn-pull-journal-scan *pp-peer* nil nil 0 0)) :end))
(assert-event (equal (fn-pull-journal-scan *pp-peer* '(0 0) nil 17 17) (list :repair 17 nil 17)))
; PRF-165: the truncate authority is the committed offset: a torn frame
; after unavailable records that no cursor record committed is repaired to
; the last cursor record, and so is a clean end after such records.
(assert-event (equal (fn-pull-journal-scan *pp-peer* '(0 0) nil 17 9) (list :repair 9 nil 9)))
(assert-event (equal (fn-pull-journal-scan *pp-peer* nil nil 17 9) (list :repair 9 nil 9)))

; Tooth (the journal replays to C): a journal that replays to another
; peer's-less cursor --- here an older journaled instant --- does not replay
; to the round's cursor after the begin.
(defconst *pp-old* (list *pp-peer* 5 0 nil))
(must-fail
 (assert-event (equal (fn-pull-replay *pp-fresh* (list *pp-old*))
                      (fn-pull-round-cursor *pp-r0*))))
; Tooth (startable C): a cursor whose advance count is not a natural begins
; a round whose cursor is not the journal's.
(defconst *pp-bad* (list *pp-peer* 5 -1 nil))
(assert-event (null (fn-pull-begin-effects *pp-bad* *pp-now*)))
(must-fail
 (assert-event (equal (fn-pull-replay *pp-bad* nil)
                      (fn-pull-round-cursor (fn-pull-begin *pp-bad* *pp-wildmat* *pp-now* *pp-bound*)))))

; KEYSTONE fn-pull-recovery-asks-the-dead-rounds-newnews.
; Witness: the held round dies (no close record); recovery at a later wall
; reading asks the dead round's instant again, not one window before LATER.
(defconst *pp-recovered* (fn-pull-replay *pp-fresh* *pp-j0*))
(assert-event (equal (fn-pull-r-since (fn-pull-begin *pp-recovered* *pp-wildmat*
                                                     (+ *pp-now* 3600000) *pp-bound*))
                     (fn-pull-r-since *pp-held*)))
; Tooth (the journal is replayed): starting over from the fresh cursor instead
; asks a later instant and would skip what the peer received in between.
(must-fail
 (assert-event (equal (fn-pull-r-since (fn-pull-begin *pp-fresh* *pp-wildmat*
                                                      (+ *pp-now* 3600000) *pp-bound*))
                      (fn-pull-r-since *pp-held*))))

; -----------------------------------------------------------------------------
; The schedule.
(defconst *pp-tbl* (fn-sched-pull-configure "innA" 60000 1000
                                            (fn-sched-pull-configure "fnB" 0 1000 nil)))
; KEYSTONE fn-sched-pull-due-is-due-and-idle: innA is due, fnB (interval 0) never.
(assert-event (equal (fn-sched-pull-due *pp-tbl* 1000) "innA"))
(must-fail (assert-event (fn-sched-pull-due *pp-tbl* 999)))
; KEYSTONE fn-sched-pull-started-is-not-due.
(assert-event (null (fn-sched-pull-due (fn-sched-pull-start "innA" *pp-tbl*) 5000)))
; KEYSTONE fn-sched-pull-finished-waits-its-interval.
(defconst *pp-fin* (fn-sched-pull-finish "innA" 5000 (fn-sched-pull-start "innA" *pp-tbl*)))
(assert-event (null (fn-sched-pull-due *pp-fin* 64999)))
; Tooth (LATER below NOW plus the interval): at exactly that instant it is due.
(assert-event (equal (fn-sched-pull-due *pp-fin* 65000) "innA"))
; Tooth (a peer name): the nil key is "not due" whatever the table.
(must-fail (assert-event (not (equal (fn-sched-pull-due (fn-sched-pull-start nil *pp-tbl*) 999) nil))))

; -----------------------------------------------------------------------------
; The plan read from configuration rows: interval, clear NNTP transport,
; inbound wildmat; a TLS transport without its server name and trust anchor
; rows denotes no security and is not pulled (the TLS plans are
; tests/acl2/peer-pull-session-tests.lisp's).
(defconst *pp-rows*
  (list (fn-cfg-row-make "innA" "path-identity" "inn.example" 0)
        (fn-cfg-row-make "innA" "transport-nntp" "127.0.0.1" 119)
        (fn-cfg-row-make "innA" "inbound-groups" "fn.*" 1048576)
        (fn-cfg-row-make "innA" "inbound-inflight" "" 4)
        (fn-cfg-row-make "innA" "pull-interval" "" 60)))
(assert-event (equal (fn-pull-plans *pp-rows*)
                     (list (list *pp-peer* (fn-record-string-octets "127.0.0.1") 119
                                 *pp-wildmat* 60000 (list :clear) nil
                                 *fn-pull-default-unavailable-rounds*))))
(assert-event (null (fn-pull-plans
                     (append *pp-rows*
                             (list (fn-cfg-row-make "innA" "transport-security"
                                                    "implicit" 0))))))

; -----------------------------------------------------------------------------
; PRF-165: the unavailable class (PKT-213).
;
; Round 1: the peer lists <a> and <b>, the local node wants <a> (335), the
; peer answers ARTICLE <a> with 430, the local transit connection is
; reopened, and <b> draws 435.  Bound 2.  Round 2 begins from round 1's
; cursor and goes the same way.
(defconst *pp-u-events*
  (list (cons :remote (pp-line "200 innA ready"))
        (cons :remote (pp-line "111 20260925120000"))
        (cons :remote (append (pp-line "230 list follows")
                              (pp-line "<a@fn.invalid>")
                              (pp-line "<b@fn.invalid>")
                              (pp-line ".")))
        (cons :local (pp-line "200 transit"))
        (cons :local (pp-line "335 send it"))
        (cons :remote (pp-line "430 no such article"))
        (cons :local (pp-line "200 transit"))
        (cons :local (pp-line "435 have it"))))
(defconst *pp-u1-run* (pp-run *pp-r0* *pp-u-events*))
(defconst *pp-u1* (car *pp-u1-run*))
(defconst *pp-u1-close* (fn-pull-close *pp-u1*))
(defconst *pp-u2-r0* (fn-pull-begin *pp-u1-close* *pp-wildmat* (+ *pp-now* 60000) *pp-bound*))
(defconst *pp-u2* (car (pp-run *pp-u2-r0* *pp-u-events*)))
(defconst *pp-u2-close* (fn-pull-close *pp-u2*))

; The 430 reopens the local connection (the wire) and the round goes on.
(assert-event (member-equal (list :reopen-local) (cadr *pp-u1-run*)))
(assert-event (equal (fn-pull-r-phase *pp-u1*) :done))
(assert-event (equal (fn-pull-r-unavailable *pp-u1*) (list *pp-a*)))
(assert-event (equal (fn-pull-answer-of *pp-b* (fn-pull-r-answers *pp-u1*)) 435))
(assert-event (fn-pull-completep *pp-u1*))

; KEYSTONE fn-pull-unavailable-id-is-retried-below-the-bound.
; Witness: <a> unavailable, a Message-ID, count 0+1 < 2: the instant holds
; and the journaled count is 1.
(assert-event (member-equal *pp-a* (fn-pull-list (fn-pull-r-unavailable *pp-u1*))))
(assert-event (fn-pull-msgidp *pp-a*))
(assert-event (< (+ 1 (fn-pull-count-of *pp-a* (fn-pull-r-pending *pp-u1*)))
                 (fn-pull-bound-of (fn-pull-r-bound *pp-u1*))))
(assert-event (equal (fn-pull-cursor-since *pp-u1-close*) (fn-pull-r-since *pp-u1*)))
(assert-event (equal (fn-pull-cursor-advances *pp-u1-close*) (fn-pull-r-advances *pp-u1*)))
(assert-event (equal (fn-pull-count-of *pp-a* (fn-pull-cursor-pending *pp-u1-close*)) 1))
(assert-event (equal (fn-pull-close-effects *pp-u1*) (list (cons :journal *pp-u1-close*))))
; Tooth (member): <b> was not unavailable; its count does not rise.
(must-fail (assert-event (equal (fn-pull-count-of *pp-b* (fn-pull-cursor-pending *pp-u1-close*))
                                (+ 1 (fn-pull-count-of *pp-b* (fn-pull-r-pending *pp-u1*))))))
; Tooth (below the bound): in round 2 <a>'s count reaches 2 = bound and the
; instant moves.
(assert-event (member-equal *pp-a* (fn-pull-list (fn-pull-r-unavailable *pp-u2*))))
(assert-event (equal (+ 1 (fn-pull-count-of *pp-a* (fn-pull-r-pending *pp-u2*))) 2))
(must-fail (assert-event (equal (fn-pull-cursor-since *pp-u2-close*) (fn-pull-r-since *pp-u2*))))
; Tooth (a Message-ID; corrupted state, unreachable from the host: only a
; listed id is ever current): a non-Message-ID in UNAVAILABLE is not counted.
(defconst *pp-junk* (fn-record-string-octets "junk"))
(defconst *pp-u1-corrupt* (fn-pull-with *pp-u1* :unavailable (list *pp-junk* *pp-a*)))
(must-fail (assert-event (equal (fn-pull-count-of *pp-junk*
                                                  (fn-pull-cursor-pending (fn-pull-close *pp-u1-corrupt*)))
                                1)))

; KEYSTONE fn-pull-complete-round-past-the-bound-advances.
; Witness: round 2 is complete, nothing holds, the cursor advances and PENDING
; clears; <a> is dropped (logged) exactly now.
(assert-event (fn-pull-completep *pp-u2*))
(assert-event (not (fn-pull-holdingp (fn-pull-list (fn-pull-r-unavailable *pp-u2*))
                                     (fn-pull-r-pending *pp-u2*) (fn-pull-r-bound *pp-u2*))))
(assert-event (equal *pp-u2-close*
                     (fn-pull-cursor *pp-peer* (fn-pull-back (fn-pull-r-started *pp-u2*) 1000)
                                     1 nil)))
(assert-event (equal (fn-pull-dropped *pp-u2*) (list *pp-a*)))
(assert-event (equal (fn-pull-dropped *pp-u1*) nil))
; Tooth (not holding): round 1 holds; its close is not the advance.
(must-fail (assert-event (equal *pp-u1-close*
                                (fn-pull-cursor *pp-peer* (fn-pull-back (fn-pull-r-started *pp-u1*) 1000)
                                                1 nil))))
; Tooth (complete): a round lost after its list with nothing unavailable is
; not complete, and does not advance.
(assert-event (not (fn-pull-holdingp nil nil *pp-bound*)))
(must-fail (assert-event (fn-pull-completep *pp-lost*)))
(must-fail (assert-event (equal (fn-pull-cursor-advances (fn-pull-close *pp-lost*)) 1)))

; KEYSTONE fn-pull-close-advances-only-past-a-fully-answered-round (PRF-165).
; Witness: round 2's close moves the advance count; the round is done, every
; listed id is answered or dropped, the instant is the DATE less a second,
; PENDING is nil.
(assert-event (not (equal (fn-pull-cursor-advances *pp-u2-close*) (fn-pull-r-advances *pp-u2*))))
(assert-event (equal (fn-pull-r-phase *pp-u2*) :done))
(assert-event (fn-pull-all-answered-or-droppedp (fn-pull-r-listed *pp-u2*) (fn-pull-r-answers *pp-u2*)
                                                (fn-pull-r-unavailable *pp-u2*) (fn-pull-r-pending *pp-u2*)
                                                (fn-pull-r-bound *pp-u2*)))
(assert-event (equal (fn-pull-cursor-since *pp-u2-close*)
                     (fn-pull-back (fn-pull-r-started *pp-u2*) *fn-pull-overlap-ms*)))
(assert-event (null (fn-pull-cursor-pending *pp-u2-close*)))
; Tooth (the antecedent): round 1 does not move the advance count, and its
; PENDING is not nil.
(must-fail (assert-event (not (equal (fn-pull-cursor-advances *pp-u1-close*)
                                     (fn-pull-r-advances *pp-u1*)))))
(must-fail (assert-event (null (fn-pull-cursor-pending *pp-u1-close*))))
; The OLD form of the keystone (every listed id terminal) is false of the
; new behaviour: round 2 advances past <a>, which drew no terminal answer.
(must-fail (assert-event (fn-pull-all-answeredp (fn-pull-r-listed *pp-u2*)
                                                (fn-pull-r-answers *pp-u2*))))

; KEYSTONE fn-pull-close-advances-past-all-answered-when-nothing-is-unavailable.
; Witness: the good round (nothing unavailable) moves, every id terminal.
(assert-event (not (consp (fn-pull-r-unavailable *pp-good*))))
(assert-event (not (equal (fn-pull-close *pp-good*) (fn-pull-round-cursor *pp-good*))))
(assert-event (fn-pull-all-answeredp (fn-pull-r-listed *pp-good*) (fn-pull-r-answers *pp-good*)))
; Tooth (nothing unavailable): round 2 moves with <a> unavailable, and not
; every id is terminal (the must-fail above).
(assert-event (consp (fn-pull-r-unavailable *pp-u2*)))

; KEYSTONE fn-pull-unanswered-id-holds-the-cursor (restated).
; Witness: <a> in round 1: listed, no terminal answer, not dropped: held.
(assert-event (member-equal *pp-a* (fn-pull-r-listed *pp-u1*)))
(assert-event (not (fn-pull-terminal-codep (fn-pull-answer-of *pp-a* (fn-pull-r-answers *pp-u1*)))))
; Tooth (not dropped): the same id in round 2 is dropped and the instant moves
; (the must-fail on round 2's since above).

; KEYSTONE fn-pull-step-marks-unavailable-only-on-the-peers-reply.
(defconst *pp-at-article* (car (pp-run *pp-r0* (take 5 *pp-u-events*))))
(defconst *pp-430* (cons :remote (pp-line "430 no such article")))
(assert-event (equal (fn-pull-r-phase *pp-at-article*) :article))
(assert-event (equal (fn-pull-r-unavailable (car (pp-step *pp-at-article* *pp-430*)))
                     (cons (fn-pull-r-current *pp-at-article*)
                           (fn-pull-list (fn-pull-r-unavailable *pp-at-article*)))))
(assert-event (equal (fn-pull-r-current *pp-at-article*) *pp-a*))
; Tooth (a peer reply): the same 430 line from the LOCAL node in :offer marks
; nothing (it is an answer the local node gave, not the peer's).
(defconst *pp-offer-u* (car (pp-run *pp-r0* (take 4 *pp-u-events*))))
(assert-event (equal (fn-pull-r-unavailable (car (pp-step *pp-offer-u* (cons :local (pp-line "430 no")))))
                     (fn-pull-r-unavailable *pp-offer-u*)))
(must-fail (assert-event (equal (fn-pull-r-unavailable (car (pp-step *pp-offer-u* (cons :local (pp-line "430 no")))))
                                (cons *pp-a* nil))))

; KEYSTONE fn-pull-records-replay-is-the-replay.
; Witness: the logical journal of round 1 (the begin's cursor, then the held
; cursor with <a> counted once) scans back as records that fold to it.
(defconst *pp-uj* (list (car *pp-j0*) *pp-u1-close*))
(assert-event (equal (fn-pull-journal-records *pp-uj*)
                     (list (list :cursor *pp-peer* (- *pp-now* *fn-pull-first-window-ms*) 0)
                           (list :unavailable *pp-peer* *pp-a* 1)
                           (list :cursor *pp-peer* (fn-pull-cursor-since *pp-u1-close*) 0))))
(assert-event (equal (fn-pull-records-replay *pp-fresh* (fn-pull-journal-records *pp-uj*))
                     *pp-u1-close*))
(assert-event (equal (fn-pull-replay *pp-fresh* *pp-uj*) *pp-u1-close*))
; Mutation (order): a cursor record BEFORE its unavailable records commits
; nothing; the count is lost.
(must-fail (assert-event (equal (fn-pull-records-replay
                                 *pp-fresh*
                                 (list (list :cursor *pp-peer* (fn-pull-cursor-since *pp-u1-close*) 0)
                                       (list :unavailable *pp-peer* *pp-a* 1)))
                                *pp-u1-close*)))
; The unavailable record's frame decodes back to its values.
(defconst *pp-u-encoded* (fn-pull-encode :pull-unavailable (list *pp-peer* *pp-a* 1) *pp-digest*))
(assert-event (consp *pp-u-encoded*))
(assert-event (equal (fn-pull-decode *pp-u-encoded* *pp-digest*)
                     (fn-frame-ok *fn-pull-magic* *fn-frame-version* :pull-unavailable
                                  (list *pp-peer* *pp-a* 1))))

; KEYSTONE fn-pull-records-replay-ignores-an-uncommitted-tail.
; Witness: round 2's close record torn after its unavailable records (none
; here: round 2 advanced) -- use round 1's: the tail of <a> without its cursor
; record recovers the begin's cursor.
(assert-event (equal (fn-pull-records-replay
                      *pp-fresh*
                      (append (fn-pull-journal-records (list (car *pp-j0*)))
                              (fn-pull-pending-records *pp-peer* (fn-pull-cursor-pending *pp-u1-close*))))
                     (car *pp-j0*)))
; Tooth (uncommitted): with its cursor record the same tail commits.
(must-fail (assert-event (equal (fn-pull-records-replay
                                 *pp-fresh* (fn-pull-journal-records *pp-uj*))
                                (car *pp-j0*))))

; The log line names the drop.
(assert-event (equal (fn-pull-log-line *pp-u2*)
                     (append (fn-record-string-octets "pull peer=innA round=done cursor=advanced unavailable=1 dropped=")
                             *pp-a*)))
