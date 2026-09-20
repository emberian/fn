; Evidence for the mutable service owner (books/owner.lisp,
; books/owner-invariants.lisp).
;
; Order follows docs/proof-style.md section 6: the guard-world audit, then the
; scenario (an owner driven from the initial store through the real
; allocation, staging, publication and completion events, with two readers
; pinned at different versions, a post between them, a stalled reader and a
; crash-plus-reopen), then the teeth: one concrete violating value per
; hypothesis of each keystone, each an assert-event on the negated conclusion.

(in-package "ACL2")
(include-book "../../books/owner-invariants")

; -----------------------------------------------------------------------------
; Guard-world audit: the served port and the connection events are total in
; the executable sense (guard t, verified); the store events carry the
; kernel's invariant as their guard.

(assert-event (equal (symbol-class 'fn-own-read (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-own-read nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-own-open (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-own-open nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-own-advance (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-own-close (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-own-start (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-own-complete (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-own-complete nil (w state))
                     '(fn-sn-statep (fn-own-store o))))
(assert-event (equal (guard 'fn-own-step nil (w state))
                     '(fn-sn-statep (fn-own-store o))))

; -----------------------------------------------------------------------------
; A post as the owner sees it: the same event sequence tools/run_owner.py
; reports (host/owner-host.lisp), from reservation to completion.

(defconst *own-groups* '("fn.letters" "fn.test"))

; Obligation id, content subject and release evidence are derived from the
; Message-ID as tools/run_store.py's metadata does: retention refuses a known
; obligation id (fn-retain-known-obligation-id-is-not-reused), so two posts
; cannot share one.
(defun own-record (sequence txid msgid)
  (fn-record-make sequence txid txid msgid
                  (list 77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10
                        72 105 13 10)
                  '("fn.letters")
                  (concatenate 'string "own-pin:" msgid)
                  (concatenate 'string "own-content:" msgid)
                  (concatenate 'string "own-release:" msgid)
                  2))

(defun own-post-events (record)
  (list '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare record))
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        '(:complete)))

(defconst *own-group-command*
  (list :command (fn-nntp-string-octets "GROUP fn.letters")))
(defconst *own-group-octets*
  (append (fn-nntp-string-octets "GROUP fn.letters") '(13 10)))

; The owner over the initial store, bound to four connections.
(defconst *own-0* (fn-own-start (fn-sn-initial *own-groups* 10) 4))
(assert-event (fn-own-relation *own-0*))
(assert-event (equal (fn-own-view-version (fn-own-view *own-0*)) 0))

; Reader A opens at version 0 and is greeted.
(defconst *own-open-a* (fn-own-open *own-0*))
(assert-event (equal (fn-served-reply-octets (car *own-open-a*)) *fn-served-greeting*))
(defconst *own-a* (cdr *own-open-a*))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 0 (fn-own-conns *own-a*))) 0))

; Connection 1 (the CLI post path) opens and posts; the transaction runs
; through the real kernel events and completes.
(defconst *own-b* (fn-own-step *own-a* '(:open)))
(defconst *own-begun* (fn-own-step *own-b* '(:begin 1)))
(assert-event (equal (fn-own-pending *own-begun*) 1))
(defconst *own-posted* (fn-own-run *own-begun* (own-post-events (own-record 0 0 "<one@example>"))))
(assert-event (fn-own-relation *own-posted*))
(assert-event (equal (fn-own-view-version (fn-own-view *own-posted*)) 1))
(assert-event (equal (len (fn-own-ledger *own-posted*)) 1))
(assert-event (null (fn-own-pending *own-posted*)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store *own-posted*))) :ready))

; Reader A is still pinned at version 0 after the post; reader C opens at 1.
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 0 (fn-own-conns *own-posted*))) 0))
(defconst *own-c* (fn-own-step *own-posted* '(:open)))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 2 (fn-own-conns *own-c*))) 1))

; The same read answers differently on the two pins: A sees an empty group,
; C sees one article.  This is the two-readers-at-different-versions witness
; for the served port (fn-own-read-is-served-step-on-pinned-prefix) and for
; its per-event law (fn-own-reader-sees-pinned-prefix-replay).
(defconst *own-read-a* (fn-own-read *own-c* 0 *own-group-octets*))
(defconst *own-read-c* (fn-own-read *own-c* 2 *own-group-octets*))
(assert-event (not (equal (car *own-read-a*) (car *own-read-c*))))
(assert-event (equal (fn-served-reply-octets (car *own-read-c*))
                     (append (fn-nntp-string-octets "211 1 1 1 fn.letters") (list 13 10))))
(assert-event (equal (fn-own-take 5 (fn-served-reply-octets (car *own-read-a*)))
                     (fn-nntp-string-octets "211 0")))
(assert-event (not (fn-served-closingp (car *own-read-a*))))
(assert-event (fn-own-relation (cdr *own-read-a*)))
; The served port keeps the wire state: a read cut inside the command line
; frames nothing, the rest of the line completes it (fn-served-run-is-the-
; concatenated-step, books/served.lisp).
(defconst *own-read-cut*
  (fn-own-read (cdr (fn-own-read *own-c* 2 (fn-own-take 7 *own-group-octets*)))
               2 (nthcdr 7 *own-group-octets*)))
(assert-event (null (car (fn-own-read *own-c* 2 (fn-own-take 7 *own-group-octets*)))))
(assert-event (equal (car *own-read-cut*) (car *own-read-c*)))

(defconst *own-reply-a* (car (fn-own-read-step *own-c* 0 *own-group-command*)))
(defconst *own-reply-c* (car (fn-own-read-step *own-c* 2 *own-group-command*)))
(assert-event (not (equal *own-reply-a* *own-reply-c*)))
(assert-event (equal *own-reply-c*
                     (list (fn-nntp-reply-effect
                            (append (fn-nntp-string-octets "211 1 1 1 fn.letters") (list 13 10))))))
(assert-event (equal (car *own-read-c*) *own-reply-c*))

; K1 (served) and K1 (per event) hold on the witness in their stated forms.
(assert-event
 (let* ((conn (fn-own-find-conn 0 (fn-own-conns *own-c*)))
        (s (fn-own-store *own-c*)))
   (equal (car *own-read-a*)
          (fn-served-result-effects
           (fn-served-step
            (fn-served-make-conn
             (fn-own-conn-wire conn) (fn-own-conn-session conn)
             (fn-node-acceptance
              (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                 (fn-own-take (fn-own-conn-version conn)
                                              (fn-sf-records (fn-sn-files s)))
                                 (fn-own-conn-frontier conn))))
            *own-group-octets*)))))
(assert-event
 (let* ((conn (fn-own-find-conn 0 (fn-own-conns *own-c*)))
        (s (fn-own-store *own-c*)))
   (equal *own-reply-a*
          (fn-nntp-result-effects
           (fn-nntp-step (fn-own-conn-session conn)
                         (fn-node-acceptance
                          (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                             (fn-own-take (fn-own-conn-version conn)
                                                          (fn-sf-records (fn-sn-files s)))
                                             (fn-own-conn-frontier conn)))
                         *own-group-command*)))))

; Reader A advances and now sees the newest version.
(defconst *own-advanced* (fn-own-step *own-c* '(:advance 0)))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 0 (fn-own-conns *own-advanced*))) 1))
(assert-event (equal (car (fn-own-read *own-advanced* 0 *own-group-octets*))
                     (car *own-read-c*)))

; A stalled reader (connection 2 receives no events) does not block a second
; post; connection 1 posts again while 2 stays pinned at version 1.
(defconst *own-posted-2*
  (fn-own-run (fn-own-step *own-advanced* '(:begin 1))
              (own-post-events (own-record 1 1 "<two@example>"))))
(assert-event (fn-own-relation *own-posted-2*))
(assert-event (equal (fn-own-view-version (fn-own-view *own-posted-2*)) 2))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 2 (fn-own-conns *own-posted-2*))) 1))
(assert-event (equal (len (fn-own-ledger *own-posted-2*)) 2))

; The connection that posted closes; then the process crashes and reopens
; over the exact image on disk.  Every completed post is still in the
; durable history and a fresh reader sees the newest version.
(defconst *own-closed* (fn-own-step *own-posted-2* '(:close 1)))
(assert-event (null (fn-own-find-conn 1 (fn-own-conns *own-closed*))))
(defconst *own-image-frontier* (fn-sf-frontier (fn-sn-files (fn-own-store *own-closed*))))
(defconst *own-image-records* (fn-sf-records (fn-sn-files (fn-own-store *own-closed*))))
(defconst *own-reopened*
  (fn-own-step *own-closed* (list :reopen *own-image-frontier* *own-image-records*)))
(assert-event (fn-own-relation *own-reopened*))
(assert-event (null (fn-own-conns *own-reopened*)))
(assert-event (null (fn-own-clock *own-reopened*)))
(assert-event (equal (fn-own-view-version (fn-own-view *own-reopened*)) 2))
(assert-event (fn-own-ledger-durablep (fn-own-ledger *own-reopened*)
                                      (fn-sf-records (fn-sn-files (fn-own-store *own-reopened*)))))
(defconst *own-after* (fn-own-step *own-reopened* '(:open)))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 3 (fn-own-conns *own-after*))) 2))
(assert-event (equal (fn-served-reply-octets (car (fn-own-read *own-after* 3 *own-group-octets*)))
                     (append (fn-nntp-string-octets "211 2 1 2 fn.letters") (list 13 10))))

; The whole witness is one finite owner-event trace from the initial owner.
(defconst *own-trace*
  (append (list '(:open) '(:open) '(:begin 1))
          (own-post-events (own-record 0 0 "<one@example>"))
          (list '(:open) '(:advance 0) '(:begin 1))
          (own-post-events (own-record 1 1 "<two@example>"))
          (list '(:close 1)
                (list :reopen *own-image-frontier* *own-image-records*)
                '(:open))))
(assert-event (equal (fn-own-run *own-0* *own-trace*) *own-after*))

; The host's restart dispatch: the image's open result has kind :ok, and the
; owner started over it satisfies the relation (fn-own-open-kind-ok-is-okp,
; fn-own-open-observed-start-relation).
(assert-event (equal (fn-sn-open-kind (fn-sn-open-observed *own-groups* 10 *own-image-frontier*
                                                           *own-image-records*))
                     :ok))

; -----------------------------------------------------------------------------
; K2: completion consumed once.  The witness is a completing owner on which
; one completion changes the state and the second is the identity.

(defconst *own-completing*
  (fn-own-run *own-begun* (butlast (own-post-events (own-record 0 0 "<one@example>")) 1)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store *own-completing*))) :completing))
(assert-event (not (equal (fn-own-complete *own-completing*) *own-completing*)))
(assert-event (equal (fn-own-complete (fn-own-complete *own-completing*))
                     (fn-own-complete *own-completing*)))
(assert-event (equal (fn-own-ledger (fn-own-complete *own-completing*))
                     (list (fn-sf-completion (fn-sn-files (fn-own-store *own-completing*))))))
; A completion away from :completing changes nothing at all.
(assert-event (equal (fn-own-complete *own-posted*) *own-posted*))
(assert-event (equal (fn-own-complete *own-a*) *own-a*))

; -----------------------------------------------------------------------------
; K3 and the reclaim floor on the witness: connection 1 opened at version 0
; and never advanced, so the floor is 0 while it is open; closing it raises
; the floor to the next lowest pin (A and C at 1); after the reopen the only
; pin is D's at 2.  The pinned prefix of every connection is unchanged by the
; whole trace.

(assert-event (equal (fn-own-reclaim-floor *own-posted-2*) 0))
(assert-event (equal (fn-own-reclaim-floor *own-closed*) 1))
(assert-event (equal (fn-own-reclaim-floor *own-after*) 2))
(assert-event (equal (fn-own-take 1 (fn-sf-records (fn-sn-files (fn-own-store *own-posted-2*))))
                     (fn-own-take 1 (fn-sf-records (fn-sn-files (fn-own-store *own-c*))))))

; -----------------------------------------------------------------------------
; K4 on the witness: the bound is real.  A fifth open is refused and greets
; nothing.

(defconst *own-full*
  (fn-own-run *own-after* '((:open) (:open) (:open) (:open))))
(assert-event (equal (len (fn-own-conns *own-full*)) 4))
(assert-event (equal (fn-own-max-conns *own-full*) 4))
(assert-event (fn-own-conns-boundedp (fn-own-conns *own-full*) *own-groups*))
(assert-event (null (car (fn-own-open *own-full*))))
(assert-event (equal (cdr (fn-own-open *own-full*)) *own-full*))

; -----------------------------------------------------------------------------
; Clock and facts on the witness.

(defconst *own-obs* (fn-clock-observation 1000 1600000000000 5000 t))
(defconst *own-obs-later* (fn-clock-observation 9000 1600000008000 5000 t))
(defconst *own-obs-backwards* (fn-clock-observation 500 1600000000000 5000 t))
(assert-event (equal (fn-own-declare-group *own-after* "fn.new") *own-after*))
(defconst *own-clocked* (fn-own-step *own-after* (list :observe *own-obs*)))
(assert-event (equal (fn-own-clock *own-clocked*) *own-obs*))
(assert-event (equal (fn-own-step *own-clocked* (list :observe *own-obs-backwards*))
                     *own-clocked*))
(defconst *own-declared* (fn-own-step *own-clocked* '(:declare-group "fn.new")))
(assert-event (equal (fn-own-replay-facts (fn-own-facts *own-declared*)) '("fn.new")))
(assert-event (equal (fn-own-group-fact-stamp (car (fn-own-facts *own-declared*))) *own-obs*))
(assert-event (fn-own-relation (fn-own-step *own-declared* (list :observe *own-obs-later*))))

; -----------------------------------------------------------------------------
; Teeth.  One concrete violating value per hypothesis of each keystone: the
; conclusion evaluated to false on an owner with that hypothesis dropped.
; Values outside a guard are evaluated under with-guard-checking :none.

; A hand-built owner that violates the relation: connection 0 claims version
; 0 but carries the version-2 archive.  Reachable states cannot do this.
(defconst *own-bogus*
  (let* ((archive (fn-own-view-archive (fn-own-view *own-after*)))
         (sconn (fn-served-result-conn
                 (fn-served-open archive *fn-nntp-max-initial-line-octets*
                                 *fn-own-body-limit*))))
    (fn-own-make (fn-own-store *own-after*) (fn-own-view *own-after*)
                 (list (fn-own-conn-make 0 0 0 (fn-served-conn-wire sconn)
                                         (fn-served-conn-session sconn) archive))
                 1 4 nil nil nil nil)))
(assert-event (not (fn-own-relation *own-bogus*)))

; K1 (served) without (fn-own-relation o): the reply is not the served step
; over the pinned prefix.
(assert-event
 (let* ((o *own-bogus*)
        (conn (fn-own-find-conn 0 (fn-own-conns o)))
        (s (fn-own-store o)))
   (not (equal (car (fn-own-read o 0 *own-group-octets*))
               (fn-served-result-effects
                (fn-served-step
                 (fn-served-make-conn
                  (fn-own-conn-wire conn) (fn-own-conn-session conn)
                  (fn-node-acceptance
                   (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                      (fn-own-take (fn-own-conn-version conn)
                                                   (fn-sf-records (fn-sn-files s)))
                                      (fn-own-conn-frontier conn))))
                 *own-group-octets*))))))
; K1 (served) without (fn-own-find-conn id conns): an unknown connection
; reads nothing, while a served step over the view's prefix answers.
(assert-event
 (let* ((o *own-after*)
        (s (fn-own-store o))
        (sconn (fn-served-result-conn
                (fn-served-open (fn-own-view-archive (fn-own-view o))
                                *fn-nntp-max-initial-line-octets* *fn-own-body-limit*))))
   (not (equal (car (fn-own-read o 99 *own-group-octets*))
               (fn-served-result-effects
                (fn-served-step
                 (fn-served-make-conn
                  (fn-served-conn-wire sconn) (fn-served-conn-session sconn)
                  (fn-node-acceptance
                   (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                      (fn-own-take 2 (fn-sf-records (fn-sn-files s)))
                                      (fn-sf-frontier (fn-sn-files s)))))
                 *own-group-octets*))))))

; K1 (per event) without (fn-own-relation o).
(assert-event
 (let* ((o *own-bogus*)
        (conn (fn-own-find-conn 0 (fn-own-conns o)))
        (s (fn-own-store o)))
   (not (equal (car (fn-own-read-step o 0 *own-group-command*))
               (fn-nntp-result-effects
                (fn-nntp-step (fn-own-conn-session conn)
                              (fn-node-acceptance
                               (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                                  (fn-own-take (fn-own-conn-version conn)
                                                               (fn-sf-records (fn-sn-files s)))
                                                  (fn-own-conn-frontier conn)))
                              *own-group-command*))))))
; K1 (per event) without (fn-own-find-conn id conns).
(assert-event
 (let* ((o *own-after*)
        (s (fn-own-store o)))
   (not (equal (car (fn-own-read-step o 99 *own-group-command*))
               (fn-nntp-result-effects
                (fn-nntp-step (fn-nntp-open-session (fn-own-view-archive (fn-own-view o)))
                              (fn-node-acceptance
                               (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                                  (fn-own-take 2 (fn-sf-records (fn-sn-files s)))
                                                  (fn-sf-frontier (fn-sn-files s))))
                              *own-group-command*))))))
; The after-any-trace forms, on the same values with the empty trace.
(assert-event (not (fn-own-relation (fn-own-run *own-bogus* nil))))
(assert-event (null (fn-own-find-conn 99 (fn-own-conns (fn-own-run *own-after* nil)))))

; K3 without (fn-own-relation o): a bogus pin above the history is not a
; prefix that survives the trace.
(defconst *own-bogus-pin*
  (fn-own-make (fn-own-store *own-0*) (fn-own-view *own-0*)
               (list (fn-own-conn-make 0 7 0 nil nil nil))
               1 4 nil nil nil nil))
(assert-event
 (not (equal (fn-own-take 7 (fn-sf-records (fn-sn-files (fn-own-store
                                                         (fn-own-run *own-bogus-pin* *own-trace*)))))
             (fn-own-take 7 (fn-sf-records (fn-sn-files (fn-own-store *own-bogus-pin*)))))))
; K3 without (fn-own-find-conn id conns): OPEN, no violating value.  For an
; absent connection fn-own-conn-version is nil and fn-own-take of nil is nil
; on both sides, so the conclusion holds vacuously; the hypothesis is
; unnecessary and is kept only because the statement is frozen this wave.
; The reclaim-floor keystone's same hypothesis does have a violating value:
(assert-event
 (with-guard-checking :none
  (not (<= (fn-own-reclaim-floor *own-after*)
           (fn-own-conn-version (fn-own-find-conn 99 (fn-own-conns *own-after*)))))))
; Reclaim floor without (fn-own-relation o): a non-natural pin.
(assert-event
 (with-guard-checking :none
  (let ((o (fn-own-make (fn-own-store *own-0*) (fn-own-view-make 3 0 nil)
                        (list (fn-own-conn-make 0 "seven" 0 nil nil nil))
                        1 4 nil nil nil nil)))
    (not (<= (fn-own-reclaim-floor o)
             (fn-own-conn-version (fn-own-find-conn 0 (fn-own-conns o))))))))

; K4 without (fn-own-relation o): five hand-built connections under a bound
; of 4, both conjuncts false.
(defconst *own-over*
  (fn-own-make (fn-own-store *own-after*) (fn-own-view *own-after*)
               (list (fn-own-conn-make 0 2 2 nil nil nil) (fn-own-conn-make 1 2 2 nil nil nil)
                     (fn-own-conn-make 2 2 2 nil nil nil) (fn-own-conn-make 3 2 2 nil nil nil)
                     (fn-own-conn-make 4 2 2 nil nil nil))
               5 4 nil nil nil nil))
(assert-event (not (<= (len (fn-own-conns (fn-own-run *own-over* nil)))
                       (fn-own-max-conns *own-over*))))
(assert-event (not (fn-own-conns-boundedp (fn-own-conns (fn-own-run *own-over* nil))
                                          *own-groups*)))

; K5 without (fn-own-relation o): a ledger entry with no record.
(defconst *own-forged*
  (fn-own-make (fn-own-store *own-0*) (fn-own-view *own-0*) nil 0 4 nil
               (list (cons 0 0)) nil nil))
(assert-event
 (not (fn-sf-record-has-pairp (cons 0 0)
                              (fn-sf-records (fn-sn-files (fn-own-store
                                                           (fn-own-run *own-forged* nil)))))))
; K5 without (member-equal pair ledger): a pair never consumed is not durable.
(assert-event
 (not (fn-sf-record-has-pairp (cons 9 9)
                              (fn-sf-records (fn-sn-files (fn-own-store
                                                           (fn-own-run *own-after* nil)))))))

; K6 without (fn-own-relation o): the bogus owner does not satisfy it after
; the empty trace either, and neither does its store relation claim hold of a
; non-state.
(assert-event (not (fn-own-relation (fn-own-run *own-bogus* nil))))
(assert-event
 (with-guard-checking :none
  (not (fn-snt-relation (fn-own-store (fn-own-run (fn-own-make nil nil nil 0 4 nil nil nil nil)
                                                  nil))))))

; Root without open-okp: a rejected image (malformed frontier) has kind
; :error and starts nothing that satisfies the relation.
(assert-event
 (equal (fn-sn-open-kind (fn-sn-open-observed *own-groups* 10 "frontier" *own-image-records*))
        :error))
(assert-event
 (with-guard-checking :none
  (not (fn-own-relation
        (fn-own-start (fn-sn-open-state
                       (fn-sn-open-observed *own-groups* 10 "frontier" *own-image-records*))
                      4)))))
; Root without (natp max-conns).
(assert-event
 (not (fn-own-relation
       (fn-own-start (fn-sn-open-state
                      (fn-sn-open-observed *own-groups* 10 *own-image-frontier*
                                           *own-image-records*))
                     -1))))

; Facts.  fn-own-declared-group-is-replayed without a clock observation: the
; group is not in the replay; without (stringp name): neither is a non-string.
(assert-event (not (member-equal "fn.new" (fn-own-replay-facts
                                           (fn-own-facts (fn-own-declare-group *own-after* "fn.new"))))))
(assert-event (not (member-equal 42 (fn-own-replay-facts
                                     (fn-own-facts (fn-own-declare-group *own-clocked* 42))))))
; fn-own-every-fact-is-clock-stamped without (fn-own-relation o): a fact
; stamped nil; without (member-equal fact facts): a fact the log never held.
(defconst *own-unstamped*
  (fn-own-make (fn-own-store *own-0*) (fn-own-view *own-0*) nil 0 4 nil nil nil
               (list (fn-own-group-fact-make "fn.new" nil))))
(assert-event (not (fn-own-relation *own-unstamped*)))
(assert-event (not (fn-clock-observationp
                    (fn-own-group-fact-stamp (car (fn-own-facts *own-unstamped*))))))
(assert-event (not (fn-clock-observationp
                    (fn-own-group-fact-stamp (fn-own-group-fact-make "fn.other" nil)))))
