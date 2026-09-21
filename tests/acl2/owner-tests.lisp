; Evidence for the mutable service owner (books/owner.lisp,
; books/owner-invariants.lisp).
;
; Order follows docs/proof-style.md section 6: the guard-world audit, then the
; scenario (an owner driven from the initial store through the real
; allocation, staging, publication and completion events, with two readers
; pinned at different versions, a post between them, a stalled reader and a
; crash-plus-reopen, then the served POST path: a post through the served
; port, the writer step, the store events, the outcome rendered by the book,
; a reader pinned across it), then the teeth: one concrete violating value
; per hypothesis of each keystone, each an assert-event on the negated
; conclusion.

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
(assert-event (equal (symbol-class 'fn-own-take-submission (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-own-take-submission nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-own-outcome (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-own-outcome nil (w state)) *t*))
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
(defconst *own-open-a* (fn-own-open *own-0* nil))
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
                                 (fn-own-conn-frontier conn)))
             (fn-own-conn-config conn) (fn-own-conn-observation conn)
             (fn-own-clock *own-c*))
            *own-group-octets*)))))
(assert-event
 (let* ((conn (fn-own-find-conn 0 (fn-own-conns *own-c*)))
        (s (fn-own-store *own-c*)))
   (equal *own-reply-a*
          (fn-served-result-effects
           (fn-served-dispatch
            (fn-served-make-conn
             (fn-own-conn-wire conn) (fn-own-conn-session conn)
             (fn-node-acceptance
              (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                 (fn-own-take (fn-own-conn-version conn)
                                              (fn-sf-records (fn-sn-files s)))
                                 (fn-own-conn-frontier conn)))
             (fn-own-conn-config conn) (fn-own-conn-observation conn)
             (fn-own-clock *own-c*))
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

; -----------------------------------------------------------------------------
; D14-b, the owner half of the counterexample: why the recovery freedom is
; fn-sf-recovery-crash-imagep and NOT a widening of fn-sf-crash-imagep, which
; is the gate of fn-own-reopen (owner.lisp:911).
;
; *own-reopened* is an ordinary reachable owner: its store is a
; recovery-window state, its own success history is empty (fn-sn-open-observed
; keeps no ghost), and its LEDGER still names both records -- including the
; second, which an earlier process completed and acknowledged and which is
; therefore fenced.  The kernel cannot see that: which of its records are
; fenced is a fact about the byte store's pending list.  So the platform
; predicate admits the rolled-back image of this very state, while the ledger
; clause of fn-own-relation is false on it.  Had fn-sf-crash-imagep been
; widened, fn-own-reopen would take that image and
; fn-own-reopen-preserves-relation would be FALSE.

(assert-event (fn-sf-record-rollback-visiblep (fn-sn-files (fn-own-store *own-reopened*))))
(assert-event (equal (fn-sf-successes (fn-sn-files (fn-own-store *own-reopened*))) nil))
(assert-event (equal (len (fn-own-ledger *own-reopened*)) 2))
(defconst *own-rolled-back-image* (fn-sf-but-last *own-image-records*))
(assert-event (equal (len *own-rolled-back-image*) 1))
; The platform predicate admits it; the reliance predicate does not.
(assert-event (fn-sf-recovery-crash-imagep (fn-sn-files (fn-own-store *own-reopened*))
                                           *own-image-frontier* *own-rolled-back-image*))
(assert-event (not (fn-sf-crash-imagep (fn-sn-files (fn-own-store *own-reopened*))
                                       *own-image-frontier* *own-rolled-back-image*)))
; The reopen on it would hold exactly the shorter list...
(assert-event (equal (fn-sf-records
                      (fn-sn-files
                       (fn-sn-open-state
                        (fn-sn-open-observed *own-groups* 10 *own-image-frontier*
                                             *own-rolled-back-image*))))
                     *own-rolled-back-image*))
; ...fn-own-reopen carries the ledger across unchanged...
(assert-event (equal (fn-own-ledger *own-reopened*) (fn-own-ledger *own-closed*)))
; ...and the ledger clause of fn-own-relation is false on that list, which is
; the counterexample: relation in, no relation out.
(assert-event (fn-own-relation *own-reopened*))
(assert-event (fn-own-ledger-durablep (fn-own-ledger *own-reopened*) *own-image-records*))
(assert-event (with-guard-checking :none
               (not (fn-own-ledger-durablep (fn-own-ledger *own-reopened*)
                                            *own-rolled-back-image*))))

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
(assert-event (null (car (fn-own-open *own-full* nil))))
(assert-event (equal (cdr (fn-own-open *own-full* nil)) *own-full*))

; -----------------------------------------------------------------------------
; Clock and facts on the witness.

(defconst *own-obs* (fn-clock-observation 1000 1600000000000 5000 t))
(defconst *own-obs-later* (fn-clock-observation 9000 1600000008000 5000 t))
(defconst *own-obs-backwards* (fn-clock-observation 500 1600000000000 5000 t))
(assert-event (equal (fn-own-declare-group *own-after* "fn.new") *own-after*))
(defconst *own-clocked* (fn-own-step *own-after* (list :observe *own-obs*)))
(assert-event (equal (fn-own-clock *own-clocked*) *own-obs*))
; D10-a.  A reading that is not a later observation of the same clock is
; REFUSED, and the refusal costs the owner the clock it held.  This line
; used to assert that the owner was UNCHANGED, which is exactly the
; behaviour that let a node go on deciding -- minting Message-Ids, stamping
; facts, answering DATE -- under a clock its host had just contradicted.
(assert-event (equal (fn-own-observe-outcome *own-clocked* *own-obs-backwards*)
                     :refused))
(defconst *own-contradicted*
  (fn-own-step *own-clocked* (list :observe *own-obs-backwards*)))
(assert-event (null (fn-own-clock *own-contradicted*)))
(assert-event (fn-own-relation *own-contradicted*))
(assert-event (equal (fn-own-conns *own-contradicted*) (fn-own-conns *own-clocked*)))
(assert-event (equal (fn-own-ledger *own-contradicted*) (fn-own-ledger *own-clocked*)))
; Recovery is one event: with no clock, the very next reading is admitted,
; whatever it says.  The node stops being sure and then starts again.
(assert-event (equal (fn-own-observe-outcome *own-contradicted* *own-obs-backwards*)
                     :observed))
; The case the HOST used to get wrong: a reading EQUAL to the one held is
; admitted, and the owner does not move because it does not have to.
; host/owner-host.lisp inferred the word from exactly that non-movement.
(assert-event (equal (fn-own-observe-outcome *own-clocked* *own-obs*) :observed))
(assert-event (equal (fn-own-step *own-clocked* (list :observe *own-obs*))
                     *own-clocked*))
; The third word.  A host message that carries no observation changes
; nothing, including the clock.
(assert-event (equal (fn-own-observe-outcome *own-clocked* 7) :invalid))
(assert-event (equal (fn-own-step *own-clocked* '(:observe 7)) *own-clocked*))
; TEETH for fn-own-observe-refusal-names-a-contradiction, one witness per
; disjunct of its conclusion, each SEPARATING: only the named reading moved
; backwards.  *own-obs-backwards* is the monotonic disjunct (500 < 1000 with
; the same wall and the same bound, so the earliest admissible true time did
; not move).
(assert-event (and (< (fn-clock-monotonic *own-obs-backwards*)
                      (fn-clock-monotonic *own-obs*))
                   (equal (fn-clock-earliest-true *own-obs-backwards*)
                          (fn-clock-earliest-true *own-obs*))
                   (equal (fn-clock-has-wall *own-obs-backwards*)
                          (fn-clock-has-wall *own-obs*))))
; The earliest-admissible-time disjunct alone: the monotonic counter went
; FORWARD and the wall reading went back.
(defconst *own-obs-wall-back* (fn-clock-observation 9000 1599999000000 5000 t))
(assert-event (and (< (fn-clock-monotonic *own-obs*)
                      (fn-clock-monotonic *own-obs-wall-back*))
                   (< (fn-clock-earliest-true *own-obs-wall-back*)
                      (fn-clock-earliest-true *own-obs*))))
(assert-event (equal (fn-own-observe-outcome *own-clocked* *own-obs-wall-back*)
                     :refused))
; The has-wall disjunct alone: a host that stops claiming a wall reading is
; not reporting the same clock, whatever its numbers say.
(defconst *own-obs-no-wall* (fn-clock-observation 9000 1600000008000 5000 nil))
(assert-event (equal (fn-own-observe-outcome *own-clocked* *own-obs-no-wall*)
                     :refused))
; TOOTH for the theorem's one real hypothesis, (fn-own-relation o): an owner
; whose clock field is not an observation at all -- unreachable, and the
; relation is what excludes it -- is :refused with the conclusion FALSE.
; (The hypothesis that a clock is held is NOT in the theorem: with none the
; outcome is :observed, so that instance is vacuous rather than a tooth.)
(defconst *own-clock-garbage*
  (fn-own-make (fn-own-store *own-clocked*) (fn-own-view *own-clocked*)
               (fn-own-conns *own-clocked*) (fn-own-next-id *own-clocked*)
               (fn-own-max-conns *own-clocked*) (fn-own-pending *own-clocked*)
               (fn-own-ledger *own-clocked*)
               (list :fn-clock-observation 'x 1600000000000 5000 t)
               (fn-own-facts *own-clocked*) (fn-own-config *own-clocked*)
               (fn-own-queue *own-clocked*) (fn-own-inflight *own-clocked*)
               (fn-own-feeds *own-clocked*)))
(assert-event (not (fn-own-relation *own-clock-garbage*)))
(assert-event (equal (fn-own-observe-outcome *own-clock-garbage* *own-obs*) :refused))
(assert-event
 (with-guard-checking :none
  (not (or (< (fn-clock-monotonic *own-obs*)
              (fn-clock-monotonic (fn-own-clock *own-clock-garbage*)))
           (not (equal (fn-clock-has-wall *own-obs*)
                       (fn-clock-has-wall (fn-own-clock *own-clock-garbage*))))
           (< (fn-clock-earliest-true *own-obs*)
              (fn-clock-earliest-true (fn-own-clock *own-clock-garbage*)))))))
(defconst *own-declared* (fn-own-step *own-clocked* '(:declare-group "fn.new")))
(assert-event (equal (fn-own-replay-facts (fn-own-facts *own-declared*)) '("fn.new")))
(assert-event (equal (fn-own-group-fact-stamp (car (fn-own-facts *own-declared*))) *own-obs*))
(assert-event (fn-own-relation (fn-own-step *own-declared* (list :observe *own-obs-later*))))
; A contradicted reading costs the owner the clock and nothing else: the
; facts already created keep the stamps they were created under, which are
; readings and not the current one, and no NEW fact can be created until a
; reading is accepted again.
(defconst *own-declared-contradicted*
  (fn-own-step *own-declared* (list :observe *own-obs-backwards*)))
(assert-event (null (fn-own-clock *own-declared-contradicted*)))
(assert-event (equal (fn-own-replay-facts (fn-own-facts *own-declared-contradicted*))
                     '("fn.new")))
(assert-event (equal (fn-own-group-fact-stamp
                      (car (fn-own-facts *own-declared-contradicted*)))
                     *own-obs*))
(assert-event (equal (fn-own-declare-group *own-declared-contradicted* "fn.other")
                     *own-declared-contradicted*))
(assert-event (fn-own-relation *own-declared-contradicted*))

; -----------------------------------------------------------------------------
; The served POST path on the witness, from *own-closed* (two posts durable,
; the kernel :ready, connections 0 and 2 open).  The owner is configured for
; posting and observes a clock; reader R (3) opens before the post; poster P
; (4) sends POST and the article through the served port; the writer takes
; the submission; the same store events tools/run_owner.py reports run; the
; outcome is rendered by the book for P alone; R keeps its pinned view and a
; reader opened afterwards (5, once 0 has closed under the bound of four)
; sees the article.

(defconst *own-agent*
  '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))
(defconst *own-config*
  (fn-inj-make-config t *own-agent*
                      (list (fn-nntp-string-octets "fn.letters")
                            (fn-nntp-string-octets "fn.test"))
                      32768))
(defconst *own-post-obs* (fn-clock-observation 2000000 1600000010000 500 t))
(defconst *own-post-command* (append (fn-nntp-string-octets "POST") '(13 10)))
(defconst *own-article*
  (append (fn-nntp-string-octets "From: poster@example.invalid") '(13 10)
          (fn-nntp-string-octets "Subject: hello") '(13 10)
          (fn-nntp-string-octets "Newsgroups: fn.letters") '(13 10)
          '(13 10)
          (fn-nntp-string-octets "Hello, news.") '(13 10)
          '(46 13 10)))
(defconst *own-bad-article*
  (append (fn-nntp-string-octets "Subject: hello") '(13 10)
          (fn-nntp-string-octets "Newsgroups: fn.letters") '(13 10)
          '(13 10)
          (fn-nntp-string-octets "Hello.") '(13 10)
          '(46 13 10)))

; Without a configuration POST is 440 and nothing is queued.
(defconst *own-440* (fn-own-read (fn-own-step *own-closed* '(:open)) 3 *own-post-command*))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets (car *own-440*)))
                     (fn-nntp-string-octets "440 ")))
(assert-event (null (fn-own-queue (cdr *own-440*))))

(defconst *own-p0*
  (fn-own-run *own-closed* (list (list :configure *own-config*)
                                 (list :observe *own-post-obs*))))
(assert-event (fn-own-relation *own-p0*))
(defconst *own-p1* (fn-own-run *own-p0* '((:open) (:open))))
(assert-event (equal (fn-own-conn-observation (fn-own-find-conn 4 (fn-own-conns *own-p1*)))
                     *own-post-obs*))
(assert-event (equal (fn-own-conn-config (fn-own-find-conn 4 (fn-own-conns *own-p1*)))
                     *own-config*))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 3 (fn-own-conns *own-p1*))) 2))

; The offer is 340; the article is no reply and one queued submission
; against connection 4 at version 2; an outcome before the take is nothing.
(defconst *own-offer* (fn-own-read *own-p1* 4 *own-post-command*))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets (car *own-offer*)))
                     (fn-nntp-string-octets "340 ")))
(defconst *own-submitted* (fn-own-read (cdr *own-offer*) 4 *own-article*))
(assert-event (null (fn-served-reply-octets (car *own-submitted*))))
(assert-event (fn-inj-injectedp (fn-served-submission (car *own-submitted*))))
(defconst *own-q* (cdr *own-submitted*))
(assert-event (fn-own-relation *own-q*))
(assert-event (equal (len (fn-own-queue *own-q*)) 1))
(assert-event (equal (fn-own-sub-id (car (fn-own-queue *own-q*))) 4))
(assert-event (equal (fn-own-sub-version (car (fn-own-queue *own-q*))) 2))
(assert-event (null (fn-own-inflight *own-q*)))
(assert-event (null (car (fn-own-outcome *own-q* 4 :durable))))

; The writer step: in flight, owning the transaction, marked at ledger length 2.
(defconst *own-taken* (fn-own-step *own-q* '(:take)))
(assert-event (null (fn-own-queue *own-taken*)))
(assert-event (equal (fn-own-sub-id (fn-own-inflight *own-taken*)) 4))
(assert-event (equal (fn-own-sub-mark (fn-own-inflight *own-taken*)) 2))
(assert-event (equal (fn-own-pending *own-taken*) 4))
; A second submission cannot be taken while one is in flight.
(assert-event (equal (fn-own-take-submission
                      (fn-own-enqueue *own-taken* (fn-own-sub-make 3 2 nil nil)))
                     (fn-own-enqueue *own-taken* (fn-own-sub-make 3 2 nil nil))))
; A host word of :durable before any completion is consumed is not 240.
(defconst *own-early* (fn-own-outcome *own-taken* 4 :durable))
(assert-event (equal (fn-own-outcome-completion *own-taken* :durable) :uncertain))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets (car *own-early*)))
                     (fn-nntp-string-octets "441 ")))

; The store events of the durable path, then the completion; then 240.
(defconst *own-p-done*
  (fn-own-run *own-taken* (own-post-events (own-record 2 2 "<three@example>"))))
(assert-event (fn-own-relation *own-p-done*))
(assert-event (equal (len (fn-own-ledger *own-p-done*)) 3))
(assert-event (equal (fn-own-view-version (fn-own-view *own-p-done*)) 3))
(assert-event (equal (fn-own-outcome-completion *own-p-done* :durable) :durable))
(defconst *own-240* (fn-own-outcome *own-p-done* 4 :durable))
(assert-event (equal (fn-served-reply-octets (car *own-240*))
                     (append (fn-nntp-string-octets "240 article received OK") '(13 10))))
(assert-event (null (fn-own-inflight (cdr *own-240*))))
(assert-event (null (fn-own-pending (cdr *own-240*))))
(assert-event (fn-own-relation (cdr *own-240*)))
; TEETH for the 2026-09-20 repair of fn-own-conn-boundedp.  It tested
; fn-post-sessionp on a session that has been a PEER session since the
; inbound transit port, so it was false on every connection the served path
; opens; the re-pin branch of fn-own-advance was never taken and this line
; asserted that fn-own-conns was UNCHANGED by a durable outcome -- it was
; pinning the defect.  First the non-vacuity witness: the predicate holds on
; a connection fn-own-open actually built.
(assert-event (fn-own-conn-boundedp
               (fn-own-find-conn 4 (fn-own-conns *own-p-done*))
               (fn-sn-groups (fn-own-store *own-p-done*))))
; Then K1 read-back: the poster's connection moves to the committed view.
(assert-event (not (equal (fn-own-conns (cdr *own-240*))
                          (fn-own-conns *own-p-done*))))
(assert-event (equal (fn-own-conn-version
                      (fn-own-find-conn 4 (fn-own-conns (cdr *own-240*))))
                     (fn-own-view-version (fn-own-view *own-p-done*))))
(assert-event (equal (fn-own-conn-archive
                      (fn-own-find-conn 4 (fn-own-conns (cdr *own-240*))))
                     (fn-own-view-archive (fn-own-view *own-p-done*))))
; and the reply reached connection 4 alone: connection 0 is found as it was.
(assert-event (equal (fn-own-find-conn 0 (fn-own-conns (cdr *own-240*)))
                     (fn-own-find-conn 0 (fn-own-conns *own-p-done*))))
(assert-event (null (car (fn-own-outcome *own-p-done* 3 :durable))))
; The three words render three distinct lines; the two 441s differ.
(assert-event (equal (fn-served-reply-octets (car (fn-own-outcome *own-p-done* 4 :refused)))
                     (append (fn-nntp-string-octets "441 posting failed; the article was refused")
                             '(13 10))))
(assert-event (not (equal (car (fn-own-outcome *own-p-done* 4 :refused))
                          (car (fn-own-outcome *own-p-done* 4 :uncertain)))))
(assert-event (not (equal (car (fn-own-outcome *own-p-done* 4 :uncertain)) (car *own-240*))))
(assert-event (equal (car (fn-own-outcome *own-p-done* 4 :fault))
                     (car (fn-own-outcome *own-p-done* 4 :uncertain))))

; R, pinned before the post, still sees two articles; a reader opened after
; the post sees three; R's pinned prefix is unchanged.
(defconst *own-after-post* (cdr *own-240*))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 3 (fn-own-conns *own-after-post*))) 2))
(assert-event (equal (fn-served-reply-octets (car (fn-own-read *own-after-post* 3 *own-group-octets*)))
                     (append (fn-nntp-string-octets "211 2 1 2 fn.letters") '(13 10))))
(defconst *own-late* (fn-own-run *own-after-post* '((:close 0) (:open))))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 5 (fn-own-conns *own-late*))) 3))
(assert-event (equal (fn-served-reply-octets (car (fn-own-read *own-late* 5 *own-group-octets*)))
                     (append (fn-nntp-string-octets "211 3 1 3 fn.letters") '(13 10))))
(assert-event (equal (fn-own-take 2 (fn-sf-records (fn-sn-files (fn-own-store *own-late*))))
                     (fn-own-take 2 (fn-sf-records (fn-sn-files (fn-own-store *own-p1*))))))

; A refused proto-article (no From) is the served step's 441 with its reason
; and queues nothing; closing a poster with a queued submission drops it.
(defconst *own-bad*
  (fn-own-read (cdr (fn-own-read *own-late* 4 *own-post-command*)) 4 *own-bad-article*))
(assert-event (equal (fn-served-reply-octets (car *own-bad*))
                     (append (fn-nntp-string-octets "441 posting failed; From is required")
                             '(13 10))))
(assert-event (null (fn-own-queue (cdr *own-bad*))))
(defconst *own-queued-again*
  (cdr (fn-own-read (cdr (fn-own-read *own-late* 4 *own-post-command*)) 4 *own-article*)))
(assert-event (equal (len (fn-own-queue *own-queued-again*)) 1))
(assert-event (null (fn-own-queue (fn-own-step *own-queued-again* '(:close 4)))))

; -----------------------------------------------------------------------------
; D10-a on the served path: a connection posts MORE THAN ONCE, each post
; decides under the reading the owner last admitted, and a contradicted
; clock is refused as a clock fault and not as an article verdict.
;
; The subject is fn-own-read, which is what host/owner-host.lisp
; `fn-owner-chunk' calls on every socket chunk; connection 4 has already had
; one 240 above and is re-pinned to the committed view.

(defconst *own-article-2*
  (append (fn-nntp-string-octets "From: poster@example.invalid") '(13 10)
          (fn-nntp-string-octets "Subject: again") '(13 10)
          (fn-nntp-string-octets "Newsgroups: fn.letters") '(13 10)
          '(13 10)
          (fn-nntp-string-octets "Hello again, news.") '(13 10)
          '(46 13 10)))
(defconst *own-obs-2* (fn-clock-observation 2000500 1600000010500 500 t))
(defconst *own-obs-2-back* (fn-clock-observation 1999000 1600000009000 500 t))

; The host reports a later reading and the owner admits it.
(assert-event (equal (fn-own-observe-outcome *own-late* *own-obs-2*) :observed))
(defconst *own-late-2* (fn-own-step *own-late* (list :observe *own-obs-2*)))
(assert-event (fn-own-relation *own-late-2*))
; POST is offered again on the same connection, and the article is injected.
(defconst *own-second*
  (fn-own-read (cdr (fn-own-read *own-late-2* 4 *own-post-command*)) 4 *own-article-2*))
(assert-event (null (fn-served-reply-octets (car *own-second*))))
(assert-event (fn-inj-injectedp (fn-served-submission (car *own-second*))))
(assert-event (equal (len (fn-own-queue (cdr *own-second*))) 1))
(assert-event (fn-own-relation (cdr *own-second*)))
; and its identity is NOT the first post's: the second post on a connection
; is a new article, which is what the per-submission injection clock buys.
(assert-event (not (equal (fn-own-sub-msgid (car (fn-own-queue (cdr *own-second*))))
                          (fn-own-sub-msgid (car (fn-own-queue *own-q*))))))

; TOOTH for the hypothesis that the two readings differ
; (fn-post-distinct-injection-clocks-give-distinct-identities,
; books/nntp-post.lisp).  Under the reading the FIRST post used, a second
; article with a different body receives the SAME generated Message-ID.
; That collision is the duplicate the durable path refuses, and before the
; per-submission seam every post on a connection was in it.
(defconst *own-second-stale*
  (fn-own-read (cdr (fn-own-read *own-late* 4 *own-post-command*)) 4 *own-article-2*))
(assert-event (equal (fn-own-clock *own-late*) *own-post-obs*))
(assert-event (not (equal *own-article-2* *own-article*)))
(assert-event (equal (fn-own-sub-msgid (car (fn-own-queue (cdr *own-second-stale*))))
                     (fn-own-sub-msgid (car (fn-own-queue *own-q*)))))

; THE CLOCK FAULT IS NOT AN ARTICLE VERDICT.  A reading that contradicts the
; one the owner held costs it the clock; the next article on the connection
; is refused with the CLOCK line and queues nothing, and that line is not
; the line a refused article gets.  Before D10-a the owner kept the
; contradicted reading, minted the previous identity again, and the poster
; was told `441 posting failed; the article was refused'.
(assert-event (equal (fn-own-observe-outcome *own-late* *own-obs-2-back*) :refused))
(defconst *own-late-noclock* (fn-own-step *own-late* (list :observe *own-obs-2-back*)))
(assert-event (null (fn-own-clock *own-late-noclock*)))
(assert-event (fn-own-relation *own-late-noclock*))
(defconst *own-clockless*
  (fn-own-read (cdr (fn-own-read *own-late-noclock* 4 *own-post-command*)) 4
               *own-article-2*))
(assert-event
 (equal (fn-served-reply-octets (car *own-clockless*))
        (append (fn-nntp-string-octets
                 "441 posting failed; this server has no usable clock reading")
                '(13 10))))
(assert-event (null (fn-own-queue (cdr *own-clockless*))))
(assert-event
 (not (equal (fn-served-reply-octets (car *own-clockless*))
             (append (fn-nntp-string-octets "441 posting failed; the article was refused")
                     '(13 10)))))
(assert-event
 (not (equal (fn-served-reply-octets (car *own-clockless*))
             (fn-served-reply-octets (car *own-bad*)))))
; A group fact is refused for the same reason and DATE answers 503 on a
; connection opened while the clock is gone.
(assert-event (equal (fn-own-declare-group *own-late-noclock* "fn.new")
                     *own-late-noclock*))
(defconst *own-clockless-reader* (fn-own-run *own-late-noclock* '((:close 3) (:open))))
(assert-event (null (fn-own-conn-observation
                     (fn-own-find-conn 6 (fn-own-conns *own-clockless-reader*)))))
(assert-event
 (equal (fn-served-reply-octets
         (car (fn-own-read *own-clockless-reader* 6
                           (append (fn-nntp-string-octets "DATE") '(13 10)))))
        (append (fn-nntp-string-octets "503 no clock observation supplied") '(13 10))))
; Recovery is one event: the next reading is admitted and the connection
; opened after it posts again.
(assert-event (equal (fn-own-observe-outcome *own-late-noclock* *own-obs-2-back*)
                     :observed))
(defconst *own-recovered*
  (fn-own-step *own-late-noclock* (list :observe *own-obs-2-back*)))
(assert-event (equal (fn-own-clock *own-recovered*) *own-obs-2-back*))
(assert-event
 (fn-inj-injectedp
  (fn-served-submission
   (car (fn-own-read (cdr (fn-own-read *own-recovered* 4 *own-post-command*)) 4
                     *own-article-2*)))))

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
                                 *fn-own-body-limit* nil nil nil nil))))
    (fn-own-make (fn-own-store *own-after*) (fn-own-view *own-after*)
                 (list (fn-own-conn-make 0 0 0 (fn-served-conn-wire sconn)
                                         (fn-served-conn-session sconn) archive nil nil))
                 1 4 nil nil nil nil nil nil nil nil)))
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
                                      (fn-own-conn-frontier conn)))
                  (fn-own-conn-config conn) (fn-own-conn-observation conn)
                  (fn-own-clock o))
                 *own-group-octets*))))))
; K1 (served) without (fn-own-find-conn id conns): an unknown connection
; reads nothing, while a served step over the view's prefix answers.
(assert-event
 (let* ((o *own-after*)
        (s (fn-own-store o))
        (sconn (fn-served-result-conn
                (fn-served-open (fn-own-view-archive (fn-own-view o))
                                *fn-nntp-max-initial-line-octets* *fn-own-body-limit*
                                nil nil nil nil))))
   (not (equal (car (fn-own-read o 99 *own-group-octets*))
               (fn-served-result-effects
                (fn-served-step
                 (fn-served-make-conn
                  (fn-served-conn-wire sconn) (fn-served-conn-session sconn)
                  (fn-node-acceptance
                   (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                      (fn-own-take 2 (fn-sf-records (fn-sn-files s)))
                                      (fn-sf-frontier (fn-sn-files s))))
                  nil nil nil)
                 *own-group-octets*))))))

; K1 (per event) without (fn-own-relation o).
(assert-event
 (let* ((o *own-bogus*)
        (conn (fn-own-find-conn 0 (fn-own-conns o)))
        (s (fn-own-store o)))
   (not (equal (car (fn-own-read-step o 0 *own-group-command*))
               (fn-served-result-effects
                (fn-served-dispatch
                 (fn-served-make-conn
                  (fn-own-conn-wire conn) (fn-own-conn-session conn)
                  (fn-node-acceptance
                   (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                      (fn-own-take (fn-own-conn-version conn)
                                                   (fn-sf-records (fn-sn-files s)))
                                      (fn-own-conn-frontier conn)))
                  (fn-own-conn-config conn) (fn-own-conn-observation conn)
                  (fn-own-clock o))
                 *own-group-command*))))))
; K1 (per event) without (fn-own-find-conn id conns).
(assert-event
 (let* ((o *own-after*)
        (s (fn-own-store o)))
   (not (equal (car (fn-own-read-step o 99 *own-group-command*))
               (fn-served-result-effects
                (fn-served-dispatch
                 (fn-served-result-conn
                  (fn-served-open
                   (fn-node-acceptance
                    (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                       (fn-own-take 2 (fn-sf-records (fn-sn-files s)))
                                       (fn-sf-frontier (fn-sn-files s))))
                   *fn-nntp-max-initial-line-octets* *fn-own-body-limit* nil nil nil
                   nil))
                 *own-group-command*))))))
; The after-any-trace forms, on the same values with the empty trace.
(assert-event (not (fn-own-relation (fn-own-run *own-bogus* nil))))
(assert-event (null (fn-own-find-conn 99 (fn-own-conns (fn-own-run *own-after* nil)))))

; K3 without (fn-own-relation o): a bogus pin above the history is not a
; prefix that survives the trace.
(defconst *own-bogus-pin*
  (fn-own-make (fn-own-store *own-0*) (fn-own-view *own-0*)
               (list (fn-own-conn-make 0 7 0 nil nil nil nil nil))
               1 4 nil nil nil nil nil nil nil nil))
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
                        (list (fn-own-conn-make 0 "seven" 0 nil nil nil nil nil))
                        1 4 nil nil nil nil nil nil nil nil)))
    (not (<= (fn-own-reclaim-floor o)
             (fn-own-conn-version (fn-own-find-conn 0 (fn-own-conns o))))))))

; K4 without (fn-own-relation o): five hand-built connections under a bound
; of 4, both conjuncts false.
(defconst *own-over*
  (fn-own-make (fn-own-store *own-after*) (fn-own-view *own-after*)
               (list (fn-own-conn-make 0 2 2 nil nil nil nil nil)
                     (fn-own-conn-make 1 2 2 nil nil nil nil nil)
                     (fn-own-conn-make 2 2 2 nil nil nil nil nil)
                     (fn-own-conn-make 3 2 2 nil nil nil nil nil)
                     (fn-own-conn-make 4 2 2 nil nil nil nil nil))
               5 4 nil nil nil nil nil nil nil nil))
(assert-event (not (<= (len (fn-own-conns (fn-own-run *own-over* nil)))
                       (fn-own-max-conns *own-over*))))
(assert-event (not (fn-own-conns-boundedp (fn-own-conns (fn-own-run *own-over* nil))
                                          *own-groups*)))

; K5 without (fn-own-relation o): a ledger entry with no record.
(defconst *own-forged*
  (fn-own-make (fn-own-store *own-0*) (fn-own-view *own-0*) nil 0 4 nil
               (list (cons 0 0)) nil nil nil nil nil nil))
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
  (not (fn-snt-relation (fn-own-store (fn-own-run (fn-own-make nil nil nil 0 4 nil nil nil nil nil nil nil nil)
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
               (list (fn-own-group-fact-make "fn.new" nil)) nil nil nil nil))
(assert-event (not (fn-own-relation *own-unstamped*)))
(assert-event (not (fn-clock-observationp
                    (fn-own-group-fact-stamp (car (fn-own-facts *own-unstamped*))))))
(assert-event (not (fn-clock-observationp
                    (fn-own-group-fact-stamp (fn-own-group-fact-make "fn.other" nil)))))

; fn-own-durable-reply-names-a-durable-record without (fn-own-relation o): a
; forged ledger pair with no record, a submission in flight marked below it
; and the word :durable render the 240 line, yet the newest ledger pair names
; no durable record.
(defconst *own-forged-post*
  (fn-own-make (fn-own-store *own-p1*) (fn-own-view *own-p1*) (fn-own-conns *own-p1*)
               5 4 4 (list (cons 9 9)) (fn-own-clock *own-p1*) nil *own-config* nil
               (fn-own-sub-make 4 2 0 (fn-served-submission (car *own-submitted*)))
               nil))
(assert-event (not (fn-own-relation *own-forged-post*)))
(assert-event
 (let ((conn (fn-own-find-conn 4 (fn-own-conns *own-forged-post*))))
   (equal (car (fn-own-outcome *own-forged-post* 4 :durable))
          (fn-served-result-effects
           (fn-served-post-outcome
            (fn-served-make-conn (fn-own-conn-wire conn) (fn-own-conn-session conn)
                                 (fn-own-conn-archive conn) (fn-own-conn-config conn)
                                 (fn-own-conn-observation conn)
                                 (fn-own-clock *own-forged-post*))
            :durable)))))
(assert-event
 (not (fn-sf-record-has-pairp (car (last (fn-own-ledger *own-forged-post*)))
                              (fn-sf-records (fn-sn-files (fn-own-store *own-forged-post*))))))
; Without (fn-own-find-conn id conns): the owner answers an unknown
; connection NOTHING and nothing is in flight.  Until `w10/session-depth'
; this was also the witness that the theorem's equality hypothesis can hold
; with no connection, because the served outcome over the absent
; connection's fields was nothing too.  It is not any more:
; `fn-nntp-post-outcome' now answers a malformed session with the FOURTH
; outcome, 403 (`*fn-post-malformed-session-line*',
; books/nntp-post.lisp), so the two sides DIFFER.  What is asserted is
; therefore the separation: the owner's refusal is its own, taken before
; the served path is entered, and it is not the served 403.
; That settles the hypothesis: no connection-free state can satisfy the
; equality any more, so `(fn-own-find-conn id (fn-own-conns o))' has no
; violating value and is DELETED from
; `fn-own-durable-reply-names-a-durable-record' (docs/proof-style.md
; section 5).  The theorem is strictly stronger; this assertion is why.
(assert-event
 (with-guard-checking :none
  (let ((conn (fn-own-find-conn 99 (fn-own-conns *own-after-post*))))
    (and (null (car (fn-own-outcome *own-after-post* 99 :durable)))
         (not (equal (car (fn-own-outcome *own-after-post* 99 :durable))
                     (fn-served-result-effects
                      (fn-served-post-outcome
                       (fn-served-make-conn (fn-own-conn-wire conn) (fn-own-conn-session conn)
                                            (fn-own-conn-archive conn) (fn-own-conn-config conn)
                                            (fn-own-conn-observation conn)
                                            (fn-own-clock *own-after-post*))
                       :durable))))
         (null (fn-own-inflight *own-after-post*))))))
; Without the 240 hypothesis: the reply on *own-taken* is the uncertain 441
; and nothing was consumed after the mark.
(assert-event (not (< (fn-own-sub-mark (fn-own-inflight *own-taken*))
                      (len (fn-own-ledger *own-taken*)))))

; fn-own-read-touches-only-its-connection without (not (equal id other)): the
; read connection itself changes (its wire consumed the offer).
(assert-event (not (equal (fn-own-find-conn 4 (fn-own-conns (cdr *own-offer*)))
                          (fn-own-find-conn 4 (fn-own-conns *own-p1*)))))
; fn-own-outcome-touches-only-its-connection without (not (equal (sub-id
; inflight) id)): the connection in flight is answered.
(assert-event (consp (car *own-240*)))
