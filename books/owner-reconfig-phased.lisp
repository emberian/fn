; fn: a live reconfiguration as quanta, with its durable I/O off the owner
; (ruling 19, item LOCK-R2-LIVE-RECONFIGURE-IO; 2026-10-07).
;
; THE DEFECT THIS RETIRES.  fnn-owner-live-reconfigure-locked
; (host/native/admin.lisp) runs inside the caller's quantum: it stages the
; record and asks ACL2 to authorize it, observes the next name (lstat),
; publishes the record (open, write, fsync, link, directory fsync, unlink),
; completes it (fn-owner-reconfigure-complete), refreshes the store's
; configuration cache, and opens the feed journals of the peers the new
; configuration names (open, fstat, mkdir, read, ftruncate, fsync).  All of
; that runs with the owner mutex O held, and for `store limit' the extent
; mutex E as well.  A slow disk freezes every reader for that time.
;
; THE SHAPE.  Decided under O, executed off O, completed under O, as the
; batch job is (books/owner-queued-work.lisp):
;   QUANTUM 1 (under O)  :stage, :authorize (ACL2 fn-oclc-live-authorizep),
;                        and for `store limit' :reserve under E; a refusal
;                        unstages and refuses here.
;   OFF O (window A)     :observe (the next name's lstat), then :publish
;                        (the immutable publication, fn-jpub's steps).
;   QUANTUM 2 (under O)  by the outcome: a refusal unstages; an uncertain
;                        publication fences; a fault faults; a durable one
;                        runs :complete (fn-oclc-publish) and, when its
;                        verdict is :durable, :refresh.
;   OFF O (window B)     (:feed-io . PEER) for each newly configured peer, in
;                        order: open, read the journal and run the pure scan
;                        (fn-feed-journal-scan needs no owner), and repair.
;   QUANTUM 3 (under O)  (:feed-replay . PEER) for each peer (the owner's
;                        replay of the entries the scan returned), :install,
;                        :accept.  A feed that ended uncertain fences and one
;                        that faulted faults, as inline.
; Between the quanta the staged record holds the configuration lock
; (books/owner-config.lisp fn-ocfg-step refuses :begin and :take while it is
; staged), and the gate admits no quantum that stages, posts or commits
; (owed: the gate's hold, item LOCK-R2-LIVE-RECONFIGURE-IO note of
; 2026-10-07).
;
; STATEMENTS (statement first; ruling 19).  W is the six answers: STAGE (the
; stage's word), AUTH (fn-oclc-live-authorizep's), OBSERVE, PUBLISH (the
; publication's outcome), VERDICT (fn-oclc-publish's), FEEDS (one
; (PEER . WORD) per newly configured peer).
;   R0 fn-orp-step-runs-the-phased-run: the host's loop over fn-orp-step (the
;      function it calls), fed the effects' observations, runs fn-orp-run.
;   R1 fn-orp-phased-keeps-the-durable-effects: the phased run's durable
;      effects (:publish and each :feed-io), in order, are the inline run's,
;      under every W.
;   R2 fn-orp-phased-answers-as-inline: the run ends in the inline run's
;      answer (:accept, :refuse, :fence or :fault), under every W, given that
;      the convert succeeded on every run that reaches it
;      (fn-orp-reaches-convert).  That hypothesis is OWED, not discharged:
;      see the note above R2.
;   R3 fn-orp-accepted-keeps-the-owner-effects: an accepted run has the
;      inline run's owner effects in their order (same owed hypothesis).
;   R4 fn-orp-phased-holds-the-owner-only-in-quanta: every effect the run
;      labels :off is I/O and every I/O effect is :off.
;   R5 fn-orp-refusal-unstages-and-fence-keeps-the-stage: a refused run
;      that staged unstages before the refusal; a fenced or faulted run never
;      unstages (recovery decides the staged record).
;   R6 fn-orp-reservation-is-converted-or-released: RESERVE (the store-limit
;      caller) takes a growth reservation under E in quantum 1, before any
;      effect off O; acceptance converts it into the budget reduction, a later
;      refusal releases it; an accepted run never releases.  With RESERVE
;      quantum 3's :convert is a real call (CONVERT is its word) and can
;      refuse, so :convert in the effects is an ATTEMPT, not a success; a
;      run with both :convert and :release is exactly R7's refused convert,
;      and it faults.
;   R7 fn-orp-refused-convert-faults-after-release: a refused convert releases
;      the reservation, then faults; it never accepts or continues.
; :continue is the caller's own work after the answer (the redeem reply, the
; budget reduction's reply, the BP drive): the host passes it to the wrapper
; as a continuation and it runs in the quantum that decides the answer, as
; fnn-owner-held-commit runs its caller's THUNK.
;
; THE HOST'S SIDE OF THE GAPS (C7, 2026-10-08).  The hold the gate keeps
; across windows A and B admits :inspect and :reader and the caller's own
; re-entry; the committer may not START under it.  A second reconfiguration
; is refused by ACL2 itself while the record is staged
; (fn-ocfg-reconfig-refusal :busy).  Window B scans only the journals of
; peers the installed feed table does not hold, which no writer reaches
; until quantum 3 installs them, so its scan's safe offsets still hold at
; quantum 3.  The owner's side of the gap is books/owner-reconfig-lock.lisp.
(in-package "ACL2")

; -----------------------------------------------------------------------------
; Field access with guard t.
(defun fn-orp-car (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-orp-cdr (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

; -----------------------------------------------------------------------------
; The inline run as the host runs it today (fnn-owner-live-reconfigure-locked
; and fnn-owner-feed-open-missing): one peer's journal opened, read and
; repaired, then replayed, peer by peer; the journals installed together.
(defun fn-orp-inline-feeds (feeds)
  (declare (xargs :guard t))
  (if (consp feeds)
      (let ((peer (fn-orp-car (car feeds))) (word (fn-orp-cdr (car feeds))))
        (cons (cons :feed-io peer)
              (cond ((eq word :ok)
                     (cons (cons :feed-replay peer) (fn-orp-inline-feeds (cdr feeds))))
                    ((eq word :uncertain) '(:fence))
                    (t '(:fault)))))
    '(:install :continue :accept)))

(defun fn-orp-inline (stage auth observe publish verdict feeds)
  (declare (xargs :guard t))
  (cons :stage
        (cond ((not (eq stage :staged)) '(:continue :refuse))
              ((not auth) '(:authorize :unstage :continue :refuse))
              (t (list* :authorize :observe
                        (cond ((eq observe :refused) '(:unstage :continue :refuse))
                              ((not (eq observe :ok)) '(:fault))
                              (t (cons :publish
                                       (cond ((eq publish :durable)
                                              (cons :complete
                                                    (if (eq verdict :durable)
                                                        (cons :refresh (fn-orp-inline-feeds feeds))
                                                      '(:fence))))
                                             ((eq publish :refused) '(:unstage :continue :refuse))
                                             ((eq publish :uncertain) '(:fence))
                                             (t '(:fault)))))))))))

; -----------------------------------------------------------------------------
; The phased run: each effect with where it runs.
(defun fn-orp-label (where effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (cons (cons where (car effects)) (fn-orp-label where (cdr effects)))
    nil))

; Window B: the journals' I/O, in order, up to the first that did not return.
(defun fn-orp-feeds-io (feeds)
  (declare (xargs :guard t))
  (if (consp feeds)
      (cons (cons :feed-io (fn-orp-car (car feeds)))
            (if (eq (fn-orp-cdr (car feeds)) :ok) (fn-orp-feeds-io (cdr feeds)) nil))
    nil))

(defun fn-orp-feeds-final (feeds)
  (declare (xargs :guard t))
  (if (consp feeds)
      (let ((word (fn-orp-cdr (car feeds))))
        (cond ((eq word :ok) (fn-orp-feeds-final (cdr feeds)))
              ((eq word :uncertain) :uncertain)
              (t :fault)))
    :ok))

(defun fn-orp-feeds-replay (feeds)
  (declare (xargs :guard t))
  (if (consp feeds)
      (cons (cons :feed-replay (fn-orp-car (car feeds))) (fn-orp-feeds-replay (cdr feeds)))
    nil))

; Quantum 3.
(defun fn-orp-convert-tail (convert)
  (declare (xargs :guard t))
  (if (eq convert :converted) '(:continue :accept) '(:release :fault)))

(defun fn-orp-q3 (reserve feeds convert)
  (declare (xargs :guard t))
  (let ((final (fn-orp-feeds-final feeds)))
    (cond ((eq final :ok)
           (append (fn-orp-feeds-replay feeds)
                   (if reserve
                       (list* :install :convert (fn-orp-convert-tail convert))
                     '(:install :continue :accept))))
          ((eq final :uncertain) '(:fence))
          (t '(:fault)))))

; Quantum 2 after a durable publication, then window B and quantum 3.
(defun fn-orp-after-durable (reserve verdict feeds convert)
  (declare (xargs :guard t))
  (if (eq verdict :durable)
      (append (fn-orp-label :owner '(:complete :refresh))
              (fn-orp-label :off (fn-orp-feeds-io feeds))
              (fn-orp-label :owner (fn-orp-q3 reserve feeds convert)))
    (fn-orp-label :owner '(:complete :fence))))

(defun fn-orp-refused-in-q2 (reserve)
  (declare (xargs :guard t))
  (fn-orp-label :owner (if reserve '(:release :unstage :continue :refuse) '(:unstage :continue :refuse))))

(defun fn-orp-run (reserve stage auth observe publish verdict feeds convert)
  (declare (xargs :guard t))
  (cons
   '(:owner . :stage)
   (cond ((not (eq stage :staged)) '((:owner . :continue) (:owner . :refuse)))
         ((not auth) '((:owner . :authorize) (:owner . :unstage) (:owner . :continue) (:owner . :refuse)))
         (t (cons
             '(:owner . :authorize)
             (append
              (if reserve '((:owner . :reserve)) nil)
              (fn-orp-label :off (if (eq observe :ok) '(:observe :publish) '(:observe)))
              (cond ((eq observe :refused) (fn-orp-refused-in-q2 reserve))
                    ((not (eq observe :ok)) '((:owner . :fault)))
                    ((eq publish :durable) (fn-orp-after-durable reserve verdict feeds convert))
                    ((eq publish :refused) (fn-orp-refused-in-q2 reserve))
                    ((eq publish :uncertain) '((:owner . :fence)))
                    (t '((:owner . :fault))))))))))

; The runs that read CONVERT: RESERVE, a staged and authorized record, an ok
; observation, a durable publication and completion, every journal ok.  Every
; other run ends before quantum 3's :convert and never reads the word
; (fn-orp-convert-attempted-iff-reached below).
(defun fn-orp-reaches-convert (reserve stage auth observe publish verdict feeds)
  (declare (xargs :guard t))
  (and reserve (eq stage :staged) auth (eq observe :ok)
       (eq publish :durable) (eq verdict :durable)
       (eq (fn-orp-feeds-final feeds) :ok)
       t))

; -----------------------------------------------------------------------------
; The projections.
(defun fn-orp-io-p (e)
  (declare (xargs :guard t))
  (or (eq e :observe) (eq e :publish) (and (consp e) (eq (car e) :feed-io))))

(defun fn-orp-durable-p (e)
  (declare (xargs :guard t))
  (or (eq e :publish) (and (consp e) (eq (car e) :feed-io))))

(defun fn-orp-durable (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (if (fn-orp-durable-p (car effects))
          (cons (car effects) (fn-orp-durable (cdr effects)))
        (fn-orp-durable (cdr effects)))
    nil))

(defun fn-orp-reservation-p (e)
  (declare (xargs :guard t))
  (or (eq e :reserve) (eq e :convert) (eq e :release)))

(defun fn-orp-owner (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (if (or (fn-orp-io-p (car effects)) (fn-orp-reservation-p (car effects)))
          (fn-orp-owner (cdr effects))
        (cons (car effects) (fn-orp-owner (cdr effects))))
    nil))

(defun fn-orp-answer (effects)
  (declare (xargs :guard t))
  (cond ((atom effects) nil)
        ((atom (cdr effects)) (car effects))
        (t (fn-orp-answer (cdr effects)))))

(defun fn-orp-labelsp (run)
  (declare (xargs :guard t))
  (if (consp run)
      (and (consp (car run))
           (member-eq (car (car run)) '(:owner :off))
           (iff (eq (car (car run)) :off) (fn-orp-io-p (cdr (car run))))
           (fn-orp-labelsp (cdr run)))
    t))

; The effects before the first E (all of them when E is absent).
(defun fn-orp-before (e effects)
  (declare (xargs :guard t))
  (cond ((atom effects) nil)
        ((equal (car effects) e) nil)
        (t (cons (car effects) (fn-orp-before e (cdr effects))))))

; -----------------------------------------------------------------------------
; The statements.

; The projections distribute over the run's pieces; window B's I/O and
; quantum 3 against the inline peer-by-peer loop.
(local (defthm fn-orp-strip-cdrs-of-append
  (equal (strip-cdrs (append a b)) (append (strip-cdrs a) (strip-cdrs b)))))
(local (defthm fn-orp-strip-cdrs-of-label
  (implies (true-listp e) (equal (strip-cdrs (fn-orp-label w e)) e))))
(local (defthm fn-orp-durable-of-append
  (equal (fn-orp-durable (append a b)) (append (fn-orp-durable a) (fn-orp-durable b)))))
(local (defthm fn-orp-owner-of-append
  (equal (fn-orp-owner (append a b)) (append (fn-orp-owner a) (fn-orp-owner b)))))
(local (defthm fn-orp-answer-of-append
  (equal (fn-orp-answer (append a b)) (if (consp b) (fn-orp-answer b) (fn-orp-answer a)))))
(local (defthm fn-orp-labelsp-of-append
  (equal (fn-orp-labelsp (append a b)) (and (fn-orp-labelsp a) (fn-orp-labelsp b)))))
(local (defthm fn-orp-true-listp-feeds-io (true-listp (fn-orp-feeds-io feeds))))
(local (defthm fn-orp-true-listp-q3 (true-listp (fn-orp-q3 reserve feeds convert))))
(local (defthm fn-orp-durable-of-inline-feeds
  (equal (fn-orp-durable (fn-orp-inline-feeds feeds)) (fn-orp-feeds-io feeds))))
(local (defthm fn-orp-durable-of-feeds-io
  (equal (fn-orp-durable (fn-orp-feeds-io feeds)) (fn-orp-feeds-io feeds))))
(local (defthm fn-orp-durable-of-replay
  (equal (fn-orp-durable (fn-orp-feeds-replay feeds)) nil)))
(local (defthm fn-orp-durable-of-q3
  (equal (fn-orp-durable (fn-orp-q3 reserve feeds convert)) nil)))
(local (defthm fn-orp-consp-q3 (consp (fn-orp-q3 reserve feeds convert))))
(local (defthm fn-orp-answer-of-inline-feeds
  (implies (implies (and reserve (equal (fn-orp-feeds-final feeds) :ok))
                    (equal convert :converted))
           (equal (fn-orp-answer (fn-orp-inline-feeds feeds)) (fn-orp-answer (fn-orp-q3 reserve feeds convert))))))
(local (defthm fn-orp-owner-of-feeds-io
  (equal (fn-orp-owner (fn-orp-feeds-io feeds)) nil)))
(local (defthm fn-orp-owner-of-replay
  (equal (fn-orp-owner (fn-orp-feeds-replay feeds)) (fn-orp-feeds-replay feeds))))
(local (defthm fn-orp-owner-of-inline-feeds-accepted
  (implies (equal (fn-orp-feeds-final feeds) :ok)
           (equal (fn-orp-owner (fn-orp-inline-feeds feeds))
                  (append (fn-orp-feeds-replay feeds) '(:install :continue :accept))))))
(local (defthm fn-orp-owner-of-q3-converted
  (implies (and (equal (fn-orp-feeds-final feeds) :ok)
                (or (not reserve) (equal convert :converted)))
           (equal (fn-orp-owner (fn-orp-q3 reserve feeds convert))
                  (append (fn-orp-feeds-replay feeds) '(:install :continue :accept))))))
(local (defthm fn-orp-answer-of-inline-feeds-by-final
  (equal (fn-orp-answer (fn-orp-inline-feeds feeds))
         (let ((final (fn-orp-feeds-final feeds)))
           (cond ((eq final :ok) :accept) ((eq final :uncertain) :fence) (t :fault))))))
(local (defthm fn-orp-answer-of-inline-feeds-accept-iff
  (iff (equal (fn-orp-answer (fn-orp-inline-feeds feeds)) :accept)
       (equal (fn-orp-feeds-final feeds) :ok))))
(local (defthm fn-orp-labelsp-off-feeds-io
  (fn-orp-labelsp (fn-orp-label :off (fn-orp-feeds-io feeds)))))
(local (defthm fn-orp-labelsp-owner-replay
  (fn-orp-labelsp (fn-orp-label :owner (fn-orp-feeds-replay feeds)))))
(local (defthm fn-orp-feeds-io-has-no-atom
  (implies (atom k) (not (member-equal k (fn-orp-feeds-io feeds))))))
(local (defthm fn-orp-replay-has-no-atom
  (implies (atom k) (not (member-equal k (fn-orp-feeds-replay feeds))))))
(local (defthm fn-orp-label-of-append
  (equal (fn-orp-label w (append a b)) (append (fn-orp-label w a) (fn-orp-label w b)))))
(local (defthm fn-orp-labelsp-owner-q3
  (fn-orp-labelsp (fn-orp-label :owner (fn-orp-q3 reserve feeds convert)))
  :hints (("Goal" :in-theory (disable fn-orp-feeds-replay)))))
(local (defthm fn-orp-member-of-append
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b)))))

(local (defthm fn-orp-before-of-append-absent
  (implies (not (member-equal e a))
           (equal (fn-orp-before e (append a b)) (append a (fn-orp-before e b))))))

; KEYSTONE R1.
(defthm fn-orp-phased-keeps-the-durable-effects
  (equal (fn-orp-durable (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
         (fn-orp-durable (fn-orp-inline stage auth observe publish verdict feeds))))

; THE OWED HYPOTHESIS OF R2 AND R3.  On a run that reaches quantum 3's
; :convert (fn-orp-reaches-convert), the convert word is :converted.  Nothing
; in this book discharges it: CONVERT is the host's observation of the
; converter, a free input here.  The discharge it waits on is a chain, open
; at two links: (i) the host's word is :converted exactly when
; fn-prl-convert-growth answers :protected-growth-admitted (the host call,
; C's reconfig-host lane; no correspondence theorem yet); (ii) that answer is
; G2 (books/page-read-budget-growth.lisp
; fn-prl-convert-growth-when-charged-covers-the-reserve), whose
; charged-covers-the-reserve hypothesis holds across draws only by repair
; item PRL-ROW-SUM-INVARIANT (open, not a theorem).  Runs that do not reach
; the convert are unconstrained by it, and R7 states what a refused convert
; does instead.
; KEYSTONE R2.
(defthm fn-orp-phased-answers-as-inline
  (implies
   (implies (fn-orp-reaches-convert reserve stage auth observe publish verdict feeds)
            (equal convert :converted))
   (let ((answer (fn-orp-answer (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))))
    (and (equal answer
                (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds)))
         (member-equal answer '(:accept :refuse :fence :fault))))))

; KEYSTONE R3.  The same owed hypothesis as R2.
(defthm fn-orp-accepted-keeps-the-owner-effects
  (implies (and (implies (fn-orp-reaches-convert reserve stage auth observe publish verdict feeds)
                         (equal convert :converted))
                (equal (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds))
                       :accept))
           (equal (fn-orp-owner (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
                  (fn-orp-owner (fn-orp-inline stage auth observe publish verdict feeds)))))

; KEYSTONE R4.
(defthm fn-orp-phased-holds-the-owner-only-in-quanta
  (fn-orp-labelsp (fn-orp-run reserve stage auth observe publish verdict feeds convert)))

; KEYSTONE R5.
(defthm fn-orp-refusal-unstages-and-fence-keeps-the-stage
  (let ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
    (and (implies (and (equal (fn-orp-answer effects) :refuse) (equal stage :staged))
                  (member-equal :unstage (fn-orp-before :refuse effects)))
         (implies (member-equal (fn-orp-answer effects) '(:fence :fault))
                  (not (member-equal :unstage effects))))))

; KEYSTONE R6.  The store-limit caller's growth reservation (RESERVE; C7's
; option (a): the extent pool's growth preview decided under E in quantum 1
; is held as a reservation across the windows).  It is taken in quantum 1
; before any effect off O, exactly for a staged, authorized record; an
; accepted run converts it into the budget reduction; a refusal after it
; releases it before the unstage.  :convert is the convert ATTEMPT: a run
; may hold both :convert and :release, and then (R7) the convert refused,
; the release follows it and the run faults (the last conjunct); an
; accepted run holds :convert and never :release.
(defthm fn-orp-reservation-is-converted-or-released
  (let* ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
         (answer (fn-orp-answer effects)))
    (and (iff (member-equal :reserve effects)
              (and reserve (equal stage :staged) auth))
         (implies (member-equal :reserve effects)
                  (member-equal :reserve (fn-orp-before :observe effects)))
         (implies (equal answer :accept)
                  (iff (member-equal :convert effects) reserve))
         (implies (member-equal :convert effects)
                  (or (equal answer :accept)
                      (and (equal answer :fault)
                           (member-equal :release (fn-orp-before :fault effects)))))
         (implies (and (equal answer :refuse) (member-equal :reserve effects))
                  (member-equal :release (fn-orp-before :unstage effects)))
         (implies (equal answer :accept) (not (member-equal :release effects)))
         (implies (member-equal :release effects) (member-equal :reserve effects))
         (implies (and (member-equal :convert effects) (member-equal :release effects))
                  (equal answer :fault)))))

; KEYSTONE R7.  A durable path to :converting (RESERVE, a staged and
; authorized record, an ok observation, a durable publication and completion,
; every journal ok) whose convert word is not :converted: the reservation is
; released after the convert attempt, then the service faults; nothing is
; accepted and the caller's :continue never runs.
(defthm fn-orp-refused-convert-faults-after-release
  (implies (and reserve (equal stage :staged) auth (equal observe :ok)
                (equal publish :durable) (equal verdict :durable)
                (equal (fn-orp-feeds-final feeds) :ok)
                (not (equal convert :converted)))
           (let ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert))))
             (and (equal (fn-orp-answer effects) :fault)
                  (member-equal :convert (fn-orp-before :release effects))
                  (member-equal :release (fn-orp-before :fault effects))
                  (not (member-equal :accept effects))
                  (not (member-equal :continue effects))))))

; The convert word is read exactly on the runs fn-orp-reaches-convert names:
; :convert is among the effects iff the run reaches it, so R2/R3's owed
; hypothesis constrains no run that ends earlier.
(defthm fn-orp-convert-attempted-iff-reached
  (iff (member-equal :convert (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds convert)))
       (fn-orp-reaches-convert reserve stage auth observe publish verdict feeds)))

(defun fn-orp-replay-peers (peers)
  (declare (xargs :guard t))
  (if (consp peers)
      (cons (cons :feed-replay (car peers)) (fn-orp-replay-peers (cdr peers)))
    nil))

(defun fn-orp-peers (feeds)
  (declare (xargs :guard t))
  (if (consp feeds)
      (cons (fn-orp-car (car feeds)) (fn-orp-peers (cdr feeds)))
    nil))

; -----------------------------------------------------------------------------
; The step the host calls.  The host holds PHASE; it calls
; (fn-orp-step PHASE RESERVE EVENT) with what the effects it last ran
; observed, and runs the effects answered, in order, each where its label
; says, until PHASE is :done.  The events: :go to begin; the stage's word;
; :authorized or :unauthorized (fn-oclc-live-authorizep); the observation's,
; the publication's and the completion's words; in window B (:feed PEER)
; before each newly configured peer's journal, then its word; :feeds-done
; after the last.  With RESERVE :feeds-done answers the replays, :install and
; :convert and the phase is :converting, where the convert's word is the event:
; :converted continues and accepts, any other word releases and faults.
(defun fn-orp-step (phase reserve event)
  (declare (xargs :guard t))
  (cond
   ((eq phase :start)
    (if (eq event :go) (mv '((:owner . :stage)) :staging) (mv '((:owner . :fault)) :done)))
   ((eq phase :staging)
    (if (eq event :staged)
        (mv '((:owner . :authorize)) :authorizing)
      (mv '((:owner . :continue) (:owner . :refuse)) :done)))
   ((eq phase :authorizing)
    (if (eq event :authorized)
        (mv (if reserve '((:owner . :reserve) (:off . :observe)) '((:off . :observe)))
            :observing)
      (mv '((:owner . :unstage) (:owner . :continue) (:owner . :refuse)) :done)))
   ((eq phase :observing)
    (cond ((eq event :ok) (mv '((:off . :publish)) :publishing))
          ((eq event :refused) (mv (fn-orp-refused-in-q2 reserve) :done))
          (t (mv '((:owner . :fault)) :done))))
   ((eq phase :publishing)
    (cond ((eq event :durable) (mv '((:owner . :complete)) :completing))
          ((eq event :refused) (mv (fn-orp-refused-in-q2 reserve) :done))
          ((eq event :uncertain) (mv '((:owner . :fence)) :done))
          (t (mv '((:owner . :fault)) :done))))
   ((eq phase :completing)
    (if (eq event :durable)
        (mv '((:owner . :refresh)) (list :feeding))
      (mv '((:owner . :fence)) :done)))
   ;; (:feeding . DONE): the peers whose journals returned, in order.
   ((and (consp phase) (eq (car phase) :feeding))
    (cond ((and (consp event) (eq (car event) :feed))
           (mv (list (list* :off :feed-io (fn-orp-car (cdr event))))
               (list* :feed-io (fn-orp-car (cdr event)) (cdr phase))))
          ((eq event :feeds-done)
           (if reserve
               (mv (fn-orp-label :owner (append (fn-orp-replay-peers (cdr phase)) '(:install :convert)))
                   :converting)
             (mv (fn-orp-label :owner (append (fn-orp-replay-peers (cdr phase)) '(:install :continue :accept)))
                 :done)))
          (t (mv '((:owner . :fault)) :done))))
   ;; (:feed-io PEER . DONE): PEER's journal I/O ran; EVENT is its word.
   ((and (consp phase) (eq (car phase) :feed-io))
    (cond ((eq event :ok)
           (mv nil (cons :feeding (append (true-list-fix (fn-orp-cdr (cdr phase)))
                                          (list (fn-orp-car (cdr phase)))))))
          ((eq event :uncertain) (mv '((:owner . :fence)) :done))
          (t (mv '((:owner . :fault)) :done))))
   ;; :converting: the convert (fn-prl-convert-growth) ran; EVENT is its word.
   ((eq phase :converting)
    (mv (fn-orp-label :owner (fn-orp-convert-tail event)) :done))
   (t (mv '((:owner . :fault)) :done))))

(defun fn-orp-trace (phase reserve events)
  (declare (xargs :guard t :measure (acl2-count events)))
  (if (or (atom events) (eq phase :done))
      nil
    (mv-let (effects next) (fn-orp-step phase reserve (car events))
      (append effects (fn-orp-trace next reserve (cdr events))))))

; The host's observations for the six answers.
(defun fn-orp-feed-events (feeds)
  (declare (xargs :guard t))
  (if (consp feeds)
      (list* (list :feed (fn-orp-car (car feeds)))
             (fn-orp-cdr (car feeds))
             (fn-orp-feed-events (cdr feeds)))
    '(:feeds-done)))

(defun fn-orp-events-tail (reserve feeds convert)
  (declare (xargs :guard t))
  (append (fn-orp-feed-events feeds) (if reserve (list convert) nil)))

(defun fn-orp-events (reserve stage auth observe publish verdict feeds convert)
  (declare (xargs :guard t))
  (list* :go stage (if auth :authorized :unauthorized) observe publish verdict
         (fn-orp-events-tail reserve feeds convert)))

; Window B's loop, from any peers already done.
(local (defthm fn-orp-replay-peers-of-append
  (equal (fn-orp-replay-peers (append a b))
         (append (fn-orp-replay-peers a) (fn-orp-replay-peers b)))))
(local (defthm fn-orp-feeds-replay-is-replay-peers
  (equal (fn-orp-feeds-replay feeds) (fn-orp-replay-peers (fn-orp-peers feeds)))))
(local (defthm fn-orp-append-assoc
  (equal (append (append a b) c) (append a (append b c)))))
(local (defthm fn-orp-true-list-fix-of-true-list (implies (true-listp x) (equal (true-list-fix x) x))))
(local (defun fn-orp-feed-ind (done feeds)
  (if (consp feeds)
      (fn-orp-feed-ind (append done (list (fn-orp-car (car feeds)))) (cdr feeds))
    done)))
(local (defthm fn-orp-trace-of-feeding
  (implies (true-listp done) (equal (fn-orp-trace (cons :feeding done) reserve (fn-orp-events-tail reserve feeds convert))
         (append (fn-orp-label :off (fn-orp-feeds-io feeds))
                 (fn-orp-label :owner
                               (let ((final (fn-orp-feeds-final feeds)))
                                 (cond ((eq final :ok)
                                        (append (fn-orp-replay-peers (append done (fn-orp-peers feeds)))
                                                (if reserve
                                                    (list* :install :convert (fn-orp-convert-tail convert))
                                                  '(:install :continue :accept))))
                                       ((eq final :uncertain) '(:fence))
                                       (t '(:fault))))))))
  :hints (("Goal" :induct (fn-orp-feed-ind done feeds)))))

; KEYSTONE R0.  The host's loop over fn-orp-step, fed what the effects
; observed, runs exactly the phased run.  The subject is fn-orp-step, the
; function the host's wrapper calls (host side: lane commit-held-host's
; successor, C).
(defthm fn-orp-step-runs-the-phased-run
  (equal (fn-orp-trace :start reserve (fn-orp-events reserve stage auth observe publish verdict feeds convert))
         (fn-orp-run reserve stage auth observe publish verdict feeds convert))
  :hints (("Goal" :in-theory (disable fn-orp-events-tail))))

(local (defthm fn-orp-labelsp-owner-replay-peers
  (fn-orp-labelsp (fn-orp-label :owner (fn-orp-replay-peers peers)))))

; KEYSTONE R4 per call.  Every effect fn-orp-step answers is labelled, and it
; is labelled :off exactly when it is I/O: the host, which runs each effect
; where its label says, holds the owner for no I/O in any single step.  The
; subject is fn-orp-step, the function host/native/admin.lisp's phased
; wrapper (lane reconfig-host) calls.
(defthm fn-orp-step-holds-the-owner-only-in-quanta
  (fn-orp-labelsp (mv-nth 0 (fn-orp-step phase reserve event)))
  :hints (("Goal" :in-theory (enable fn-orp-step))))
