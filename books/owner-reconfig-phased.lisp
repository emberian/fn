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
;   R1 fn-orp-phased-keeps-the-durable-effects: the phased run's durable
;      effects (:publish and each :feed-io), in order, are the inline run's,
;      under every W.
;   R2 fn-orp-phased-answers-as-inline: the run ends in the inline run's
;      answer (:accept, :refuse, :fence or :fault), under every W.
;   R3 fn-orp-accepted-keeps-the-owner-effects: an accepted run has the
;      inline run's owner effects in their order.
;   R4 fn-orp-phased-holds-the-owner-only-in-quanta: every effect the run
;      labels :off is I/O and every I/O effect is :off.
;   R5 fn-orp-refusal-unstages-and-fence-keeps-the-stage: a refused run
;      that staged unstages before the refusal; a fenced or faulted run never
;      unstages (recovery decides the staged record).
;   R6 fn-orp-reservation-is-converted-or-released: RESERVE (the store-limit
;      caller) takes a growth reservation under E in quantum 1, before any
;      effect off O; acceptance converts it into the budget reduction, a later
;      refusal releases it, never both.
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
(defun fn-orp-q3 (reserve feeds)
  (declare (xargs :guard t))
  (let ((final (fn-orp-feeds-final feeds)))
    (cond ((eq final :ok)
           (append (fn-orp-feeds-replay feeds)
                   (if reserve '(:install :convert :continue :accept) '(:install :continue :accept))))
          ((eq final :uncertain) '(:fence))
          (t '(:fault)))))

; Quantum 2 after a durable publication, then window B and quantum 3.
(defun fn-orp-after-durable (reserve verdict feeds)
  (declare (xargs :guard t))
  (if (eq verdict :durable)
      (append (fn-orp-label :owner '(:complete :refresh))
              (fn-orp-label :off (fn-orp-feeds-io feeds))
              (fn-orp-label :owner (fn-orp-q3 reserve feeds)))
    (fn-orp-label :owner '(:complete :fence))))

(defun fn-orp-refused-in-q2 (reserve)
  (declare (xargs :guard t))
  (fn-orp-label :owner (if reserve '(:release :unstage :continue :refuse) '(:unstage :continue :refuse))))

(defun fn-orp-run (reserve stage auth observe publish verdict feeds)
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
                    ((eq publish :durable) (fn-orp-after-durable reserve verdict feeds))
                    ((eq publish :refused) (fn-orp-refused-in-q2 reserve))
                    ((eq publish :uncertain) '((:owner . :fence)))
                    (t '((:owner . :fault))))))))))

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
(local (defthm fn-orp-true-listp-q3 (true-listp (fn-orp-q3 reserve feeds))))
(local (defthm fn-orp-durable-of-inline-feeds
  (equal (fn-orp-durable (fn-orp-inline-feeds feeds)) (fn-orp-feeds-io feeds))))
(local (defthm fn-orp-durable-of-feeds-io
  (equal (fn-orp-durable (fn-orp-feeds-io feeds)) (fn-orp-feeds-io feeds))))
(local (defthm fn-orp-durable-of-replay
  (equal (fn-orp-durable (fn-orp-feeds-replay feeds)) nil)))
(local (defthm fn-orp-durable-of-q3
  (equal (fn-orp-durable (fn-orp-q3 reserve feeds)) nil)))
(local (defthm fn-orp-consp-q3 (consp (fn-orp-q3 reserve feeds))))
(local (defthm fn-orp-answer-of-inline-feeds
  (equal (fn-orp-answer (fn-orp-inline-feeds feeds)) (fn-orp-answer (fn-orp-q3 reserve feeds)))))
(local (defthm fn-orp-owner-of-feeds-io
  (equal (fn-orp-owner (fn-orp-feeds-io feeds)) nil)))
(local (defthm fn-orp-owner-of-replay
  (equal (fn-orp-owner (fn-orp-feeds-replay feeds)) (fn-orp-feeds-replay feeds))))
(local (defthm fn-orp-owner-of-inline-feeds-accepted
  (implies (equal (fn-orp-feeds-final feeds) :ok)
           (equal (fn-orp-owner (fn-orp-inline-feeds feeds)) (fn-orp-owner (fn-orp-q3 reserve feeds))))))
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
  (fn-orp-labelsp (fn-orp-label :owner (fn-orp-q3 reserve feeds)))
  :hints (("Goal" :in-theory (disable fn-orp-feeds-replay)))))
(local (defthm fn-orp-member-of-append
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b)))))

; KEYSTONE R1.
(defthm fn-orp-phased-keeps-the-durable-effects
  (equal (fn-orp-durable (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))
         (fn-orp-durable (fn-orp-inline stage auth observe publish verdict feeds))))

; KEYSTONE R2.
(defthm fn-orp-phased-answers-as-inline
  (let ((answer (fn-orp-answer (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))))
    (and (equal answer
                (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds)))
         (member-equal answer '(:accept :refuse :fence :fault)))))

; KEYSTONE R3.
(defthm fn-orp-accepted-keeps-the-owner-effects
  (implies (equal (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds))
                  :accept)
           (equal (fn-orp-owner (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))
                  (fn-orp-owner (fn-orp-inline stage auth observe publish verdict feeds)))))

; KEYSTONE R4.
(defthm fn-orp-phased-holds-the-owner-only-in-quanta
  (fn-orp-labelsp (fn-orp-run reserve stage auth observe publish verdict feeds)))

; KEYSTONE R5.
(defthm fn-orp-refusal-unstages-and-fence-keeps-the-stage
  (let ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds))))
    (and (implies (and (equal (fn-orp-answer effects) :refuse) (equal stage :staged))
                  (member-equal :unstage (fn-orp-before :refuse effects)))
         (implies (member-equal (fn-orp-answer effects) '(:fence :fault))
                  (not (member-equal :unstage effects))))))

; KEYSTONE R6.  The store-limit caller's growth reservation (RESERVE; C7's
; option (a): the extent pool's growth preview decided under E in quantum 1
; is held as a reservation across the windows).  It is taken in quantum 1
; before any effect off O, exactly for a staged, authorized record; an
; accepted run converts it into the budget reduction; a refusal after it
; releases it before the unstage; never both.
(defthm fn-orp-reservation-is-converted-or-released
  (let* ((effects (strip-cdrs (fn-orp-run reserve stage auth observe publish verdict feeds)))
         (answer (fn-orp-answer effects)))
    (and (iff (member-equal :reserve effects)
              (and reserve (equal stage :staged) auth))
         (implies (member-equal :reserve effects)
                  (member-equal :reserve (fn-orp-before :observe effects)))
         (implies (equal answer :accept)
                  (iff (member-equal :convert effects) reserve))
         (implies (member-equal :convert effects) (equal answer :accept))
         (implies (and (equal answer :refuse) (member-equal :reserve effects))
                  (member-equal :release (fn-orp-before :unstage effects)))
         (not (and (member-equal :convert effects) (member-equal :release effects))))))
