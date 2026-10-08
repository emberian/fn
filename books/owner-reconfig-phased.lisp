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
;   QUANTUM 1 (under O)  :stage, :authorize (ACL2 fn-oclc-live-authorizep);
;                        a refusal unstages and refuses here.
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
    '(:install :accept)))

(defun fn-orp-inline (stage auth observe publish verdict feeds)
  (declare (xargs :guard t))
  (cons :stage
        (cond ((not (eq stage :staged)) '(:refuse))
              ((not auth) '(:authorize :unstage :refuse))
              (t (list* :authorize :observe
                        (cond ((eq observe :refused) '(:unstage :refuse))
                              ((not (eq observe :ok)) '(:fault))
                              (t (cons :publish
                                       (cond ((eq publish :durable)
                                              (cons :complete
                                                    (if (eq verdict :durable)
                                                        (cons :refresh (fn-orp-inline-feeds feeds))
                                                      '(:fence))))
                                             ((eq publish :refused) '(:unstage :refuse))
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
(defun fn-orp-q3 (feeds)
  (declare (xargs :guard t))
  (let ((final (fn-orp-feeds-final feeds)))
    (cond ((eq final :ok) (append (fn-orp-feeds-replay feeds) '(:install :accept)))
          ((eq final :uncertain) '(:fence))
          (t '(:fault)))))

; Quantum 2 after a durable publication, then window B and quantum 3.
(defun fn-orp-after-durable (verdict feeds)
  (declare (xargs :guard t))
  (if (eq verdict :durable)
      (append (fn-orp-label :owner '(:complete :refresh))
              (fn-orp-label :off (fn-orp-feeds-io feeds))
              (fn-orp-label :owner (fn-orp-q3 feeds)))
    (fn-orp-label :owner '(:complete :fence))))

(defun fn-orp-run (stage auth observe publish verdict feeds)
  (declare (xargs :guard t))
  (cons
   '(:owner . :stage)
   (cond ((not (eq stage :staged)) '((:owner . :refuse)))
         ((not auth) '((:owner . :authorize) (:owner . :unstage) (:owner . :refuse)))
         (t (cons
             '(:owner . :authorize)
             (append
              (fn-orp-label :off (if (eq observe :ok) '(:observe :publish) '(:observe)))
              (cond ((eq observe :refused) '((:owner . :unstage) (:owner . :refuse)))
                    ((not (eq observe :ok)) '((:owner . :fault)))
                    ((eq publish :durable) (fn-orp-after-durable verdict feeds))
                    ((eq publish :refused) '((:owner . :unstage) (:owner . :refuse)))
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

(defun fn-orp-owner (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (if (fn-orp-io-p (car effects))
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
(local (defthm fn-orp-true-listp-q3 (true-listp (fn-orp-q3 feeds))))
(local (defthm fn-orp-durable-of-inline-feeds
  (equal (fn-orp-durable (fn-orp-inline-feeds feeds)) (fn-orp-feeds-io feeds))))
(local (defthm fn-orp-durable-of-feeds-io
  (equal (fn-orp-durable (fn-orp-feeds-io feeds)) (fn-orp-feeds-io feeds))))
(local (defthm fn-orp-durable-of-replay
  (equal (fn-orp-durable (fn-orp-feeds-replay feeds)) nil)))
(local (defthm fn-orp-durable-of-q3
  (equal (fn-orp-durable (fn-orp-q3 feeds)) nil)))
(local (defthm fn-orp-consp-q3 (consp (fn-orp-q3 feeds))))
(local (defthm fn-orp-answer-of-inline-feeds
  (equal (fn-orp-answer (fn-orp-inline-feeds feeds)) (fn-orp-answer (fn-orp-q3 feeds)))))
(local (defthm fn-orp-owner-of-feeds-io
  (equal (fn-orp-owner (fn-orp-feeds-io feeds)) nil)))
(local (defthm fn-orp-owner-of-replay
  (equal (fn-orp-owner (fn-orp-feeds-replay feeds)) (fn-orp-feeds-replay feeds))))
(local (defthm fn-orp-owner-of-inline-feeds-accepted
  (implies (equal (fn-orp-feeds-final feeds) :ok)
           (equal (fn-orp-owner (fn-orp-inline-feeds feeds)) (fn-orp-owner (fn-orp-q3 feeds))))))
(local (defthm fn-orp-answer-of-inline-feeds-accept-iff
  (iff (equal (fn-orp-answer (fn-orp-inline-feeds feeds)) :accept)
       (equal (fn-orp-feeds-final feeds) :ok))))
(local (defthm fn-orp-labelsp-off-feeds-io
  (fn-orp-labelsp (fn-orp-label :off (fn-orp-feeds-io feeds)))))
(local (defthm fn-orp-labelsp-owner-replay
  (fn-orp-labelsp (fn-orp-label :owner (fn-orp-feeds-replay feeds)))))
(local (defthm fn-orp-feeds-io-has-no-unstage
  (not (member-equal :unstage (fn-orp-feeds-io feeds)))))
(local (defthm fn-orp-replay-has-no-unstage
  (not (member-equal :unstage (fn-orp-feeds-replay feeds)))))
(local (defthm fn-orp-member-of-append
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b)))))

; KEYSTONE R1.
(defthm fn-orp-phased-keeps-the-durable-effects
  (equal (fn-orp-durable (strip-cdrs (fn-orp-run stage auth observe publish verdict feeds)))
         (fn-orp-durable (fn-orp-inline stage auth observe publish verdict feeds))))

; KEYSTONE R2.
(defthm fn-orp-phased-answers-as-inline
  (let ((answer (fn-orp-answer (strip-cdrs (fn-orp-run stage auth observe publish verdict feeds)))))
    (and (equal answer
                (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds)))
         (member-equal answer '(:accept :refuse :fence :fault)))))

; KEYSTONE R3.
(defthm fn-orp-accepted-keeps-the-owner-effects
  (implies (equal (fn-orp-answer (fn-orp-inline stage auth observe publish verdict feeds))
                  :accept)
           (equal (fn-orp-owner (strip-cdrs (fn-orp-run stage auth observe publish verdict feeds)))
                  (fn-orp-owner (fn-orp-inline stage auth observe publish verdict feeds)))))

; KEYSTONE R4.
(defthm fn-orp-phased-holds-the-owner-only-in-quanta
  (fn-orp-labelsp (fn-orp-run stage auth observe publish verdict feeds)))

; KEYSTONE R5.
(defthm fn-orp-refusal-unstages-and-fence-keeps-the-stage
  (let ((effects (strip-cdrs (fn-orp-run stage auth observe publish verdict feeds))))
    (and (implies (and (equal (fn-orp-answer effects) :refuse) (equal stage :staged))
                  (member-equal :unstage (fn-orp-before :refuse effects)))
         (implies (member-equal (fn-orp-answer effects) '(:fence :fault))
                  (not (member-equal :unstage effects))))))
