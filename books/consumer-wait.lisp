; fn: a consumer WAIT, a poll that sleeps until there is news (PRF-252,
; CNS-007; specs/consumer-progress.md "Waiting").
;
; An agent's consumer should sleep until an event it can read is committed,
; not poll on a timer.  `consumer wait' / `bound-wait' (FNCL request codes 9
; and 10, books/consumer-local-control.lisp) carry a timeout of 0 to 3 600
; seconds.  The owner answers them with exactly what a poll of the same
; consumer answers at the moment the wait returns:
;
;   * the host polls (the same ACL2 poll a `poll' / `bound-poll' request
;     runs, `fn-cwait-poll') under the owner mutex and hands the answer and
;     the elapsed milliseconds to `fn-cwait-step';
;   * `fn-cwait-step' answers the poll's answer, unless it is an accepted
;     EMPTY page and the deadline has not passed, in which case it answers
;     (:sleep MS), the milliseconds left;
;   * the host then sleeps on the owner's commit signal (raised after each
;     durable Store publication, host/native/owner.lisp
;     `fnn-owner-publish-prepared') for at most MS, never in a busy loop, and
;     polls again.
;
; So a wait answers a refusal at once (a refused poll is not an empty page:
; a bound consumer outside its account's rule is refused, not left asleep),
; an event as soon as one is committed and readable, and the empty page only
; at its deadline (`fn-cwait-step-is-the-poll-or-a-sleep-on-an-empty-page').
; A wait writes nothing: every answer is a poll's, so PRF-116 and PRF-234
; hold of it unchanged (at-least-once; one transition per repeated delivery
; is the ack's, and the wait never acks).
;
; Waiters hold a local-control worker each, so they are admitted up to
; `fn-cwait-capacity', four fewer than the control worker ceiling
; (`fn-native-control-max-active-clients'), and refused by name
; (:refused :waiters) past it (`fn-cwait-admit-leaves-workers-free').  The
; heap reservation already counts every control worker's thread
; (books/heap-reservation.lisp), so a waiter costs no memory it does not
; already reserve.
;
; Host callers: host/owner-host.lisp `fn-owner-consumer-local-wait-step'
; and `fn-owner-consumer-local-wait-admit', reached from
; host/native/owner.lisp `fnn-owner-consumer-local-wait'.
(in-package "ACL2")
(include-book "consumer-bound")
(include-book "consumer-wait-codec")

(defconst *fn-cwait-reserved-workers* 4)

(defun fn-cwait-capacity ()
  (declare (xargs :guard t))
  (- (fn-native-control-max-active-clients) *fn-cwait-reserved-workers*))

(defthm fn-cwait-capacity-is-positive
  (posp (fn-cwait-capacity))
  :rule-classes :type-prescription)

; WAITERS is the count of waits already asleep or polling.
(defun fn-cwait-admit (waiters)
  (declare (xargs :guard t))
  (if (and (natp waiters) (< waiters (fn-cwait-capacity)))
      :admit
    (list :refused :waiters)))

; The poll a wait runs: a bound wait (SECRET, the account's password) is a
; bound poll, a plain wait (no SECRET) a plain poll.
(defun fn-cwait-poll (oc acfg consumer secret fn-hist)
  (declare (xargs :stobjs fn-hist :guard t :verify-guards nil))
  (if secret
      (fn-cbind-poll oc acfg consumer secret fn-hist)
    (fn-cbind-plain-poll oc consumer fn-hist)))

; An accepted page that carries no event: the poll's answer when nothing
; the consumer can read lies past its position.
(defun fn-cwait-empty-pagep (answer)
  (declare (xargs :guard t))
  (and (true-listp answer)
       (equal (len answer) 3)
       (eq (car answer) :poll)
       (null (caddr answer))))

(defun fn-cwait-deadline-ms (seconds)
  (declare (xargs :guard t))
  (* 1000 (nfix seconds)))

; One step of a wait: ELAPSED milliseconds since it was admitted, SECONDS
; its timeout.
(defun fn-cwait-decide (answer elapsed seconds)
  (declare (xargs :guard t))
  (if (and (fn-cwait-empty-pagep answer)
           (natp elapsed)
           (< elapsed (fn-cwait-deadline-ms seconds)))
      (list :sleep (- (fn-cwait-deadline-ms seconds) elapsed))
    (list :answer answer)))

(defun fn-cwait-step (oc acfg consumer secret elapsed seconds fn-hist)
  (declare (xargs :stobjs fn-hist :guard t :verify-guards nil))
  (fn-cwait-decide (fn-cwait-poll oc acfg consumer secret fn-hist) elapsed seconds))

(local
 (defthm fn-cwait-empty-pagep-is-a-list
   (implies (not (consp x)) (not (fn-cwait-empty-pagep x)))))

; KEYSTONE 1 (a wait answers the poll at its return point).  A step either
; answers exactly the consumer's poll at that moment, or sleeps; it sleeps
; only on an accepted empty page before the deadline, for a positive time
; that does not pass the deadline.  An answer that is an empty page is given
; only at or after the deadline (the timeout answers the empty page), and at
; or after the deadline every step answers.
(defthm fn-cwait-step-is-the-poll-or-a-sleep-on-an-empty-page
  (let ((r (fn-cwait-step oc acfg consumer secret elapsed seconds fn-hist))
        (p (fn-cwait-poll oc acfg consumer secret fn-hist)))
    (and (or (equal r (list :answer p))
             (and (equal (car r) :sleep)
                  (fn-cwait-empty-pagep p)
                  (natp elapsed)
                  (< elapsed (fn-cwait-deadline-ms seconds))
                  (posp (cadr r))
                  (equal (+ elapsed (cadr r))
                         (fn-cwait-deadline-ms seconds))))
         (implies (and (natp elapsed)
                       (fn-cwait-empty-pagep (cadr r)))
                  (<= (fn-cwait-deadline-ms seconds) elapsed))
         (implies (<= (fn-cwait-deadline-ms seconds) elapsed)
                  (equal r (list :answer p)))
         (implies (not (fn-cwait-empty-pagep p))
                  (equal r (list :answer p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cwait-step fn-cwait-decide
                                   fn-cwait-empty-pagep-is-a-list)
                                  (fn-cwait-poll fn-cwait-empty-pagep)))))

; The wait loop the host runs, as a model: OBSERVATIONS are the owner states
; and elapsed times at which the host polls, in order (the first at
; admission, each later one after a commit signal or the sleep's end).  It
; answers the first step that answers, or nil when the observations run
; out before one does.
(defun fn-cwait-run (observations acfg consumer secret seconds fn-hist)
  (declare (xargs :stobjs fn-hist :guard t :verify-guards nil))
  (if (consp observations)
      (let* ((o (car observations))
             (r (fn-cwait-step (car o) acfg consumer secret (cdr o) seconds fn-hist)))
        (if (equal (car r) :answer)
            (list :answer (cadr r) (car o) (cdr o))
          (fn-cwait-run (cdr observations) acfg consumer secret seconds fn-hist)))
    nil))

; KEYSTONE 2 (the loop).  When the wait answers, it answers the poll of the
; owner state at its return point; every earlier observation was an empty
; page before the deadline (the wait slept over no event and no refusal:
; `fn-cwait-run-sleeps-only-over-empty-pages'); and an empty answer is
; given only at or after the deadline.
(defthm fn-cwait-run-answers-the-poll-at-its-return-point
  (let ((r (fn-cwait-run observations acfg consumer secret seconds fn-hist)))
    (implies r
             (and (equal (car r) :answer)
                  (equal (cadr r)
                         (fn-cwait-poll (caddr r) acfg consumer secret fn-hist))
                  (implies (and (natp (cadddr r))
                                (fn-cwait-empty-pagep (cadr r)))
                           (<= (fn-cwait-deadline-ms seconds) (cadddr r))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cwait-run observations acfg consumer secret seconds fn-hist)
           :in-theory (e/d (fn-cwait-run fn-cwait-step fn-cwait-decide)
                           (fn-cwait-poll fn-cwait-empty-pagep)))))

(defthm fn-cwait-run-sleeps-only-over-empty-pages
  (implies (not (equal (car (fn-cwait-step (car (car observations)) acfg
                                           consumer secret
                                           (cdr (car observations))
                                           seconds fn-hist))
                       :answer))
           (and (fn-cwait-empty-pagep
                 (fn-cwait-poll (car (car observations)) acfg consumer secret fn-hist))
                (natp (cdr (car observations)))
                (< (cdr (car observations)) (fn-cwait-deadline-ms seconds))
                (equal (fn-cwait-run observations acfg consumer secret seconds fn-hist)
                       (fn-cwait-run (cdr observations) acfg consumer secret
                                     seconds fn-hist))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cwait-run fn-cwait-step fn-cwait-decide)
                                  (fn-cwait-poll fn-cwait-empty-pagep)))))

; KEYSTONE 3 (bounded waiters).  An admitted wait leaves at least
; *fn-cwait-reserved-workers* control workers for every other request; past
; the capacity a wait is refused by name.
(defthm fn-cwait-admit-leaves-workers-free
  (and (implies (equal (fn-cwait-admit waiters) :admit)
                (and (natp waiters)
                     (<= (+ 1 waiters) (fn-cwait-capacity))
                     (<= (+ 1 waiters *fn-cwait-reserved-workers*)
                         (fn-native-control-max-active-clients))))
       (implies (<= (fn-cwait-capacity) waiters)
                (equal (fn-cwait-admit waiters) '(:refused :waiters))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cwait-admit fn-cwait-capacity))))

(verify-guards fn-cwait-poll)
(verify-guards fn-cwait-step)

; -----------------------------------------------------------------------------
; The step over the payload arena (records flip)
;
; The Store retains held rows, and a held article row's report is its wire
; form read through the arena (books/consumer-bound.lisp fn-cbind-poll-over,
; fn-cbind-plain-poll-over); the arena-free poll refuses it (:refused
; :report).  The host's step switches to fn-cwait-step-over with the live
; arena (flip-bridge REQUEST to the host lane).  KEYSTONE 2 is restated over
; the arena below (fn-cwait-run-over): each observation carries the payloads
; the owner sealed since the one before it, so the arena each poll reads is
; the arena at that observation.

(defun fn-cwait-poll-over (oc acfg consumer secret fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :verify-guards nil))
  (if secret
      (fn-cbind-poll-over oc acfg consumer secret fn-arena fn-hist)
    (fn-cbind-plain-poll-over oc consumer fn-arena fn-hist)))

(defun fn-cwait-step-over (oc acfg consumer secret elapsed seconds fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :verify-guards nil))
  (fn-cwait-decide (fn-cwait-poll-over oc acfg consumer secret fn-arena fn-hist)
                   elapsed seconds))

(verify-guards fn-cwait-poll-over)
(verify-guards fn-cwait-step-over)

; The bridge: on a selection that is no held row the step over the arena is
; the step above.
(defthm fn-cwait-step-over-is-step-unless-a-held-row
  (implies (not (fn-held-p (caddr (fn-col-poll (fn-ocfg-owner oc) consumer fn-hist))))
           (equal (fn-cwait-step-over oc acfg consumer secret elapsed seconds fn-arena fn-hist)
                  (fn-cwait-step oc acfg consumer secret elapsed seconds fn-hist)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cbind-poll-over-is-poll-unless-a-held-row))
           :in-theory (e/d (fn-cwait-step-over fn-cwait-step
                            fn-cwait-poll-over fn-cwait-poll)
                           (fn-cbind-poll-over fn-cbind-poll fn-cbind-plain-poll-over
                            fn-cbind-plain-poll fn-cwait-decide fn-col-poll)))))

; KEYSTONE 1 over the arena: the host's step answers exactly the consumer's
; poll over the arena at that moment, or sleeps only on an accepted empty
; page before the deadline, for a positive time that does not pass it.
(defthm fn-cwait-step-over-is-the-poll-or-a-sleep-on-an-empty-page
  (let ((r (fn-cwait-step-over oc acfg consumer secret elapsed seconds fn-arena fn-hist))
        (p (fn-cwait-poll-over oc acfg consumer secret fn-arena fn-hist)))
    (and (or (equal r (list :answer p))
             (and (equal (car r) :sleep)
                  (fn-cwait-empty-pagep p)
                  (natp elapsed)
                  (< elapsed (fn-cwait-deadline-ms seconds))
                  (posp (cadr r))
                  (equal (+ elapsed (cadr r))
                         (fn-cwait-deadline-ms seconds))))
         (implies (and (natp elapsed)
                       (fn-cwait-empty-pagep (cadr r)))
                  (<= (fn-cwait-deadline-ms seconds) elapsed))
         (implies (<= (fn-cwait-deadline-ms seconds) elapsed)
                  (equal r (list :answer p)))
         (implies (not (fn-cwait-empty-pagep p))
                  (equal r (list :answer p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cwait-step-over fn-cwait-decide
                                   fn-cwait-empty-pagep-is-a-list)
                                  (fn-cwait-poll-over fn-cwait-empty-pagep)))))

; The wait loop over the arena, as a model.  An observation is
; (OWNER-CONFIG ELAPSED . SEALS): the owner configuration and elapsed
; milliseconds at which the host polls, and the payloads the owner sealed
; into the arena since the previous observation (a durable publication seals
; its article's octets, then raises the commit signal the waiter sleeps on).
; The run seals them, steps over the arena, and answers the first step that
; answers, with the arena as it stood then; nil when the observations run
; out before one does.
(defun fn-cwait-seal-all (seals fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp seals)
      (let ((fn-arena (fn-arena-seal-list (car seals) fn-arena)))
        (fn-cwait-seal-all (cdr seals) fn-arena))
    fn-arena))

(defun fn-cwait-run-over (observations acfg consumer secret seconds fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :verify-guards nil))
  (if (consp observations)
      (let* ((o (car observations))
             (fn-arena (fn-cwait-seal-all (cddr o) fn-arena)))
        (let ((r (fn-cwait-step-over (car o) acfg consumer secret (cadr o) seconds
                                     fn-arena fn-hist)))
          (if (equal (car r) :answer)
              (mv (list :answer (cadr r) (car o) (cadr o)) fn-arena)
            (fn-cwait-run-over (cdr observations) acfg consumer secret seconds
                               fn-arena fn-hist))))
    (mv nil fn-arena)))

; KEYSTONE 2 over the arena (the loop the host runs over fn-cwait-step-over).
; When the wait answers, it answers the poll over the arena of the owner
; configuration at its return point, read through the arena as it stood
; there (the run's returned arena); and an empty answer is given only at or
; after the deadline.
(defthm fn-cwait-run-over-answers-the-poll-at-its-return-point
  (let* ((run (fn-cwait-run-over observations acfg consumer secret seconds fn-arena fn-hist))
         (r (mv-nth 0 run)))
    (implies r
             (and (equal (car r) :answer)
                  (equal (cadr r)
                         (fn-cwait-poll-over (caddr r) acfg consumer secret
                                             (mv-nth 1 run) fn-hist))
                  (implies (and (natp (cadddr r))
                                (fn-cwait-empty-pagep (cadr r)))
                           (<= (fn-cwait-deadline-ms seconds) (cadddr r))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cwait-run-over observations acfg consumer secret seconds
                                             fn-arena fn-hist)
           :in-theory (e/d (fn-cwait-run-over fn-cwait-step-over fn-cwait-decide)
                           (fn-cwait-poll-over fn-cwait-empty-pagep
                            fn-cwait-seal-all)))))

; Every observation the wait slept over was an empty page before the
; deadline: a step that does not answer is one, and the run continues from
; the next observation over the arena with this one's seals.
(defthm fn-cwait-run-over-sleeps-only-over-empty-pages
  (let* ((o (car observations))
         (a (fn-cwait-seal-all (cddr o) fn-arena)))
    (implies (and (consp observations)
                  (not (equal (car (fn-cwait-step-over (car o) acfg consumer secret
                                                       (cadr o) seconds a fn-hist))
                              :answer)))
             (and (fn-cwait-empty-pagep
                   (fn-cwait-poll-over (car o) acfg consumer secret a fn-hist))
                  (natp (cadr o))
                  (< (cadr o) (fn-cwait-deadline-ms seconds))
                  (equal (fn-cwait-run-over observations acfg consumer secret seconds
                                            fn-arena fn-hist)
                         (fn-cwait-run-over (cdr observations) acfg consumer secret
                                            seconds a fn-hist)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cwait-run-over fn-cwait-step-over fn-cwait-decide)
                                  (fn-cwait-poll-over fn-cwait-empty-pagep
                                   fn-cwait-seal-all)))))
