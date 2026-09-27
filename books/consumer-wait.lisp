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
(defun fn-cwait-poll (oc acfg consumer secret)
  (declare (xargs :guard t :verify-guards nil))
  (if secret
      (fn-cbind-poll oc acfg consumer secret)
    (fn-cbind-plain-poll oc consumer)))

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

(defun fn-cwait-step (oc acfg consumer secret elapsed seconds)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cwait-decide (fn-cwait-poll oc acfg consumer secret) elapsed seconds))

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
  (let ((r (fn-cwait-step oc acfg consumer secret elapsed seconds))
        (p (fn-cwait-poll oc acfg consumer secret)))
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
(defun fn-cwait-run (observations acfg consumer secret seconds)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp observations)
      (let* ((o (car observations))
             (r (fn-cwait-step (car o) acfg consumer secret (cdr o) seconds)))
        (if (equal (car r) :answer)
            (list :answer (cadr r) (car o) (cdr o))
          (fn-cwait-run (cdr observations) acfg consumer secret seconds)))
    nil))

; KEYSTONE 2 (the loop).  When the wait answers, it answers the poll of the
; owner state at its return point; every earlier observation was an empty
; page before the deadline (the wait slept over no event and no refusal:
; `fn-cwait-run-sleeps-only-over-empty-pages'); and an empty answer is
; given only at or after the deadline.
(defthm fn-cwait-run-answers-the-poll-at-its-return-point
  (let ((r (fn-cwait-run observations acfg consumer secret seconds)))
    (implies r
             (and (equal (car r) :answer)
                  (equal (cadr r)
                         (fn-cwait-poll (caddr r) acfg consumer secret))
                  (implies (and (natp (cadddr r))
                                (fn-cwait-empty-pagep (cadr r)))
                           (<= (fn-cwait-deadline-ms seconds) (cadddr r))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cwait-run observations acfg consumer secret seconds)
           :in-theory (e/d (fn-cwait-run fn-cwait-step fn-cwait-decide)
                           (fn-cwait-poll fn-cwait-empty-pagep)))))

(defthm fn-cwait-run-sleeps-only-over-empty-pages
  (implies (not (equal (car (fn-cwait-step (car (car observations)) acfg
                                           consumer secret
                                           (cdr (car observations))
                                           seconds))
                       :answer))
           (and (fn-cwait-empty-pagep
                 (fn-cwait-poll (car (car observations)) acfg consumer secret))
                (natp (cdr (car observations)))
                (< (cdr (car observations)) (fn-cwait-deadline-ms seconds))
                (equal (fn-cwait-run observations acfg consumer secret seconds)
                       (fn-cwait-run (cdr observations) acfg consumer secret
                                     seconds))))
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
