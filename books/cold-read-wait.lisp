; A served miss past the cold-read workers waits, bounded (item
; COLD-READ-WORKERS-REFUSE-AT-16). Today a miss that finds every worker busy
; is refused at once (books/page-read-direct.lisp fn-pio-direct-admit,
; :read-resources-unavailable -> the 403 of books/owner-resource-line.lisp):
; at 16 concurrent readers 62% of requests were refused by Deputy L's W7 run
; with four workers. The decision is here; the host only waits on a condition
; for the time this book names and asks again.
;
; Statement: a request that arrives with fewer than WAIT-QUEUE requests
; already waiting is admitted at once (an idle worker for it) or queued; a
; queued request is answered by a worker as soon as one is idle for it, and is
; refused only once its dependency deadline (books/owner-time-bars.lisp
; fn-otb-dependency-step: the same SINCE/NOW/LIMIT as every other page
; dependency) has passed; only a request that arrives with the queue full is
; refused by name, at arrival.
(in-package "ACL2")
(include-book "profile-limits")
(include-book "owner-time-bars")

(defconst *fn-cwq-bound* (fn-profile-limit :cold-wait-queue))

(defun fn-cwq-bound ()
  (declare (xargs :guard t)) *fn-cwq-bound*)

;; The queue's storage is part of the node's fixed reservation: WAIT-QUEUE
;; waiting reads of one struct (12 slots and its header, 112 octets) and one
;; list cell (16), 128 octets each. books/cold-read-reservation.lisp charges it
;; with the persistent workers' native storage (fn-crv-native-baseline).
(defconst *fn-cwq-entry-octets* 128)

(defun fn-cwq-queue-octets ()
  (declare (xargs :guard t))
  (* *fn-cwq-entry-octets* (fn-cwq-bound)))

; The arrival decision. WAITING: requests already queued; IDLE: idle workers.
; An idle worker is the arriving request's only if no queued request is ahead
; of it for that worker.
(defun fn-cwq-arrive (waiting idle)
  (declare (xargs :guard t))
  (cond ((< (nfix waiting) (nfix idle)) :admit)
        ((< (nfix waiting) (fn-cwq-bound)) :enqueue)
        (t :queue-full)))

; A queued request's decision when the host wakes it (a worker was released,
; or the wait it was told expired). AHEAD: queued requests before it.
(defun fn-cwq-step (ahead idle since now limit)
  (declare (xargs :guard t))
  (cond ((< (nfix ahead) (nfix idle)) :admit)
        (t (let ((d (fn-otb-dependency-step since now limit nil)))
             (if (equal d :unavailable) :unavailable d)))))

; The refusal the arriving request gets today (the twin this replaces).
(defun fn-cwq-arrive-refuse-now (waiting idle)
  (declare (xargs :guard t))
  (if (< (nfix waiting) (nfix idle)) :admit :queue-full))

; --- keystones -------------------------------------------------------------

; An arrival under the bound is never refused.
(defthm fn-cwq-arrival-under-the-bound-is-never-refused
  (implies (< (nfix waiting) (fn-cwq-bound))
           (member-eq (fn-cwq-arrive waiting idle) '(:admit :enqueue)))
  :rule-classes nil)

; Only a full queue refuses at arrival, and the queue never exceeds its bound:
; an enqueue leaves at most WAIT-QUEUE waiting.
(defthm fn-cwq-queue-never-exceeds-its-bound
  (implies (equal (fn-cwq-arrive waiting idle) :enqueue)
           (<= (1+ (nfix waiting)) (fn-cwq-bound)))
  :rule-classes nil)
(defthm fn-cwq-queue-full-only-when-full
  (implies (equal (fn-cwq-arrive waiting idle) :queue-full)
           (and (<= (fn-cwq-bound) (nfix waiting)) (<= (nfix idle) (nfix waiting))))
  :rule-classes nil)

; A queued request is refused iff it has no worker and its deadline has passed.
(defthm fn-cwq-refused-only-at-the-deadline
  (iff (equal (fn-cwq-step ahead idle since now limit) :unavailable)
       (and (<= (nfix idle) (nfix ahead))
            (<= (fn-otb-dependency-of-limit limit)
                (fn-otb-dependency-elapsed since now))))
  :hints (("Goal" :in-theory (enable fn-otb-dependency-step)))
  :rule-classes nil)

; A request with a worker is served whatever the clock says.
(defthm fn-cwq-a-worker-for-it-admits
  (implies (< (nfix ahead) (nfix idle))
           (equal (fn-cwq-step ahead idle since now limit) :admit))
  :rule-classes nil)

; Before the deadline the answer is a wait of at least 1 ms and at most the
; time left: the host's timer fires by the deadline, not after.
(defthm fn-cwq-the-wait-ends-at-the-deadline
  (implies (and (<= (nfix idle) (nfix ahead))
                (consp (fn-cwq-step ahead idle since now limit)))
           (let ((ms (cadr (fn-cwq-step ahead idle since now limit))))
             (and (equal (car (fn-cwq-step ahead idle since now limit)) :wait)
                  (posp ms)
                  (equal (+ (fn-otb-dependency-elapsed since now) ms)
                         (fn-otb-dependency-of-limit limit)))))
  :hints (("Goal" :in-theory (enable fn-otb-dependency-step)))
  :rule-classes nil)

; Teeth.
; (1) The twin it replaces refuses an arrival the bound admits: the first
;     keystone's conclusion fails for it.
(defthm fn-cwq-tooth-refuse-now-violates-the-arrival-keystone
  (let ((waiting 0) (idle 0))
    (and (< waiting (fn-cwq-bound))                                  ; antecedent holds
         (not (member-eq (fn-cwq-arrive-refuse-now waiting idle) '(:admit :enqueue)))
         (member-eq (fn-cwq-arrive waiting idle) '(:admit :enqueue)))) ; the new one conforms
  :rule-classes nil)
; (2) A refusal before the deadline is possible for a mutant that refuses
;     every queued request that finds no worker: witnessed at elapsed 0.
(defun fn-cwq-step-mutant (ahead idle)
  (declare (xargs :guard t))
  (if (< (nfix ahead) (nfix idle)) :admit :unavailable))
(defthm fn-cwq-tooth-mutant-refuses-before-the-deadline
  (let ((ahead 0) (idle 0) (since 100) (now 100) (limit 5000))
    (and (equal (fn-cwq-step-mutant ahead idle) :unavailable)
         (not (<= (fn-otb-dependency-of-limit limit) (fn-otb-dependency-elapsed since now)))
         (equal (fn-cwq-step ahead idle since now limit) '(:wait 5000))))
  :rule-classes nil)
; (3) Positive witnesses: the 16-readers case with four workers and 64 slots.
(defthm fn-cwq-witness-sixteen-readers
  (and (equal (fn-cwq-arrive 0 4) :admit)
       (equal (fn-cwq-arrive 4 0) :enqueue)
       (equal (fn-cwq-arrive 12 0) :enqueue)
       (equal (fn-cwq-arrive 64 0) :queue-full)
       (equal (fn-cwq-step 3 0 0 10 5000) '(:wait 4990))
       (equal (fn-cwq-step 3 0 0 5000 5000) :unavailable)
       (equal (fn-cwq-step 3 4 0 5000 5000) :admit))
  :rule-classes nil)
