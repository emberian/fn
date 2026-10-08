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

; --- the queue is ACL2's -----------------------------------------------------
; The waiting requests are an ACL2 value Q = (NEXT . IDS): IDS the waiting
; requests' ids in arrival order, NEXT the id the next arrival gets. The host
; holds Q opaquely (host/native/owner.lisp *fnn-cold-queue*) and the objects
; the ids name; it never counts the waiting, the position ahead of a request or
; the idle workers: ACL2 reads WAITING from Q, AHEAD from the id's position in
; Q, and IDLE from FREE, the list of idle worker rows the host offers (as
; fn-pio-direct-admit's WORKER is the row the host offers).
; The place of ID in IDS (0 first), NIL when it is not there.
(defun fn-cwq-pos (id ids)
  (declare (xargs :guard t))
  (cond ((atom ids) nil)
        ((equal id (car ids)) 0)
        (t (let ((r (fn-cwq-pos id (cdr ids)))) (and r (1+ r))))))

(defun fn-cwq-below (ids n)
  (declare (xargs :guard (and (nat-listp ids) (natp n))))
  (if (consp ids) (and (< (car ids) n) (fn-cwq-below (cdr ids) n)) t))

(defun fn-cwq-p (q)
  (declare (xargs :guard t))
  (and (consp q) (natp (car q)) (nat-listp (cdr q)) (no-duplicatesp-equal (cdr q))
       (<= (len (cdr q)) (fn-cwq-bound)) (fn-cwq-below (cdr q) (car q))))

(defun fn-cwq-new () (declare (xargs :guard t)) (cons 0 nil))

(defun fn-cwq-waiting (q)
  (declare (xargs :guard (fn-cwq-p q))) (len (cdr q)))

; The arrival decision. FREE: the idle workers' rows. (mv WORD Q1 ID): ID the
; arrival's place in Q1 when WORD is :enqueue, else NIL. An idle worker is the
; arriving request's only if no queued request is ahead of it for that worker.
(defun fn-cwq-arrive (q free)
  (declare (xargs :guard (and (fn-cwq-p q) (true-listp free))))
  (let ((waiting (len (cdr q))) (idle (len free)))
    (cond ((< waiting idle) (mv :admit q nil))
          ((< waiting (fn-cwq-bound))
           (mv :enqueue (cons (1+ (car q)) (append (cdr q) (list (car q)))) (car q)))
          (t (mv :queue-full q nil)))))

; A request leaves the queue: it issued, its connection ended, or its admitted
; hold lapsed, or ACL2 refused it at its deadline (fn-cwq-step).
(defun fn-cwq-drop (q id)
  (declare (xargs :guard (fn-cwq-p q)))
  (cons (car q) (remove1-equal id (cdr q))))

; A queued request's decision when the host wakes it (a worker was released,
; or the wait it was told expired): (mv WORD Q1). :gone (not queued),
; :admit (a worker is idle for it: the line runs again and issues),
; (:wait MS), or :unavailable, which drops it from Q1.
(defun fn-cwq-step (q id free since now limit)
  (declare (xargs :guard (and (fn-cwq-p q) (true-listp free))))
  (let ((ahead (fn-cwq-pos id (cdr q))))
    (cond ((null ahead) (mv :gone q))
          ((< ahead (len free)) (mv :admit q))
          (t (let ((d (fn-otb-dependency-step since now limit nil)))
               (if (equal d :unavailable)
                   (mv :unavailable (fn-cwq-drop q id))
                 (mv d q)))))))

; The refusal the arriving request gets today (the twin this replaces).
(defun fn-cwq-arrive-refuse-now (q free)
  (declare (xargs :guard (and (fn-cwq-p q) (true-listp free))))
  (if (< (len (cdr q)) (len free)) (mv :admit q nil) (mv :queue-full q nil)))

; --- keystones -------------------------------------------------------------

(defthm fn-cwq-member-iff-position
  (iff (fn-cwq-pos id ids) (member-equal id ids)))

(defthm fn-cwq-len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-cwq-member-remove1-member
  (implies (member-equal y (remove1-equal x ids)) (member-equal y ids)))

(defthm fn-cwq-member-append-single
  (iff (member-equal y (append ids (list x))) (or (member-equal y ids) (equal y x))))

(defthm fn-cwq-below-not-member
  (implies (and (fn-cwq-below ids n) (natp x) (<= n x)) (not (member-equal x ids))))

(defthm fn-cwq-below-monotone
  (implies (and (fn-cwq-below ids n) (<= n m)) (fn-cwq-below ids m)))

(defthm fn-cwq-below-append
  (equal (fn-cwq-below (append a b) n) (and (fn-cwq-below a n) (fn-cwq-below b n))))

(defthm fn-cwq-below-remove1
  (implies (fn-cwq-below ids n) (fn-cwq-below (remove1-equal x ids) n)))

(defthm fn-cwq-no-dup-remove1
  (implies (no-duplicatesp-equal ids) (no-duplicatesp-equal (remove1-equal x ids)))
  :hints (("Goal" :induct (remove1-equal x ids))))

(defthm fn-cwq-nat-listp-remove1
  (implies (nat-listp ids) (nat-listp (remove1-equal x ids))))

(defthm fn-cwq-len-remove1
  (<= (len (remove1-equal x ids)) (len ids)) :rule-classes :linear)

(defthm fn-cwq-no-dup-append-fresh
  (implies (and (no-duplicatesp-equal ids) (not (member-equal x ids)))
           (no-duplicatesp-equal (append ids (list x))))
  :hints (("Goal" :induct (no-duplicatesp-equal ids))))

(defthm fn-cwq-nat-listp-append
  (implies (and (nat-listp ids) (natp x)) (nat-listp (append ids (list x)))))

(defthm fn-cwq-position-append-last
  (implies (not (member-equal x ids))
           (equal (fn-cwq-pos x (append ids (list x))) (len ids))))

(defthm fn-cwq-member-remove1-other
  (implies (and (member-equal y ids) (not (equal x y)))
           (member-equal y (remove1-equal x ids))))

; The queue never exceeds its bound, and stays well formed, whichever verb.
(defthm fn-cwq-arrive-preserves-the-queue
  (implies (and (fn-cwq-p q) (true-listp free))
           (fn-cwq-p (mv-nth 1 (fn-cwq-arrive q free))))
  :hints (("Goal" :in-theory (enable fn-cwq-arrive fn-cwq-p)
                  :use ((:instance fn-cwq-below-not-member (ids (cdr q)) (n (car q)) (x (car q))))))
  :rule-classes nil)

(defthm fn-cwq-drop-preserves-the-queue
  (implies (fn-cwq-p q) (fn-cwq-p (fn-cwq-drop q id)))
  :hints (("Goal" :in-theory (enable fn-cwq-drop fn-cwq-p)))
  :rule-classes nil)

(defthm fn-cwq-step-preserves-the-queue
  (implies (and (fn-cwq-p q) (true-listp free))
           (fn-cwq-p (mv-nth 1 (fn-cwq-step q id free since now limit))))
  :hints (("Goal" :in-theory (enable fn-cwq-step fn-cwq-drop fn-cwq-p)))
  :rule-classes nil)

; An arrival under the bound is never refused.
(defthm fn-cwq-arrival-under-the-bound-is-never-refused
  (implies (< (fn-cwq-waiting q) (fn-cwq-bound))
           (member-eq (mv-nth 0 (fn-cwq-arrive q free)) '(:admit :enqueue)))
  :hints (("Goal" :in-theory (enable fn-cwq-arrive fn-cwq-waiting)))
  :rule-classes nil)

; Only a full queue refuses at arrival.
(defthm fn-cwq-queue-full-only-when-full
  (implies (equal (mv-nth 0 (fn-cwq-arrive q free)) :queue-full)
           (and (<= (fn-cwq-bound) (fn-cwq-waiting q)) (<= (len free) (fn-cwq-waiting q))
                (equal (mv-nth 1 (fn-cwq-arrive q free)) q)))
  :hints (("Goal" :in-theory (enable fn-cwq-arrive fn-cwq-waiting)))
  :rule-classes nil)

; An enqueued arrival has exactly the waiting requests ahead of it.
(defthm fn-cwq-an-enqueued-arrival-waits-behind-those-already-waiting
  (implies (and (fn-cwq-p q) (equal (mv-nth 0 (fn-cwq-arrive q free)) :enqueue))
           (and (equal (fn-cwq-pos (mv-nth 2 (fn-cwq-arrive q free))
                                       (cdr (mv-nth 1 (fn-cwq-arrive q free))))
                       (fn-cwq-waiting q))
                (equal (fn-cwq-waiting (mv-nth 1 (fn-cwq-arrive q free)))
                       (1+ (fn-cwq-waiting q)))))
  :hints (("Goal" :in-theory (enable fn-cwq-arrive fn-cwq-waiting fn-cwq-p)
                  :use ((:instance fn-cwq-below-not-member (ids (cdr q)) (n (car q)) (x (car q))))))
  :rule-classes nil)

; A queued request is refused iff it has no worker and its deadline has passed.
(defthm fn-cwq-refused-only-at-the-deadline
  (iff (equal (mv-nth 0 (fn-cwq-step q id free since now limit)) :unavailable)
       (and (member-equal id (cdr q))
            (<= (len free) (fn-cwq-pos id (cdr q)))
            (<= (fn-otb-dependency-of-limit limit)
                (fn-otb-dependency-elapsed since now))))
  :hints (("Goal" :in-theory (enable fn-cwq-step fn-otb-dependency-step)))
  :rule-classes nil)

; The refused request leaves the queue; every other request keeps its place.
(defthm fn-cwq-a-refusal-leaves-the-queue
  (implies (equal (mv-nth 0 (fn-cwq-step q id free since now limit)) :unavailable)
           (equal (mv-nth 1 (fn-cwq-step q id free since now limit)) (fn-cwq-drop q id)))
  :hints (("Goal" :in-theory (enable fn-cwq-step)))
  :rule-classes nil)

; A request with a worker is served whatever the clock says.
(defthm fn-cwq-a-worker-for-it-admits
  (implies (and (member-equal id (cdr q))
                (< (fn-cwq-pos id (cdr q)) (len free)))
           (equal (mv-nth 0 (fn-cwq-step q id free since now limit)) :admit))
  :hints (("Goal" :in-theory (enable fn-cwq-step)))
  :rule-classes nil)

; Before the deadline the answer is a wait of at least 1 ms and at most the
; time left: the host's timer fires by the deadline, not after.
(defthm fn-cwq-the-wait-ends-at-the-deadline
  (implies (and (member-equal id (cdr q))
                (<= (len free) (fn-cwq-pos id (cdr q)))
                (consp (mv-nth 0 (fn-cwq-step q id free since now limit))))
           (let ((ms (cadr (mv-nth 0 (fn-cwq-step q id free since now limit)))))
             (and (equal (car (mv-nth 0 (fn-cwq-step q id free since now limit))) :wait)
                  (posp ms)
                  (equal (+ (fn-otb-dependency-elapsed since now) ms)
                         (fn-otb-dependency-of-limit limit)))))
  :hints (("Goal" :in-theory (enable fn-cwq-step fn-otb-dependency-step)))
  :rule-classes nil)

; Teeth.
; (1) The twin it replaces refuses an arrival the bound admits: the first
;     keystone's conclusion fails for it, while the new one conforms.
(defthm fn-cwq-tooth-refuse-now-violates-the-arrival-keystone
  (let ((q (fn-cwq-new)))
    (and (fn-cwq-p q) (< (fn-cwq-waiting q) (fn-cwq-bound))          ; antecedent holds
         (not (member-eq (mv-nth 0 (fn-cwq-arrive-refuse-now q nil)) '(:admit :enqueue)))
         (member-eq (mv-nth 0 (fn-cwq-arrive q nil)) '(:admit :enqueue))))
  :rule-classes nil)
; (2) A refusal before the deadline is possible for a mutant that refuses
;     every queued request that finds no worker: witnessed at elapsed 0.
(defun fn-cwq-step-mutant (q id free)
  (declare (xargs :guard (and (fn-cwq-p q) (true-listp free))))
  (let ((ahead (fn-cwq-pos id (cdr q))))
    (cond ((null ahead) :gone) ((< ahead (len free)) :admit) (t :unavailable))))
(defthm fn-cwq-tooth-mutant-refuses-before-the-deadline
  (let ((q (cons 1 '(0))) (id 0) (free nil) (since 100) (now 100) (limit 5000))
    (and (fn-cwq-p q)
         (equal (fn-cwq-step-mutant q id free) :unavailable)
         (not (<= (fn-otb-dependency-of-limit limit) (fn-otb-dependency-elapsed since now)))
         (equal (mv-nth 0 (fn-cwq-step q id free since now limit)) '(:wait 5000))))
  :rule-classes nil)
; (3) An arrival the bound refuses: a mutant that enqueues past the bound grows
;     the queue beyond it; the real arrival refuses by name and leaves Q alone.
(defun fn-cwq-arrive-unbounded (q free)
  (declare (xargs :guard (and (fn-cwq-p q) (true-listp free))))
  (if (< (len (cdr q)) (len free))
      (mv :admit q nil)
    (mv :enqueue (cons (1+ (car q)) (append (cdr q) (list (car q)))) (car q))))
(defun fn-cwq-iota (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons (1- n) (fn-cwq-iota (1- n)))))
(defun fn-cwq-full-queue ()
  (declare (xargs :guard t))
  (cons (fn-cwq-bound) (fn-cwq-iota (fn-cwq-bound))))
(defthm fn-cwq-tooth-unbounded-enqueue-exceeds-the-bound
  (let ((q (fn-cwq-full-queue)))
    (and (fn-cwq-p q)
         (equal (fn-cwq-waiting q) (fn-cwq-bound))                 ; the bound premise is at its edge
         (equal (mv-nth 0 (fn-cwq-arrive-unbounded q nil)) :enqueue)
         (not (fn-cwq-p (mv-nth 1 (fn-cwq-arrive-unbounded q nil))))
         (equal (mv-nth 0 (fn-cwq-arrive q nil)) :queue-full)
         (equal (mv-nth 1 (fn-cwq-arrive q nil)) q)))
  :rule-classes nil)
; (4) Positive witnesses: the 16-readers case with four workers and 64 slots.
;     FREE lists idle worker rows (any values: ACL2 counts them).
(defthm fn-cwq-witness-sixteen-readers
  (let* ((q0 (fn-cwq-new))
         (q4 (cons 4 '(0 1 2 3)))
         (q12 (cons 12 (fn-cwq-iota 12)))
         (q64 (fn-cwq-full-queue)))
    (and (fn-cwq-p q4) (fn-cwq-p q12) (fn-cwq-p q64)
         (equal (mv-nth 0 (fn-cwq-arrive q0 '(w0 w1 w2 w3))) :admit)
         (equal (mv-nth 0 (fn-cwq-arrive q4 nil)) :enqueue)
         (equal (mv-nth 0 (fn-cwq-arrive q12 nil)) :enqueue)
         (equal (mv-nth 0 (fn-cwq-arrive q64 nil)) :queue-full)
         ;; the request behind three others, no worker: waits the time left
         (equal (mv-nth 0 (fn-cwq-step (cons 4 '(0 1 2 3)) 3 nil 0 10 5000)) '(:wait 4990))
         (equal (mv-nth 0 (fn-cwq-step (cons 4 '(0 1 2 3)) 3 nil 0 5000 5000)) :unavailable)
         (equal (mv-nth 1 (fn-cwq-step (cons 4 '(0 1 2 3)) 3 nil 0 5000 5000)) (cons 4 '(0 1 2)))
         (equal (mv-nth 0 (fn-cwq-step (cons 4 '(0 1 2 3)) 3 '(w0 w1 w2 w3) 0 5000 5000)) :admit)))
  :rule-classes nil)
