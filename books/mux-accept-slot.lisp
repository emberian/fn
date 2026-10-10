; fn: the pending-accept slot, decided here (r71 F13; lane serve-next,
; 2026-10-05).
;
; An accept thread takes a socket from the kernel only into an I/O loop's
; free pending slot (host/native/mux.lisp fnn-mux-reserve): the socket is
; then the loop's, in its inbox, until the loop begins it (fn-exp-open
; admits or refuses it there).  Until this book the host decided which loop
; was free and whether to take a socket at all.  Now it observes, per loop,
; whether the slot is reserved, how many sockets wait in the inbox and
; whether the loop has closed, and asks:
;
;   (fn-mxa-reserve CURSOR LOOPS STOPPING)
;     -> (:reserved K)       loop K's slot is this caller's; take one socket
;      | (:deferred :pending-accept-bound)
;                            every loop holds a pending socket or a
;                            reservation: take nothing, the connections wait
;                            in the kernel's listen queue
;      | (:refused :stopping) the service stops or has no loop
;
; Round robin from CURSOR.  KEYSTONES: a reservation names a loop that holds
; no reservation, no pending socket and is open; while every loop holds one
; pending socket the answer is the named deferral; and, with the reservation
; it grants, no loop holds more than one pending socket, so the accepted and
; not yet begun sockets never exceed the loop count.

(in-package "ACL2")
(include-book "def-loop")
(local (include-book "arithmetic-5/top" :dir :system))

; One loop's observation: (RESERVED PENDING CLOSED), PENDING a natural.
(defun fn-mxa-loop-freep (obs)
  (declare (xargs :guard t))
  (and (consp obs) (consp (cdr obs)) (consp (cddr obs))
       (not (car obs)) (equal (cadr obs) 0) (not (caddr obs))))

; The first free loop at or after position K (mod N), trying at most COUNT.
(defun fn-mxa-find (k n count loops)
  (declare (xargs :guard (and (natp k) (posp n) (natp count) (true-listp loops))
                  :measure (nfix count)))
  (if (zp count) nil
    (let ((at (mod (nfix k) n)))
      (if (fn-mxa-loop-freep (nth at loops)) at
        (fn-mxa-find (+ 1 (nfix k)) n (- count 1) loops)))))

(defun fn-mxa-reserve (cursor loops stopping)
  (declare (xargs :guard (true-listp loops)))
  (cond ((or stopping (atom loops)) (list :refused :stopping))
        (t (let ((at (fn-mxa-find (nfix cursor) (len loops) (len loops) loops)))
             (if (natp at) (list :reserved at)
               (list :deferred :pending-accept-bound))))))

(defun fn-mxa-loop-pending (obs)
  (declare (xargs :guard t))
  (if (and (consp obs) (consp (cdr obs)))
      (+ (if (car obs) 1 0) (nfix (cadr obs)))
    0))

; Every loop holds at most one pending socket or reservation.
(defun fn-mxa-at-most-one-each (loops)
  (declare (xargs :guard t))
  (if (atom loops) t
    (and (<= (fn-mxa-loop-pending (car loops)) 1)
         (fn-mxa-at-most-one-each (cdr loops)))))

(def-loop fn-mxa-pending-total (loops)
  :shape :sum :over loops :elt l
  :body (fn-mxa-loop-pending l))

; The observation after the grant: loop K's slot reserved.
(defun fn-mxa-grant (k loops)
  (declare (xargs :guard (natp k)))
  (if (atom loops) loops
    (if (zp k)
        (cons (list t (and (consp (car loops)) (consp (cdar loops)) (cadar loops))
                    (and (consp (car loops)) (consp (cdar loops)) (consp (cddar loops))
                         (caddar loops)))
              (cdr loops))
      (cons (car loops) (fn-mxa-grant (- k 1) (cdr loops))))))

(local
 (defthm fn-mxa-find-is-free-and-in-range
   (implies (and (posp n) (fn-mxa-find k n count loops))
            (and (natp (fn-mxa-find k n count loops))
                 (< (fn-mxa-find k n count loops) n)
                 (fn-mxa-loop-freep (nth (fn-mxa-find k n count loops) loops))))))

(local
 (defun fn-mxa-find-ind (k count i)
   (declare (xargs :measure (nfix count)))
   (if (zp count) (list k i)
     (fn-mxa-find-ind (+ 1 (nfix k)) (- count 1) (- i 1)))))

(local
 (defthm fn-mxa-find-none-means-none-free-from-k
   (implies (and (posp n) (natp k) (natp i) (< i (nfix count))
                 (not (fn-mxa-find k n count loops)))
            (not (fn-mxa-loop-freep (nth (mod (+ k i) n) loops))))
   :hints (("Goal" :induct (fn-mxa-find-ind k count i)
            :in-theory (disable fn-mxa-loop-freep)))))

(local
 (defthm fn-mxa-find-none-means-none-free
   (implies (and (posp n) (natp k) (natp j) (< j n) (<= n (nfix count))
                 (not (fn-mxa-find k n count loops)))
            (not (fn-mxa-loop-freep (nth j loops))))
   :hints (("Goal" :use ((:instance fn-mxa-find-none-means-none-free-from-k
                                    (i (mod (- j k) n))))
            :in-theory (disable fn-mxa-find-none-means-none-free-from-k fn-mxa-loop-freep)))))

(local (defthm fn-mxa-consp-len-posp
         (implies (consp x) (< 0 (len x))) :rule-classes :linear))

; KEYSTONE (a reservation names a free loop).
(defthm fn-mxa-reserve-grants-only-a-free-loop
  (let ((r (fn-mxa-reserve cursor loops stopping)))
    (implies (equal (car r) :reserved)
             (and (not stopping) (consp loops)
                  (natp (cadr r)) (< (cadr r) (len loops))
                  (fn-mxa-loop-freep (nth (cadr r) loops)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mxa-reserve) (fn-mxa-find fn-mxa-loop-freep))
           :use ((:instance fn-mxa-find-is-free-and-in-range
                            (k (nfix cursor)) (n (len loops)) (count (len loops)))))))

; KEYSTONE (the named deferral is exactly "no loop is free").
(defthm fn-mxa-reserve-defers-exactly-when-no-loop-is-free
  (implies (and (not stopping) (consp loops) (true-listp loops))
           (iff (equal (fn-mxa-reserve cursor loops stopping)
                       (list :deferred :pending-accept-bound))
                (not (fn-mxa-find (nfix cursor) (len loops) (len loops) loops))))
  :rule-classes nil)

(defthm fn-mxa-reserve-defers-when-every-loop-holds-one
  (implies (and (not stopping) (consp loops) (true-listp loops)
                (natp j) (< j (len loops))
                (equal (fn-mxa-reserve cursor loops stopping)
                       (list :deferred :pending-accept-bound)))
           (not (fn-mxa-loop-freep (nth j loops))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-mxa-find-none-means-none-free
                                   (k (nfix cursor)) (n (len loops)) (count (len loops)))))))

(local
 (defthm fn-mxa-grant-keeps-one-each
   (implies (and (fn-mxa-at-most-one-each loops) (natp k)
                 (fn-mxa-loop-freep (nth k loops)))
            (fn-mxa-at-most-one-each (fn-mxa-grant k loops)))))

(local
 (defthm fn-mxa-one-each-bounds-the-total
   (implies (fn-mxa-at-most-one-each loops)
            (<= (fn-mxa-pending-total loops) (len loops)))
   :rule-classes :linear))

(local
 (defthm fn-mxa-grant-len
   (equal (len (fn-mxa-grant k loops)) (len loops))))

; KEYSTONE (the bound).  With at most one pending socket per loop before, the
; reservation granted keeps it so, and the accepted-and-unbegun sockets
; (each loop's reservation and inbox) never exceed the loop count.
(defthm fn-mxa-reservation-keeps-the-pending-bound
  (let ((r (fn-mxa-reserve cursor loops stopping)))
    (implies (and (fn-mxa-at-most-one-each loops) (equal (car r) :reserved))
             (and (fn-mxa-at-most-one-each (fn-mxa-grant (cadr r) loops))
                  (<= (fn-mxa-pending-total (fn-mxa-grant (cadr r) loops)) (len loops)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-mxa-reserve-grants-only-a-free-loop))
           :in-theory (disable fn-mxa-reserve))))

;; Decimal digits of N before ACC.
(defun fn-mxa-dec (n acc)
  (declare (xargs :guard (and (natp n) (character-listp acc)) :measure (nfix n)))
  (let ((d (code-char (+ 48 (mod (nfix n) 10)))))
    (if (< (nfix n) 10) (cons d acc)
      (fn-mxa-dec (floor (nfix n) 10) (cons d acc)))))

(local
 (defthm fn-mxa-dec-character-listp
   (implies (character-listp acc) (character-listp (fn-mxa-dec n acc)))))

; The deferral's log line (the service log): the bound and what holds it.
(defun fn-mxa-deferral-line (loops)
  (declare (xargs :guard t))
  (concatenate 'string "accept deferred reason=pending-accept-bound pending="
               (coerce (fn-mxa-dec (fn-mxa-pending-total loops) nil) 'string)
               " loops="
               (coerce (fn-mxa-dec (len loops) nil) 'string)))

(in-theory (disable fn-mxa-reserve fn-mxa-find fn-mxa-grant fn-mxa-pending-total
                    fn-mxa-at-most-one-each fn-mxa-loop-freep fn-mxa-loop-pending))
