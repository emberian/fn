; Witnesses and teeth for books/served-plan.lisp (PRF-248; lane
; owner-scheduler, 2026-09-26).
;
; Keystone 1 (`fn-splan-window-is-a-prefix-of-the-reply'): the window's
; range followed by the continuation's debt is the plan's debt, the window is
; at most W, and under :ok a window of an unfinished plan writes something.
; Keystone 2 (`fn-splan-windows-are-the-reply'): the windows of a plan that
; was drained to done concatenate to the served reply.  Here: the reachable
; witness (the ARTICLE-shaped reply of served-reply-buffer's tests, split
; over two effects with a :close between, drained in windows of 5 over a
; buffer holding a longer stale value); the must-fail for each hypothesis
; of the progress conjunct (:ok, a positive W, an unfinished plan); the
; must-fail for keystone 2's hypothesis (a drain stopped before done); the
; :malformed status; and the served-size witness (a 3 MiB body in 64 KiB
; windows).
(in-package "ACL2")
(include-book "../../books/served-plan")
(include-book "must-fail-checked")

(defconst *spt-stale* '(88 88 88 88 88 88 88 88 88 88 88 88))
(defconst *spt-effects*
  (list (list :reply '(50 50 48 32 49 13 10))      ; "220 1\r\n"
        (list :close)
        (list :reply '(104 105 13 10 46 13 10))))   ; "hi\r\n.\r\n"
(defconst *spt-reply* (fn-served-reply-octets *spt-effects*))
(defconst *spt-bad* (list (list :reply '(50 50)) (list :reply '(300 51))))

; One window over a buffer that first holds STALE: (status range len plan').
(defun spt-window (stale p w)
  (declare (xargs :guard (and (fn-cbor-octet-listp stale) (natp w))))
  (with-local-stobj fn-octets
    (mv-let (status range len p2 fn-octets)
      (let* ((fn-octets (fn-octets-from-list stale fn-octets)))
        (mv-let (status p2 fn-octets)
          (fn-splan-window p w fn-octets)
          (mv status
              (fn-oct-slice-list 0 (fn-octets-len fn-octets) fn-octets)
              (fn-octets-len fn-octets)
              p2 fn-octets)))
      (list status range len p2))))

; The host's loop over the stobj: windows until done; (status octets windows).
(defun spt-loop (p w fuel acc n)
  (declare (xargs :guard (and (natp w) (natp fuel) (true-listp acc) (natp n))
                  :measure (nfix fuel)))
  (if (or (zp fuel) (fn-splan-donep p))
      (list :ok acc n)
    (let ((r (spt-window nil p w)))
      (if (equal (first r) :ok)
          (spt-loop (fourth r) w (- fuel 1) (append acc (second r)) (+ n 1))
        (list (first r) acc n)))))

; -----------------------------------------------------------------------------
; KEYSTONE 1: the reachable witness (W = 5 over the 14-octet reply).  The
; progress conjunct's antecedent holds here: W is positive, the plan is not
; done, and the window's status is :ok (asserted with the conclusion).
(defconst *spt-p* (fn-splan-of-effects *spt-effects*))
(assert-event (equal (fn-splan-remaining *spt-p*) *spt-reply*))
(assert-event (equal (len *spt-reply*) 14))
(assert-event (not (fn-splan-donep *spt-p*)))
(assert-event
 (let ((r (spt-window *spt-stale* *spt-p* 5)))
   (and (equal (first r) :ok)
        (equal (third r) 5)
        (equal (second r) (take 5 *spt-reply*))
        (equal (append (second r) (fn-splan-remaining (fourth r))) *spt-reply*)
        (not (fn-splan-donep (fourth r))))))
; The second window crosses the :close and the effect boundary.
(assert-event
 (let* ((r1 (spt-window *spt-stale* *spt-p* 5))
        (r2 (spt-window *spt-stale* (fourth r1) 5)))
   (and (equal (first r2) :ok)
        (equal (second r2) '(13 10 104 105 13))
        (equal (append (second r1) (second r2) (fn-splan-remaining (fourth r2))) *spt-reply*))))

; MUST-FAIL for the progress conjunct's hypotheses.
; (a) :ok -- a plan whose first octet is not one: :malformed and nothing written.
(defconst *spt-pbad* (cons '(300 51) nil))
(assert-event (equal (first (spt-window *spt-stale* *spt-pbad* 5)) :malformed))
(assert-event (not (fn-splan-donep *spt-pbad*)))
(must-fail-checked (assert-event (posp (third (spt-window *spt-stale* *spt-pbad* 5)))))
; The prefix law still holds there (it is unconditional): the bad octet
; stays in the continuation.
(assert-event
 (let ((r (spt-window *spt-stale* *spt-pbad* 5)))
   (equal (append (second r) (fn-splan-remaining (fourth r)))
          (fn-splan-remaining *spt-pbad*))))
; (b) a positive W -- W = 0 writes nothing of an unfinished plan (the
; retained hypotheses hold: the status is :ok and the plan is not done).
(assert-event (equal (first (spt-window *spt-stale* *spt-p* 0)) :ok))
(assert-event (not (fn-splan-donep *spt-p*)))
(assert-event (equal (third (spt-window *spt-stale* *spt-p* 0)) 0))
(must-fail-checked (assert-event (posp (third (spt-window *spt-stale* *spt-p* 0)))))
; (c) an unfinished plan -- a done plan writes nothing (the status is :ok
; and W is positive).
(defconst *spt-done* (fn-splan-of-effects (list (list :close))))
(assert-event (fn-splan-donep *spt-done*))
(assert-event (equal (first (spt-window *spt-stale* *spt-done* 5)) :ok))
(must-fail-checked (assert-event (posp (third (spt-window *spt-stale* *spt-done* 5)))))

; -----------------------------------------------------------------------------
; The window size ACL2 hands the host (fn-splan-window-size): the whole of
; the effect the window starts in, positive exactly while the plan is not
; done (fn-splan-window-size-is-positive-until-done).  The reachable witness:
; the two reply effects are two windows, the :close between them costs none.
(assert-event (equal (fn-splan-window-size *spt-p*) 7))
(assert-event (and (posp (fn-splan-window-size *spt-p*)) (not (fn-splan-donep *spt-p*))))
(assert-event
 (let* ((r1 (spt-window *spt-stale* *spt-p* (fn-splan-window-size *spt-p*)))
        (r2 (spt-window *spt-stale* (fourth r1) (fn-splan-window-size (fourth r1)))))
   (and (equal (first r1) :ok) (equal (first r2) :ok)
        (equal (second r1) '(50 50 48 32 49 13 10))
        (equal (fn-splan-window-size (fourth r1)) 7)
        (equal (second r2) '(104 105 13 10 46 13 10))
        (equal (append (second r1) (second r2)) *spt-reply*)
        (fn-splan-donep (fourth r2))
        (equal (fn-splan-window-size (fourth r2)) 0))))
; A plan whose current effect is spent and whose rest starts with an
; effect without octets: the size is the next reply effect's, not zero.
(defconst *spt-mid* (cons nil (list (list :close) (list :reply '(104 105)))))
(assert-event (and (not (fn-splan-donep *spt-mid*)) (equal (fn-splan-window-size *spt-mid*) 2)))
; The other side of the iff: a done plan's size is zero.
(assert-event (equal (fn-splan-window-size *spt-done*) 0))
(must-fail-checked (assert-event (posp (fn-splan-window-size *spt-done*))))

; -----------------------------------------------------------------------------
; KEYSTONE 2: the drained windows are the reply (W = 5: three windows; W =
; 100: one), on the list model and on the stobj loop the host runs.
(assert-event
 (mv-let (status octets p3) (fn-splan-drain *spt-p* 5 3)
   (and (equal status :ok) (fn-splan-donep p3) (equal octets *spt-reply*))))
(assert-event
 (mv-let (status octets p3) (fn-splan-drain *spt-p* 100 1)
   (and (equal status :ok) (fn-splan-donep p3) (equal octets *spt-reply*))))
(assert-event (equal (spt-loop *spt-p* 5 10 nil 0) (list :ok *spt-reply* 3)))
(assert-event (equal (spt-loop *spt-p* 100 10 nil 0) (list :ok *spt-reply* 1)))

; MUST-FAIL for keystone 2's hypothesis: two windows of 5 are not done, and
; the octets are not the reply.
(assert-event
 (mv-let (status octets p3) (fn-splan-drain *spt-p* 5 2)
   (and (equal status :ok) (not (fn-splan-donep p3)) (equal (len octets) 10))))
(must-fail-checked
 (assert-event
  (mv-let (status octets p3) (fn-splan-drain *spt-p* 5 2)
    (declare (ignore status p3))
    (equal octets *spt-reply*))))
; A malformed plan is never drained to done, and the host's loop reports it.
(assert-event (equal (first (spt-loop (fn-splan-of-effects *spt-bad*) 5 10 nil 0)) :malformed))
(assert-event
 (mv-let (status octets p3) (fn-splan-drain (fn-splan-of-effects *spt-bad*) 5 10)
   (and (equal status :malformed) (not (fn-splan-donep p3)) (equal octets '(50 50)))))

; -----------------------------------------------------------------------------
; SERVED SIZE: a 3 MiB body behind the status line, in 64 KiB windows (the
; window the host uses): 49 windows, the concatenation is the reply, and
; no window exceeds W.
(defun spt-body (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))))
  (if (zp n) acc (spt-body (- n 1) (cons (if (equal (mod n 80) 0) 10 120) acc))))
(defconst *spt-big-body* (spt-body (* 3 1024 1024) '(13 10 46 13 10)))
(defconst *spt-big-effects*
  (list (list :reply '(50 50 48 32 49 13 10)) (list :reply *spt-big-body*)))
(defconst *spt-big-reply* (fn-served-reply-octets *spt-big-effects*))
(assert-event
 (let ((r (spt-loop (fn-splan-of-effects *spt-big-effects*) 65536 100 nil 0)))
   (and (equal (first r) :ok)
        (equal (third r) 49)
        (equal (len (second r)) (len *spt-big-reply*))
        (equal (second r) *spt-big-reply*))))
(assert-event
 (let ((r (spt-window nil (fn-splan-of-effects *spt-big-effects*) 65536)))
   (and (equal (first r) :ok) (equal (third r) 65536))))

; -----------------------------------------------------------------------------
; fn-splan-step-handshake-owed (lane served-leftovers): the step the host
; reads for its handshake.  Reachable positive: a STARTTLS step (the 382 and
; the effect) that neither closes nor meets the exposure close owes the
; handshake, and every conjunct of the lemma's conclusion holds.  Each
; conjunct's failure: a step that also closes (its own :close), one the
; exposure closes (its 400), and one with no 382 owe none.
(defconst *spt-382* (list (list :reply '(51 56 50 13 10)) (fn-auth-starttls-effect)))
(defconst *spt-400* '(52 48 48 13 10))
(defconst *spt-tls* (fn-splan-step-make *spt-382* nil t nil 10 nil nil))
(assert-event (fn-splan-step-p *spt-tls*))
(assert-event (fn-splan-step-handshake-owed *spt-tls*))
(assert-event (and (fn-splan-step-starttlsp *spt-tls*)
                   (not (fn-splan-step-closep *spt-tls*))
                   (not (fn-splan-step-exposure-close *spt-tls*))))
(assert-event (not (fn-splan-step-handshake-owed
                    (fn-splan-step-make *spt-382* t t nil 10 nil nil))))
(assert-event (not (fn-splan-step-handshake-owed
                    (fn-splan-step-make *spt-382* nil t nil 10 nil *spt-400*))))
(assert-event (not (fn-splan-step-handshake-owed
                    (fn-splan-step-make *spt-382* nil nil nil 10 nil nil))))

;; Lane join-f2-13 (PRF-1020): a plan at a CURSOR effect, (:over-cursor CUR),
;; the served OVER/XOVER range arm's.  A window writes the octets in front
;; of it and STOPS (status :cursor); the continuation is at the cursor
;; (fn-splan-at-cursorp): neither done nor sized, and a window of it writes
;; nothing.  The cursor's quantum is books/served-plan-cursor.lisp's.
(defconst *spt-cursor*
  (fn-splan-of-effects (list (list :reply '(50 50)) (list :over-cursor '("g" 1 3 3 nil t))
                             (list :reply '(46 13 10)))))
(assert-event (not (fn-splan-at-cursorp *spt-cursor*)))
(assert-event (equal (fn-splan-window-size *spt-cursor*) 2))
(assert-event (equal (fn-splan-remaining *spt-cursor*) '(50 50 46 13 10)))
(assert-event (let ((r (spt-window *spt-stale* *spt-cursor* 5)))
                (and (equal (first r) :cursor)
                     (equal (second r) '(50 50))
                     (equal (third r) 2)
                     (fn-splan-at-cursorp (fourth r))
                     (equal (fn-splan-window-size (fourth r)) 0)
                     (not (fn-splan-donep (fourth r))))))
(defconst *spt-at-cursor* (fourth (spt-window *spt-stale* *spt-cursor* 5)))
(assert-event (let ((r (spt-window *spt-stale* *spt-at-cursor* 5)))
                (and (equal (first r) :cursor) (equal (third r) 0)
                     (equal (fourth r) *spt-at-cursor*))))
(must-fail-checked (assert-event (posp (fn-splan-window-size *spt-at-cursor*))))
(must-fail-checked (assert-event (fn-splan-donep *spt-at-cursor*)))
(must-fail-checked (assert-event (equal (first (spt-window *spt-stale* *spt-at-cursor* 5)) :ok)))
;; A window of no size at a cursor moves nothing and is :ok (the host asks
;; fn-splan-at-cursorp before it sizes a window).
(assert-event (equal (first (spt-window *spt-stale* *spt-at-cursor* 0)) :ok))
