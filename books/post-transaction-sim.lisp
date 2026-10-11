; The POST transaction machine simulates L's commit driver (Builder P, landing 1: P4,
; AckEligible => DurableCommitEvidence for the machine).
;
; books/post-transaction.lisp is the machine (fn-ptx); books/post-transaction-durable.lisp is
; L's driver fn-ptd, whose keystone fn-ptd-posted-records-are-recovered-at-every-later-cut says
; every record fn-ptd answers :posted is recovered at every later cut.  This book maps the
; machine's completions to fn-ptd's inputs and relates the two states, so the records the machine
; answers :posted are fn-ptd's, and the keystone carries over; P6
; (fn-ptx-split-crash-images-are-entry-crash-images, books/post-transaction-crash.lisp) covers the
; cuts inside the machine's split entry write.
;
; The machine reads its message (the entry's octets, the spans of fn-ptx-spans) through the
; layer's view at each step; the environment's side is the rely (fn-ptx-rely): the octets the
; machine wrote at the head's end read back, and the message is unchanged from then on except for
; the trailer the last hashing step appends.  For layer runs the rely follows from the layer's
; write and ownership theorems (the handed buffer is the machine's :out lease, its workspaces its
; own), stated separately.
(in-package "ACL2")
(include-book "post-transaction")
(include-book "post-transaction-crash")

; -----------------------------------------------------------------------------
; The message and the record.

; The entry's head: the frame header (fixed length) and the chain field.
(defun fn-ptx-head-len () (+ (len (fn-ptx-frame-header 0)) 32))
(defun fn-ptx-message (m id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((spans (fn-ptx-spans m)))
    (fn-ptx-msg-range 0 (fn-ptx-spans-len spans) spans id inc fn-rtc-st)))
; The record: the message (the trailer included once hashed) less the head and the trailer.
(defun fn-ptx-record (m id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((w (fn-ptx-message m id inc fn-rtc-st)))
    (nthcdr (fn-ptx-head-len) (take (- (len w) 32) w))))

; The digest's held stack over the whole windows of PREFIX (fn-b3-append-window's state).
(defun fn-ptx-stack-of (prefix)
  (if (consp prefix)
      (fn-b3-stack-push-all *fn-b3-iv* 0 *fn-ptx-wexp*
                            (fn-b3-window-outs *fn-b3-iv* *fn-ptx-wexp* 0 prefix 0) nil)
    nil))

; While hashing: the message is octets, its head is the frame header of its length and the chain
; field, and the held stack is the digest's state over the octets absorbed.
(defun fn-ptx-hash-invp (m id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((w (fn-ptx-message m id inc fn-rtc-st)) (hs (fn-ptx-hs m)))
    (and (fn-cbor-octet-listp w)
         (equal (take (fn-ptx-head-len) w)
                (append (fn-ptx-frame-header (- (len w) (fn-ptx-head-len))) (fn-ptx-kd-last (fn-ptx-kd m))))
         (equal (fn-rtc-get 1 hs) (fn-ptx-stack-of (take (nfix (fn-rtc-get 0 hs)) w))))))

; -----------------------------------------------------------------------------
; The map: the fn-ptd inputs one machine step gives.  R is the record read after the step; FO the
; host's outcome of a failed log action (any value but :ok; the trace supplies it).
(defun fn-ptx-ptd-ins (m ev m2 r fo)
  (let ((ph (fn-ptx-ph m)) (kind (fn-rtc-get 0 ev)) (ph2 (fn-ptx-ph m2))
        (bad (if (equal fo :ok) :eio fo)))
    (cond ((and (eq ph :hashing) (member-eq ph2 '(:extending :payload-writing))) (list (list :begin r)))
          ((and (eq ph :extending) (eq kind :extend))
           (list (cons :pwrite (if (eq ph2 :extsyncing) :ok bad))))
          ((and (eq ph :extsyncing) (eq kind :fsync))
           (list (cons :fsync (if (eq ph2 :payload-writing) :ok bad))))
          ((and (eq ph :payload-writing) (eq kind :pwrite))
           (if (eq ph2 :fenced) (list (cons :pwrite bad)) nil))
          ((and (eq ph :log-writing) (eq kind :pwrite))
           (list (cons :pwrite (if (eq ph2 :committing) :ok bad))))
          ((and (eq ph :committing) (eq kind :fsync))
           (list (cons :fsync (if (fn-ptx-committedp m2) :ok bad))))
          (t nil))))

; -----------------------------------------------------------------------------
; The relation.  Phases map; at rest the kernel projection is the driver kernel's, which has no
; batch, nothing in flight and no fault (fn-ptd-begin's take and append need all three), and while
; hashing the digest's state is the message's; in flight the projection is the kernel's before the
; take (one txid less), the extents agree, the driver's record is the machine's, and the message
; with the padding is the driver's entry.
(defun fn-ptx-ptd-phase (ph)
  (case ph ((:idle :reading :hashing) :ready) (:extending :extending) (:extsyncing :extsyncing)
    ((:payload-writing :log-writing) :writing) (:committing :syncing) (:fenced :fenced) (otherwise nil)))
(defun fn-ptx-kd-before-take (ks)
  (fn-ptx-kd-mk (len (fn-lgk-committed ks)) (fn-lgk-last ks) (fn-lgk-frontier ks)
                (- (fn-lgk-next-txid ks) 1) (fn-lgk-acked ks)))
(defun fn-ptx-simp (m ptd id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((ph (fn-ptx-ph m)) (pph (fn-ptd-ph ptd)) (ks (fn-ptd-ks ptd)))
    (and (equal pph (fn-ptx-ptd-phase ph))
         (case pph
           (:ready (and (equal (fn-ptx-kd m) (fn-ptx-kd-of ks))
                        (equal (fn-ptd-ext ptd) (fn-ptx-ext m))
                        (not (consp (fn-lgk-batch ks))) (not (consp (fn-lgk-inflight ks)))
                        (not (equal (fn-lgk-phase ks) :fault))
                        (implies (equal ph :hashing) (fn-ptx-hash-invp m id inc fn-rtc-st))))
           (:fenced t)
           (otherwise
            (let ((w (fn-ptx-message m id inc fn-rtc-st)))
              (and (equal (fn-ptx-kd m) (fn-ptx-kd-before-take ks))
                   (equal (fn-ptd-ext ptd) (fn-ptx-ext m))
                   (equal (fn-ptd-nxt ptd) (fn-ptx-nxt m))
                   (equal (fn-ptd-rec ptd) (fn-ptx-record m id inc fn-rtc-st))
                   (equal (append w (fn-bs-zeros (nfix (fn-rtc-get 2 (fn-ptx-hs m)))))
                          (fn-lg-log (list (fn-ptd-rec ptd)) (fn-lgk-last ks) (fn-ptx-unit m))))))))))

; The rely (the environment's side): across a step into the hashing phase the message is octets
; and its head reads back as written (the frame header of its length, the chain field); across a
; step within the hashing phase, or within the log phases, the message is unchanged; across the
; step that ends the hashing, the message gains exactly its trailer.
(defun fn-ptx-in-flight-p (ph) (member-eq ph '(:extending :extsyncing :payload-writing :log-writing :committing)))
(defun-nx fn-ptx-rely (m m2 id inc st st2)
  (let ((ph (fn-ptx-ph m)) (ph2 (fn-ptx-ph m2)))
    (and (implies (and (equal ph2 :hashing) (not (equal ph :hashing)))
                  (let ((w2 (fn-ptx-message m2 id inc st2)))
                    (and (fn-cbor-octet-listp w2)
                         (equal (take (fn-ptx-head-len) w2)
                                (append (fn-ptx-frame-header (- (len w2) (fn-ptx-head-len)))
                                        (fn-ptx-kd-last (fn-ptx-kd m2)))))))
         (implies (and (equal ph2 :hashing) (equal ph :hashing))
                  (equal (fn-ptx-message m2 id inc st2) (fn-ptx-message m id inc st)))
         (implies (fn-ptx-in-flight-p ph2)
                  (if (fn-ptx-in-flight-p ph)
                      (equal (fn-ptx-message m2 id inc st2) (fn-ptx-message m id inc st))
                    (equal (fn-ptx-message m2 id inc st2)
                           (append (fn-ptx-message m id inc st) (fn-rtc-get 1 (fn-ptx-hs m2)))))))))

; The answer a machine step gives its current post, against the driver's.
(defun fn-ptx-code-of-ptd (ans)
  (and (consp ans) (case (car (car ans)) (:posted 0) (:refused 1) (:uncertain 2) (otherwise nil))))

; P4-1, the simulation step: from a related state, the driver stepped on the mapped inputs stays
; related, and an answer the driver gives is the machine's to its current post, for the same record.
(defun-nx fn-ptx-p4-1 (m ptd ev st st2 q fo ino id inc)
  (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
    (declare (ignore c))
    (mv-let (ptd2 acts ans ops)
        (fn-ptd-run ptd (fn-ptx-ptd-ins m ev m2 (fn-ptx-record m2 id inc st2) fo)
                    ino (fn-ptx-unit m) (fn-ptx-fmax m))
      (declare (ignore acts ops))
      (implies (and (fn-ptx-okp m) (not (equal (fn-ptx-ph m) :closed))
                    (fn-ptx-simp m ptd id inc st)
                    (fn-ptx-rely m m2 id inc st st2)
                    (equal (fn-rtc-ev-id ev) id) (equal (fn-rtc-ev-inc ev) inc))
               (and (fn-ptx-simp m2 ptd2 id inc st2)
                    (implies (consp ans)
                             (and (equal (fn-ptx-cur-code m reqs) (fn-ptx-code-of-ptd ans))
                                  (equal (cdr (car ans)) (fn-ptx-record m id inc st)))))))))

; -----------------------------------------------------------------------------
; Traces.  A trace is a list of steps (EV ST Q FO): the event, the machine's view at it (the
; layer's view-state of its slot), the quantum, and the host's outcome were a log action to fail.
; ST2 of a step is the next step's ST (the view at the following event); the last step's is its own.
(defun-nx fn-ptx-trace-run (m trace id inc)
  (declare (xargs :measure (len trace) :hints (("Goal" :in-theory (disable fn-ptx-step)))))
  ; (mv m-final ptd-inputs posted-records): the records of the machine's answers of code 0, in order
  (if (atom trace)
      (mv m nil nil)
    (let* ((x (car trace)) (ev (nth 0 x)) (st (nth 1 x)) (q (nth 2 x)) (fo (nth 3 x))
           (st2 (if (consp (cdr trace)) (nth 1 (cadr trace)) st)))
      (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
        (declare (ignore c))
        (mv-let (mf ins posted) (fn-ptx-trace-run m2 (cdr trace) id inc)
          (mv mf
              (append (fn-ptx-ptd-ins m ev m2 (fn-ptx-record m2 id inc st2) fo) ins)
              (if (equal (fn-ptx-cur-code m reqs) 0)
                  (cons (fn-ptx-record m id inc st) posted)
                posted)))))))
(defun-nx fn-ptx-trace-relies-p (m trace id inc)
  (declare (xargs :measure (len trace) :hints (("Goal" :in-theory (disable fn-ptx-step fn-ptx-rely)))))
  ; the rely at every step, and every event the machine's own slot's
  (if (atom trace) t
    (let* ((x (car trace)) (ev (nth 0 x)) (st (nth 1 x)) (q (nth 2 x))
           (st2 (if (consp (cdr trace)) (nth 1 (cadr trace)) st))
           (m2 (mv-nth 0 (fn-ptx-step m ev st q))))
      (and (equal (fn-rtc-ev-id ev) id) (equal (fn-rtc-ev-inc ev) inc)
           (fn-ptx-rely m m2 id inc st st2)
           (fn-ptx-trace-relies-p m2 (cdr trace) id inc)))))

; P4-2 (KEYSTONE, AckEligible => DurableCommitEvidence for the machine): from the machine the open
; admits over L's open (KS0 related to BS), along any trace that keeps the rely, the records the
; machine answered :posted are exactly fn-ptd's posted records over the mapped inputs, in order.
;   (implies (and (fn-lgk-relp bs ks0 ino genesis max) (fn-ptd-open-kernelp ks0)
;                 (not (equal (fn-lgk-phase ks0) :fault))
;                 (equal ext (len (fn-bs-durable-content bs ino)))
;                 (equal geo (list (fn-bs-unit bs) max hmax))
;                 (fn-ptx-okp (fn-ptx-opened (fn-ptx-kd-of ks0) ext geo))
;                 (fn-ptx-trace-relies-p (fn-ptx-opened (fn-ptx-kd-of ks0) ext geo) trace id inc))
;            (mv-let (mf ins posted) (fn-ptx-trace-run (fn-ptx-opened (fn-ptx-kd-of ks0) ext geo) trace id inc)
;              (declare (ignore mf))
;              (equal posted
;                     (fn-ptd-posted (mv-nth 2 (fn-ptd-run (fn-ptd-init ks0 ext) ins ino (fn-bs-unit bs) max))))))
