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
; batch, nothing in flight and no fault (fn-ptd-begin's take and append need all three) and has
; acknowledged every committed record (the commit's acknowledgement counts one), and while
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
                        (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                        (true-listp (fn-lgk-committed ks))
                        (implies (equal ph :hashing) (fn-ptx-hash-invp m id inc fn-rtc-st))))
           (:fenced t)
           (otherwise
            (let ((w (fn-ptx-message m id inc fn-rtc-st)))
              (and (equal (fn-ptx-kd m) (fn-ptx-kd-before-take ks))
                   (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                   (true-listp (fn-lgk-committed ks))
                   (<= 1 (fn-lgk-next-txid ks))
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

; -----------------------------------------------------------------------------
; Proofs (Builder P): the message, the digest's held state, the trailer and the entry.
; The held stack over whole windows is the binary-counter stack of their subtree outputs
; (fn-ptx-absorb-is-the-stack), the trailer is BLAKE3 of the message
; (fn-ptx-trailer-is-the-digest), and the message with its trailer and padding is the log of
; its record (fn-ptx-entry-of-message).
(defthm fn-ptx-len-of-msg-range (equal (len (fn-ptx-msg-range i n spans id inc st)) (nfix n)))
(defun fn-ptx-mr-ind (i a n)
  (if (zp a) (list i n) (fn-ptx-mr-ind (+ 1 (nfix i)) (- a 1) (- (nfix n) 1))))
(defthm fn-ptx-nthcdr-of-msg-range
  (implies (and (natp i) (natp a) (<= a (nfix n)))
           (equal (nthcdr a (fn-ptx-msg-range i n spans id inc st))
                  (fn-ptx-msg-range (+ i a) (- (nfix n) a) spans id inc st)))
  :hints (("Goal" :induct (fn-ptx-mr-ind i a n) :in-theory (disable fn-ptx-msg-byte))))
(defthm fn-ptx-take-of-msg-range
  (implies (and (natp a) (<= a (nfix n)))
           (equal (take a (fn-ptx-msg-range i n spans id inc st))
                  (fn-ptx-msg-range i a spans id inc st)))
  :hints (("Goal" :induct (fn-ptx-mr-ind i a n) :in-theory (disable fn-ptx-msg-byte))))
(defun fn-ptx-tps-ind (a w) (if (zp a) w (fn-ptx-tps-ind (- a 1) (cdr w))))
(defthm fn-ptx-take-plus-split
  (implies (and (natp a) (natp b) (<= (+ a b) (len w)))
           (equal (take (+ a b) w) (append (take a w) (take b (nthcdr a w)))))
  :hints (("Goal" :induct (fn-ptx-tps-ind a w))))
(defthm fn-ptx-stack-of-append-window
  (implies (and (true-listp p) (consp p) (posp j) (equal (len p) (* 1024 j))
                (consp x) (<= (len x) 1024))
           (equal (fn-ptx-stack-of (append p x))
                  (fn-b3-cv-push *fn-b3-iv* 0 0 (fn-b3-node *fn-b3-iv* x j 0) (fn-ptx-stack-of p))))
  :hints (("Goal" :use ((:instance fn-b3-window-outs-of-append-window
                                   (key *fn-b3-iv*) (k 0) (base 0) (prefix p) (w x) (flags 0)))
                  :in-theory (disable fn-b3-window-outs fn-b3-node fn-b3-cv-push)
                  :expand ((fn-ptx-stack-of p) (fn-ptx-stack-of (append p x))))))
(defthm fn-ptx-stack-of-first-window
  (implies (and (consp x) (<= (len x) 1024))
           (equal (fn-ptx-stack-of x)
                  (fn-b3-cv-push *fn-b3-iv* 0 0 (fn-b3-node *fn-b3-iv* x 0 0) nil)))
  :hints (("Goal" :expand ((fn-b3-window-outs *fn-b3-iv* 0 0 x 0)
                           (fn-b3-stack-push-all *fn-b3-iv* 0 0 (list (fn-b3-node *fn-b3-iv* x 0 0)) nil))
                  :in-theory (disable fn-b3-node fn-b3-cv-push))))
(defthm fn-ptx-consp-take
  (equal (consp (take n w)) (not (zp n))))
(defthm fn-ptx-stack-of-push-window
  (implies (and (natp j) (<= (+ (* 1024 j) 1024) (len w)))
           (equal (fn-ptx-stack-of (take (+ (* 1024 j) 1024) w))
                  (fn-b3-cv-push *fn-b3-iv* 0 0
                                 (fn-b3-node *fn-b3-iv* (take 1024 (nthcdr (* 1024 j) w)) j 0)
                                 (fn-ptx-stack-of (take (* 1024 j) w)))))
  :hints (("Goal" :cases ((equal j 0)) :do-not-induct t
                  :in-theory (disable fn-b3-node fn-b3-cv-push fn-ptx-stack-of fn-ptx-take-plus-split
                                      fn-b3-node-splits-at-left-chunks))
          ("Subgoal 2" :use ((:instance fn-ptx-take-plus-split (a (* 1024 j)) (b 1024))
                             (:instance fn-ptx-stack-of-append-window (p (take (* 1024 j) w))
                                        (x (take 1024 (nthcdr (* 1024 j) w))))))
          ("Subgoal 1" :use ((:instance fn-ptx-stack-of-first-window (x (take 1024 w)))))))
(defun fn-ptx-abs-ind (nw j n stk)
  (if (or (zp nw) (<= (nfix n) (+ (* 1024 (nfix j)) 1024)))
      (list stk)
    (fn-ptx-abs-ind (- nw 1) (+ 1 (nfix j)) n stk)))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-floor-1024-j
    (implies (natp j) (equal (floor (* 1024 j) 1024) j)))
  (defthm fn-ptx-mod-1024-j
    (implies (natp j) (equal (mod (* 1024 j) 1024) 0))))
(defthm fn-ptx-absorb-is-the-stack
  (implies (and (natp j) (natp n) (<= (* 1024 j) n))
           (let ((r (fn-ptx-absorb nw (* 1024 j)
                                   (fn-ptx-stack-of (take (* 1024 j) (fn-ptx-msg-range 0 n spans id inc st)))
                                   n spans id inc st)))
             (and (equal (mv-nth 1 r)
                         (fn-ptx-stack-of (take (mv-nth 0 r) (fn-ptx-msg-range 0 n spans id inc st))))
                  (natp (mv-nth 0 r))
                  (equal (mod (mv-nth 0 r) 1024) 0)
                  (<= (* 1024 j) (mv-nth 0 r))
                  (implies (< (* 1024 j) n) (< (mv-nth 0 r) n)))))
  :hints (("Goal" :induct (fn-ptx-abs-ind nw j n stk)
                  :in-theory (disable fn-b3-node fn-b3-cv-push fn-ptx-stack-of fn-ptx-take-plus-split
                                      fn-b3-node-splits-at-left-chunks fn-ptx-msg-range))
          ("Subgoal *1/2" :expand ((fn-ptx-absorb nw (* 1024 j)
                                   (fn-ptx-stack-of (take (* 1024 j) (fn-ptx-msg-range 0 n spans id inc st)))
                                   n spans id inc st))
                          :use ((:instance fn-ptx-stack-of-push-window (w (fn-ptx-msg-range 0 n spans id inc st)))))
          ("Subgoal *1/1" :expand ((fn-ptx-absorb nw (* 1024 j)
                                   (fn-ptx-stack-of (take (* 1024 j) (fn-ptx-msg-range 0 n spans id inc st)))
                                   n spans id inc st)))))
(defthm fn-ptx-cbor-octets-are-b3-octets
  (implies (fn-cbor-octet-listp x) (fn-b3-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-b3-octet-listp))))
(defthm fn-ptx-b3-octets-take
  (implies (and (fn-b3-octet-listp x) (<= (nfix n) (len x))) (fn-b3-octet-listp (take n x)))
  :hints (("Goal" :in-theory (enable fn-b3-octet-listp))))
(defthm fn-ptx-b3-octets-nthcdr
  (implies (fn-b3-octet-listp x) (fn-b3-octet-listp (nthcdr n x)))
  :hints (("Goal" :in-theory (enable fn-b3-octet-listp))))
(defthm fn-ptx-b3-octets-true-listp
  (implies (fn-b3-octet-listp x) (true-listp x))
  :hints (("Goal" :in-theory (enable fn-b3-octet-listp)))
  :rule-classes :forward-chaining)
(defthm fn-ptx-fold-of-single
  (equal (fn-b3-stack-fold key flags (fn-b3-cv-push key flags h x nil)) x)
  :hints (("Goal" :in-theory (enable fn-b3-stack-fold fn-b3-stack-spine fn-b3-cv-push fn-b3-nthx))))
(defthm fn-ptx-append-take-nthcdr
  (implies (and (natp n) (<= n (len w))) (equal (append (take n w) (nthcdr n w)) w))
  :hints (("Goal" :induct (fn-ptx-tps-ind n w))))
(defthm fn-ptx-digest-of-held-state
  (implies (and (fn-b3-octet-listp w) (natp j) (< (* 1024 j) (len w)) (<= (len w) (+ (* 1024 j) 1024)))
           (equal (fn-b3-output-root
                   (fn-b3-stack-fold *fn-b3-iv* 0
                                     (fn-b3-cv-push *fn-b3-iv* 0 0
                                                    (fn-b3-node *fn-b3-iv* (nthcdr (* 1024 j) w) j 0)
                                                    (fn-ptx-stack-of (take (* 1024 j) w)))))
                  (fn-blake3 w)))
  :hints (("Goal" :cases ((equal j 0)) :do-not-induct t
                  :in-theory (e/d (fn-blake3 fn-b3-hash)
                                  (fn-b3-node fn-b3-cv-push fn-ptx-stack-of fn-ptx-take-plus-split
                                   fn-b3-node-splits-at-left-chunks fn-b3-stack-fold fn-b3-output-root floor)))
          ("Subgoal 2" :use ((:instance fn-b3-append-window
                                        (key *fn-b3-iv*) (flags 0) (k 0) (counter 0)
                                        (prefix (take (* 1024 j) w)) (w (nthcdr (* 1024 j) w)))
                             (:instance fn-ptx-append-take-nthcdr (n (* 1024 j))))
                       :expand ((fn-ptx-stack-of (take (* 1024 j) w))))
          ("Subgoal 1" :expand ((fn-ptx-stack-of nil)) :in-theory (e/d (fn-blake3 fn-b3-hash fn-b3-stack-fold fn-b3-stack-spine fn-b3-nthx) (fn-b3-node fn-b3-output-root)))))
(defthm fn-ptx-trailer-is-the-digest
  (implies (and (natp j) (natp n) (< (* 1024 j) n) (<= n (+ (* 1024 j) 1024))
                (fn-cbor-octet-listp (fn-ptx-msg-range 0 n spans id inc st)))
           (equal (fn-ptx-finish-digest (* 1024 j)
                                        (fn-ptx-stack-of (take (* 1024 j) (fn-ptx-msg-range 0 n spans id inc st)))
                                        n spans id inc st)
                  (fn-blake3 (fn-ptx-msg-range 0 n spans id inc st))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-ptx-digest-of-held-state (w (fn-ptx-msg-range 0 n spans id inc st)))
                        (:instance fn-ptx-nthcdr-of-msg-range (i 0) (a (* 1024 j))))
                  :in-theory (e/d (fn-ptx-finish-digest)
                                  (fn-b3-node fn-b3-cv-push fn-ptx-stack-of fn-ptx-take-plus-split fn-ptx-take-of-msg-range
                                   fn-b3-node-splits-at-left-chunks fn-b3-stack-fold fn-b3-output-root floor
                                   fn-ptx-msg-range fn-ptx-nthcdr-of-msg-range fn-blake3)))))
(defthm fn-ptx-head-len-value (equal (fn-ptx-head-len) 42)
  :hints (("Goal" :in-theory (enable fn-ptx-head-len fn-ptx-frame-header fn-frame-header fn-cbor-u32-bytes))))
(defthm fn-ptx-frame-of-parts
  (implies (and (true-listp r) (true-listp last) (equal (len last) 32))
           (equal (fn-lg-frame last (list r))
                  (append (fn-ptx-frame-header (len r)) last r
                          (fn-blake3 (append (fn-ptx-frame-header (len r)) last r)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-lg-frame fn-lg-frame-kind fn-lg-frame-body fn-frame-seal fn-frame-encode
                                   fn-frame-protected fn-ptx-frame-header fn-frame-digest)
                                  (fn-blake3 fn-frame-header)))))
(defthm fn-ptx-w-is-head-and-rest
  (implies (and (<= 42 (len w)) (equal (take 42 w) x))
           (equal (append x (nthcdr 42 w)) w))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ptx-append-take-nthcdr (n 42))) :in-theory (disable fn-ptx-append-take-nthcdr fn-rtc-append-take-nthcdr))))
(defthm fn-ptx-append3-then
  (implies (equal (append a b c) w) (equal (append a b c d) (append w d)))
  :rule-classes nil)
(defthm fn-ptx-frame-of-message
  (implies (and (true-listp w) (<= 42 (len w)) (true-listp last) (equal (len last) 32)
                (equal (take 42 w) (append (fn-ptx-frame-header (- (len w) 42)) last)))
           (equal (fn-lg-frame last (list (nthcdr 42 w)))
                  (append w (fn-blake3 w))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-ptx-w-is-head-and-rest (x (append (fn-ptx-frame-header (- (len w) 42)) last)))
                        (:instance fn-ptx-frame-of-parts (r (nthcdr 42 w)))
                        (:instance fn-ptx-append3-then (a (fn-ptx-frame-header (- (len w) 42))) (b last) (c (nthcdr 42 w)) (d (fn-blake3 w))))
                  :in-theory (e/d () (fn-blake3 fn-ptx-append-take-nthcdr fn-ptx-frame-of-parts fn-frame-header
                                      fn-ptx-frame-header fn-lg-frame fn-rtc-append-take-nthcdr)))))
(defthm fn-ptx-log-of-one
  (equal (fn-lg-log (list r) last unit) (fn-lg-entry last (list r) unit))
  :hints (("Goal" :expand ((fn-lg-log (list r) last unit))
                  :in-theory (e/d (fn-lg-chunk-len fn-lg-fit-count fn-bs-take) (fn-lg-entry fn-lg-frame)))))
(defthm fn-ptx-entry-of-message
  (implies (and (true-listp w) (<= 42 (len w)) (true-listp last) (equal (len last) 32)
                (equal (take 42 w) (append (fn-ptx-frame-header (- (len w) 42)) last))
                (equal (len (fn-blake3 w)) 32))
           (equal (append w (fn-blake3 w) (fn-bs-zeros (fn-lg-pad-len (+ (len w) 32) unit)))
                  (fn-lg-log (list (nthcdr 42 w)) last unit)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-ptx-frame-of-message))
                  :in-theory (e/d (fn-lg-entry) (fn-blake3 fn-lg-frame fn-ptx-frame-of-message fn-ptx-frame-header fn-lg-pad-len fn-bs-zeros)))))
(defthm fn-ptx-take-is-prepare
  (implies (not (equal (fn-lgk-phase ks) :fault))
           (equal (fn-lgk-host-step ks (fn-ptd-take-op ks r unit)) (fn-lgk-prepare ks r)))
  :hints (("Goal" :in-theory (e/d (fn-lgk-host-step fn-olr-take fn-ptd-take-op) (fn-lgk-prepare)))))
(defthm fn-ptx-prepare-fields
  (implies (not (equal (fn-lgk-phase ks) :fault))
           (let ((ks1 (fn-lgk-prepare ks r)))
             (and (equal (fn-lgk-last ks1) (fn-lgk-last ks))
                  (equal (fn-lgk-frontier ks1) (fn-lgk-frontier ks))
                  (equal (fn-lgk-committed ks1) (fn-lgk-committed ks))
                  (equal (fn-lgk-acked ks1) (fn-lgk-acked ks))
                  (equal (fn-lgk-next-txid ks1) (+ 1 (fn-lgk-next-txid ks)))
                  (equal (fn-lgk-batch ks1) (append (true-list-fix (fn-lgk-batch ks)) (list r)))
                  (equal (fn-lgk-inflight ks1) (fn-lgk-inflight ks))
                  (equal (fn-lgk-phase ks1) (fn-lgk-phase ks)))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-prepare) (fn-lgk-make fn-lgk-last fn-lgk-frontier fn-lgk-committed fn-lgk-acked
                                                    fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-phase)))))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-extension-target-bounds
    (implies (and (fn-olr-extension-needed-p front e ext unit) (posp unit) (natp front) (natp e) (natp ext))
             (and (< ext (fn-olr-extension-target front e ext unit))
                  (<= (+ front e) (fn-olr-extension-target front e ext unit))
                  (natp (fn-olr-extension-target front e ext unit))))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable fn-olr-extension-needed-p fn-olr-extension-target)))))
(defthm fn-ptx-no-extension-fits
  (implies (and (not (fn-olr-extension-needed-p front e ext unit)) (natp front) (natp e) (natp ext))
           (<= (+ front e) ext))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-olr-extension-needed-p))))
(defthm fn-ptx-ptd-begin-takes
  (implies (and (equal (fn-ptd-ph st) :ready)
                (not (consp (fn-lgk-batch (fn-ptd-ks st))))
                (not (consp (fn-lgk-inflight (fn-ptd-ks st))))
                (not (equal (fn-lgk-phase (fn-ptd-ks st)) :fault))
                (fn-lg-recordp r max) (posp unit))
           (let* ((ks (fn-ptd-ks st)) (ext (fn-ptd-ext st))
                  (ks1 (fn-lgk-prepare ks r))
                  (e (len (fn-lg-log (list r) (fn-lgk-last ks) unit)))
                  (tk (fn-ptd-take-op ks r unit)))
             (equal (fn-ptd-begin st r ino unit max)
                    (if (fn-olr-extension-needed-p (fn-lgk-frontier ks) e ext unit)
                        (let ((nxt (fn-olr-extension-target (fn-lgk-frontier ks) e ext unit)))
                          (mv (fn-ptd-mk :extending ks1 r ext nxt)
                              (list (list :pwrite ino ext (fn-bs-zeros (- nxt ext)))) nil (list tk)))
                      (mv (fn-ptd-mk :writing ks1 r ext ext)
                          (list (fn-ptd-record-write ks1 ino unit)) nil (list tk))))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-ptx-extension-target-bounds (front (fn-lgk-frontier (fn-ptd-ks st))) (e (len (fn-lg-log (list r) (fn-lgk-last (fn-ptd-ks st)) unit))) (ext (fn-ptd-ext st)))
                        (:instance fn-ptx-no-extension-fits (front (fn-lgk-frontier (fn-ptd-ks st))) (e (len (fn-lg-log (list r) (fn-lgk-last (fn-ptd-ks st)) unit))) (ext (fn-ptd-ext st))))
                  :in-theory (e/d (fn-ptd-begin fn-lgk-sealed-extent fn-lgk-append-octets fn-lg-append-admitsp fn-lgk-fitsp
                                   fn-lgu-take-verdict)
                                  (fn-olr-extension-needed-p fn-olr-extension-target fn-lg-log fn-ptx-log-of-one fn-lg-entry fn-lg-pad-len fn-ptd-record-write fn-bs-zeros fn-lg-recordp fn-lgk-prepare fn-ptd-take-op
                                   fn-lgk-host-step fn-lgk-make fn-lgk-last fn-lgk-frontier fn-lgk-committed fn-lgk-acked
                                   fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-phase fn-ptd-ks fn-ptd-ph fn-ptd-ext)))))
(defthm fn-ptx-last-trailer-of-one
  (equal (fn-lg-last-trailer (list r) last) (fn-lg-trailer (fn-lg-frame last (list r))))
  :hints (("Goal" :expand ((fn-lg-last-trailer (list r) last))
                  :in-theory (e/d (fn-lg-chunk-len fn-lg-fit-count fn-bs-take) (fn-lg-trailer fn-lg-frame)))))
(defthm fn-ptx-trailer-of-message-frame
  (implies (and (true-listp w) (<= 42 (len w)) (true-listp last) (equal (len last) 32)
                (equal (take 42 w) (append (fn-ptx-frame-header (- (len w) 42)) last)))
           (equal (fn-lg-last-trailer (list (nthcdr 42 w)) last) (fn-blake3 w)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-ptx-frame-of-message))
                  :in-theory (e/d (fn-lg-trailer) (fn-blake3 fn-lg-frame fn-ptx-frame-of-message fn-ptx-frame-header)))))
(defthm fn-ptx-commit-is-the-kernel-commit
  (implies (and (equal (fn-lgk-inflight ks) (list r))
                (true-listp (fn-lgk-committed ks))
                (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (<= 1 (fn-lgk-next-txid ks))
                (equal trailer (fn-lg-last-trailer (list r) (fn-lgk-last ks)))
                (equal elen (len (fn-lg-log (list r) (fn-lgk-last ks) unit))))
           (equal (fn-ptx-kd-commit (fn-ptx-kd-before-take ks) trailer elen)
                  (fn-ptx-kd-of (fn-lgk-finish-one (fn-lgk-fence ks unit)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-lgk-fence fn-lgk-finish-one fn-ptx-kd-commit fn-ptx-kd-before-take fn-ptx-kd-of
                                   fn-ptx-kd-mk fn-ptx-kd-count fn-ptx-kd-frontier fn-ptx-kd-txid fn-ptx-kd-acked)
                                  (fn-lg-log fn-ptx-log-of-one fn-lg-last-trailer fn-lgk-make fn-lgk-last fn-lgk-frontier
                                   fn-lgk-committed fn-lgk-acked fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-phase)))))
