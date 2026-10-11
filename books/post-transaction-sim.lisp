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
(set-verify-guards-eagerness 0)
; The proofs below run in the machine's theory as of its P5 statement: the machine book's later
; proof lemmas (P0, P3) and the crash book's rules stay disabled here unless a hint names them.
(local (in-theory (current-theory 'fn-ptx-p5)))

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

; While hashing: the message is octets, holds its whole head, which is the frame header of its
; length and the chain field, and the held stack is the digest's state over the octets absorbed.
(defun fn-ptx-hash-invp (m id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((w (fn-ptx-message m id inc fn-rtc-st)) (hs (fn-ptx-hs m)))
    (and (fn-cbor-octet-listp w)
         (<= (fn-ptx-head-len) (len w))
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
; take (one txid less), the extents agree, the driver's record is the machine's, the message
; with the padding is the driver's entry, and the kernel holds the record as the driver's
; invariant fn-ptd-invp has it: before the seal the batch is the record, nothing is in flight and
; the append admits it (so the kernel is not faulted); after the seal the record is in flight
; and the kernel is :appended; and the trailer the machine holds is the chain's trailer of the
; record (the commit makes it the chain head).  (Restated from Sonnet 6's counterexample: a held
; trailer other than the digest is otherwise related, and the commit then diverges from the fence.)  (Restated from the counterexample of a driver at :writing over a
; kernel with an empty batch: its two :ok completions answer :posted and commit nothing, while
; the machine commits the record.)
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
                   (equal (fn-rtc-get 1 (fn-ptx-hs m)) (fn-lg-last-trailer (list (fn-ptd-rec ptd)) (fn-lgk-last ks)))
                   (equal (append w (fn-bs-zeros (nfix (fn-rtc-get 2 (fn-ptx-hs m)))))
                          (fn-lg-log (list (fn-ptd-rec ptd)) (fn-lgk-last ks) (fn-ptx-unit m)))
                   (if (equal pph :syncing)
                       (and (equal (fn-lgk-phase ks) :appended)
                            (equal (fn-lgk-inflight ks) (list (fn-ptd-rec ptd)))
                            (not (consp (fn-lgk-batch ks))))
                     (and (equal (fn-lgk-batch ks) (list (fn-ptd-rec ptd)))
                          (fn-lg-append-admitsp ks (fn-ptx-unit m) (fn-ptd-nxt ptd)))))))))))

; The rely (the environment's side): across a step into the hashing phase the message is octets
; and its head reads back as written (all of it: the frame header of its length, the chain field); across a
; step within the hashing phase, or within the log phases, the message is unchanged; across the
; step that ends the hashing, the message gains exactly its trailer.
(defun fn-ptx-in-flight-p (ph) (member-eq ph '(:extending :extsyncing :payload-writing :log-writing :committing)))
(defun-nx fn-ptx-rely (m m2 id inc st st2)
  (let ((ph (fn-ptx-ph m)) (ph2 (fn-ptx-ph m2)))
    (and (implies (and (equal ph2 :hashing) (not (equal ph :hashing)))
                  (let ((w2 (fn-ptx-message m2 id inc st2)))
                    (and (fn-cbor-octet-listp w2)
                         (<= (fn-ptx-head-len) (len w2))
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
  (declare (xargs :measure (len trace) :hints (("Goal" :in-theory (union-theories '(len o< o-finp o-p natp (:type-prescription len) (:compound-recognizer natp-compound-recognizer)) (theory 'minimal-theory))))))
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
  (declare (xargs :measure (len trace) :hints (("Goal" :in-theory (union-theories '(len o< o-finp o-p natp (:type-prescription len) (:compound-recognizer natp-compound-recognizer)) (theory 'minimal-theory))))))
  ; the rely at every step, and every event the machine's own slot's
  (if (atom trace) t
    (let* ((x (car trace)) (ev (nth 0 x)) (st (nth 1 x)) (q (nth 2 x))
           (st2 (if (consp (cdr trace)) (nth 1 (cadr trace)) st))
           (m2 (mv-nth 0 (fn-ptx-step m ev st q))))
      (and (equal (fn-rtc-ev-id ev) id) (equal (fn-rtc-ev-inc ev) inc)
           (fn-ptx-rely m m2 id inc st st2)
           (fn-ptx-trace-relies-p m2 (cdr trace) id inc)))))

; The kernel the open hands the machine: L's open kernel (no batch, nothing in flight, every
; committed record acknowledged) that is not faulted.  The open's kernel is one
; (fn-ptx-open-kernelp-of-the-open: fn-lgk-recover leaves :ready), and the relation carries
; "not faulted" through every phase but :fenced (fn-ptx-related-kernel-is-faulted-only-fenced), so
; the machine is never stepped against a faulted kernel.  Without it P4-2 is false: a kernel in
; :fault with no batch is fn-ptd-open-kernelp and R-related to the same store (neither reads the
; phase), fn-ptd-begin refuses its take, and the machine, whose projection fn-ptx-kd-of reads no
; phase, posts.
(defun fn-ptx-open-kernelp (ks)
  (and (fn-ptd-open-kernelp ks) (not (equal (fn-lgk-phase ks) :fault))))

; P4-2 (KEYSTONE, AckEligible => DurableCommitEvidence for the machine): from the machine the open
; admits over L's open (KS0 related to BS), along any trace that keeps the rely, the records the
; machine answered :posted are exactly fn-ptd's posted records over the mapped inputs, in order.
;   (implies (and (fn-lgk-relp bs ks0 ino genesis max) (fn-ptx-open-kernelp ks0)
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

; The open's kernel is not faulted, and a related kernel is faulted only when the machine is
; :fenced: the machine is never stepped against a faulted kernel.
(defthm fn-ptx-open-kernelp-of-the-open
  (fn-ptx-open-kernelp (fn-lgt-recover c genesis unit max floor))
  :hints (("Goal" :use ((:instance fn-ptd-open-kernelp-of-the-open))
                  :in-theory (e/d (fn-lgt-recover fn-lgk-recover)
                                  (fn-ptd-open-kernelp fn-lg-scan fn-lg-scan-last fn-lgt-next-after)))))
(defthm fn-ptx-related-kernel-is-faulted-only-fenced
  (implies (and (fn-ptx-simp m ptd id inc st) (not (equal (fn-ptx-ph m) :fenced)))
           (not (equal (fn-lgk-phase (fn-ptd-ks ptd)) :fault)))
  :hints (("Goal" :in-theory (e/d (fn-ptx-simp fn-ptx-ptd-phase fn-lg-append-admitsp)
                                  (fn-ptx-message fn-ptx-record fn-ptx-hash-invp fn-lg-log fn-bs-zeros
                                   fn-ptx-kd-of fn-ptx-kd-before-take)))))

; -----------------------------------------------------------------------------
; P4-1 (Builder P, Sonnet 6 and 7): the simulation step, by arms of the machine's step.
; The lemmas run in the theory the book opens with; each arm is fn-ptx-p4-1 restricted to one
; phase and event, the top theorem the case split over them.
(defthm fn-ptx-record-frame
  (implies (equal (fn-ptx-message m2 id inc st2) (fn-ptx-message m id inc st))
           (equal (fn-ptx-record m2 id inc st2) (fn-ptx-record m id inc st)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ptx-message) :expand ((fn-ptx-record m2 id inc st2) (fn-ptx-record m id inc st)))))
(defthm fn-ptx-hash-invp-frame
  (implies (and (equal (fn-ptx-message m2 id inc st2) (fn-ptx-message m id inc st))
                (equal (fn-ptx-hs m2) (fn-ptx-hs m)) (equal (fn-ptx-kd m2) (fn-ptx-kd m)))
           (equal (fn-ptx-hash-invp m2 id inc st2) (fn-ptx-hash-invp m id inc st)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ptx-message fn-ptx-hs fn-ptx-kd) :expand ((fn-ptx-hash-invp m2 id inc st2) (fn-ptx-hash-invp m id inc st)))))
(defthm fn-ptx-simp-frame
  (implies (and (equal (fn-ptx-ph m2) (fn-ptx-ph m)) (equal (fn-ptx-kd m2) (fn-ptx-kd m))
                (equal (fn-ptx-ext m2) (fn-ptx-ext m)) (equal (fn-ptx-nxt m2) (fn-ptx-nxt m))
                (equal (fn-ptx-hs m2) (fn-ptx-hs m)) (equal (fn-ptx-geo m2) (fn-ptx-geo m))
                (equal (fn-ptx-message m2 id inc st2) (fn-ptx-message m id inc st)))
           (equal (fn-ptx-simp m2 ptd id inc st2) (fn-ptx-simp m ptd id inc st)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-simp fn-ptx-unit))
           :do-not-induct t
           :use ((:instance fn-ptx-record-frame) (:instance fn-ptx-hash-invp-frame)))))
(defthm fn-ptx-simp-frame-nomsg
  (implies (and (member-eq (fn-ptx-ph m) '(:idle :reading :fenced))
                (equal (fn-ptx-ph m2) (fn-ptx-ph m)) (equal (fn-ptx-kd m2) (fn-ptx-kd m))
                (equal (fn-ptx-ext m2) (fn-ptx-ext m)) (equal (fn-ptx-nxt m2) (fn-ptx-nxt m))
                (equal (fn-ptx-hs m2) (fn-ptx-hs m)) (equal (fn-ptx-geo m2) (fn-ptx-geo m)))
           (equal (fn-ptx-simp m2 ptd id inc st2) (fn-ptx-simp m ptd id inc st)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-simp fn-ptx-unit fn-ptx-ptd-phase member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)))
           :do-not-induct t)))
(defthm fn-ptx-simp-frame-rely
  (implies (and (fn-ptx-okp m) (not (equal (fn-ptx-ph m) :closed))
                (fn-ptx-rely m m2 id inc st st2)
                (equal (fn-ptx-ph m2) (fn-ptx-ph m)) (equal (fn-ptx-kd m2) (fn-ptx-kd m))
                (equal (fn-ptx-ext m2) (fn-ptx-ext m)) (equal (fn-ptx-nxt m2) (fn-ptx-nxt m))
                (equal (fn-ptx-hs m2) (fn-ptx-hs m)) (equal (fn-ptx-geo m2) (fn-ptx-geo m)))
           (equal (fn-ptx-simp m2 ptd id inc st2) (fn-ptx-simp m ptd id inc st)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-rely fn-ptx-in-flight-p member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart not)))
           :do-not-induct t
           :use ((:instance fn-ptx-okp-wfp) (:instance fn-ptx-wfp-phase)
                 (:instance fn-ptx-simp-frame) (:instance fn-ptx-simp-frame-nomsg)))))
(defthm fn-ptx-nfix-ext (equal (nfix (fn-ptx-ext m)) (fn-ptx-ext m)) :hints (("Goal" :in-theory (enable fn-ptx-ext))))
(defthm fn-ptx-nfix-nxt (equal (nfix (fn-ptx-nxt m)) (fn-ptx-nxt m)) :hints (("Goal" :in-theory (enable fn-ptx-nxt))))
(defthm fn-ptx-ptd-run-nil
  (and (equal (mv-nth 0 (fn-ptd-run st nil ino unit max)) st)
       (equal (mv-nth 1 (fn-ptd-run st nil ino unit max)) nil)
       (equal (mv-nth 2 (fn-ptd-run st nil ino unit max)) nil)
       (equal (mv-nth 3 (fn-ptd-run st nil ino unit max)) nil))
  :hints (("Goal" :in-theory (enable fn-ptd-run))))
(defun fn-ptx-driver-arm (ph kind)
  (or (and (equal ph :extending) (equal kind :extend))
      (and (equal ph :extsyncing) (equal kind :fsync))
      (and (equal ph :payload-writing) (equal kind :pwrite))
      (and (equal ph :log-writing) (equal kind :pwrite))
      (and (equal ph :committing) (equal kind :fsync))))
(defthm fn-ptx-ptd-ins-nil
  (implies (and (equal (fn-ptx-ph m2) (fn-ptx-ph m))
                (not (fn-ptx-driver-arm (fn-ptx-ph m) (fn-rtc-get 0 ev))))
           (equal (fn-ptx-ptd-ins m ev m2 r fo) nil))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-ptd-ins fn-ptx-driver-arm member-equal (:executable-counterpart member-equal))))))
(defthm fn-ptx-m0-fields
  (let ((m0 (fn-ptx-chg m :committed nil)))
    (and (equal (fn-ptx-ph m0) (fn-ptx-ph m)) (equal (fn-ptx-kd m0) (fn-ptx-kd m))
         (equal (fn-ptx-ext m0) (fn-ptx-ext m)) (equal (fn-ptx-nxt m0) (fn-ptx-nxt m))
         (equal (fn-ptx-hs m0) (fn-ptx-hs m)) (equal (fn-ptx-geo m0) (fn-ptx-geo m))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt)))))
(defthm fn-ptx-m0q-fields
  (let ((m0 (fn-ptx-chg (fn-ptx-chg m :committed nil) :q qq)))
    (and (equal (fn-ptx-ph m0) (fn-ptx-ph m)) (equal (fn-ptx-kd m0) (fn-ptx-kd m))
         (equal (fn-ptx-ext m0) (fn-ptx-ext m)) (equal (fn-ptx-nxt m0) (fn-ptx-nxt m))
         (equal (fn-ptx-hs m0) (fn-ptx-hs m)) (equal (fn-ptx-geo m0) (fn-ptx-geo m))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt)))))
(defthm fn-ptx-p4-1-other
  (implies (and (not (member-equal (fn-rtc-get 0 ev) '(:opened :handed :hand)))
                (not (fn-ptx-driver-arm (fn-ptx-ph m) (fn-rtc-get 0 ev)))
                (not (and (equal (fn-ptx-ph m) :reading) (equal (fn-rtc-get 0 ev) :timer)))
                (not (and (equal (fn-ptx-ph m) :hashing) (equal (fn-rtc-get 0 ev) :timer))))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-p4-1 fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-ptd-run-nil fn-ptx-ptd-ins-nil
                      member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart consp)
                      (:executable-counterpart eq) fn-ptx-driver-arm))
           :do-not-induct t
           :use ((:instance fn-ptx-m0-fields)
                 (:instance fn-ptx-simp-frame-rely (m2 (fn-ptx-chg m :committed nil)))))))
(defthm fn-ptx-p4-1-opened-or-hand
  (implies (or (equal (fn-rtc-get 0 ev) :opened) (equal (fn-rtc-get 0 ev) :hand))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-p4-1 fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-ptd-run-nil fn-ptx-ptd-ins-nil
                      member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart consp)
                      (:executable-counterpart eq) fn-ptx-driver-arm))
           :do-not-induct t
           :use ((:instance fn-ptx-m0-fields)
                 (:instance fn-ptx-simp-frame-rely (m2 (fn-ptx-chg m :committed nil)))))))
(defthm fn-ptx-simp-ready-keep
  (implies (and (member-equal (fn-ptx-ph m) '(:idle :reading :hashing))
                (fn-ptx-simp m ptd id inc st)
                (member-equal (fn-ptx-ph m2) '(:idle :reading))
                (equal (fn-ptx-kd m2) (fn-ptx-kd m))
                (equal (fn-ptx-ext m2) (fn-ptx-ext m)))
           (fn-ptx-simp m2 ptd id inc st2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn-ptx-simp fn-ptx-ptd-phase member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)))
           :do-not-induct t)))
(defthm fn-ptx-start-fields
  (let ((m2 (mv-nth 0 (fn-ptx-start p q kd ext geo committed))))
    (and (equal (fn-ptx-ph m2) :reading) (equal (fn-ptx-kd m2) kd) (equal (fn-ptx-ext m2) (nfix ext))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-start-0 fn-ptx-accessors-of-mk)))))
(defthm fn-ptx-ptd-ins-nil2
  (implies (and (not (equal (fn-ptx-ph m) :hashing))
                (not (fn-ptx-driver-arm (fn-ptx-ph m) (fn-rtc-get 0 ev))))
           (equal (fn-ptx-ptd-ins m ev m2 r fo) nil))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-ptd-ins fn-ptx-driver-arm member-equal (:executable-counterpart member-equal))))))
(defthm fn-ptx-p4-1-handed-idle
  (implies (and (equal (fn-rtc-get 0 ev) :handed) (equal (fn-ptx-ph m) :idle))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-p4-1 fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-ptd-run-nil fn-ptx-ptd-ins-nil
                      member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart consp)
                      (:executable-counterpart eq) fn-ptx-driver-arm fn-ptx-start-fields fn-ptx-nfix-ext fn-ptx-ptd-ins-nil2))
           :do-not-induct t
           :use ((:instance fn-ptx-simp-ready-keep (m2 (mv-nth 0 (fn-ptx-start (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev))) nil (fn-ptx-kd m) (fn-ptx-ext m) (fn-ptx-geo m) nil))))))))
(defthm fn-ptx-p4-1-handed-busy
  (implies (and (equal (fn-rtc-get 0 ev) :handed) (not (equal (fn-ptx-ph m) :idle)))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-p4-1 fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-ptd-run-nil fn-ptx-ptd-ins-nil
                      member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart consp)
                      (:executable-counterpart eq) fn-ptx-driver-arm))
           :do-not-induct t
           :use ((:instance fn-ptx-m0-fields)
                 (:instance fn-ptx-m0q-fields (qq (append (true-list-fix (fn-ptx-q m)) (list (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev)))))))
                 (:instance fn-ptx-simp-frame-rely (m2 (fn-ptx-chg m :committed nil)))
                 (:instance fn-ptx-simp-frame-rely (m2 (fn-ptx-chg (fn-ptx-chg m :committed nil) :q (append (true-list-fix (fn-ptx-q m)) (list (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev)) (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev))))))))))))
(defthm fn-ptx-end-nf-fields
  (let ((m2 (mv-nth 0 (fn-ptx-end m o kd ext nil committed id inc st))))
    (and (member-equal (fn-ptx-ph m2) '(:idle :reading))
         (equal (fn-ptx-kd m2) kd) (equal (fn-ptx-ext m2) (nfix ext))
         (equal (fn-ptx-committedp m2) (and committed t))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn-ptx-end-0 fn-ptx-start-0 fn-ptx-accessors-of-mk member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)))
           :do-not-induct t)))
(defthm fn-ptx-end-fenced-fields
  (let ((m2 (mv-nth 0 (fn-ptx-end m o kd ext t committed id inc st))))
    (and (equal (fn-ptx-ph m2) :fenced)
         (equal (fn-ptx-kd m2) kd) (equal (fn-ptx-ext m2) (nfix ext))
         (equal (fn-ptx-committedp m2) (and committed t))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn-ptx-end-0 fn-ptx-accessors-of-mk))
           :do-not-induct t)))
(defthm fn-ptx-end-nf-not-hashing
  (not (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-end m o kd ext nil committed id inc st))) :hashing))
  :hints (("Goal" :use (fn-ptx-end-nf-fields) :in-theory (union-theories (theory 'minimal-theory) '(member-equal (:executable-counterpart member-equal) (:executable-counterpart equal))))))
(defthm fn-ptx-read-fields
  (implies (equal (fn-ptx-ph m) :reading)
  (let ((m2 (mv-nth 0 (fn-ptx-read m q id inc st))))
    (and (equal (fn-ptx-kd m2) (fn-ptx-kd m)) (equal (fn-ptx-ext m2) (fn-ptx-ext m))
         (or (and (member-equal (fn-ptx-ph m2) '(:idle :reading)))
             (and (equal (fn-ptx-ph m2) :hashing) (equal (fn-ptx-hs m2) (list 0 nil)))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn-ptx-read-1 fn-ptx-rd-end0 fn-ptx-rd-endr fn-ptx-rd-cont fn-ptx-rd-hashing
                     fn-ptx-end-nf-fields fn-ptx-end-nf-not-hashing fn-ptx-accessors-of-mk fn-ptx-nfix-ext member-equal
                     (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart mv-nth) mv-nth))
           :do-not-induct t)))
(defthm fn-ptx-take-0 (equal (take 0 x) nil))
(defthm fn-ptx-simp-hash-start
  (implies (and (equal (fn-ptx-ph m) :reading)
                (fn-ptx-simp m ptd id inc st)
                (equal (fn-ptx-ph m2) :hashing)
                (equal (fn-ptx-kd m2) (fn-ptx-kd m))
                (equal (fn-ptx-ext m2) (fn-ptx-ext m))
                (equal (fn-ptx-hs m2) (list 0 nil))
                (fn-ptx-rely m m2 id inc st st2))
           (fn-ptx-simp m2 ptd id inc st2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn-ptx-simp fn-ptx-hash-invp fn-ptx-rely fn-ptx-ptd-phase fn-ptx-stack-of fn-rtc-get fn-ptx-take-0
                     (:executable-counterpart fn-rtc-get) (:executable-counterpart take) (:executable-counterpart nfix)
                     (:executable-counterpart equal) (:executable-counterpart not) member-equal (:executable-counterpart member-equal) fn-ptx-in-flight-p car-cons cdr-cons))
           :do-not-induct t)))
(defthm fn-ptx-p4-1-reading
  (implies (and (equal (fn-ptx-ph m) :reading) (equal (fn-rtc-get 0 ev) :timer))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-p4-1 fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-ptd-run-nil fn-ptx-ptd-ins-nil2
                      member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart consp)
                      (:executable-counterpart eq) fn-ptx-driver-arm))
           :do-not-induct t
           :use ((:instance fn-ptx-read-fields (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-simp-ready-keep (m2 (mv-nth 0 (fn-ptx-read m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st))) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-simp-hash-start (m2 (mv-nth 0 (fn-ptx-read m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st))) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-mul-1024-floor
    (implies (and (natp pos) (equal (mod pos 1024) 0)) (equal (* 1024 (floor pos 1024)) pos)))
  (defthm fn-ptx-natp-floor-1024
    (implies (natp pos) (natp (floor pos 1024)))))
(defthm fn-ptx-absorb-from-pos
  (implies (and (natp pos) (equal (mod pos 1024) 0) (natp n) (<= pos n))
           (let ((r (fn-ptx-absorb nw pos
                                   (fn-ptx-stack-of (take pos (fn-ptx-msg-range 0 n spans id inc st)))
                                   n spans id inc st)))
             (and (equal (mv-nth 1 r)
                         (fn-ptx-stack-of (take (mv-nth 0 r) (fn-ptx-msg-range 0 n spans id inc st))))
                  (natp (mv-nth 0 r))
                  (equal (mod (mv-nth 0 r) 1024) 0)
                  (<= pos (mv-nth 0 r))
                  (implies (< pos n) (< (mv-nth 0 r) n)))))
  :hints (("Goal" :use ((:instance fn-ptx-absorb-is-the-stack (j (floor pos 1024))))
                  :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-mul-1024-floor fn-ptx-natp-floor-1024)))))
(defun fn-ptx-hnmsg (m) (fn-ptx-spans-len (fn-ptx-spans m)))
(defun fn-ptx-hnw (q) (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
(defun fn-ptx-hpos (m q id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (pos stk) (fn-ptx-absorb (fn-ptx-hnw q) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m))
                                   (fn-ptx-hnmsg m) (fn-ptx-spans m) id inc fn-rtc-st)
    (declare (ignore stk)) pos))
(defun fn-ptx-hstk (m q id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (pos stk) (fn-ptx-absorb (fn-ptx-hnw q) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m))
                                   (fn-ptx-hnmsg m) (fn-ptx-spans m) id inc fn-rtc-st)
    (declare (ignore pos)) stk))
(defthm fn-ptx-hash-0h
  (equal (mv-nth 0 (fn-ptx-hash m q id inc st))
         (let* ((nmsg (fn-ptx-hnmsg m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (b3 (fn-ptx-b3 m))
                (m0 (fn-ptx-chg m :committed nil))
                (pos (fn-ptx-hpos m q id inc st)) (stk (fn-ptx-hstk m q id inc st)))
           (if (< (+ pos 1024) nmsg)
               (fn-ptx-chg m0 :hs (list pos stk))
             (let* ((trailer (fn-ptx-finish-digest pos stk nmsg (fn-ptx-spans m) id inc st))
                    (pad (fn-ptx-pad-len (+ nmsg 32) (fn-ptx-unit m)))
                    (b3x (list (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3)))
                    (elen (+ nmsg 32 pad))
                    (front (fn-ptx-kd-frontier kd)))
               (if (fn-olr-extension-needed-p front elen ext (fn-ptx-unit m))
                   (let ((nx (fn-olr-extension-target front elen ext (fn-ptx-unit m))))
                     (if (<= (expt 2 64) nx)
                         (mv-nth 0 (fn-ptx-end m0 :refused kd ext nil nil id inc st))
                       (fn-ptx-chg m0 :ph :extending :k 0 :nxt nx :b3 b3x :hs (list nmsg trailer pad) :evd nil)))
                 (fn-ptx-chg m0 :ph :payload-writing :k 0 :nxt ext :b3 b3x :hs (list nmsg trailer pad) :evd nil))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-hash-0 fn-ptx-hpos fn-ptx-hstk fn-ptx-hnmsg fn-ptx-hnw (:executable-counterpart mv-nth) mv-nth))
           :do-not-induct t)))
(defthm fn-ptx-hnmsg-is-nmsg (equal (fn-ptx-hnmsg m) (fn-ptx-nmsg m))
  :hints (("Goal" :in-theory (enable fn-ptx-hnmsg fn-ptx-nmsg))))
(defthm fn-ptx-message-is-msg-range
  (equal (fn-ptx-message m id inc st) (fn-ptx-msg-range 0 (fn-ptx-hnmsg m) (fn-ptx-spans m) id inc st))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-message fn-ptx-hnmsg)))))
(defthm fn-ptx-hash-absorb-facts
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (fn-ptx-hash-invp m id inc st))
           (let ((pos (fn-ptx-hpos m q id inc st)) (stk (fn-ptx-hstk m q id inc st)))
             (and (equal stk (fn-ptx-stack-of (take pos (fn-ptx-message m id inc st))))
                  (natp pos) (equal (mod pos 1024) 0) (< (fn-rtc-get 0 (fn-ptx-hs m)) (fn-ptx-hnmsg m))
                  (<= (fn-rtc-get 0 (fn-ptx-hs m)) pos)
                  (< pos (fn-ptx-hnmsg m)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-hpos fn-ptx-hstk fn-ptx-hash-invp fn-ptx-hnmsg-is-nmsg fn-ptx-nfix-natp-rw fn-ptx-nmsg-natp natp))
           :do-not-induct t
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-message-is-msg-range)
                 (:instance fn-ptx-absorb-from-pos (nw (fn-ptx-hnw q)) (pos (fn-rtc-get 0 (fn-ptx-hs m))) (n (fn-ptx-hnmsg m)) (spans (fn-ptx-spans m)))))))
(defthm fn-ptx-simp-hash-keep
  (implies (and (equal (fn-ptx-ph m) :hashing)
                (fn-ptx-simp m ptd id inc st)
                (equal (fn-ptx-ph m2) :hashing)
                (equal (fn-ptx-kd m2) (fn-ptx-kd m))
                (equal (fn-ptx-ext m2) (fn-ptx-ext m))
                (equal (fn-rtc-get 1 (fn-ptx-hs m2)) (fn-ptx-stack-of (take (nfix (fn-rtc-get 0 (fn-ptx-hs m2))) (fn-ptx-message m id inc st))))
                (fn-ptx-rely m m2 id inc st st2))
           (fn-ptx-simp m2 ptd id inc st2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn-ptx-simp fn-ptx-hash-invp fn-ptx-rely fn-ptx-ptd-phase member-equal (:executable-counterpart member-equal)
                     (:executable-counterpart equal) fn-ptx-in-flight-p))
           :do-not-induct t)))
(defthm fn-ptx-simp-hashing-facts
  (implies (and (equal (fn-ptx-ph m) :hashing) (fn-ptx-simp m ptd id inc st))
           (and (fn-ptx-hash-invp m id inc st)
                (equal (fn-ptd-ph ptd) :ready)
                (equal (fn-ptx-kd m) (fn-ptx-kd-of (fn-ptd-ks ptd)))
                (equal (fn-ptd-ext ptd) (fn-ptx-ext m))
                (not (consp (fn-lgk-batch (fn-ptd-ks ptd)))) (not (consp (fn-lgk-inflight (fn-ptd-ks ptd))))
                (not (equal (fn-lgk-phase (fn-ptd-ks ptd)) :fault))
                (equal (fn-lgk-acked (fn-ptd-ks ptd)) (len (fn-lgk-committed (fn-ptd-ks ptd))))
                (true-listp (fn-lgk-committed (fn-ptd-ks ptd)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn-ptx-simp fn-ptx-ptd-phase member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)))
           :do-not-induct t)))
(defthm fn-ptx-m0hs-fields
  (let ((m0 (fn-ptx-chg (fn-ptx-chg m :committed nil) :hs hh)))
    (and (equal (fn-ptx-ph m0) (fn-ptx-ph m)) (equal (fn-ptx-kd m0) (fn-ptx-kd m))
         (equal (fn-ptx-ext m0) (fn-ptx-ext m)) (equal (fn-ptx-hs m0) hh)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt)))))
(defthm fn-ptx-get-of-list2 (and (equal (fn-rtc-get 0 (list a b)) a) (equal (fn-rtc-get 1 (list a b)) b)))
(defthm fn-ptx-simp-hash-keep2
  (implies (and (equal (fn-ptx-ph m) :hashing)
                (fn-ptx-simp m ptd id inc st)
                (equal (fn-ptx-ph m2) :hashing)
                (equal (fn-ptx-kd m2) (fn-ptx-kd m))
                (equal (fn-ptx-ext m2) (fn-ptx-ext m))
                (equal (fn-ptx-hs m2) (list pos stk))
                (natp pos)
                (equal stk (fn-ptx-stack-of (take pos (fn-ptx-message m id inc st))))
                (fn-ptx-rely m m2 id inc st st2))
           (fn-ptx-simp m2 ptd id inc st2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-get-of-list2 fn-ptx-nfix-natp-rw natp (:executable-counterpart equal)))
           :do-not-induct t
           :use ((:instance fn-ptx-simp-hash-keep)))))
(defthm fn-ptx-p4-1-hash-more
  (implies (and (equal (fn-ptx-ph m) :hashing) (equal (fn-rtc-get 0 ev) :timer)
                (< (+ (fn-ptx-hpos m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) 1024) (fn-ptx-hnmsg m)))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-p4-1 fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-hash-0h fn-ptx-ptd-run-nil fn-ptx-ptd-ins-nil
                      member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart consp)
                      (:executable-counterpart eq) fn-ptx-driver-arm))
           :do-not-induct t
           :use ((:instance fn-ptx-m0hs-fields (hh (list (fn-ptx-hpos m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) (fn-ptx-hstk m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st))))
                 (:instance fn-ptx-simp-hashing-facts (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-hash-absorb-facts (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-simp-hash-keep2 (m2 (fn-ptx-chg (fn-ptx-chg m :committed nil) :hs (list (fn-ptx-hpos m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) (fn-ptx-hstk m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st))))
                           (pos (fn-ptx-hpos m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)) (stk (fn-ptx-hstk m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st))
                           (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defun fn-ptx-hpad (m) (fn-ptx-pad-len (+ (fn-ptx-hnmsg m) 32) (fn-ptx-unit m)))
(defun fn-ptx-helen (m) (+ (fn-ptx-hnmsg m) 32 (fn-ptx-hpad m)))
(defun fn-ptx-hneed (m) (fn-olr-extension-needed-p (fn-ptx-kd-frontier (fn-ptx-kd m)) (fn-ptx-helen m) (fn-ptx-ext m) (fn-ptx-unit m)))
(defun fn-ptx-hnx (m) (fn-olr-extension-target (fn-ptx-kd-frontier (fn-ptx-kd m)) (fn-ptx-helen m) (fn-ptx-ext m) (fn-ptx-unit m)))
(defun fn-ptx-htrailer (m q id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (fn-ptx-finish-digest (fn-ptx-hpos m q id inc fn-rtc-st) (fn-ptx-hstk m q id inc fn-rtc-st) (fn-ptx-hnmsg m) (fn-ptx-spans m) id inc fn-rtc-st))
(defun fn-ptx-hb3x (m) (list (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (+ (fn-ptx-buf-len (fn-ptx-b3 m)) 32) (fn-ptx-buf-x (fn-ptx-b3 m))))
(defthm fn-ptx-hash-0h2
  (equal (mv-nth 0 (fn-ptx-hash m q id inc st))
         (if (< (+ (fn-ptx-hpos m q id inc st) 1024) (fn-ptx-hnmsg m))
             (fn-ptx-chg (fn-ptx-chg m :committed nil) :hs (list (fn-ptx-hpos m q id inc st) (fn-ptx-hstk m q id inc st)))
           (if (fn-ptx-hneed m)
               (if (<= (expt 2 64) (fn-ptx-hnx m))
                   (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) nil nil id inc st))
                 (fn-ptx-chg (fn-ptx-chg m :committed nil) :ph :extending :k 0 :nxt (fn-ptx-hnx m) :b3 (fn-ptx-hb3x m)
                             :hs (list (fn-ptx-hnmsg m) (fn-ptx-htrailer m q id inc st) (fn-ptx-hpad m)) :evd nil))
             (fn-ptx-chg (fn-ptx-chg m :committed nil) :ph :payload-writing :k 0 :nxt (fn-ptx-ext m) :b3 (fn-ptx-hb3x m)
                         :hs (list (fn-ptx-hnmsg m) (fn-ptx-htrailer m q id inc st) (fn-ptx-hpad m)) :evd nil))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-hash-0h fn-ptx-hpad fn-ptx-helen fn-ptx-hneed fn-ptx-hnx fn-ptx-htrailer fn-ptx-hb3x))
           :do-not-induct t)))
(defthm fn-ptx-ptd-ins-nil3
  (implies (and (not (member-equal (fn-ptx-ph m2) '(:extending :payload-writing)))
                (not (fn-ptx-driver-arm (fn-ptx-ph m) (fn-rtc-get 0 ev))))
           (equal (fn-ptx-ptd-ins m ev m2 r fo) nil))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-ptd-ins fn-ptx-driver-arm member-equal (:executable-counterpart member-equal))))))
(defthm fn-ptx-p4-1-hash-refused
  (implies (and (equal (fn-ptx-ph m) :hashing) (equal (fn-rtc-get 0 ev) :timer)
                (not (< (+ (fn-ptx-hpos m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) 1024) (fn-ptx-hnmsg m)))
                (fn-ptx-hneed m) (<= (expt 2 64) (fn-ptx-hnx m)))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-p4-1 fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-hash-0h2 fn-ptx-ptd-run-nil fn-ptx-ptd-ins-nil3 fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt
                      member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart consp)
                      (:executable-counterpart eq) fn-ptx-driver-arm))
           :do-not-induct t
           :use ((:instance fn-ptx-end-nf-fields (m (fn-ptx-chg m :committed nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (committed nil)
                            (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-simp-ready-keep (m2 (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) nil nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))
                           (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defthm fn-ptx-run-one
  (implies (not (equal k :begin))
           (and (equal (mv-nth 0 (fn-ptd-run st (list (cons k o)) ino unit max))
                       (mv-nth 0 (fn-ptd-complete st (cons k o) ino unit)))
                (equal (mv-nth 2 (fn-ptd-run st (list (cons k o)) ino unit max))
                       (binary-append (mv-nth 2 (fn-ptd-complete st (cons k o) ino unit)) nil))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptd-run fn-ptd-step fn-ptx-ptd-run-nil (:executable-counterpart equal) (:executable-counterpart consp) car-cons cdr-cons
                (:executable-counterpart mv-nth) mv-nth (:executable-counterpart atom) atom zp (:executable-counterpart zp)
                (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart not)))
           :do-not-induct t)))
(defthm fn-ptx-nfix-ptd-ext (equal (nfix (fn-ptd-ext st)) (fn-ptd-ext st)) :hints (("Goal" :in-theory (enable fn-ptd-ext))))
(defthm fn-ptx-nfix-ptd-nxt (equal (nfix (fn-ptd-nxt st)) (fn-ptd-nxt st)) :hints (("Goal" :in-theory (enable fn-ptd-nxt))))
(deftheory fn-ptx-cmp-th
  (union-theories (theory 'minimal-theory)
              '(fn-ptd-complete fn-ptd-fields-of-mk fn-ptx-nfix-ptd-ext fn-ptx-nfix-ptd-nxt
                (:executable-counterpart equal) (:executable-counterpart consp) car-cons cdr-cons
                (:executable-counterpart mv-nth) mv-nth zp (:executable-counterpart zp)
                (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart not))))
(defthm fn-ptx-cmp-extending-ok
  (implies (and (equal (fn-ptd-ph st) :extending) (equal o :ok))
           (let ((r (fn-ptd-complete st (cons :pwrite o) ino unit)))
             (and (equal (fn-ptd-ph (mv-nth 0 r)) :extsyncing)
                  (equal (fn-ptd-ks (mv-nth 0 r)) (fn-ptd-ks st))
                  (equal (fn-ptd-rec (mv-nth 0 r)) (fn-ptd-rec st))
                  (equal (fn-ptd-ext (mv-nth 0 r)) (fn-ptd-ext st))
                  (equal (fn-ptd-nxt (mv-nth 0 r)) (fn-ptd-nxt st))
                  (equal (mv-nth 2 r) nil))))
  :rule-classes nil :hints (("Goal" :in-theory (theory 'fn-ptx-cmp-th) :do-not-induct t)))
(defthm fn-ptx-cmp-extending-bad
  (implies (and (equal (fn-ptd-ph st) :extending) (not (equal o :ok)))
           (let ((r (fn-ptd-complete st (cons :pwrite o) ino unit)))
             (and (equal (fn-ptd-ph (mv-nth 0 r)) :fenced)
                  (equal (mv-nth 2 r) (list (cons :refused (fn-ptd-rec st)))))))
  :rule-classes nil :hints (("Goal" :in-theory (theory 'fn-ptx-cmp-th) :do-not-induct t)))
(defthm fn-ptx-cmp-extsyncing-ok
  (implies (and (equal (fn-ptd-ph st) :extsyncing) (equal o :ok))
           (let ((r (fn-ptd-complete st (cons :fsync o) ino unit)))
             (and (equal (fn-ptd-ph (mv-nth 0 r)) :writing)
                  (equal (fn-ptd-ks (mv-nth 0 r)) (fn-ptd-ks st))
                  (equal (fn-ptd-rec (mv-nth 0 r)) (fn-ptd-rec st))
                  (equal (fn-ptd-ext (mv-nth 0 r)) (fn-ptd-ext st))
                  (equal (fn-ptd-nxt (mv-nth 0 r)) (fn-ptd-nxt st))
                  (equal (mv-nth 2 r) nil))))
  :rule-classes nil :hints (("Goal" :in-theory (theory 'fn-ptx-cmp-th) :do-not-induct t)))
(defthm fn-ptx-cmp-extsyncing-bad
  (implies (and (equal (fn-ptd-ph st) :extsyncing) (not (equal o :ok)))
           (let ((r (fn-ptd-complete st (cons :fsync o) ino unit)))
             (and (equal (fn-ptd-ph (mv-nth 0 r)) :fenced)
                  (equal (mv-nth 2 r) (list (cons :refused (fn-ptd-rec st)))))))
  :rule-classes nil :hints (("Goal" :in-theory (theory 'fn-ptx-cmp-th) :do-not-induct t)))
(defthm fn-ptx-cmp-writing-ok
  (implies (and (equal (fn-ptd-ph st) :writing) (equal o :ok))
           (let ((r (fn-ptd-complete st (cons :pwrite o) ino unit)))
             (and (equal (fn-ptd-ph (mv-nth 0 r)) :syncing)
                  (equal (fn-ptd-ks (mv-nth 0 r)) (fn-ptd-sealed (fn-ptd-ks st) unit (fn-ptd-nxt st) t))
                  (equal (fn-ptd-rec (mv-nth 0 r)) (fn-ptd-rec st))
                  (equal (fn-ptd-ext (mv-nth 0 r)) (fn-ptd-ext st))
                  (equal (fn-ptd-nxt (mv-nth 0 r)) (fn-ptd-nxt st))
                  (equal (mv-nth 2 r) nil))))
  :rule-classes nil :hints (("Goal" :in-theory (theory 'fn-ptx-cmp-th) :do-not-induct t)))
(defthm fn-ptx-cmp-writing-bad
  (implies (and (equal (fn-ptd-ph st) :writing) (not (equal o :ok)))
           (let ((r (fn-ptd-complete st (cons :pwrite o) ino unit)))
             (and (equal (fn-ptd-ph (mv-nth 0 r)) :fenced)
                  (equal (mv-nth 2 r) (list (cons :uncertain (fn-ptd-rec st)))))))
  :rule-classes nil :hints (("Goal" :in-theory (theory 'fn-ptx-cmp-th) :do-not-induct t)))
(defthm fn-ptx-cmp-syncing-ok
  (implies (and (equal (fn-ptd-ph st) :syncing) (equal o :ok))
           (let ((r (fn-ptd-complete st (cons :fsync o) ino unit)))
             (and (equal (fn-ptd-ph (mv-nth 0 r)) :ready)
                  (equal (fn-ptd-ks (mv-nth 0 r)) (fn-lgk-finish-one (fn-lgk-fence (fn-ptd-ks st) unit)))
                  (equal (fn-ptd-ext (mv-nth 0 r)) (fn-ptd-nxt st))
                  (equal (fn-ptd-nxt (mv-nth 0 r)) (fn-ptd-nxt st))
                  (equal (mv-nth 2 r) (list (cons :posted (fn-ptd-rec st)))))))
  :rule-classes nil :hints (("Goal" :in-theory (theory 'fn-ptx-cmp-th) :do-not-induct t)))
(defthm fn-ptx-cmp-syncing-bad
  (implies (and (equal (fn-ptd-ph st) :syncing) (not (equal o :ok)))
           (let ((r (fn-ptd-complete st (cons :fsync o) ino unit)))
             (and (equal (fn-ptd-ph (mv-nth 0 r)) :fenced)
                  (equal (mv-nth 2 r) (list (cons :uncertain (fn-ptd-rec st)))))))
  :rule-classes nil :hints (("Goal" :in-theory (theory 'fn-ptx-cmp-th) :do-not-induct t)))
(defmacro m2* () '(mv-nth 0 (fn-ptx-step m ev st q)))
(defmacro reqs* () '(mv-nth 1 (fn-ptx-step m ev st q)))
(defthm fn-ptx-rely-flight
  (implies (and (fn-ptx-rely m m2 id inc st st2) (fn-ptx-in-flight-p (fn-ptx-ph m)) (fn-ptx-in-flight-p (fn-ptx-ph m2)))
           (equal (fn-ptx-message m2 id inc st2) (fn-ptx-message m id inc st)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-ptx-rely member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart not)))
           :do-not-induct t)))
(defthm fn-ptx-simp-flight-frame
  (implies (and (fn-ptx-simp m ptd id inc st)
                (member-equal (fn-ptd-ph ptd) '(:extending :extsyncing :writing))
                (member-equal (fn-ptd-ph ptd2) '(:extending :extsyncing :writing))
                (equal (fn-ptd-ks ptd2) (fn-ptd-ks ptd)) (equal (fn-ptd-rec ptd2) (fn-ptd-rec ptd))
                (equal (fn-ptd-ext ptd2) (fn-ptd-ext ptd)) (equal (fn-ptd-nxt ptd2) (fn-ptd-nxt ptd))
                (equal (fn-ptd-ph ptd2) (fn-ptx-ptd-phase (fn-ptx-ph m2)))
                (equal (fn-ptx-kd m2) (fn-ptx-kd m)) (equal (fn-ptx-ext m2) (fn-ptx-ext m))
                (equal (fn-ptx-nxt m2) (fn-ptx-nxt m)) (equal (fn-ptx-hs m2) (fn-ptx-hs m))
                (equal (fn-ptx-geo m2) (fn-ptx-geo m))
                (equal (fn-ptx-message m2 id inc st2) (fn-ptx-message m id inc st)))
           (fn-ptx-simp m2 ptd2 id inc st2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-ptx-simp fn-ptx-unit member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart not)))
           :do-not-induct t
           :use ((:instance fn-ptx-record-frame)))))
(deftheory fn-ptx-stp-th
  (union-theories (theory 'minimal-theory)
    '(fn-ptx-step fn-ptx-step1 (:executable-counterpart equal) (:executable-counterpart eq) (:executable-counterpart consp)
      (:executable-counterpart member-equal) member-equal (:executable-counterpart mv-nth) mv-nth zp (:executable-counterpart zp)
      (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart not) car-cons cdr-cons
      fn-rtc-ev-id fn-rtc-ev-inc)))
(defthm fn-ptx-simp-ph
  (implies (fn-ptx-simp m ptd id inc st)
           (equal (fn-ptd-ph ptd) (fn-ptx-ptd-phase (fn-ptx-ph m))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-simp)) :do-not-induct t)))
(defthm fn-ptx-step-ext-ok
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extending) (equal (fn-rtc-get 0 ev) :extend)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (and (equal (fn-ptx-ph (m2*)) :extsyncing) (equal (fn-ptx-kd (m2*)) (fn-ptx-kd m))
                (equal (fn-ptx-ext (m2*)) (fn-ptx-ext m)) (equal (fn-ptx-nxt (m2*)) (fn-ptx-nxt m))
                (equal (fn-ptx-hs (m2*)) (fn-ptx-hs m)) (equal (fn-ptx-geo (m2*)) (fn-ptx-geo m))))
  :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'fn-ptx-stp-th) '(fn-ptx-step fn-ptx-step1)) '(fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt))
           :do-not-induct t)))
(defthm fn-ptx-p4-1-ext-ok
  (implies (and (equal (fn-ptx-ph m) :extending) (equal (fn-rtc-get 0 ev) :extend)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-in-flight-p fn-ptx-ptd-phase binary-append member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-ext-ok)
                 (:instance fn-ptx-simp-ph)
                 (:instance fn-ptx-cmp-extending-ok (st ptd) (o :ok) (unit (fn-ptx-unit m)))
                 (:instance fn-ptx-rely-flight (m2 (m2*)))
                 (:instance fn-ptx-simp-flight-frame (m2 (m2*)) (ptd2 (mv-nth 0 (fn-ptd-complete ptd (cons :pwrite :ok) ino (fn-ptx-unit m)))))))))
(defthm fn-ptx-len-7-consp (implies (equal (len x) 7) (consp x))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-len-atom (:executable-counterpart equal))) :do-not-induct t
           :use ((:instance fn-ptx-len-atom (q x))))))
(defthm fn-ptx-okp-cur-consp
  (implies (and (fn-ptx-okp m) (member-equal (fn-ptx-ph m) '(:extending :extsyncing :payload-writing :log-writing :committing)))
           (consp (fn-ptx-cur m)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) fn-ptx-len-7-consp))
           :do-not-induct t :use ((:instance fn-ptx-okp-elim)))))
(defthm fn-ptx-end-fenced-facts
  (implies (consp (fn-ptx-cur m))
           (and (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) o kd ext t nil id inc st))) :fenced)
                (equal (fn-ptx-committedp (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) o kd ext t nil id inc st))) nil)
                (equal (fn-ptx-cur-code m (mv-nth 1 (fn-ptx-end (fn-ptx-chg m :committed nil) o kd ext t nil id inc st)))
                       (fn-ptx-code o))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-end-fenced-fields fn-ptx-end-cur-code fn-ptx-accessors-of-mk (:executable-counterpart consp)))
           :do-not-induct t
           :use ((:instance fn-ptx-end-fenced-fields (m (fn-ptx-chg m :committed nil)) (committed nil))
                 (:instance fn-ptx-end-cur-code (m0 (fn-ptx-chg m :committed nil)) (fenced t) (committed nil))))))
(defthm fn-ptx-step-ext-bad-eqn
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extending) (equal (fn-rtc-get 0 ev) :extend) (not (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
           (and (equal (m2*) (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))
                (equal (reqs*) (mv-nth 1 (fn-ptx-end (fn-ptx-chg m :committed nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'fn-ptx-stp-th) :do-not-induct t :use ((:instance fn-ptx-okp-wfp)))))
(defthm fn-ptx-stepf-ext-bad
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extending) (equal (fn-rtc-get 0 ev) :extend) (not (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
           (and (equal (fn-ptx-ph (m2*)) :fenced) (equal (fn-ptx-committedp (m2*)) nil)
                (equal (fn-ptx-cur-code m (reqs*)) 1)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) fn-ptx-code (:executable-counterpart fn-ptx-code)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-ext-bad-eqn) (:instance fn-ptx-okp-cur-consp)
                 (:instance fn-ptx-end-fenced-facts (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defthm fn-ptx-step-xs-bad-eqn
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extsyncing) (equal (fn-rtc-get 0 ev) :fsync) (not (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
           (and (equal (m2*) (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))
                (equal (reqs*) (mv-nth 1 (fn-ptx-end (fn-ptx-chg m :committed nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'fn-ptx-stp-th) :do-not-induct t :use ((:instance fn-ptx-okp-wfp)))))
(defthm fn-ptx-stepf-xs-bad
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extsyncing) (equal (fn-rtc-get 0 ev) :fsync) (not (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
           (and (equal (fn-ptx-ph (m2*)) :fenced) (equal (fn-ptx-committedp (m2*)) nil)
                (equal (fn-ptx-cur-code m (reqs*)) 1)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) fn-ptx-code (:executable-counterpart fn-ptx-code)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-xs-bad-eqn) (:instance fn-ptx-okp-cur-consp)
                 (:instance fn-ptx-end-fenced-facts (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defthm fn-ptx-step-pw-bad-eqn
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :payload-writing) (equal (fn-rtc-get 0 ev) :pwrite) (not (and (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))))
           (and (equal (m2*) (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) :uncertain (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))
                (equal (reqs*) (mv-nth 1 (fn-ptx-end (fn-ptx-chg m :committed nil) :uncertain (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'fn-ptx-stp-th) :do-not-induct t :use ((:instance fn-ptx-okp-wfp)))))
(defthm fn-ptx-stepf-pw-bad
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :payload-writing) (equal (fn-rtc-get 0 ev) :pwrite) (not (and (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))))
           (and (equal (fn-ptx-ph (m2*)) :fenced) (equal (fn-ptx-committedp (m2*)) nil)
                (equal (fn-ptx-cur-code m (reqs*)) 2)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) fn-ptx-code (:executable-counterpart fn-ptx-code)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-pw-bad-eqn) (:instance fn-ptx-okp-cur-consp)
                 (:instance fn-ptx-end-fenced-facts (o :uncertain) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defthm fn-ptx-step-lw-bad-eqn
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :log-writing) (equal (fn-rtc-get 0 ev) :pwrite) (not (and (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))))
           (and (equal (m2*) (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) :uncertain (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))
                (equal (reqs*) (mv-nth 1 (fn-ptx-end (fn-ptx-chg m :committed nil) :uncertain (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'fn-ptx-stp-th) :do-not-induct t :use ((:instance fn-ptx-okp-wfp)))))
(defthm fn-ptx-stepf-lw-bad
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :log-writing) (equal (fn-rtc-get 0 ev) :pwrite) (not (and (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))))
           (and (equal (fn-ptx-ph (m2*)) :fenced) (equal (fn-ptx-committedp (m2*)) nil)
                (equal (fn-ptx-cur-code m (reqs*)) 2)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) fn-ptx-code (:executable-counterpart fn-ptx-code)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-lw-bad-eqn) (:instance fn-ptx-okp-cur-consp)
                 (:instance fn-ptx-end-fenced-facts (o :uncertain) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defthm fn-ptx-step-cm-bad-eqn
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :committing) (equal (fn-rtc-get 0 ev) :fsync) (not (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
           (and (equal (m2*) (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) :uncertain (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))
                (equal (reqs*) (mv-nth 1 (fn-ptx-end (fn-ptx-chg m :committed nil) :uncertain (fn-ptx-kd m) (fn-ptx-ext m) t nil (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'fn-ptx-stp-th) :do-not-induct t :use ((:instance fn-ptx-okp-wfp)))))
(defthm fn-ptx-stepf-cm-bad
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :committing) (equal (fn-rtc-get 0 ev) :fsync) (not (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
           (and (equal (fn-ptx-ph (m2*)) :fenced) (equal (fn-ptx-committedp (m2*)) nil)
                (equal (fn-ptx-cur-code m (reqs*)) 2)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) fn-ptx-code (:executable-counterpart fn-ptx-code)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-cm-bad-eqn) (:instance fn-ptx-okp-cur-consp)
                 (:instance fn-ptx-end-fenced-facts (o :uncertain) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defthm fn-ptx-simp-rec
  (implies (and (fn-ptx-simp m ptd id inc st) (member-equal (fn-ptd-ph ptd) '(:extending :extsyncing :writing :syncing)))
           (equal (fn-ptd-rec ptd) (fn-ptx-record m id inc st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-simp member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)))
           :do-not-induct t)))
(defthm fn-ptx-p4-1-ext-bad
  (implies (and (equal (fn-ptx-ph m) :extending) (equal (fn-rtc-get 0 ev) :extend) (not (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-in-flight-p fn-ptx-ptd-phase binary-append fn-ptx-code-of-ptd fn-ptx-simp
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-stepf-ext-bad) (:instance fn-ptx-simp-ph) (:instance fn-ptx-simp-rec)
                 (:instance fn-ptx-cmp-extending-bad (st ptd) (o (if (equal fo :ok) :eio fo)) (unit (fn-ptx-unit m)))))))
(defthm fn-ptx-p4-1-xs-bad
  (implies (and (equal (fn-ptx-ph m) :extsyncing) (equal (fn-rtc-get 0 ev) :fsync) (not (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-in-flight-p fn-ptx-ptd-phase binary-append fn-ptx-code-of-ptd fn-ptx-simp
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-stepf-xs-bad) (:instance fn-ptx-simp-ph) (:instance fn-ptx-simp-rec)
                 (:instance fn-ptx-cmp-extsyncing-bad (st ptd) (o (if (equal fo :ok) :eio fo)) (unit (fn-ptx-unit m)))))))
(defthm fn-ptx-p4-1-pw-bad
  (implies (and (equal (fn-ptx-ph m) :payload-writing) (equal (fn-rtc-get 0 ev) :pwrite) (not (and (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-in-flight-p fn-ptx-ptd-phase binary-append fn-ptx-code-of-ptd fn-ptx-simp
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-stepf-pw-bad) (:instance fn-ptx-simp-ph) (:instance fn-ptx-simp-rec)
                 (:instance fn-ptx-cmp-writing-bad (st ptd) (o (if (equal fo :ok) :eio fo)) (unit (fn-ptx-unit m)))))))
(defthm fn-ptx-p4-1-lw-bad
  (implies (and (equal (fn-ptx-ph m) :log-writing) (equal (fn-rtc-get 0 ev) :pwrite) (not (and (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-in-flight-p fn-ptx-ptd-phase binary-append fn-ptx-code-of-ptd fn-ptx-simp
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-stepf-lw-bad) (:instance fn-ptx-simp-ph) (:instance fn-ptx-simp-rec)
                 (:instance fn-ptx-cmp-writing-bad (st ptd) (o (if (equal fo :ok) :eio fo)) (unit (fn-ptx-unit m)))))))
(defthm fn-ptx-p4-1-cm-bad
  (implies (and (equal (fn-ptx-ph m) :committing) (equal (fn-rtc-get 0 ev) :fsync) (not (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-in-flight-p fn-ptx-ptd-phase binary-append fn-ptx-code-of-ptd fn-ptx-simp
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-stepf-cm-bad) (:instance fn-ptx-simp-ph) (:instance fn-ptx-simp-rec)
                 (:instance fn-ptx-cmp-syncing-bad (st ptd) (o (if (equal fo :ok) :eio fo)) (unit (fn-ptx-unit m)))))))
(defthm fn-ptx-step-xs-ok
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :extsyncing) (equal (fn-rtc-get 0 ev) :fsync)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (and (equal (fn-ptx-ph (m2*)) :payload-writing) (equal (fn-ptx-kd (m2*)) (fn-ptx-kd m))
                (equal (fn-ptx-ext (m2*)) (fn-ptx-ext m)) (equal (fn-ptx-nxt (m2*)) (fn-ptx-nxt m))
                (equal (fn-ptx-hs (m2*)) (fn-ptx-hs m)) (equal (fn-ptx-geo (m2*)) (fn-ptx-geo m))))
  :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'fn-ptx-stp-th) '(fn-ptx-step fn-ptx-step1)) '(fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt))
           :do-not-induct t)))
(defthm fn-ptx-p4-1-xs-ok
  (implies (and (equal (fn-ptx-ph m) :extsyncing) (equal (fn-rtc-get 0 ev) :fsync)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-in-flight-p fn-ptx-ptd-phase binary-append
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-xs-ok)
                 (:instance fn-ptx-simp-ph)
                 (:instance fn-ptx-cmp-extsyncing-ok (st ptd) (o :ok) (unit (fn-ptx-unit m)))
                 (:instance fn-ptx-rely-flight (m2 (m2*)))
                 (:instance fn-ptx-simp-flight-frame (m2 (m2*)) (ptd2 (mv-nth 0 (fn-ptd-complete ptd (cons :fsync :ok) ino (fn-ptx-unit m)))))))))
(defthm fn-ptx-step-pw-more
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :payload-writing) (equal (fn-rtc-get 0 ev) :pwrite)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))
           (and (equal (fn-ptx-ptd-phase (fn-ptx-ph (m2*))) :writing) (not (equal (fn-ptx-ph (m2*)) :fenced)) (fn-ptx-in-flight-p (fn-ptx-ph (m2*)))
                (equal (fn-ptx-kd (m2*)) (fn-ptx-kd m))
                (equal (fn-ptx-ext (m2*)) (fn-ptx-ext m)) (equal (fn-ptx-nxt (m2*)) (fn-ptx-nxt m))
                (equal (fn-ptx-hs (m2*)) (fn-ptx-hs m)) (equal (fn-ptx-geo (m2*)) (fn-ptx-geo m))))
  :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'fn-ptx-stp-th) '(fn-ptx-step fn-ptx-step1)) '(fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt fn-ptx-ptd-phase fn-ptx-in-flight-p))
           :do-not-induct t)))
(defthm fn-ptx-p4-1-pw-more
  (implies (and (equal (fn-ptx-ph m) :payload-writing) (equal (fn-rtc-get 0 ev) :pwrite)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-ptd-run-nil binary-append fn-ptx-ptd-phase fn-ptx-in-flight-p
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-pw-more)
                 (:instance fn-ptx-simp-ph)
                 (:instance fn-ptx-rely-flight (m2 (m2*)))
                 (:instance fn-ptx-simp-flight-frame (m2 (m2*)) (ptd2 ptd))))))
(defthm fn-ptx-append-fields2
  (implies (fn-lg-append-admitsp ks unit extent)
           (let ((k2 (fn-lgk-append ks unit extent)))
             (and (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                  (equal (fn-lgk-last k2) (fn-lgk-last ks))
                  (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
                  (equal (fn-lgk-next-txid k2) (fn-lgk-next-txid ks))
                  (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
                  (equal (fn-lgk-batch k2) nil)
                  (equal (fn-lgk-inflight k2) (true-list-fix (fn-lgk-batch ks)))
                  (equal (fn-lgk-phase k2) :appended))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-append fn-lg-append-admitsp) (fn-lgk-fitsp fn-lgk-append-octets fn-lg-log)))))
(defthm fn-ptx-simp-seal
  (implies (and (fn-ptx-simp m ptd id inc st)
                (equal (fn-ptd-ph ptd) :writing)
                (equal (fn-ptd-ph ptd2) :syncing)
                (equal (fn-ptd-ks ptd2) (fn-lgk-append (fn-ptd-ks ptd) (fn-ptx-unit m) (fn-ptd-nxt ptd)))
                (equal (fn-ptd-rec ptd2) (fn-ptd-rec ptd)) (equal (fn-ptd-ext ptd2) (fn-ptd-ext ptd)) (equal (fn-ptd-nxt ptd2) (fn-ptd-nxt ptd))
                (equal (fn-ptx-ph m2) :committing)
                (equal (fn-ptx-kd m2) (fn-ptx-kd m)) (equal (fn-ptx-ext m2) (fn-ptx-ext m))
                (equal (fn-ptx-nxt m2) (fn-ptx-nxt m)) (equal (fn-ptx-hs m2) (fn-ptx-hs m))
                (equal (fn-ptx-geo m2) (fn-ptx-geo m))
                (equal (fn-ptx-message m2 id inc st2) (fn-ptx-message m id inc st)))
           (fn-ptx-simp m2 ptd2 id inc st2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-ptx-simp fn-ptx-unit fn-ptx-kd-before-take fn-ptx-ptd-phase member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart not)
               (:executable-counterpart eq) (:executable-counterpart consp) car-cons cdr-cons true-list-fix))
           :do-not-induct t
           :use ((:instance fn-ptx-record-frame)
                 (:instance fn-ptx-append-fields2 (ks (fn-ptd-ks ptd)) (unit (fn-ptx-unit m)) (extent (fn-ptd-nxt ptd)))))))
(defthm fn-ptx-step-lw-ok
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :log-writing) (equal (fn-rtc-get 0 ev) :pwrite)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))
           (and (equal (fn-ptx-ph (m2*)) :committing) (equal (fn-ptx-kd (m2*)) (fn-ptx-kd m))
                (equal (fn-ptx-ext (m2*)) (fn-ptx-ext m)) (equal (fn-ptx-nxt (m2*)) (fn-ptx-nxt m))
                (equal (fn-ptx-hs (m2*)) (fn-ptx-hs m)) (equal (fn-ptx-geo (m2*)) (fn-ptx-geo m))))
  :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'fn-ptx-stp-th) '(fn-ptx-step fn-ptx-step1)) '(fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt))
           :do-not-induct t)))
(defthm fn-ptx-p4-1-lw-ok
  (implies (and (equal (fn-ptx-ph m) :log-writing) (equal (fn-rtc-get 0 ev) :pwrite)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-in-flight-p fn-ptx-ptd-phase binary-append fn-ptd-sealed
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-lw-ok)
                 (:instance fn-ptx-simp-ph)
                 (:instance fn-ptx-cmp-writing-ok (st ptd) (o :ok) (unit (fn-ptx-unit m)))
                 (:instance fn-ptx-rely-flight (m2 (m2*)))
                 (:instance fn-ptx-simp-seal (m2 (m2*)) (ptd2 (mv-nth 0 (fn-ptd-complete ptd (cons :pwrite :ok) ino (fn-ptx-unit m)))))))))
(defthm fn-ptx-step-cm-ok-eqn
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :committing) (equal (fn-rtc-get 0 ev) :fsync)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (and (equal (m2*) (mv-nth 0 (fn-ptx-end (fn-ptx-chg m :committed nil) :posted
                                                   (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m))
                                                   (fn-ptx-nxt m) nil t (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))
                (equal (reqs*) (mv-nth 1 (fn-ptx-end (fn-ptx-chg m :committed nil) :posted
                                                     (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m))
                                                     (fn-ptx-nxt m) nil t (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'fn-ptx-stp-th) :do-not-induct t :use ((:instance fn-ptx-okp-wfp)))))
(defthm fn-ptx-step-cm-ok
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :committing) (equal (fn-rtc-get 0 ev) :fsync)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (and (member-equal (fn-ptx-ph (m2*)) '(:idle :reading))
                (equal (fn-ptx-kd (m2*)) (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m)))
                (equal (fn-ptx-ext (m2*)) (fn-ptx-nxt m))
                (equal (fn-ptx-committedp (m2*)) t)
                (equal (fn-ptx-cur-code m (reqs*)) 0)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) fn-ptx-code (:executable-counterpart fn-ptx-code) fn-ptx-nfix-nxt fn-ptx-accessors-of-mk
                (:executable-counterpart consp)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-cm-ok-eqn) (:instance fn-ptx-okp-cur-consp)
                 (:instance fn-ptx-end-nf-fields (m (fn-ptx-chg m :committed nil)) (o :posted)
                            (kd (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m)))
                            (ext (fn-ptx-nxt m)) (committed t) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
                 (:instance fn-ptx-end-cur-code (m0 (fn-ptx-chg m :committed nil)) (o :posted)
                            (kd (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m)))
                            (ext (fn-ptx-nxt m)) (fenced nil) (committed t) (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defthm fn-ptx-fence-finish-fields
  (implies (and (equal (fn-lgk-inflight ks) (list r)) (true-listp (fn-lgk-committed ks))
                (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks))) (not (consp (fn-lgk-batch ks))))
           (let ((k2 (fn-lgk-finish-one (fn-lgk-fence ks unit))))
             (and (equal (fn-lgk-committed k2) (append (fn-lgk-committed ks) (list r)))
                  (not (consp (fn-lgk-batch k2))) (not (consp (fn-lgk-inflight k2)))
                  (not (equal (fn-lgk-phase k2) :fault))
                  (equal (fn-lgk-acked k2) (len (fn-lgk-committed k2)))
                  (true-listp (fn-lgk-committed k2)))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-fence fn-lgk-finish-one) (fn-lg-log fn-lg-last-trailer fn-lgk-make fn-lgk-last fn-lgk-frontier
                                    fn-lgk-committed fn-lgk-acked fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-phase)))))
(defthm fn-ptx-len-of-message
  (equal (len (fn-ptx-message m id inc st)) (fn-ptx-nmsg m))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-message fn-ptx-nmsg fn-ptx-len-of-msg-range fn-ptx-nfix-natp-rw natp fn-ptx-spans-len-natp))
           :do-not-induct t)))
(defthm fn-ptx-elen-is-log-len
  (implies (equal (append (fn-ptx-message m id inc st) (fn-bs-zeros (nfix (fn-rtc-get 2 (fn-ptx-hs m))))) lg)
           (equal (fn-ptx-elen m) (len lg)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-elen fn-ptx-len-of-message fn-ptx-zeros-len fn-ptx-len-append fn-ptx-nfix-nfix))
           :do-not-induct t
           :use ((:instance fn-ptx-len-of-message)))))
(defthm fn-ptx-simp-commit
  (implies (and (fn-ptx-simp m ptd id inc st)
                (equal (fn-ptd-ph ptd) :syncing)
                (member-equal (fn-ptx-ph m2) '(:idle :reading))
                (equal (fn-ptd-ph ptd2) :ready)
                (equal (fn-ptd-ks ptd2) (fn-lgk-finish-one (fn-lgk-fence (fn-ptd-ks ptd) (fn-ptx-unit m))))
                (equal (fn-ptd-ext ptd2) (fn-ptd-nxt ptd))
                (equal (fn-ptx-kd m2) (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m)))
                (equal (fn-ptx-ext m2) (fn-ptx-nxt m)))
           (fn-ptx-simp m2 ptd2 id inc st2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-ptx-simp fn-ptx-ptd-phase member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart not)
               (:executable-counterpart eq) (:executable-counterpart consp) car-cons cdr-cons))
           :do-not-induct t
           :use ((:instance fn-ptx-fence-finish-fields (ks (fn-ptd-ks ptd)) (r (fn-ptd-rec ptd)) (unit (fn-ptx-unit m)))
                 (:instance fn-ptx-elen-is-log-len (lg (fn-lg-log (list (fn-ptd-rec ptd)) (fn-lgk-last (fn-ptd-ks ptd)) (fn-ptx-unit m))))
                 (:instance fn-ptx-commit-is-the-kernel-commit (ks (fn-ptd-ks ptd)) (r (fn-ptd-rec ptd)) (trailer (fn-rtc-get 1 (fn-ptx-hs m)))
                            (elen (fn-ptx-elen m)) (unit (fn-ptx-unit m)))))))
(defthm fn-ptx-p4-1-cm-ok
  (implies (and (equal (fn-ptx-ph m) :committing) (equal (fn-rtc-get 0 ev) :fsync)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-ptd-phase binary-append fn-ptx-code-of-ptd
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-cm-ok)
                 (:instance fn-ptx-simp-ph) (:instance fn-ptx-simp-rec)
                 (:instance fn-ptx-cmp-syncing-ok (st ptd) (o :ok) (unit (fn-ptx-unit m)))
                 (:instance fn-ptx-simp-commit (m2 (m2*)) (ptd2 (mv-nth 0 (fn-ptd-complete ptd (cons :fsync :ok) ino (fn-ptx-unit m)))))))))
(defthm fn-ptx-htrailer-is-digest
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (fn-ptx-hash-invp m id inc st)
                (not (< (+ (fn-ptx-hpos m q id inc st) 1024) (fn-ptx-hnmsg m))))
           (equal (fn-ptx-htrailer m q id inc st) (fn-blake3 (fn-ptx-message m id inc st))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-htrailer fn-ptx-hash-invp fn-ptx-mul-1024-floor fn-ptx-natp-floor-1024 natp fn-ptx-hnmsg-is-nmsg fn-ptx-nfix-natp-rw (:type-prescription fn-ptx-nmsg-natp)))
           :do-not-induct t
           :use ((:instance fn-ptx-hash-absorb-facts)
                 (:instance fn-ptx-message-is-msg-range)
                 (:instance fn-ptx-trailer-is-the-digest (j (floor (fn-ptx-hpos m q id inc st) 1024)) (n (fn-ptx-hnmsg m)) (spans (fn-ptx-spans m)))))))
(defthm fn-ptx-prepared-admits
  (implies (and (not (consp (fn-lgk-inflight ks))) (not (equal (fn-lgk-phase ks) :fault)) (not (consp (fn-lgk-batch ks)))
                (posp unit) (natp ext))
           (fn-lg-append-admitsp (fn-lgk-prepare ks r) unit
              (if (fn-olr-extension-needed-p (fn-lgk-frontier ks) (len (fn-lg-log (list r) (fn-lgk-last ks) unit)) ext unit)
                  (fn-olr-extension-target (fn-lgk-frontier ks) (len (fn-lg-log (list r) (fn-lgk-last ks) unit)) ext unit)
                ext)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-append-admitsp fn-lgk-fitsp fn-lgk-append-octets)
                           (fn-olr-extension-needed-p fn-olr-extension-target fn-lg-log fn-ptx-log-of-one fn-lg-entry fn-lg-pad-len fn-lgk-prepare fn-lgk-make fn-lgk-last fn-lgk-frontier fn-lgk-committed fn-lgk-acked fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-phase))
           :use ((:instance fn-ptx-prepare-fields)
                 (:instance fn-ptx-extension-target-bounds (front (fn-lgk-frontier ks)) (e (len (fn-lg-log (list r) (fn-lgk-last ks) unit))))
                 (:instance fn-ptx-no-extension-fits (front (fn-lgk-frontier ks)) (e (len (fn-lg-log (list r) (fn-lgk-last ks) unit))))))))
(defun fn-ptx-cdr-ind (w) (if (consp w) (fn-ptx-cdr-ind (cdr w)) w))
(defthm fn-ptx-take-len-append
  (implies (true-listp w) (equal (take (len w) (append w tr)) w))
  :hints (("Goal" :induct (fn-ptx-cdr-ind w))))
(defthm fn-ptx-arith-32 (equal (+ -32 (len w) 32) (len w)))
(defthm fn-ptx-record-of-trailered
  (implies (and (true-listp w) (equal (len tr) 32))
           (equal (nthcdr 42 (take (- (len (append w tr)) 32) (append w tr))) (nthcdr 42 w)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-len-append fn-ptx-take-len-append fn-ptx-arith-32 (:executable-counterpart binary-+) (:executable-counterpart unary--)))
           :use ((:instance fn-ptx-take-len-append)))))
(defthm fn-ptx-true-listp-append-tail
  (implies (true-listp (append h l)) (true-listp l))
  :hints (("Goal" :induct (fn-ptx-cdr-ind h))))
(defthm fn-ptx-true-listp-take (true-listp (take n w)))
(defthm fn-ptx-true-listp-of-append-tail
  (implies (equal (take n w) (append h l)) (true-listp l))
  :hints (("Goal" :do-not-induct t :in-theory (disable take)
           :use ((:instance fn-ptx-true-listp-take) (:instance fn-ptx-true-listp-append-tail)))))
(defthm fn-ptx-kd-last-of-kd-of
  (equal (fn-ptx-kd-last (fn-ptx-kd-of ks)) (fn-lgk-last ks))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-kd-of fn-ptx-kd-mk fn-ptx-kd-last fn-rtc-get (:executable-counterpart nfix)
                                  car-cons cdr-cons (:executable-counterpart nth) nth (:executable-counterpart zp) zp (:executable-counterpart binary-+) (:executable-counterpart equal)))
           :do-not-induct t)))
(defthm fn-ptx-hash-invp-elim
  (implies (fn-ptx-hash-invp m id inc st)
           (let ((w (fn-ptx-message m id inc st)))
             (and (fn-cbor-octet-listp w) (<= (fn-ptx-head-len) (len w))
                  (equal (take (fn-ptx-head-len) w)
                         (append (fn-ptx-frame-header (- (len w) (fn-ptx-head-len))) (fn-ptx-kd-last (fn-ptx-kd m)))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-hash-invp)) :do-not-induct t)))
(defthm fn-ptx-begin-pre-facts
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (fn-ptx-simp m ptd id inc st))
           (let ((w (fn-ptx-message m id inc st)) (last (fn-lgk-last (fn-ptd-ks ptd))))
             (and (true-listp w) (<= 42 (len w)) (true-listp last) (equal (len last) 32)
                  (equal (take 42 w) (append (fn-ptx-frame-header (- (len w) 42)) last)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-simp-hashing-facts fn-ptx-kd-last-of-kd-of fn-ptx-head-len-value commutativity-of-+ fn-ptx-true-listp-of-append-tail fn-cbor-octet-listp-implies-true-listp
                (:executable-counterpart equal) member-equal (:executable-counterpart member-equal)))
           :do-not-induct t
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-simp-hashing-facts) (:instance fn-ptx-hash-invp-elim)
                 (:instance fn-ptx-true-listp-of-append-tail (n 42) (w (fn-ptx-message m id inc st)) (h (fn-ptx-frame-header (- (len (fn-ptx-message m id inc st)) 42))) (l (fn-lgk-last (fn-ptd-ks ptd))))
                 (:instance fn-cbor-octet-listp-implies-true-listp (xs (fn-ptx-message m id inc st)))))))
(defthm fn-ptx-pad-of-message
  (equal (nfix (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) u))
         (fn-lg-pad-len (+ (len (fn-ptx-message m id inc st)) 32) u))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-pad-len fn-ptx-len-of-message fn-lg-pad-len-natp fn-ptx-nfix-natp-rw (:type-prescription fn-ptx-nmsg-natp) natp))
           :do-not-induct t)))
(defthm fn-ptx-append-assoc (equal (append (append a b) c) (append a b c)))
(defthm fn-ptx-record-of-trailered2
  (implies (and (equal w2 (append w tr)) (true-listp w) (equal (len tr) 32))
           (equal (nthcdr 42 (take (- (len w2) 32) w2)) (nthcdr 42 w)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-record-of-trailered)) :do-not-induct t)))
(defthm fn-ptx-record-of-m2
  (implies (and (equal (fn-ptx-message m2 id inc st2) (append w tr)) (true-listp w) (equal (len tr) 32))
           (equal (fn-ptx-record m2 id inc st2) (nthcdr 42 w)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-record fn-ptx-head-len-value))
           :do-not-induct t
           :use ((:instance fn-ptx-record-of-trailered2 (w2 (fn-ptx-message m2 id inc st2)))))))
(defthm fn-ptx-entry-bridge
  (implies (and (equal w2 (append w (fn-blake3 w))) (true-listp w) (<= 42 (len w)) (true-listp last) (equal (len last) 32)
                (equal (take 42 w) (append (fn-ptx-frame-header (- (len w) 42)) last)))
           (equal (append w2 (fn-bs-zeros (fn-lg-pad-len (+ (len w) 32) unit)))
                  (fn-lg-log (list (nthcdr 42 w)) last unit)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-append-assoc fn-blake3-shape))
           :do-not-induct t
           :use ((:instance fn-ptx-entry-of-message)))))
(defthm fn-ptx-prepare-txid
  (implies (not (equal (fn-lgk-phase ks) :fault))
           (equal (+ -1 (fn-lgk-next-txid (fn-lgk-prepare ks r))) (fn-lgk-next-txid ks)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-prepare-fields)) :do-not-induct t
           :use ((:instance fn-ptx-prepare-fields)))))
(defthm fn-ptx-get-of-list3 (and (equal (fn-rtc-get 0 (list a b c)) a) (equal (fn-rtc-get 1 (list a b c)) b) (equal (fn-rtc-get 2 (list a b c)) c)))
(defthm fn-ptx-get-of-list3-bridge
  (implies (equal hs2 (list a b c))
           (and (equal (fn-rtc-get 0 hs2) a) (equal (fn-rtc-get 1 hs2) b) (equal (fn-rtc-get 2 hs2) c))))
(defthm fn-ptx-simp-begin
  (implies (and (fn-ptx-okp m) (fn-ptx-simp m ptd id inc st) (equal (fn-ptx-ph m) :hashing)
                (member-equal (fn-ptx-ph m2) '(:extending :payload-writing))
                (equal (fn-ptd-ph ptd2) (fn-ptx-ptd-phase (fn-ptx-ph m2)))
                (equal (fn-ptd-ks ptd2) (fn-lgk-prepare (fn-ptd-ks ptd) (fn-ptd-rec ptd2)))
                (equal (fn-ptd-rec ptd2) (fn-ptx-record m2 id inc st2))
                (equal (fn-ptd-ext ptd2) (fn-ptd-ext ptd))
                (equal (fn-ptd-nxt ptd2) (fn-ptx-nxt m2))
                (equal (fn-ptx-kd m2) (fn-ptx-kd m)) (equal (fn-ptx-ext m2) (fn-ptx-ext m)) (equal (fn-ptx-geo m2) (fn-ptx-geo m))
                (equal (fn-ptx-hs m2) (list (fn-ptx-nmsg m) (fn-blake3 (fn-ptx-message m id inc st)) (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))))
                (equal (fn-ptx-message m2 id inc st2) (append (fn-ptx-message m id inc st) (fn-blake3 (fn-ptx-message m id inc st))))
                (fn-lg-append-admitsp (fn-ptd-ks ptd2) (fn-ptx-unit m) (fn-ptx-nxt m2)))
           (fn-ptx-simp m2 ptd2 id inc st2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-ptx-simp fn-ptx-unit fn-ptx-kd-before-take fn-ptx-ptd-phase binary-append
               member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart not)
               (:executable-counterpart eq) (:executable-counterpart consp) car-cons cdr-cons true-list-fix fn-ptx-get-of-list2
               (:type-prescription fn-lgk-next-txid) fn-ptx-nfix-natp-rw fn-ptx-len-of-message fn-blake3-shape
               fn-ptx-pad-of-message fn-lg-pad-len-natp fn-ptx-kd-of))
           :do-not-induct t
           :cases ((equal (fn-ptx-ph m2) :extending))
           :use ((:instance fn-ptx-begin-pre-facts)
                 (:instance fn-ptx-prepare-fields (ks (fn-ptd-ks ptd)) (r (fn-ptd-rec ptd2)))
                 (:instance fn-ptx-prepare-txid (ks (fn-ptd-ks ptd)) (r (fn-ptd-rec ptd2)))
                 (:instance fn-ptx-get-of-list3-bridge (hs2 (fn-ptx-hs m2)) (a (fn-ptx-nmsg m)) (b (fn-blake3 (fn-ptx-message m id inc st))) (c (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))))
                 (:instance fn-ptx-entry-bridge (w2 (fn-ptx-message m2 id inc st2)) (w (fn-ptx-message m id inc st)) (last (fn-lgk-last (fn-ptd-ks ptd))) (unit (fn-ptx-unit m)))
                 (:instance fn-ptx-record-of-m2 (w (fn-ptx-message m id inc st)) (tr (fn-blake3 (fn-ptx-message m id inc st))))
                 (:instance fn-ptx-trailer-of-message-frame (w (fn-ptx-message m id inc st)) (last (fn-lgk-last (fn-ptd-ks ptd))))
                 (:instance fn-ptx-simp-hashing-facts)))))
(defun fn-ptx-nthcdr-ind (n x) (if (zp n) x (fn-ptx-nthcdr-ind (- n 1) (cdr x))))
(defthm fn-ptx-cbor-octets-nthcdr
  (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (nthcdr n x)))
  :hints (("Goal" :induct (fn-ptx-nthcdr-ind n x) :in-theory (enable fn-cbor-octet-listp))))
(defthm fn-ptx-len-nthcdr42
  (implies (<= 42 (len w)) (equal (len (nthcdr 42 w)) (- (len w) 42)))
  :hints (("Goal" :in-theory (enable nthcdr len))))
(defthm fn-ptx-fmax-nat (natp (fn-ptx-fmax m)) :rule-classes :type-prescription)
(defthm fn-ptx-record-recordp
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (fn-ptx-hash-invp m id inc st))
           (fn-lg-recordp (nthcdr 42 (fn-ptx-message m id inc st)) (fn-ptx-fmax m)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
              '(fn-lg-recordp fn-ptx-head-len-value (:type-prescription fn-ptx-fmax) fn-ptx-fmax-nat natp (:type-prescription fn-ptx-nmsg-natp)
                (:executable-counterpart equal) member-equal (:executable-counterpart member-equal)))
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-hash-invp-elim) (:instance fn-ptx-len-of-message)
                 (:instance fn-ptx-cbor-octets-nthcdr (x (fn-ptx-message m id inc st)) (n 42))
                 (:instance fn-ptx-len-nthcdr42 (w (fn-ptx-message m id inc st)))))))
(defthm fn-ptx-helen-is-log-len
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (fn-ptx-simp m ptd id inc st))
           (equal (fn-ptx-helen m)
                  (len (fn-lg-log (list (nthcdr 42 (fn-ptx-message m id inc st))) (fn-lgk-last (fn-ptd-ks ptd)) (fn-ptx-unit m)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-helen fn-ptx-hpad fn-ptx-hnmsg-is-nmsg fn-ptx-len-append fn-ptx-zeros-len fn-blake3-shape fn-ptx-len-of-message
                fn-lg-pad-len-natp fn-ptx-pad-len fn-ptx-nfix-natp-rw natp (:type-prescription fn-ptx-nmsg-natp) commutativity-of-+))
           :use ((:instance fn-ptx-begin-pre-facts)
                 (:instance fn-ptx-entry-bridge (w2 (append (fn-ptx-message m id inc st) (fn-blake3 (fn-ptx-message m id inc st))))
                            (w (fn-ptx-message m id inc st)) (last (fn-lgk-last (fn-ptd-ks ptd))) (unit (fn-ptx-unit m)))))))
(defthm fn-ptx-unit-posp (posp (fn-ptx-unit m)) :hints (("Goal" :in-theory (enable fn-ptx-unit posp))))
(defthm fn-ptx-hf-facts
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (fn-ptx-simp m ptd id inc st))
           (let ((e (len (fn-lg-log (list (nthcdr 42 (fn-ptx-message m id inc st))) (fn-lgk-last (fn-ptd-ks ptd)) (fn-ptx-unit m)))))
             (and (equal (fn-ptx-hneed m) (fn-olr-extension-needed-p (fn-lgk-frontier (fn-ptd-ks ptd)) e (fn-ptd-ext ptd) (fn-ptx-unit m)))
                  (equal (fn-ptx-hnx m) (fn-olr-extension-target (fn-lgk-frontier (fn-ptd-ks ptd)) e (fn-ptd-ext ptd) (fn-ptx-unit m)))
                  (fn-lg-recordp (nthcdr 42 (fn-ptx-message m id inc st)) (fn-ptx-fmax m)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-hneed fn-ptx-hnx fn-ptx-simp-hashing-facts fn-ptx-kd-frontier fn-ptx-kd-of fn-ptx-kd-mk fn-ptx-unit posp
                fn-rtc-get (:executable-counterpart nth) nth car-cons cdr-cons (:executable-counterpart zp) zp (:executable-counterpart binary-+)
                (:executable-counterpart equal) fn-ptx-nfix-natp-rw natp fn-ptx-nfix-nfix (:type-prescription fn-lgk-frontier)))
           :use ((:instance fn-ptx-helen-is-log-len) (:instance fn-ptx-simp-hashing-facts)
                 (:instance fn-ptx-record-recordp)))))
(defthm fn-ptx-admitsp-nfix
  (equal (fn-lg-append-admitsp ks u (nfix e)) (fn-lg-append-admitsp ks u e))
  :hints (("Goal" :in-theory (e/d (fn-lg-append-admitsp fn-lgk-fitsp fn-ptx-nfix-nfix) (fn-lgk-append-octets fn-lg-log)))))
(defthm fn-ptx-step-hf-ext
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (equal (fn-rtc-get 0 ev) :timer)
                (not (< (+ (fn-ptx-hpos m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) 1024) (fn-ptx-hnmsg m)))
                (fn-ptx-hneed m) (not (<= (expt 2 64) (fn-ptx-hnx m))))
           (and (equal (fn-ptx-ph (m2*)) :extending) (equal (fn-ptx-kd (m2*)) (fn-ptx-kd m))
                (equal (fn-ptx-ext (m2*)) (fn-ptx-ext m)) (equal (fn-ptx-nxt (m2*)) (nfix (fn-ptx-hnx m)))
                (equal (fn-ptx-geo (m2*)) (fn-ptx-geo m))
                (equal (fn-ptx-hs (m2*)) (list (fn-ptx-hnmsg m) (fn-ptx-htrailer m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) (fn-ptx-hpad m)))))
  :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'fn-ptx-stp-th) '(fn-ptx-step fn-ptx-step1))
                                             '(fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-hash-0h2 fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt))
           :do-not-induct t)))
(defthm fn-ptx-step-hf-pay
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (equal (fn-rtc-get 0 ev) :timer)
                (not (< (+ (fn-ptx-hpos m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) 1024) (fn-ptx-hnmsg m)))
                (not (fn-ptx-hneed m)))
           (and (equal (fn-ptx-ph (m2*)) :payload-writing) (equal (fn-ptx-kd (m2*)) (fn-ptx-kd m))
                (equal (fn-ptx-ext (m2*)) (fn-ptx-ext m)) (equal (fn-ptx-nxt (m2*)) (fn-ptx-ext m))
                (equal (fn-ptx-geo (m2*)) (fn-ptx-geo m))
                (equal (fn-ptx-hs (m2*)) (list (fn-ptx-hnmsg m) (fn-ptx-htrailer m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) (fn-ptx-hpad m)))))
  :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'fn-ptx-stp-th) '(fn-ptx-step fn-ptx-step1))
                                             '(fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-hash-0h2 fn-ptx-accessors-of-mk fn-ptx-nfix-ext fn-ptx-nfix-nxt))
           :do-not-induct t)))
(defthm fn-ptx-run-begin
  (and (equal (mv-nth 0 (fn-ptd-run st (list (list :begin r)) ino unit max))
              (mv-nth 0 (fn-ptd-begin st r ino unit max)))
       (equal (mv-nth 2 (fn-ptd-run st (list (list :begin r)) ino unit max))
              (binary-append (mv-nth 2 (fn-ptd-begin st r ino unit max)) nil)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptd-run fn-ptd-step fn-ptx-ptd-run-nil (:executable-counterpart equal) (:executable-counterpart consp) car-cons cdr-cons
                (:executable-counterpart mv-nth) mv-nth (:executable-counterpart atom) atom zp (:executable-counterpart zp)
                (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart not)))
           :do-not-induct t)))
(defthm fn-ptx-rely-trailer
  (implies (and (fn-ptx-rely m m2 id inc st st2) (not (fn-ptx-in-flight-p (fn-ptx-ph m))) (fn-ptx-in-flight-p (fn-ptx-ph m2)))
           (equal (fn-ptx-message m2 id inc st2) (append (fn-ptx-message m id inc st) (fn-rtc-get 1 (fn-ptx-hs m2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-ptx-rely member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart not)))
           :do-not-induct t)))
(defthm fn-ptx-hf-m2-message
  (implies (and (fn-ptx-rely m m2 id inc st st2) (not (fn-ptx-in-flight-p (fn-ptx-ph m))) (fn-ptx-in-flight-p (fn-ptx-ph m2))
                (equal (fn-ptx-hs m2) (list a b c)))
           (equal (fn-ptx-message m2 id inc st2) (append (fn-ptx-message m id inc st) b)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-get-of-list3-bridge))
           :do-not-induct t
           :use ((:instance fn-ptx-rely-trailer) (:instance fn-ptx-get-of-list3-bridge (hs2 (fn-ptx-hs m2)))))))
(defthm fn-ptx-begin-fields-ext
  (implies (and (equal (fn-ptd-ph st) :ready)
                (not (consp (fn-lgk-batch (fn-ptd-ks st)))) (not (consp (fn-lgk-inflight (fn-ptd-ks st))))
                (not (equal (fn-lgk-phase (fn-ptd-ks st)) :fault))
                (fn-lg-recordp r max) (posp unit)
                (fn-olr-extension-needed-p (fn-lgk-frontier (fn-ptd-ks st)) (len (fn-lg-log (list r) (fn-lgk-last (fn-ptd-ks st)) unit)) (fn-ptd-ext st) unit))
           (let ((p2 (mv-nth 0 (fn-ptd-begin st r ino unit max))))
             (and (equal (fn-ptd-ph p2) :extending)
                  (equal (fn-ptd-ks p2) (fn-lgk-prepare (fn-ptd-ks st) r))
                  (equal (fn-ptd-rec p2) r)
                  (equal (fn-ptd-ext p2) (fn-ptd-ext st))
                  (equal (fn-ptd-nxt p2) (nfix (fn-olr-extension-target (fn-lgk-frontier (fn-ptd-ks st)) (len (fn-lg-log (list r) (fn-lgk-last (fn-ptd-ks st)) unit)) (fn-ptd-ext st) unit)))
                  (equal (mv-nth 2 (fn-ptd-begin st r ino unit max)) nil))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-ptd-begin-takes fn-ptd-fields-of-mk fn-ptx-nfix-ptd-ext member-equal (:executable-counterpart equal) car-cons cdr-cons (:executable-counterpart mv-nth) mv-nth zp (:executable-counterpart zp)
                (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart not) (:executable-counterpart consp)))
           :do-not-induct t)))
(defthm fn-ptx-begin-fields-pay
  (implies (and (equal (fn-ptd-ph st) :ready)
                (not (consp (fn-lgk-batch (fn-ptd-ks st)))) (not (consp (fn-lgk-inflight (fn-ptd-ks st))))
                (not (equal (fn-lgk-phase (fn-ptd-ks st)) :fault))
                (fn-lg-recordp r max) (posp unit)
                (not (fn-olr-extension-needed-p (fn-lgk-frontier (fn-ptd-ks st)) (len (fn-lg-log (list r) (fn-lgk-last (fn-ptd-ks st)) unit)) (fn-ptd-ext st) unit)))
           (let ((p2 (mv-nth 0 (fn-ptd-begin st r ino unit max))))
             (and (equal (fn-ptd-ph p2) :writing)
                  (equal (fn-ptd-ks p2) (fn-lgk-prepare (fn-ptd-ks st) r))
                  (equal (fn-ptd-rec p2) r)
                  (equal (fn-ptd-ext p2) (fn-ptd-ext st))
                  (equal (fn-ptd-nxt p2) (fn-ptd-ext st))
                  (equal (mv-nth 2 (fn-ptd-begin st r ino unit max)) nil))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-ptd-begin-takes fn-ptd-fields-of-mk fn-ptx-nfix-ptd-ext fn-ptx-nfix-ptd-ext member-equal (:executable-counterpart equal) car-cons cdr-cons (:executable-counterpart mv-nth) mv-nth zp (:executable-counterpart zp)
                (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart not) (:executable-counterpart consp)))
           :do-not-induct t)))
(defthm fn-ptx-record-m2-rule
  (implies (and (equal (fn-ptx-message m2 id inc st2) (append (fn-ptx-message m id inc st) (fn-blake3 (fn-ptx-message m id inc st))))
                (true-listp (fn-ptx-message m id inc st)))
           (equal (fn-ptx-record m2 id inc st2) (nthcdr 42 (fn-ptx-message m id inc st))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-blake3-shape))
           :use ((:instance fn-ptx-record-of-m2 (w (fn-ptx-message m id inc st)) (tr (fn-blake3 (fn-ptx-message m id inc st))))))))
(defthm fn-ptx-p4-1-hf-ext
  (implies (and (equal (fn-ptx-ph m) :hashing) (equal (fn-rtc-get 0 ev) :timer)
                (not (< (+ (fn-ptx-hpos m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) 1024) (fn-ptx-hnmsg m)))
                (fn-ptx-hneed m) (not (<= (expt 2 64) (fn-ptx-hnx m))))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-record-m2-rule fn-ptx-hpad fn-ptx-hnmsg-is-nmsg fn-blake3-shape fn-cbor-octet-listp-implies-true-listp fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-begin binary-append fn-ptd-fields-of-mk fn-ptx-nfix-ptd-ext fn-ptx-nfix-ptd-nxt
                fn-ptx-in-flight-p fn-ptx-ptd-phase fn-ptx-admitsp-nfix (:type-prescription fn-ptd-ext) natp
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-hf-ext) (:instance fn-ptx-begin-pre-facts)
                 (:instance fn-ptx-simp-hashing-facts)
                 (:instance fn-ptx-hf-facts)
                 (:instance fn-ptx-htrailer-is-digest)
                 (:instance fn-ptx-unit-posp)
                 (:instance fn-ptx-hf-m2-message (m2 (m2*)) (a (fn-ptx-hnmsg m)) (b (fn-blake3 (fn-ptx-message m id inc st))) (c (fn-ptx-hpad m)))
                 (:instance fn-ptx-begin-fields-ext (st ptd) (r (fn-ptx-record (m2*) id inc st2)) (unit (fn-ptx-unit m)) (max (fn-ptx-fmax m)))
                 (:instance fn-ptx-prepared-admits (ks (fn-ptd-ks ptd)) (r (fn-ptx-record (m2*) id inc st2)) (unit (fn-ptx-unit m)) (ext (fn-ptd-ext ptd)))
                 (:instance fn-ptx-simp-begin (m2 (m2*)) (ptd2 (mv-nth 0 (fn-ptd-begin ptd (fn-ptx-record (m2*) id inc st2) ino (fn-ptx-unit m) (fn-ptx-fmax m)))))))))
(defthm fn-ptx-p4-1-hf-pay
  (implies (and (equal (fn-ptx-ph m) :hashing) (equal (fn-rtc-get 0 ev) :timer)
                (not (< (+ (fn-ptx-hpos m q (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) 1024) (fn-ptx-hnmsg m)))
                (not (fn-ptx-hneed m)))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-record-m2-rule fn-ptx-hpad fn-ptx-hnmsg-is-nmsg fn-blake3-shape fn-cbor-octet-listp-implies-true-listp fn-ptx-p4-1 fn-ptx-ptd-ins fn-ptx-run-begin binary-append fn-ptd-fields-of-mk fn-ptx-nfix-ptd-ext fn-ptx-nfix-ptd-nxt
                fn-ptx-in-flight-p fn-ptx-ptd-phase fn-ptx-admitsp-nfix (:type-prescription fn-ptd-ext) natp
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-hf-pay) (:instance fn-ptx-begin-pre-facts)
                 (:instance fn-ptx-simp-hashing-facts)
                 (:instance fn-ptx-hf-facts)
                 (:instance fn-ptx-htrailer-is-digest)
                 (:instance fn-ptx-unit-posp)
                 (:instance fn-ptx-hf-m2-message (m2 (m2*)) (a (fn-ptx-hnmsg m)) (b (fn-blake3 (fn-ptx-message m id inc st))) (c (fn-ptx-hpad m)))
                 (:instance fn-ptx-begin-fields-pay (st ptd) (r (fn-ptx-record (m2*) id inc st2)) (unit (fn-ptx-unit m)) (max (fn-ptx-fmax m)))
                 (:instance fn-ptx-prepared-admits (ks (fn-ptd-ks ptd)) (r (fn-ptx-record (m2*) id inc st2)) (unit (fn-ptx-unit m)) (ext (fn-ptd-ext ptd)))
                 (:instance fn-ptx-simp-begin (m2 (m2*)) (ptd2 (mv-nth 0 (fn-ptd-begin ptd (fn-ptx-record (m2*) id inc st2) ino (fn-ptx-unit m) (fn-ptx-fmax m)))))))))
(defthm fn-ptx-p4-1-hash-timer
  (implies (and (equal (fn-ptx-ph m) :hashing) (equal (fn-rtc-get 0 ev) :timer))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory) :do-not-induct t
           :use ((:instance fn-ptx-p4-1-hash-more) (:instance fn-ptx-p4-1-hash-refused)
                 (:instance fn-ptx-p4-1-hf-ext) (:instance fn-ptx-p4-1-hf-pay)))))
(defthm fn-ptx-p4-1-driver
  (implies (fn-ptx-driver-arm (fn-ptx-ph m) (fn-rtc-get 0 ev))
           (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-driver-arm (:executable-counterpart equal)))
           :do-not-induct t
           :use ((:instance fn-ptx-p4-1-ext-ok) (:instance fn-ptx-p4-1-ext-bad)
                 (:instance fn-ptx-p4-1-xs-ok) (:instance fn-ptx-p4-1-xs-bad)
                 (:instance fn-ptx-p4-1-pw-more) (:instance fn-ptx-p4-1-pw-bad)
                 (:instance fn-ptx-p4-1-lw-ok) (:instance fn-ptx-p4-1-lw-bad)
                 (:instance fn-ptx-p4-1-cm-ok) (:instance fn-ptx-p4-1-cm-bad)))))
(defthm fn-ptx-simulates-the-driver-step
  (fn-ptx-p4-1 m ptd ev st st2 q fo ino id inc)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(member-equal (:executable-counterpart member-equal)))
           :do-not-induct t
           :use ((:instance fn-ptx-p4-1-driver) (:instance fn-ptx-p4-1-hash-timer)
                 (:instance fn-ptx-p4-1-reading) (:instance fn-ptx-p4-1-opened-or-hand)
                 (:instance fn-ptx-p4-1-handed-idle) (:instance fn-ptx-p4-1-handed-busy)
                 (:instance fn-ptx-p4-1-other)))))

; -----------------------------------------------------------------------------
; P4-2 and the composition (Sonnet 7): the machine's posted records are the driver's, by induction
; over the trace on the simulation step (fn-ptx-p4-1x: P4-1 with the driver's own bound and the
; posted records of the step); then L's keystone carries them to every later cut.
(defthm fn-ptx-step-not-closed
  (implies (and (fn-ptx-okp m) (not (equal (fn-ptx-ph m) :closed)))
           (not (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-step m ev st q))) :closed)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-accessors-of-mk fn-ptx-end-0 fn-ptx-start-0 fn-ptx-hash-0h2
                      (:executable-counterpart equal) (:executable-counterpart eq) (:executable-counterpart consp) member-equal (:executable-counterpart member-equal)
                      (:executable-counterpart not) fn-rtc-ev-id fn-rtc-ev-inc))
           :do-not-induct t
           :use ((:instance fn-ptx-read-fields (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defun fn-ptx-run-ind (st a ino unit max)
  (declare (xargs :measure (len a)))
  (if (atom a) st
    (mv-let (st1 a1 w1 o1) (fn-ptd-step st (car a) ino unit max)
      (declare (ignore a1 w1 o1))
      (fn-ptx-run-ind st1 (cdr a) ino unit max))))
(defthm fn-ptx-run-append
  (equal (mv-nth 2 (fn-ptd-run st (append a b) ino unit max))
         (append (mv-nth 2 (fn-ptd-run st a ino unit max))
                 (mv-nth 2 (fn-ptd-run (mv-nth 0 (fn-ptd-run st a ino unit max)) b ino unit max))))
  :hints (("Goal" :induct (fn-ptx-run-ind st a ino unit max)
                  :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptd-run binary-append mv-nth (:executable-counterpart mv-nth) zp (:executable-counterpart zp) (:executable-counterpart equal)
                      (:executable-counterpart consp) car-cons cdr-cons fn-ptx-append-assoc (:definition fn-ptx-run-ind) (:induction fn-ptx-run-ind) atom)))))
(defthm fn-ptx-step-ans-shape
  (let ((w (mv-nth 2 (fn-ptd-step st in ino unit max))))
    (or (null w) (and (consp w) (null (cdr w)) (consp (car w)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptd-step fn-ptd-begin fn-ptd-complete (:executable-counterpart equal) (:executable-counterpart consp) car-cons cdr-cons
                (:executable-counterpart mv-nth) mv-nth zp (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)
                (:executable-counterpart not) (:executable-counterpart null) null))
           :do-not-induct t)))
(defthm fn-ptx-hashing-fmax-ge
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :hashing) (fn-ptx-simp m ptd id inc st))
           (<= 32 (fn-ptx-fmax m)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-simp-hashing-facts fn-ptx-head-len-value fn-ptx-len-of-message (:type-prescription fn-ptx-nmsg-natp)
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)))
           :do-not-induct t
           :use ((:instance fn-ptx-okp-elim) (:instance fn-ptx-simp-hashing-facts) (:instance fn-ptx-hash-invp-elim)))))
(defthm fn-ptx-ptd-ins-nonbegin
  (implies (not (equal (fn-ptx-ph m) :hashing))
           (let ((ins (fn-ptx-ptd-ins m ev m2 r fo)))
             (or (null ins) (and (consp ins) (null (cdr ins)) (consp (car ins)) (not (equal (car (car ins)) :begin))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-ptd-ins member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons (:executable-counterpart consp)
                (:executable-counterpart null) null (:executable-counterpart not)))
           :do-not-induct t)))
(defthm fn-ptx-ins-form
  (implies (and (consp ins) (null (cdr ins)) (consp (car ins)))
           (equal ins (list (cons (car (car ins)) (cdr (car ins))))))
  :rule-classes nil)
(defthm fn-ptx-run-max-indep
  (implies (or (null ins) (and (consp ins) (null (cdr ins)) (consp (car ins)) (not (equal (car (car ins)) :begin))))
           (and (equal (mv-nth 0 (fn-ptd-run st ins ino unit max1)) (mv-nth 0 (fn-ptd-run st ins ino unit max2)))
                (equal (mv-nth 2 (fn-ptd-run st ins ino unit max1)) (mv-nth 2 (fn-ptd-run st ins ino unit max2)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-run-one fn-ptx-ptd-run-nil (:executable-counterpart null) null (:executable-counterpart equal) (:executable-counterpart consp)
                car-cons cdr-cons))
           :do-not-induct t
           :use ((:instance fn-ptx-ins-form)
                 (:instance fn-ptx-run-one (k (car (car ins))) (o (cdr (car ins))) (max max1))
                 (:instance fn-ptx-run-one (k (car (car ins))) (o (cdr (car ins))) (max max2))))))
(defthm fn-ptx-step-reqs-eq
  (implies (fn-ptx-okp m)
           (equal (mv-nth 1 (fn-ptx-step m ev st q)) (mv-nth 1 (fn-ptx-step1 m ev st q))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-step (:executable-counterpart mv-nth) mv-nth))
           :use ((:instance fn-ptx-okp-wfp)) :do-not-induct t)))
(defthm fn-ptx-step-code0
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-cur-code m (mv-nth 1 (fn-ptx-step m ev st q))) 0))
           (and (equal (fn-ptx-ph m) :committing) (equal (fn-rtc-get 0 ev) :fsync)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-step-reqs-eq (:executable-counterpart equal)))
           :do-not-induct t
           :use ((:instance fn-ptx-step1-code-facts)))))
(defthm fn-ptx-ptd-ins-shape
  (let ((ins (fn-ptx-ptd-ins m ev m2 r fo)))
    (or (null ins) (and (consp ins) (null (cdr ins)) (consp (car ins)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-ptd-ins member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons (:executable-counterpart consp)
                (:executable-counterpart null) null (:executable-counterpart not)))
           :do-not-induct t)))
(defthm fn-ptx-run-single-ans-shape
  (implies (and (consp ins) (null (cdr ins)))
           (let ((w (mv-nth 2 (fn-ptd-run st ins ino unit max))))
             (or (null w) (and (consp w) (null (cdr w)) (consp (car w))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptd-run fn-ptx-ptd-run-nil (:executable-counterpart equal) (:executable-counterpart consp) car-cons cdr-cons
                (:executable-counterpart mv-nth) mv-nth (:executable-counterpart atom) atom zp (:executable-counterpart zp)
                (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart not) binary-append
                (:executable-counterpart null) null))
           :do-not-induct t
           :use ((:instance fn-ptx-step-ans-shape (in (car ins)))))))
(defthm fn-ptx-cm-ok-ans
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :committing) (equal (fn-rtc-get 0 ev) :fsync)
                (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done) (fn-ptx-simp m ptd id inc st))
           (equal (mv-nth 2 (fn-ptd-run ptd (fn-ptx-ptd-ins m ev (m2*) (fn-ptx-record (m2*) id inc st2) fo) ino (fn-ptx-unit m) max))
                  (list (cons :posted (fn-ptx-record m id inc st)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-ptd-ins fn-ptx-run-one fn-ptx-ptd-phase binary-append
                member-equal (:executable-counterpart member-equal) (:executable-counterpart equal) car-cons cdr-cons
                (:executable-counterpart consp) (:executable-counterpart eq) (:executable-counterpart not) (:executable-counterpart mv-nth)))
           :do-not-induct t
           :use ((:instance fn-ptx-step-cm-ok)
                 (:instance fn-ptx-simp-ph) (:instance fn-ptx-simp-rec)
                 (:instance fn-ptx-cmp-syncing-ok (st ptd) (o :ok) (unit (fn-ptx-unit m)))))))
(defthm fn-ptx-nfix-big (implies (and (equal f (nfix max)) (<= 32 f)) (equal max f)) :rule-classes nil)
(defthm fn-ptx-run-fmax-eq
  (implies (and (fn-ptx-okp m) (fn-ptx-simp m ptd id inc st) (equal (fn-ptx-fmax m) (nfix max)))
           (let ((ins (fn-ptx-ptd-ins m ev m2 r fo)))
             (and (equal (mv-nth 0 (fn-ptd-run ptd ins ino unit max)) (mv-nth 0 (fn-ptd-run ptd ins ino unit (fn-ptx-fmax m))))
                  (equal (mv-nth 2 (fn-ptd-run ptd ins ino unit max)) (mv-nth 2 (fn-ptd-run ptd ins ino unit (fn-ptx-fmax m)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-run-max-indep (:executable-counterpart equal)))
           :do-not-induct t
           :cases ((equal (fn-ptx-ph m) :hashing))
           :use ((:instance fn-ptx-hashing-fmax-ge) (:instance fn-ptx-ptd-ins-nonbegin) (:instance fn-ptx-nfix-big (f (fn-ptx-fmax m)))
                 (:instance fn-ptx-run-max-indep (st ptd) (ins (fn-ptx-ptd-ins m ev m2 r fo)) (max1 max) (max2 (fn-ptx-fmax m)))))))
(defthm fn-ptx-posted-from-parts
  (implies (and (or (null ans) (and (consp ans) (null (cdr ans)) (consp (car ans))))
                (implies (consp ans) (and (equal cc (fn-ptx-code-of-ptd ans)) (equal (cdr (car ans)) rec)))
                (implies (equal cc 0) (consp ans)))
           (equal (fn-ptd-posted ans) (if (equal cc 0) (list rec) nil)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptd-posted fn-ptx-code-of-ptd (:executable-counterpart equal) (:executable-counterpart consp) car-cons cdr-cons
                (:executable-counterpart null) null (:executable-counterpart not)))
           :do-not-induct t
           :cases ((consp ans)))))
(defun-nx fn-ptx-p4-1x (m ptd ev st st2 q fo ino id inc max)
  (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
    (declare (ignore c))
    (mv-let (ptd2 acts ans ops)
        (fn-ptd-run ptd (fn-ptx-ptd-ins m ev m2 (fn-ptx-record m2 id inc st2) fo) ino (fn-ptx-unit m) max)
      (declare (ignore acts ops))
      (implies (and (equal (fn-ptx-fmax m) (nfix max)) (fn-ptx-okp m) (not (equal (fn-ptx-ph m) :closed))
                    (fn-ptx-simp m ptd id inc st) (fn-ptx-rely m m2 id inc st st2)
                    (equal (fn-rtc-ev-id ev) id) (equal (fn-rtc-ev-inc ev) inc))
               (and (fn-ptx-simp m2 ptd2 id inc st2)
                    (equal (fn-ptd-posted ans)
                           (if (equal (fn-ptx-cur-code m reqs) 0) (list (fn-ptx-record m id inc st)) nil)))))))
(defthm fn-ptx-p4-1x-holds
  (fn-ptx-p4-1x m ptd ev st st2 q fo ino id inc max)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-p4-1x fn-ptx-p4-1 fn-ptx-ptd-run-nil (:executable-counterpart equal) (:executable-counterpart not) (:executable-counterpart consp) (:executable-counterpart null) null))
           :do-not-induct t
           :use ((:instance fn-ptx-simulates-the-driver-step)
                 (:instance fn-ptx-run-fmax-eq (unit (fn-ptx-unit m)) (m2 (m2*)) (r (fn-ptx-record (m2*) id inc st2)))
                 (:instance fn-ptx-ptd-ins-shape (m2 (m2*)) (r (fn-ptx-record (m2*) id inc st2)))
                 (:instance fn-ptx-run-single-ans-shape (st ptd) (ins (fn-ptx-ptd-ins m ev (m2*) (fn-ptx-record (m2*) id inc st2) fo)) (unit (fn-ptx-unit m)) (max (fn-ptx-fmax m)))
                 (:instance fn-ptx-step-code0)
                 (:instance fn-ptx-cm-ok-ans (max (fn-ptx-fmax m)))
                 (:instance fn-ptx-posted-from-parts
                            (ans (mv-nth 2 (fn-ptd-run ptd (fn-ptx-ptd-ins m ev (m2*) (fn-ptx-record (m2*) id inc st2) fo) ino (fn-ptx-unit m) (fn-ptx-fmax m))))
                            (cc (fn-ptx-cur-code m (reqs*))) (rec (fn-ptx-record m id inc st)))))))
(defthm fn-ptx-read-geo
  (implies (equal (fn-ptx-ph m) :reading)
           (equal (fn-ptx-geo (mv-nth 0 (fn-ptx-read m q id inc st))) (fn-ptx-geo m)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn-ptx-read-1 fn-ptx-rd-end0 fn-ptx-rd-endr fn-ptx-rd-cont fn-ptx-rd-hashing
                     fn-ptx-end-0 fn-ptx-start-0 fn-ptx-accessors-of-mk fn-ptx-nfix-ext member-equal
                     (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart mv-nth) mv-nth))
           :do-not-induct t)))
(defthm fn-ptx-step-geo
  (implies (and (fn-ptx-okp m) (not (equal (fn-ptx-ph m) :closed)))
           (equal (fn-ptx-geo (mv-nth 0 (fn-ptx-step m ev st q))) (fn-ptx-geo m)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-ptx-step-0 fn-ptx-step1-0 fn-ptx-accessors-of-mk fn-ptx-end-0 fn-ptx-start-0 fn-ptx-hash-0h2
                      (:executable-counterpart equal) (:executable-counterpart eq) (:executable-counterpart consp) member-equal (:executable-counterpart member-equal)
                      (:executable-counterpart not) fn-rtc-ev-id fn-rtc-ev-inc))
           :do-not-induct t
           :use ((:instance fn-ptx-read-geo (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))))))
(defmacro tev* () '(nth 0 (car trace)))
(defmacro tst* () '(nth 1 (car trace)))
(defmacro tq* () '(nth 2 (car trace)))
(defmacro tfo* () '(nth 3 (car trace)))
(defmacro tst2* () '(if (consp (cdr trace)) (nth 1 (cadr trace)) (nth 1 (car trace))))
(defmacro tm2* () '(mv-nth 0 (fn-ptx-step m (tev*) (tst*) (tq*))))
(deftheory fn-ptx-tr-th
  (union-theories (theory 'minimal-theory)
    '((:executable-counterpart consp) (:executable-counterpart equal) (:executable-counterpart mv-nth) mv-nth zp (:executable-counterpart zp)
      car-cons cdr-cons (:executable-counterpart not) binary-append)))
(defthm fn-ptx-trace-run-ins
  (implies (consp trace)
           (equal (mv-nth 1 (fn-ptx-trace-run m trace id inc))
                  (append (fn-ptx-ptd-ins m (tev*) (tm2*) (fn-ptx-record (tm2*) id inc (tst2*)) (tfo*))
                          (mv-nth 1 (fn-ptx-trace-run (tm2*) (cdr trace) id inc)))))
  :hints (("Goal" :in-theory (theory 'fn-ptx-tr-th) :expand ((fn-ptx-trace-run m trace id inc)) :do-not-induct t)))
(defthm fn-ptx-trace-run-posted
  (implies (consp trace)
           (equal (mv-nth 2 (fn-ptx-trace-run m trace id inc))
                  (if (equal (fn-ptx-cur-code m (mv-nth 1 (fn-ptx-step m (tev*) (tst*) (tq*)))) 0)
                      (cons (fn-ptx-record m id inc (tst*)) (mv-nth 2 (fn-ptx-trace-run (tm2*) (cdr trace) id inc)))
                    (mv-nth 2 (fn-ptx-trace-run (tm2*) (cdr trace) id inc)))))
  :hints (("Goal" :in-theory (theory 'fn-ptx-tr-th) :expand ((fn-ptx-trace-run m trace id inc)) :do-not-induct t)))
(defthm fn-ptx-trace-relies-unfold
  (implies (consp trace)
           (equal (fn-ptx-trace-relies-p m trace id inc)
                  (and (equal (fn-rtc-ev-id (tev*)) id) (equal (fn-rtc-ev-inc (tev*)) inc)
                       (fn-ptx-rely m (tm2*) id inc (tst*) (tst2*))
                       (fn-ptx-trace-relies-p (tm2*) (cdr trace) id inc))))
  :hints (("Goal" :in-theory (theory 'fn-ptx-tr-th) :expand ((fn-ptx-trace-relies-p m trace id inc)) :do-not-induct t)))
(defthm fn-ptx-geo-same (implies (equal (fn-ptx-geo m2) (fn-ptx-geo m)) (and (equal (fn-ptx-fmax m2) (fn-ptx-fmax m)) (equal (fn-ptx-unit m2) (fn-ptx-unit m))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-fmax fn-ptx-unit)) :do-not-induct t)))
(defun-nx fn-ptx-trace-ind (m ptd trace id inc ino max)
  (declare (xargs :measure (len trace) :hints (("Goal" :in-theory (union-theories '(len o< o-finp o-p natp (:type-prescription len) (:compound-recognizer natp-compound-recognizer)) (theory 'minimal-theory))))))
  (if (atom trace) nil
    (let* ((x (car trace)) (ev (nth 0 x)) (st (nth 1 x)) (q (nth 2 x)) (fo (nth 3 x))
           (st2 (if (consp (cdr trace)) (nth 1 (cadr trace)) st))
           (m2 (mv-nth 0 (fn-ptx-step m ev st q)))
           (ptd2 (mv-nth 0 (fn-ptd-run ptd (fn-ptx-ptd-ins m ev m2 (fn-ptx-record m2 id inc st2) fo) ino (fn-ptx-unit m) max))))
      (fn-ptx-trace-ind m2 ptd2 (cdr trace) id inc ino max))))
(defmacro tptd2* () '(mv-nth 0 (fn-ptd-run ptd (fn-ptx-ptd-ins m (tev*) (tm2*) (fn-ptx-record (tm2*) id inc (tst2*)) (tfo*)) ino (fn-ptx-unit m) max)))
(defthm fn-ptx-gen-alg
  (implies (and (equal p2 (fn-ptd-posted a2))
                (equal (fn-ptd-posted a0) (if c (list rec) nil)))
           (equal (if c (cons rec p2) p2) (fn-ptd-posted (append a0 a2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptd-posted-of-append binary-append (:executable-counterpart consp) car-cons cdr-cons (:executable-counterpart equal)))
           :do-not-induct t
           :cases (c))))
(defthm fn-ptx-gen-chain
  (implies (and (equal tt (if c (cons rec p2) p2))
                (equal ii (append a0 i2))
                (equal p2 (fn-ptd-posted (mv-nth 2 (fn-ptd-run (mv-nth 0 (fn-ptd-run ptd a0 ino unit max)) i2 ino unit max))))
                (equal (fn-ptd-posted (mv-nth 2 (fn-ptd-run ptd a0 ino unit max))) (if c (list rec) nil)))
           (equal tt (fn-ptd-posted (mv-nth 2 (fn-ptd-run ptd ii ino unit max)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-run-append))
           :do-not-induct t
           :use ((:instance fn-ptx-gen-alg (a0 (mv-nth 2 (fn-ptd-run ptd a0 ino unit max)))
                            (a2 (mv-nth 2 (fn-ptd-run (mv-nth 0 (fn-ptd-run ptd a0 ino unit max)) i2 ino unit max))))))))
(defthm fn-ptx-p4-1x-facts
  (implies (and (equal (fn-ptx-fmax m) (nfix max)) (fn-ptx-okp m) (not (equal (fn-ptx-ph m) :closed))
                (fn-ptx-simp m ptd id inc st) (fn-ptx-rely m (mv-nth 0 (fn-ptx-step m ev st q)) id inc st st2)
                (equal (fn-rtc-ev-id ev) id) (equal (fn-rtc-ev-inc ev) inc))
           (and (fn-ptx-simp (mv-nth 0 (fn-ptx-step m ev st q))
                             (mv-nth 0 (fn-ptd-run ptd (fn-ptx-ptd-ins m ev (mv-nth 0 (fn-ptx-step m ev st q)) (fn-ptx-record (mv-nth 0 (fn-ptx-step m ev st q)) id inc st2) fo) ino (fn-ptx-unit m) max))
                             id inc st2)
                (equal (fn-ptd-posted (mv-nth 2 (fn-ptd-run ptd (fn-ptx-ptd-ins m ev (mv-nth 0 (fn-ptx-step m ev st q)) (fn-ptx-record (mv-nth 0 (fn-ptx-step m ev st q)) id inc st2) fo) ino (fn-ptx-unit m) max)))
                       (if (equal (fn-ptx-cur-code m (mv-nth 1 (fn-ptx-step m ev st q))) 0) (list (fn-ptx-record m id inc st)) nil))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-p4-1x (:executable-counterpart not) (:executable-counterpart equal)))
           :do-not-induct t
           :use ((:instance fn-ptx-p4-1x-holds)))))
(defthm fn-ptx-gen-step
  (implies (and (consp trace) (fn-ptx-okp m) (not (equal (fn-ptx-ph m) :closed))
                (fn-ptx-trace-relies-p m trace id inc) (equal (fn-ptx-fmax m) (nfix max))
                (implies (consp trace) (fn-ptx-simp m ptd id inc (nth 1 (car trace))))
                (implies (and (fn-ptx-okp (tm2*)) (not (equal (fn-ptx-ph (tm2*)) :closed))
                              (fn-ptx-trace-relies-p (tm2*) (cdr trace) id inc)
                              (equal (fn-ptx-fmax (tm2*)) (nfix max))
                              (implies (consp (cdr trace)) (fn-ptx-simp (tm2*) (tptd2*) id inc (nth 1 (car (cdr trace))))))
                         (equal (mv-nth 2 (fn-ptx-trace-run (tm2*) (cdr trace) id inc))
                                (fn-ptd-posted (mv-nth 2 (fn-ptd-run (tptd2*) (mv-nth 1 (fn-ptx-trace-run (tm2*) (cdr trace) id inc)) ino (fn-ptx-unit (tm2*)) max))))))
           (equal (mv-nth 2 (fn-ptx-trace-run m trace id inc))
                  (fn-ptd-posted (mv-nth 2 (fn-ptd-run ptd (mv-nth 1 (fn-ptx-trace-run m trace id inc)) ino (fn-ptx-unit m) max)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:executable-counterpart equal) (:executable-counterpart not)))
           :do-not-induct t
           :use ((:instance fn-ptx-trace-run-posted) (:instance fn-ptx-trace-run-ins) (:instance fn-ptx-trace-relies-unfold)
                 (:instance fn-ptx-p4-1x-facts (ev (tev*)) (st (tst*)) (q (tq*)) (fo (tfo*)) (st2 (tst2*)))
                 (:instance fn-ptx-step-keeps-ok (ev (tev*)) (st (tst*)) (q (tq*)))
                 (:instance fn-ptx-step-not-closed (ev (tev*)) (st (tst*)) (q (tq*)))
                 (:instance fn-ptx-step-geo (ev (tev*)) (st (tst*)) (q (tq*)))
                 (:instance fn-ptx-geo-same (m2 (tm2*)))
                 (:instance fn-ptx-gen-chain
                            (tt (mv-nth 2 (fn-ptx-trace-run m trace id inc)))
                            (ii (mv-nth 1 (fn-ptx-trace-run m trace id inc)))
                            (a0 (fn-ptx-ptd-ins m (tev*) (tm2*) (fn-ptx-record (tm2*) id inc (tst2*)) (tfo*)))
                            (i2 (mv-nth 1 (fn-ptx-trace-run (tm2*) (cdr trace) id inc)))
                            (p2 (mv-nth 2 (fn-ptx-trace-run (tm2*) (cdr trace) id inc)))
                            (c (equal (fn-ptx-cur-code m (mv-nth 1 (fn-ptx-step m (tev*) (tst*) (tq*)))) 0))
                            (rec (fn-ptx-record m id inc (tst*))) (unit (fn-ptx-unit m)))))))
(defthm fn-ptx-trace-run-atom
  (implies (atom trace)
           (and (equal (mv-nth 1 (fn-ptx-trace-run m trace id inc)) nil)
                (equal (mv-nth 2 (fn-ptx-trace-run m trace id inc)) nil)))
  :hints (("Goal" :in-theory (theory 'fn-ptx-tr-th) :expand ((fn-ptx-trace-run m trace id inc)) :do-not-induct t)))
(defthm fn-ptx-trace-posted-gen
  (implies (and (fn-ptx-okp m) (not (equal (fn-ptx-ph m) :closed))
                (fn-ptx-trace-relies-p m trace id inc)
                (equal (fn-ptx-fmax m) (nfix max))
                (implies (consp trace) (fn-ptx-simp m ptd id inc (nth 1 (car trace)))))
           (equal (mv-nth 2 (fn-ptx-trace-run m trace id inc))
                  (fn-ptd-posted (mv-nth 2 (fn-ptd-run ptd (mv-nth 1 (fn-ptx-trace-run m trace id inc)) ino (fn-ptx-unit m) max)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ptx-trace-ind m ptd trace id inc ino max)
                  :in-theory (union-theories (theory 'minimal-theory)
                    '((:induction fn-ptx-trace-ind) fn-ptx-trace-run-atom fn-ptx-ptd-run-nil fn-ptd-posted atom (:executable-counterpart equal)
                      (:executable-counterpart null) null (:executable-counterpart consp))))
          ("Subgoal *1/2" :use ((:instance fn-ptx-gen-step)))))
(defthm fn-ptx-relp-unit-posp
  (implies (fn-lgk-relp bs ks ino genesis max) (posp (fn-bs-unit bs)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lgk-relp)) :do-not-induct t)))
(defthm fn-ptx-opened-fields
  (let ((m (fn-ptx-opened kd ext geo)))
    (and (equal (fn-ptx-ph m) :idle) (equal (fn-ptx-kd m) kd) (equal (fn-ptx-ext m) (nfix ext)) (equal (fn-ptx-geo m) geo)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-opened fn-ptx-accessors-of-mk)) :do-not-induct t)))
(defthm fn-ptx-simp-opened
  (implies (and (fn-ptx-open-kernelp ks0) (true-listp (fn-lgk-committed ks0)))
           (fn-ptx-simp (fn-ptx-opened (fn-ptx-kd-of ks0) ext geo) (fn-ptd-init ks0 ext) id inc st))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-simp fn-ptx-opened-fields fn-ptx-open-kernelp fn-ptd-open-kernelp fn-ptd-init fn-ptd-fields-of-mk fn-ptx-nfix-ptd-ext fn-ptx-ptd-phase
                (:executable-counterpart equal) (:executable-counterpart not) (:executable-counterpart consp) car-cons cdr-cons member-equal (:executable-counterpart member-equal)))
           :do-not-induct t)))
(defthm fn-ptx-unit-of-opened
  (implies (posp u) (equal (fn-ptx-unit (fn-ptx-opened kd ext (list u max hmax))) u))
  :hints (("Goal" :in-theory (enable fn-ptx-unit posp))))
(defthm fn-ptx-fmax-of-opened
  (equal (fn-ptx-fmax (fn-ptx-opened kd ext (list u max hmax))) (nfix max))
  :hints (("Goal" :in-theory (enable fn-ptx-fmax))))
(defthm fn-ptx-posted-are-the-driver-posted
  (implies (and (fn-lgk-relp bs ks0 ino genesis max) (fn-ptx-open-kernelp ks0)
                (equal ext (len (fn-bs-durable-content bs ino)))
                (equal geo (list (fn-bs-unit bs) max hmax))
                (fn-ptx-okp (fn-ptx-opened (fn-ptx-kd-of ks0) ext geo))
                (fn-ptx-trace-relies-p (fn-ptx-opened (fn-ptx-kd-of ks0) ext geo) trace id inc))
           (mv-let (mf ins posted) (fn-ptx-trace-run (fn-ptx-opened (fn-ptx-kd-of ks0) ext geo) trace id inc)
             (declare (ignore mf))
             (equal posted
                    (fn-ptd-posted (mv-nth 2 (fn-ptd-run (fn-ptd-init ks0 ext) ins ino (fn-bs-unit bs) max))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-ptx-opened-fields fn-ptx-unit-of-opened fn-ptx-fmax-of-opened (:executable-counterpart equal) (:executable-counterpart not)))
           :do-not-induct t
           :use ((:instance fn-ptx-trace-posted-gen (m (fn-ptx-opened (fn-ptx-kd-of ks0) ext geo)) (ptd (fn-ptd-init ks0 ext)))
                 (:instance fn-ptx-simp-opened (st (nth 1 (car trace))))
                 (:instance fn-lgk-relp-committed-true-listp (ks ks0))
                 (:instance fn-ptx-relp-unit-posp (ks ks0))
                 (:instance fn-ptx-unit-of-opened (u (fn-bs-unit bs)) (kd (fn-ptx-kd-of ks0)))))))
(defthm fn-ptx-posted-records-are-recovered-at-every-later-cut
  (let* ((ext (len (fn-bs-durable-content bs ino)))
         (m0 (fn-ptx-opened (fn-ptx-kd-of ks0) ext (list (fn-bs-unit bs) max hmax)))
         (run (fn-ptx-trace-run m0 trace id inc))
         (unit (fn-bs-unit bs))
         (r1 (fn-ptd-run (fn-ptd-init ks0 ext) (mv-nth 1 run) ino unit max))
         (r2 (fn-ptd-run (mv-nth 0 r1) e2 ino unit max))
         (f1 (fn-lgu-host-final bs ks0 (mv-nth 3 r1) ino max))
         (p (mv-nth 2 run))
         (a0 (fn-lgk-acked ks0))
         (recovered (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image ino) genesis unit max next-txid))))
    (implies (and (fn-lgk-relp bs ks0 ino genesis max) (fn-ptx-open-kernelp ks0)
                  (fn-ptx-okp m0)
                  (fn-ptx-trace-relies-p m0 trace id inc)
                  (member-equal pair (fn-lgu-host-run (car f1) (cdr f1) (mv-nth 3 r2) ino max))
                  (fn-bs-crash-imagep (car pair) image))
             (and (<= (+ a0 (len p)) (len recovered))
                  (equal (take a0 recovered) (take a0 (fn-lgk-committed ks0)))
                  (equal (take (len p) (nthcdr a0 recovered)) p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-open-kernelp)) :do-not-induct t
           :use ((:instance fn-ptx-posted-are-the-driver-posted (ext (len (fn-bs-durable-content bs ino))) (geo (list (fn-bs-unit bs) max hmax)))
                 (:instance fn-ptd-posted-records-are-recovered-at-every-later-cut
                            (e1 (mv-nth 1 (fn-ptx-trace-run (fn-ptx-opened (fn-ptx-kd-of ks0) (len (fn-bs-durable-content bs ino)) (list (fn-bs-unit bs) max hmax)) trace id inc))))))))
