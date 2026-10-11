; fn: the echo machine, the runtime contract's first instance: each
; connection receives into a leased buffer, sends the octets back from the
; same buffer, and keeps one receive pending while a send is outstanding.
;
; Scope of the instance's keystones: the echo never commits (its observer is
; constantly false), so its instance of the commit keystone holds vacuously;
; the commit point's non-vacuous instance is landing 2's transaction machine.
; Each machine sees its own view of the pool, with input-lease octets
; hidden and foreign buffers opaque. The echo reads configuration, owners
; and generations; its three fixed buffers per connection are reserved by home.
(in-package "ACL2")
(include-book "runtime-contract-layer")
;; Octets one receive asks for; buffers a receive's search examines, at most
;; (the search's charge is its bound, so the step's cost is a constant).
(defconst *fn-rce-cap* 64)
(defconst *fn-rce-window* 64)

; The least buffer at or above I and below the window, other than SKIP, that
; is free.
(defun fn-rce-free (i skip id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (natp i)
                  :hints (("Goal" :in-theory (disable fn-rtc-st-v-owner fn-rtc-st-config fn-rtc-nbufs)))
                  :measure (nfix (- (min (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st)) *fn-rce-window*) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (min (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st)) *fn-rce-window*))
        (if (and (not (equal i skip)) (equal (fn-rtc-st-v-owner i id inc fn-rtc-st) '(:free)))
            i
          (fn-rce-free (+ 1 i) skip id inc fn-rtc-st))
      nil)))

(defthm fn-rce-free-reads-view
  (equal (fn-rce-free i skip id inc (fn-rtc-view-state id inc st)) (fn-rce-free i skip id inc st))
  :hints (("Goal" :in-theory (disable fn-rtc-st-v-owner fn-rtc-st-config fn-rtc-nbufs))))

(defthm fn-rce-free-type
  (or (null (fn-rce-free i skip id inc st)) (natp (fn-rce-free i skip id inc st)))
  :rule-classes :type-prescription)

; State (rv sd rd rn so sl): the buffer of the outstanding :recv; the buffer
; of the outstanding :send, the offset and length it sends; the buffer of
; received octets waiting for the send, and their count.
(defun fn-rce-mk (rv sd rd rn so sl)
  (declare (xargs :guard t))
  (list (and (natp rv) rv) (and (natp sd) sd) (and (natp rd) rd) (nfix rn) (nfix so) (nfix sl)))

; Start a receive into a free buffer other than SKIP: (mv rv requests).
(defun fn-rce-start-recv (skip id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((h (fn-rce-free 0 skip id inc fn-rtc-st)))
    (if h
        (let ((g (+ 1 (fn-rtc-st-v-gen h id inc fn-rtc-st))))
          (mv h (list (list :acquire h) (list :submit :recv (list h g 0 *fn-rce-cap*) nil))))
      (mv nil nil))))

; A send of [OFF, OFF+LEN) of buffer H, at its current generation.
(defun fn-rce-send (h off len id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (list :submit :send (list (nfix h) (fn-rtc-st-v-gen h id inc fn-rtc-st) (nfix off) (nfix len)) nil))

; The step's charge: one, plus the receive search at its bound.
(defconst *fn-rce-charge* (+ 1 *fn-rce-window*))

(defun fn-rce-step (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st) (ignore q))
  (let* ((rv (fn-rtc-get 0 m)) (sd (fn-rtc-get 1 m)) (rd (fn-rtc-get 2 m)) (rn (nfix (fn-rtc-get 3 m)))
         (so (nfix (fn-rtc-get 4 m))) (sl (nfix (fn-rtc-get 5 m)))
         (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))
         (kind (fn-rtc-get 0 ev)) (out (fn-rtc-get 1 ev))
         (tag (fn-rtc-get 0 out)) (n (nfix (fn-rtc-get 1 out))))
    (cond
     ((eq kind :accept)
      (mv-let (h reqs) (fn-rce-start-recv nil id inc fn-rtc-st)
        (mv (fn-rce-mk h nil nil 0 0 0) reqs *fn-rce-charge*)))
     ((and (eq kind :recv) (member-eq tag '(:done :short)) (< 0 n) (natp rv))
      (if (natp sd)
          ;; a send is outstanding: hold these octets
          (mv (fn-rce-mk nil sd rv n so sl) nil *fn-rce-charge*)
        (mv-let (h reqs) (fn-rce-start-recv rv id inc fn-rtc-st)
          (mv (fn-rce-mk h rv nil 0 0 n)
              (cons (fn-rce-send rv 0 n id inc fn-rtc-st) reqs)
              *fn-rce-charge*))))
     ((and (eq kind :send) (eq tag :short) (natp sd) (< n sl))
      ;; a short send: send the rest
      (mv (fn-rce-mk rv sd rd rn (+ so n) (- sl n))
          (list (fn-rce-send sd (+ so n) (- sl n) id inc fn-rtc-st))
          *fn-rce-charge*))
     ((and (eq kind :send) (member-eq tag '(:done :short)) (natp sd))
      (let ((rel (list :release sd (fn-rtc-st-v-gen sd id inc fn-rtc-st))))
        (if (natp rd)
            (if (natp rv)
                (mv (fn-rce-mk rv rd nil 0 0 rn)
                    (list rel (fn-rce-send rd 0 rn id inc fn-rtc-st))
                    *fn-rce-charge*)
              (mv-let (h reqs) (fn-rce-start-recv rd id inc fn-rtc-st)
                (mv (fn-rce-mk h rd nil 0 0 rn)
                    (list* rel (fn-rce-send rd 0 rn id inc fn-rtc-st) reqs)
                    *fn-rce-charge*)))
          (mv (fn-rce-mk rv nil nil 0 0 0) (list rel) *fn-rce-charge*))))
     (t (mv (fn-rce-mk nil nil nil 0 0 0) (list (list :close)) *fn-rce-charge*)))))

(defthm fn-rce-start-recv-reads-view
  (equal (fn-rce-start-recv skip id inc (fn-rtc-view-state id inc st)) (fn-rce-start-recv skip id inc st))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                  '(fn-rce-start-recv fn-rce-free-reads-view fn-rtc-v-readers-of-view-state)))))

(defthm fn-rce-step-reads-view
  (equal (fn-rce-step m ev (fn-rtc-view-state (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) q) (fn-rce-step m ev st q))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                  '(fn-rce-step fn-rce-send fn-rce-start-recv-reads-view fn-rtc-v-readers-of-view-state)))))

(defthm fn-rce-start-recv-facts
  (and (<= (len (mv-nth 1 (fn-rce-start-recv skip id inc st))) 2)
       (equal (fn-rtc-reqs-octets (mv-nth 1 (fn-rce-start-recv skip id inc st))) 0)
       (or (null (mv-nth 0 (fn-rce-start-recv skip id inc st))) (natp (mv-nth 0 (fn-rce-start-recv skip id inc st)))))
  :hints (("Goal" :in-theory (disable fn-rce-free fn-rtc-st-v-gen)))
  :rule-classes ((:linear :corollary (<= (len (mv-nth 1 (fn-rce-start-recv skip id inc st))) 2))
                 (:rewrite :corollary (equal (fn-rtc-reqs-octets (mv-nth 1 (fn-rce-start-recv skip id inc st))) 0))))

(defthm fn-rce-mk-size
  (<= (fn-rtc-size (fn-rce-mk rv sd rd rn so sl)) 13)
  :rule-classes :linear)

(defthm fn-rce-step-facts
  (and (equal (mv-nth 2 (fn-rce-step m ev st q)) *fn-rce-charge*)
       (equal (fn-rtc-reqs-octets (mv-nth 1 (fn-rce-step m ev st q))) 0)
       (<= (len (mv-nth 1 (fn-rce-step m ev st q))) 4)
       (<= (fn-rtc-size (mv-nth 0 (fn-rce-step m ev st q))) 13))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
       '(fn-rce-step fn-rce-send fn-rce-start-recv-facts fn-rce-mk-size
         fn-rtc-reqs-octets fn-rtc-get-of-cons len mv-nth nfix natp zp member-equal (:executable-counterpart fn-rtc-get)
         car-cons cdr-cons unicity-of-0 fix (:type-prescription len)
         (:type-prescription fn-rce-mk) (:type-prescription fn-rce-start-recv)
         (:type-prescription fn-rtc-size) (:type-prescription nfix))))))

(defun fn-rce-init () (declare (xargs :guard t)) nil)
(defun fn-rce-static-init (j) (declare (xargs :guard t) (ignore j)) nil)
(defun fn-rce-committedp (m) (declare (xargs :guard t) (ignore m)) nil)
(defun fn-rce-c () (declare (xargs :guard t)) *fn-rce-charge*)
(defun fn-rce-max-reqs () (declare (xargs :guard t)) 4)
(defun fn-rce-max-state () (declare (xargs :guard t)) 13)

(fn-rtc-def-layer fn-rcl
  :step fn-rce-step :init fn-rce-init :static-init fn-rce-static-init :committedp fn-rce-committedp :c fn-rce-c
  :max-reqs fn-rce-max-reqs :max-state fn-rce-max-state :reads-view fn-rce-step-reads-view
  :hints (("Goal" :in-theory (enable fn-rcl-m-step)
           :use ((:instance fn-rce-step-facts (st pool))))))

; -----------------------------------------------------------------------------
; The multi-instance exercise (RUNTIME-MODEL section 9 item 1): a script of
; host completions over interleaved connections, the host's landing of input
; included, with every step's observation: the actions, the requests the
; layer refused, whether the contract's invariant holds of the state read
; back (`fn-rcl-invp' of `fn-rtc-x-state'), whether every outstanding :out
; use's octets are as they were before the step, and whether a completion
; that matched no outstanding use left the state and the actions empty.

; The octets every outstanding :out use names, keyed by op: (op . octets).
(defun fn-rce-out-snapshot (uses fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (if (atom uses) nil
    (let ((u (car uses)))
      (if (and (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*) (fn-rtc-handlep (fn-rtc-u-hd u)))
          (let ((hd (fn-rtc-u-hd u)))
            (cons (cons (fn-rtc-get 3 u)
                        (fn-rtc-x-bytes (fn-rtc-h-buf hd) (fn-rtc-h-off hd)
                                        (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd)) fn-rtc-st))
                  (fn-rce-out-snapshot (cdr uses) fn-rtc-st)))
        (fn-rce-out-snapshot (cdr uses) fn-rtc-st)))))

; Every op of BEFORE still in AFTER names the same octets.
(defun fn-rce-stable-p (before after)
  (declare (xargs :guard (alistp after)))
  (if (atom before) t
    (let ((a (and (consp (car before)) (assoc-equal (caar before) after))))
      (and (or (null a) (equal (cdr a) (cdar before)))
           (fn-rce-stable-p (cdr before) after)))))

(defthm fn-rce-out-snapshot-alistp (alistp (fn-rce-out-snapshot uses st)))

; The host's landing (A-HOST-LANDS): DATA at the handle of the :in use E
; completes, while its buffer is :in-leased.
(defun fn-rce-land (e data fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-st-uses fn-rtc-st))))
    (if (and u (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*) (fn-rtc-handlep (fn-rtc-u-hd u))
             (fn-cbor-octet-listp data))
        (fn-rtc-st-splice (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-h-off (fn-rtc-u-hd u)) data fn-rtc-st)
      fn-rtc-st)))

;; The host's half changed nothing but octets of :in-leased buffers: the
;; tables are as they were and the pools agree off the :in leases (what
;; `fn-rtc-landing-is-hidden' proves a landing does).
(defun fn-rce-landing-only-p (s0 s1)
  (declare (xargs :guard t))
  (and (equal (fn-rtc-config s1) (fn-rtc-config s0))
       (equal (fn-rtc-slots s1) (fn-rtc-slots s0))
       (equal (fn-rtc-uses s1) (fn-rtc-uses s0))
       (equal (fn-rtc-mstates s1) (fn-rtc-mstates s0))
       (equal (fn-rtc-next-op s1) (fn-rtc-next-op s0))
       (fn-rtc-pools-agree-off-in-leases-p (fn-rtc-pool s0) (fn-rtc-pool s1))))

;; X is an element of L.
(defun fn-rce-in-p (x l)
  (declare (xargs :guard t))
  (if (atom l) nil (or (equal x (car l)) (fn-rce-in-p x (cdr l)))))

;; Every use of USES other than the one keyed KEY is still in AFTER: only a
;; completion ends a use, and only its own.
(defun fn-rce-uses-kept-p (key uses after)
  (declare (xargs :guard t))
  (if (atom uses) t
    (and (or (equal (fn-rtc-key (car uses)) key)
             (fn-rce-in-p (car uses) after))
         (fn-rce-uses-kept-p key (cdr uses) after))))

; The host's half of an item, before the completion is delivered: a landing,
; or a fault injection (for the checks' teeth: a host that writes octets at
; (h off) whatever the buffer's state, or rewrites a buffer's generation and
; owner).
(defun fn-rce-host (item fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((e (fn-rtc-get 1 item)))
    (case (fn-rtc-get 0 item)
      (:land (fn-rce-land e (fn-rtc-get 2 item) fn-rtc-st))
      (:fault-write (let ((h (nfix (fn-rtc-get 2 item))) (off (nfix (fn-rtc-get 3 item)))
                          (data (fn-rtc-get 4 item)))
                      (if (fn-cbor-octet-listp data)
                          (let* ((g (fn-rtc-st-gen h fn-rtc-st))
                                 (owner (fn-rtc-st-owner h fn-rtc-st))
                                 (fn-rtc-st (fn-rtc-st-set-meta h g '(:workspace 1 1) fn-rtc-st))
                                 (fn-rtc-st (fn-rtc-st-splice h off data fn-rtc-st)))
                            (fn-rtc-st-set-meta h g owner fn-rtc-st))
                        fn-rtc-st)))
      (:fault-meta (fn-rtc-st-set-meta (nfix (fn-rtc-get 2 item)) (nfix (fn-rtc-get 3 item))
                                       (fn-rtc-get 4 item) fn-rtc-st))
      (otherwise fn-rtc-st))))

; One script item: (:complete E), (:land E DATA), or a fault injection
; (:fault-write E H OFF DATA) / (:fault-meta E H GEN OWNER) before E.  Its
; observation (i kind acts refused INV STAB MATCH): INV is :invp when the
; invariant holds of the state read back after the host's half and after the
; step; STAB is :stable when the host's half changed nothing but octets of
; :in-leased buffers, moved no outstanding :out use's octets, the step moved
; none of the uses it kept, and the step ended no use but the completion's
; own; MATCH is :matched, or :discarded for a completion
; that matched no use and changed neither state nor actions.
(defun fn-rce-item (i item fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((e (fn-rtc-get 1 item))
         (matched (and (fn-rtc-completionp e)
                       (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-st-uses fn-rtc-st))
                       t))
         (snap0 (fn-rce-out-snapshot (fn-rtc-st-uses fn-rtc-st) fn-rtc-st))
         (s0 (fn-rtc-x-state fn-rtc-st))
         (fn-rtc-st (fn-rce-host item fn-rtc-st))
         (before (fn-rtc-x-state fn-rtc-st))
         (uses1 (fn-rtc-st-uses fn-rtc-st))
         (snap1 (fn-rce-out-snapshot uses1 fn-rtc-st)))
    (mv-let (fn-rtc-st acts refused cost)
      (fn-rcl-x-step* e 16 fn-rtc-st)
      (declare (ignore cost))
      (let ((after (fn-rtc-x-state fn-rtc-st)))
        (mv fn-rtc-st
            (list i (fn-rtc-get 0 e) acts refused
                  (if (and (fn-rcl-invp before) (fn-rcl-invp after)) :invp :invp-violated)
                  (if (and (fn-rce-landing-only-p s0 before)
                           (fn-rce-stable-p snap0 snap1)
                           (fn-rce-stable-p snap1 (fn-rce-out-snapshot (fn-rtc-st-uses fn-rtc-st) fn-rtc-st))
                           (fn-rce-uses-kept-p (fn-rtc-key e) uses1 (fn-rtc-st-uses fn-rtc-st)))
                      :stable :moved)
                  (cond (matched :matched)
                        ((and (equal before after) (null acts)) :discarded)
                        (t :unmatched-changed))))))))

(defun fn-rce-items (i items fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (natp i) :measure (len items)))
  (if (atom items) (mv fn-rtc-st nil)
    (mv-let (fn-rtc-st obs) (fn-rce-item i (car items) fn-rtc-st)
      (mv-let (fn-rtc-st rest) (fn-rce-items (+ 1 i) (cdr items) fn-rtc-st)
        (mv fn-rtc-st (cons obs rest))))))

; The exercise: a fresh layer for CFG, then the script.  The first
; observation is the initial state's.
(defun fn-rce-run (cfg items fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (fn-rtc-st acts) (fn-rcl-x-init cfg fn-rtc-st)
    (let ((obs0 (list 0 :init acts nil
                      (if (fn-rcl-invp (fn-rtc-x-state fn-rtc-st)) :invp :invp-violated) :stable :init)))
      (mv-let (fn-rtc-st obs) (fn-rce-items 1 items fn-rtc-st)
        (mv fn-rtc-st (cons obs0 obs))))))

; The exercise's script: two interleaved connections over 3 slots and 6
; buffers of 64 octets (three reserved for each connection, no shared pool) -- pending read and send on one connection, a receive
; held while a send is outstanding, a close with a send outstanding (the
; slot drains), the late completion that retires it, a duplicate of that
; completion, slot reuse at the next incarnation with a reused buffer at a
; later generation, a stale completion naming the old incarnation, a short
; send and the send of its rest, a failed receive and a close with that send
; outstanding, and the send's completion that retires the slot.
(defconst *fn-rce-exercise-cfg* '(3 6 64 0 3 0 64))

(defconst *fn-rce-exercise-script*
  '((:complete (:accept 0 0 0 (:done 7)))
    (:complete (:accept 0 0 2 (:done 8)))
    (:land (:recv 1 1 1 (:done 5)) (104 101 108 108 111))
    (:land (:recv 2 1 3 (:done 3)) (97 98 99))
    (:land (:recv 1 1 5 (:done 4)) (109 111 114 101))
    (:complete (:send 1 1 4 (:done 5)))
    (:complete (:recv 2 1 7 (:done 0)))
    (:complete (:close 2 1 10 (:done 0)))
    (:complete (:send 2 1 6 (:done 3)))
    (:complete (:send 2 1 6 (:done 3)))
    (:complete (:accept 0 0 11 (:done 9)))
    (:land (:recv 2 1 7 (:done 2)) (120 121))
    (:complete (:send 1 1 8 (:short 2)))
    (:complete (:recv 1 1 9 (:failed :econnreset)))
    (:complete (:close 1 1 14 (:done 0)))
    (:complete (:send 1 1 13 (:done 2)))))

; The script (VARIANT 0), or its first three steps followed by a fault
; injection the checks must report: a host write into connection 1's
; :out-leased buffer with a stale completion (1, :moved), that buffer freed
; under its lease (2, :invp-violated), or the write followed by that send's
; own completion (3, :moved: the host's half is checked before the step), or
; that buffer's lease redirected to another instance (4, :moved: the host's
; half may change only octets of :in-leased buffers).
(defun fn-rce-exercise-items (variant)
  (declare (xargs :guard t))
  (case variant
    (1 (append (take 3 *fn-rce-exercise-script*)
               '((:fault-write (:send 9 9 99 (:done 0)) 0 0 (1 2 3)))))
    (2 (append (take 3 *fn-rce-exercise-script*)
               '((:fault-meta (:send 9 9 99 (:done 0)) 0 2 (:free)))))
    (3 (append (take 3 *fn-rce-exercise-script*)
               '((:fault-write (:send 1 1 4 (:done 5)) 0 0 (1 2 3)))))
    (4 (append (take 3 *fn-rce-exercise-script*)
               '((:fault-meta (:send 9 9 99 (:done 0)) 0 2 (:leased 2 1 :out)))))
    (otherwise *fn-rce-exercise-script*)))

(defun fn-rce-exercise (variant fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (fn-rce-run *fn-rce-exercise-cfg* (fn-rce-exercise-items variant) fn-rtc-st))
