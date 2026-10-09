; fn: the echo machine, the runtime contract's first instance: each
; connection receives into a leased buffer, sends the octets back from the
; same buffer, and keeps one receive pending while a send is outstanding.
(in-package "ACL2")
(include-book "runtime-contract-layer")
(defconst *fn-rce-cap* 64)

; The least buffer at or above I, other than SKIP, that is free.
(defun fn-rce-free (i skip fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (natp i)
                  :measure (nfix (- (fn-rtc-st-b-count fn-rtc-st) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (fn-rtc-st-b-count fn-rtc-st))
        (if (and (not (equal i skip)) (equal (fn-rtc-st-b-owner i fn-rtc-st) '(:free)))
            i
          (fn-rce-free (+ 1 i) skip fn-rtc-st))
      nil)))

(defthm fn-rce-free-reads-borrow
  (equal (fn-rce-free i skip (fn-rtc-borrow-state st)) (fn-rce-free i skip st)))

(defthm fn-rce-free-type
  (or (null (fn-rce-free i skip st)) (natp (fn-rce-free i skip st)))
  :rule-classes :type-prescription)

; State (rv sd rd n): the buffer of the outstanding :recv, of the outstanding
; :send, of received octets waiting for the send, and their count.
(defun fn-rce-mk (rv sd rd n)
  (declare (xargs :guard t))
  (list (and (natp rv) rv) (and (natp sd) sd) (and (natp rd) rd) (nfix n)))

; Start a receive into a free buffer other than SKIP: (mv rv requests).
(defun fn-rce-start-recv (skip fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((h (fn-rce-free 0 skip fn-rtc-st)))
    (if h
        (let ((g (+ 1 (fn-rtc-st-b-gen h fn-rtc-st))))
          (mv h (list (list :acquire h) (list :submit :recv (list h g 0 *fn-rce-cap*) nil))))
      (mv nil nil))))

(defun fn-rce-step (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st) (ignore q))
  (let* ((rv (fn-rtc-get 0 m)) (sd (fn-rtc-get 1 m)) (rd (fn-rtc-get 2 m)) (rn (fn-rtc-get 3 m))
         (kind (fn-rtc-get 0 ev)) (out (fn-rtc-get 1 ev))
         (tag (fn-rtc-get 0 out)) (n (nfix (fn-rtc-get 1 out))))
    (cond
     ((eq kind :accept)
      (mv-let (h reqs) (fn-rce-start-recv nil fn-rtc-st)
        (mv (fn-rce-mk h nil nil 0) reqs 1)))
     ((and (eq kind :recv) (member-eq tag '(:done :short)) (< 0 n) (natp rv))
      (if (natp sd)
          ;; a send is outstanding: hold these octets
          (mv (fn-rce-mk nil sd rv n) nil 1)
        (mv-let (h reqs) (fn-rce-start-recv rv fn-rtc-st)
          (mv (fn-rce-mk h rv nil 0)
              (cons (list :submit :send (list rv (fn-rtc-st-b-gen rv fn-rtc-st) 0 n) nil) reqs)
              1))))
     ((and (eq kind :send) (member-eq tag '(:done :short)) (natp sd))
      (let ((rel (list :release sd (fn-rtc-st-b-gen sd fn-rtc-st))))
        (if (natp rd)
            (if (natp rv)
                (mv (fn-rce-mk rv rd nil 0)
                    (list rel (list :submit :send (list rd (fn-rtc-st-b-gen rd fn-rtc-st) 0 (nfix rn)) nil))
                    1)
              (mv-let (h reqs) (fn-rce-start-recv rd fn-rtc-st)
                (mv (fn-rce-mk h rd nil 0)
                    (list* rel (list :submit :send (list rd (fn-rtc-st-b-gen rd fn-rtc-st) 0 (nfix rn)) nil) reqs)
                    1)))
          (mv (fn-rce-mk rv nil nil 0) (list rel) 1))))
     (t (mv (fn-rce-mk nil nil nil 0) (list (list :close)) 1)))))

(defthm fn-rce-start-recv-reads-borrow
  (equal (fn-rce-start-recv skip (fn-rtc-borrow-state st)) (fn-rce-start-recv skip st)))

(defthm fn-rce-step-reads-borrow
  (equal (fn-rce-step m ev (fn-rtc-borrow-state st) q) (fn-rce-step m ev st q))
  :hints (("Goal" :in-theory (disable fn-rce-start-recv))))

(defthm fn-rce-start-recv-facts
  (and (<= (len (mv-nth 1 (fn-rce-start-recv skip st))) 2)
       (equal (fn-rtc-reqs-octets (mv-nth 1 (fn-rce-start-recv skip st))) 0)
       (or (null (mv-nth 0 (fn-rce-start-recv skip st))) (natp (mv-nth 0 (fn-rce-start-recv skip st)))))
  :rule-classes ((:linear :corollary (<= (len (mv-nth 1 (fn-rce-start-recv skip st))) 2))
                 (:rewrite :corollary (equal (fn-rtc-reqs-octets (mv-nth 1 (fn-rce-start-recv skip st))) 0))))

(defthm fn-rce-mk-size
  (<= (fn-rtc-size (fn-rce-mk rv sd rd n)) 9)
  :rule-classes :linear)

(defthm fn-rce-step-facts
  (and (equal (mv-nth 2 (fn-rce-step m ev st q)) 1)
       (equal (fn-rtc-reqs-octets (mv-nth 1 (fn-rce-step m ev st q))) 0)
       (<= (len (mv-nth 1 (fn-rce-step m ev st q))) 4)
       (<= (fn-rtc-size (mv-nth 0 (fn-rce-step m ev st q))) 9))
  :hints (("Goal" :in-theory (e/d (fn-rce-step) (fn-rce-start-recv fn-rce-mk fn-rtc-size fn-rce-free)))))

(defun fn-rce-init () (declare (xargs :guard t)) nil)
(defun fn-rce-committedp (m) (declare (xargs :guard t) (ignore m)) nil)
(defun fn-rce-c () (declare (xargs :guard t)) 1)
(defun fn-rce-max-reqs () (declare (xargs :guard t)) 4)
(defun fn-rce-max-state () (declare (xargs :guard t)) 9)

(fn-rtc-def-layer fn-rcl
  :step fn-rce-step :init fn-rce-init :committedp fn-rce-committedp :c fn-rce-c
  :max-reqs fn-rce-max-reqs :max-state fn-rce-max-state :reads-borrow fn-rce-step-reads-borrow
  :hints (("Goal" :in-theory (enable fn-rcl-m-step)
           :use ((:instance fn-rce-step-facts (st (fn-rtc-make nil nil pool nil nil 0)))))))

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

; One script item: (:complete E), (:land E DATA), or a fault injection
; (:fault-write E H OFF DATA) / (:fault-meta E H GEN OWNER) before E.  Its observation:
; (i kind acts refused invp stable discarded).
(defun fn-rce-item (i item fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st ))
  (let* ((e (fn-rtc-get 1 item))
         (matched (and (fn-rtc-completionp e)
                       (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-st-uses fn-rtc-st))
                       t))
         (before (fn-rtc-x-state fn-rtc-st))
         (snap (fn-rce-out-snapshot (fn-rtc-st-uses fn-rtc-st) fn-rtc-st))
         (fn-rtc-st (case (fn-rtc-get 0 item)
                      (:land (fn-rce-land e (fn-rtc-get 2 item) fn-rtc-st))
                      ;; fault injection, for the checks' teeth: a host that
                      ;; writes octets at (h off) whatever the buffer's
                      ;; state, or rewrites a buffer's generation and owner
                      (:fault-write (let ((h (nfix (fn-rtc-get 2 item))) (off (nfix (fn-rtc-get 3 item)))
                                          (data (fn-rtc-get 4 item)))
                                      (if (fn-cbor-octet-listp data)
                                          (fn-rtc-st-splice h off data fn-rtc-st)
                                        fn-rtc-st)))
                      (:fault-meta (fn-rtc-st-set-meta (nfix (fn-rtc-get 2 item)) (nfix (fn-rtc-get 3 item))
                                                       (fn-rtc-get 4 item) fn-rtc-st))
                      (otherwise fn-rtc-st))))
    (mv-let (fn-rtc-st acts refused cost)
      (fn-rcl-x-step* e 16 fn-rtc-st)
      (declare (ignore cost))
      (let ((after (fn-rtc-x-state fn-rtc-st)))
        (mv fn-rtc-st
            (list i (fn-rtc-get 0 e) acts refused
                  (if (fn-rcl-invp after) :invp :invp-violated)
                  (if (fn-rce-stable-p snap (fn-rce-out-snapshot (fn-rtc-st-uses fn-rtc-st) fn-rtc-st))
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
  (mv-let (fn-rtc-st acts) (fn-rtc-x-init cfg fn-rtc-st)
    (let ((obs0 (list 0 :init acts nil
                      (if (fn-rcl-invp (fn-rtc-x-state fn-rtc-st)) :invp :invp-violated) :stable :init)))
      (mv-let (fn-rtc-st obs) (fn-rce-items 1 items fn-rtc-st)
        (mv fn-rtc-st (cons obs0 obs))))))

; The exercise's script: two interleaved connections over 3 slots and 6
; buffers of 64 octets -- pending read and send on one connection, a receive
; held while a send is outstanding, a close with a send outstanding (the
; slot drains), the late completion that retires it, a duplicate of that
; completion, slot reuse at the next incarnation with a reused buffer at a
; later generation, a stale completion naming the old incarnation, a short
; send, a failed receive and a close.
(defconst *fn-rce-exercise-cfg* '(3 6 64))

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
    (:complete (:close 1 1 13 (:done 0)))))

; The script (VARIANT 0), or its first three steps followed by a fault
; injection the checks must report: a host write into connection 1's
; :out-leased buffer (1, :moved) or that buffer freed under its lease
; (2, :invp-violated).
(defun fn-rce-exercise-items (variant)
  (declare (xargs :guard t))
  (case variant
    (1 (append (take 3 *fn-rce-exercise-script*)
               '((:fault-write (:send 9 9 99 (:done 0)) 0 0 (1 2 3)))))
    (2 (append (take 3 *fn-rce-exercise-script*)
               '((:fault-meta (:send 9 9 99 (:done 0)) 0 2 (:free)))))
    (otherwise *fn-rce-exercise-script*)))

(defun fn-rce-exercise (variant fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (fn-rce-run *fn-rce-exercise-cfg* (fn-rce-exercise-items variant) fn-rtc-st))
