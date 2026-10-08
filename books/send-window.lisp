; The octets one connection's reply may have rendered ahead of its reader
; (item LOAD-F5-SLOW-READER-ISOLATION; F5 on g41: four readers with a 4 KiB
; receive buffer and a one-octet read pulled 512 KiB articles; the fast
; clients' p99 rose 6.2x and the process grew 87.6 MB).
;
; The reply is rendered a window at a time and the next window only when the
; socket took the last one (host/native/mux.lisp fnn-mux-flush), but the
; kernel took them: a socket's send queue is 3.4 MB on the CONVERGE-2 image
; (books/send-progress.lisp), so a stopped reader had the owner scan and render
; seven 512 KiB articles ahead of it -- 13 seconds of owner-mutex quanta and
; 400 MB a second of allocation per four readers -- before the first write
; blocked.  The host now sets TCP_NOTSENT_LOWAT on every served socket to
; (fn-send-window-octets): the kernel accepts a write only while it holds
; fewer than that many unsent octets, so the same stopped reader costs the
; owner one window past the row and nothing after.
;
; The model.  A connection holds NOTSENT octets the kernel has not yet sent and
; PENDING octets of the window the host rendered and has not yet handed over;
; RENDERED and TRANSMITTED count the octets of the reply so far.  The events:
;
;   (:render N)    the host renders the next window of N octets, 0 < N <= Q
;                  (Q is the largest window any plan renders); only when
;                  nothing of the last window is pending (fnn-mux-flush);
;   (:write N)     the host hands N <= PENDING octets to the kernel, which
;                  accepts them only while NOTSENT < W (the lowat gate; the
;                  kernel's tcp_stream_memory_free);
;   (:transmit N)  the network takes N <= NOTSENT octets (the reader reads).
;
; The gate is the kernel's behaviour, an assumption this book does not prove:
; tests/test_native_over_pins.py checks it on the running owner (the kernel's
; send queue of a stopped reader against this bound).  GATEP nil is the gate
; removed, the hypothesis-removal witness.
;
; Keystones:
;   fn-sw-buffered-bounded   in every legal trace, whatever the reply's size
;     and the reader's pace, NOTSENT + PENDING < W + 2Q: the connection holds
;     fewer than W + 2Q octets rendered and not transmitted;
;   fn-sw-stalled-reader-bounded   a reader that transmits nothing makes the
;     owner render fewer than W + 2Q octets in all, however many windows the
;     reply has: the cost of a stalled connection is O(1) in the reply.

(in-package "ACL2")
(include-book "profile-limits")

(defconst *fn-sw-window* (fn-profile-limit :send-window-octets))

; The entry the host calls: the lowat it sets on each served socket.
(defun fn-send-window-octets ()
  (declare (xargs :guard t))
  *fn-sw-window*)

; State: (NOTSENT PENDING RENDERED TRANSMITTED).
(defun fn-sw-statep (st)
  (declare (xargs :guard t))
  (and (true-listp st) (equal (len st) 4)
       (natp (nth 0 st)) (natp (nth 1 st)) (natp (nth 2 st)) (natp (nth 3 st))))

(defconst *fn-sw-start* '(0 0 0 0))

(defun fn-sw-step (st ev w q gatep)
  (declare (xargs :guard (and (fn-sw-statep st) (natp w) (natp q))))
  (let ((notsent (nth 0 st)) (pending (nth 1 st))
        (rendered (nth 2 st)) (transmitted (nth 3 st))
        (kind (and (consp ev) (car ev)))
        (n (and (consp ev) (consp (cdr ev)) (cadr ev))))
    (cond ((not (posp n)) nil)
          ((eq kind :render)
           (and (equal pending 0) (<= n q)
                (list notsent n (+ rendered n) transmitted)))
          ((eq kind :write)
           (and (<= n pending) (or (not gatep) (< notsent w))
                (list (+ notsent n) (- pending n) rendered transmitted)))
          ((eq kind :transmit)
           (and (<= n notsent)
                (list (- notsent n) pending rendered (+ transmitted n))))
          (t nil))))

; The state after EVS, or NIL when an event is not legal where it stands.
(defun fn-sw-run (st evs w q gatep)
  (declare (xargs :guard (and (fn-sw-statep st) (natp w) (natp q))
                  :measure (acl2-count evs)))
  (if (atom evs)
      st
    (let ((next (fn-sw-step st (car evs) w q gatep)))
      (and next (fn-sw-run next (cdr evs) w q gatep)))))

(defun fn-sw-no-transmit-p (evs)
  (declare (xargs :guard t))
  (if (atom evs)
      t
    (and (not (and (consp (car evs)) (eq (car (car evs)) :transmit)))
         (fn-sw-no-transmit-p (cdr evs)))))

; What a reachable state satisfies: the pending window is one window at most,
; the kernel holds fewer than W + Q unsent (the gate admits a write only below
; W, and a write is at most one pending window), and the octets rendered are
; the ones unsent, pending and transmitted.
(defun fn-sw-inv (st w q)
  (declare (xargs :guard t))
  (and (fn-sw-statep st) (natp w) (posp q)
       (<= (nth 1 st) q)
       (< (nth 0 st) (+ w q))
       (equal (nth 2 st) (+ (nth 0 st) (nth 1 st) (nth 3 st)))))

(defthm fn-sw-step-keeps-inv
  (implies (and (fn-sw-inv st w q) (fn-sw-step st ev w q t))
           (fn-sw-inv (fn-sw-step st ev w q t) w q))
  :hints (("Goal" :in-theory (enable fn-sw-step fn-sw-inv fn-sw-statep))))

(defthm fn-sw-run-keeps-inv
  (implies (and (fn-sw-inv st w q) (fn-sw-run st evs w q t))
           (fn-sw-inv (fn-sw-run st evs w q t) w q))
  :hints (("Goal" :in-theory (disable fn-sw-inv fn-sw-step)
                  :induct (fn-sw-run st evs w q t))))

(defthm fn-sw-start-inv
  (implies (and (natp w) (posp q)) (fn-sw-inv *fn-sw-start* w q))
  :hints (("Goal" :in-theory (enable fn-sw-inv fn-sw-statep))))

; KEYSTONE.  Rendered and not transmitted stays under W + 2Q, at the end of
; every legal trace and so at every prefix of one.
(defthm fn-sw-buffered-bounded
  (implies (and (natp w) (posp q)
                (fn-sw-run *fn-sw-start* evs w q t))
           (let ((st (fn-sw-run *fn-sw-start* evs w q t)))
             (< (+ (nth 0 st) (nth 1 st)) (+ w (* 2 q)))))
  :hints (("Goal" :use ((:instance fn-sw-run-keeps-inv (st *fn-sw-start*))
                        (:instance fn-sw-start-inv))
           :in-theory (e/d (fn-sw-inv) (fn-sw-run-keeps-inv fn-sw-start-inv))))
  :rule-classes nil)

(defthm fn-sw-no-transmit-no-transmitted
  (implies (and (fn-sw-no-transmit-p evs) (fn-sw-run st evs w q gatep)
                (equal (nth 3 st) 0))
           (equal (nth 3 (fn-sw-run st evs w q gatep)) 0))
  :hints (("Goal" :in-theory (enable fn-sw-step)
                  :induct (fn-sw-run st evs w q gatep))))

; KEYSTONE.  A reader that transmits nothing: the owner renders under W + 2Q
; octets in all, however long the reply.
(defthm fn-sw-stalled-reader-bounded
  (implies (and (natp w) (posp q)
                (fn-sw-no-transmit-p evs)
                (fn-sw-run *fn-sw-start* evs w q t))
           (< (nth 2 (fn-sw-run *fn-sw-start* evs w q t)) (+ w (* 2 q))))
  :hints (("Goal" :use ((:instance fn-sw-run-keeps-inv (st *fn-sw-start*))
                        (:instance fn-sw-start-inv)
                        (:instance fn-sw-no-transmit-no-transmitted (st *fn-sw-start*) (gatep t)))
           :in-theory (e/d (fn-sw-inv) (fn-sw-run-keeps-inv fn-sw-no-transmit-no-transmitted
                                        fn-sw-start-inv fn-sw-run))))
  :rule-classes nil)

; The entry at the profile's row: the bound the host's setting carries, for
; the largest window Q any plan renders.
(defthm fn-send-window-octets-bounds-the-connection
  (implies (and (posp q)
                (fn-sw-run *fn-sw-start* evs (fn-send-window-octets) q t))
           (let ((st (fn-sw-run *fn-sw-start* evs (fn-send-window-octets) q t)))
             (< (+ (nth 0 st) (nth 1 st)) (+ (fn-send-window-octets) (* 2 q)))))
  :hints (("Goal" :use ((:instance fn-sw-buffered-bounded (w (fn-send-window-octets))))
           :in-theory (disable fn-send-window-octets)))
  :rule-classes nil)

; ---- teeth ----

; Positive: the bound is not vacuous.  With W = 6 and Q = 4 a legal trace holds
; 12 octets (above W) and the bound is 14.
(defthm fn-sw-window-exceeds-w-within-the-bound
  (let ((st (fn-sw-run *fn-sw-start*
                       '((:render 4) (:write 4) (:render 4) (:write 4) (:render 4))
                       6 4 t)))
    (and (equal st '(8 4 12 0))
         (< 6 (+ (nth 0 st) (nth 1 st)))
         (< (+ (nth 0 st) (nth 1 st)) (+ 6 (* 2 4)))))
  :rule-classes nil)

; The gate refuses a write at or past W: the same trace one write further is
; not legal.
(defthm fn-sw-gate-refuses-a-write-past-w
  (and (null (fn-sw-run *fn-sw-start*
                        '((:render 4) (:write 4) (:render 4) (:write 4)
                          (:render 4) (:write 4))
                        6 4 t))
       (fn-sw-run *fn-sw-start*
                  '((:render 4) (:write 4) (:render 4) (:write 4)
                    (:render 4) (:write 4))
                  6 4 nil))
  :rule-classes nil)

; Hypothesis removal: without the gate a stalled reader has the owner render
; without bound.  Ten windows, no transmit, W = 6, Q = 4: 40 octets rendered,
; far past W + 2Q = 14, and the same trace with the gate is not legal.
(defun fn-sw-ten-windows ()
  (declare (xargs :guard t))
  '((:render 4) (:write 4) (:render 4) (:write 4) (:render 4) (:write 4)
    (:render 4) (:write 4) (:render 4) (:write 4) (:render 4) (:write 4)
    (:render 4) (:write 4) (:render 4) (:write 4) (:render 4) (:write 4)
    (:render 4) (:write 4)))

(defthm fn-sw-gate-removed-the-bound-fails
  (let ((open (fn-sw-run *fn-sw-start* (fn-sw-ten-windows) 6 4 nil))
        (gated (fn-sw-run *fn-sw-start* (fn-sw-ten-windows) 6 4 t)))
    (and open
         (fn-sw-no-transmit-p (fn-sw-ten-windows))
         (equal (nth 2 open) 40)
         (<= (+ 6 (* 2 4)) (nth 2 open))
         (null gated)))
  :rule-classes nil)
