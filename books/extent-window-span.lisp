; Span-granular driving of the verified-window stream.
; Cancellation: the owner's work-permitted decision is taken once per host call,
; so a cancel observed while a span read is in flight takes effect at the next
; span boundary; the extra work after a cancel is at most one span read (the
; profile's :read-span-octets of prefix digested, tick fuel bounded per block by
; *fn-ews-block-tick-fuel*), never an unbounded run.
; One host call moves up to a profile span of the protected prefix (:read-span-octets)
; and runs the digest to its next I/O need, instead of one 64-octet block per call.
; Every function here is a composition of books/extent-window-stream.lisp's block
; step (fn-ews-read, fn-ews-tick); the equations below say so, so the stream's
; keystones carry over unchanged. Statement first: proofs follow the statements.
(in-package "ACL2")
(include-book "extent-window-stream")

; Octets one host read moves: a span of scan blocks, or the 32-octet trailer.
(defun fn-ews-span-demand (s)
  (declare (xargs :guard (true-listp s)))
  (case (nth 0 s)
    (:scan (min (fn-profile-limit :read-span-octets)
                (nfix (- (nfix (nth 3 s)) (nfix (nth 7 s))))))
    (:trailer 32)
    (otherwise 0)))

; The effect the host executes: the core's own next-block effect with its
; length widened to the span. Same ticket, incarnation, lease, file, offset.
(defun fn-ews-span-effect (s pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (true-listp s)))
  (let ((e (fn-ews-effect s pgs-digest-state)))
    (and e (if (eq (nth 0 s) :scan)
               (update-nth 5 (fn-ews-span-demand s) e)
             e))))

; Window copy of the block stored at BASE of the host's buffer.
(defun fn-ewb-capture-at (base s fn-octets fn-ew-buffer)
  (declare (xargs :stobjs (fn-octets fn-ew-buffer)
                  :guard (and (true-listp s) (natp base) (natp (nth 5 s))
                              (<= (nth 5 s) (fn-profile-limit :read-window-octets))
                              (<= (+ base (fn-ewp-demand s)) (fn-octets-len fn-octets)))
                  :guard-hints (("Goal"
                    :use (fn-ewp-window-span-bounds fn-ewp-demand-bounded)
                    :in-theory (disable fn-ewp-window-span fn-ewb-copy)))))
  (let ((span (fn-ewp-window-span s)))
    (fn-ewb-copy (+ base (car span)) (cadr span) (caddr span) fn-octets fn-ew-buffer)))

; fn-ews-read's scan arm for the block whose octets start at BASE of the buffer.
(defun fn-ews-read-block (base effect s fn-octets pgs-digest-state fn-ew-buffer)
  (declare (xargs :stobjs (fn-octets pgs-digest-state fn-ew-buffer)
                  :guard (and (true-listp s) (natp base)
                              (<= (+ base (fn-ewp-demand s)) (fn-octets-len fn-octets)))
                  :verify-guards nil))
  (let ((issued (fn-ews-effect s pgs-digest-state)))
    (if (or (not issued) (not (equal effect issued)) (not (eq (nth 0 s) :scan)))
        (mv :stale s pgs-digest-state fn-ew-buffer)
      (let* ((block (fn-b3x-words 16 0 (fn-ewp-demand s) nil 0 base fn-octets))
             (fn-ew-buffer (fn-ewb-capture-at base s fn-octets fn-ew-buffer)))
        (mv-let (hash-status pgs-digest-state)
          (pgs-dcb-step (nth 3 s) block pgs-digest-state)
          (if (eq hash-status :invalid)
              (mv :state (fn-ewp-with-phase-pos :state (nth 7 s) s) pgs-digest-state fn-ew-buffer)
            (mv-let (status s)
              (fn-ewp-complete-read effect (fn-ewp-demand s) :ok s)
              (mv status s pgs-digest-state fn-ew-buffer))))))))

; Tick until the stream needs I/O or ends; FUEL ticks at most. Exhausting FUEL
; answers :continue with a consistent state: the caller resumes.
(defun fn-ews-tick-run (fuel s pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (and (natp fuel) (true-listp s))
                  :measure (nfix fuel) :verify-guards nil))
  (if (zp fuel)
      (mv :continue s pgs-digest-state)
    (mv-let (status s pgs-digest-state)
      (fn-ews-tick s pgs-digest-state)
      (if (eq status :continue)
          (fn-ews-tick-run (1- fuel) s pgs-digest-state)
        (mv status s pgs-digest-state)))))

; Exactly N ticks, whatever they answer: the reference the run is equal to.
(defun fn-ews-tick-n (n s pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (and (natp n) (true-listp s))
                  :measure (nfix n) :verify-guards nil))
  (if (zp n)
      (mv :continue s pgs-digest-state)
    (mv-let (status s pgs-digest-state)
      (fn-ews-tick s pgs-digest-state)
      (if (zp (1- n))
          (mv status s pgs-digest-state)
        (fn-ews-tick-n (1- n) s pgs-digest-state)))))

; Ticks the core may spend between two blocks before it yields.
(defconst *fn-ews-block-tick-fuel* 1024)

; The host's tick: run to the next I/O need (one quantum of ticks).
(defun fn-ews-tick-to-io (s pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (true-listp s) :verify-guards nil))
  (fn-ews-tick-run *fn-ews-block-tick-fuel* s pgs-digest-state))

; K blocks of the span at BASE: read a block, run the digest to the next I/O
; need, and go on while the stream wants the next block of this same buffer.
(defun fn-ews-span-loop (k base s fn-octets pgs-digest-state fn-ew-buffer)
  (declare (xargs :stobjs (fn-octets pgs-digest-state fn-ew-buffer)
                  :guard (and (natp k) (natp base) (true-listp s)
                              (<= (+ base (fn-ewp-demand s)) (fn-octets-len fn-octets)))
                  :measure (nfix k) :verify-guards nil))
  (if (zp k)
      (mv :continue s pgs-digest-state fn-ew-buffer)
    (mv-let (status s pgs-digest-state fn-ew-buffer)
      (fn-ews-read-block base (fn-ews-effect s pgs-digest-state) s fn-octets
                         pgs-digest-state fn-ew-buffer)
      (if (not (eq status :continue))
          (mv status s pgs-digest-state fn-ew-buffer)
        (mv-let (status s pgs-digest-state)
          (fn-ews-tick-run *fn-ews-block-tick-fuel* s pgs-digest-state)
          (if (and (eq status :read) (< 1 k)
                   (<= (+ base 64 (fn-ewp-demand s)) (fn-octets-len fn-octets)))
              (fn-ews-span-loop (1- k) (+ base 64) s fn-octets pgs-digest-state fn-ew-buffer)
            (mv status s pgs-digest-state fn-ew-buffer)))))))

; The entry the host calls with a completed span read (the trailer is the
; stream's own single read).
(defun fn-ews-read-span (effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
  (declare (xargs :stobjs (fn-octets pgs-digest-state fn-ew-buffer)
                  :guard (true-listp s) :verify-guards nil))
  (let ((issued (fn-ews-span-effect s pgs-digest-state)))
    (cond ((or (not issued) (not (equal effect issued)))
           (mv :stale s pgs-digest-state fn-ew-buffer))
          ((or (not (eq io-status :ok))
               (not (equal (fn-octets-len fn-octets) (fn-ews-span-demand s))))
           (mv :read (fn-ewp-with-phase-pos :read (nth 7 s) s) pgs-digest-state fn-ew-buffer))
          ((eq (nth 0 s) :scan)
           (fn-ews-span-loop (ceiling (fn-ews-span-demand s) 64) 0 s fn-octets
                             pgs-digest-state fn-ew-buffer))
          (t (fn-ews-read issued io-status s fn-octets pgs-digest-state fn-ew-buffer)))))

; ---------------------------------------------------------------------------
; The reference: the stream's own block step (fn-ews-read) on the 64 octets of
; the span at OFF, and N ticks, K times over. The loop above is equal to it.
(defun-nx fn-ews-span-spec (k off s fn-octets pgs-digest-state fn-ew-buffer)
  (declare (xargs :measure (nfix k) :verify-guards nil))
  (if (zp k)
      (mv :continue s pgs-digest-state fn-ew-buffer)
    (mv-let (status s pgs-digest-state fn-ew-buffer)
      (if (eq (nth 0 s) :scan)
          (fn-ews-read (fn-ews-effect s pgs-digest-state) :ok s
                       (take (fn-ewp-demand s) (nthcdr off fn-octets))
                       pgs-digest-state fn-ew-buffer)
        (mv :stale s pgs-digest-state fn-ew-buffer))
      (if (not (eq status :continue))
          (mv status s pgs-digest-state fn-ew-buffer)
        (mv-let (status s pgs-digest-state)
          (fn-ews-tick-n *fn-ews-block-tick-fuel* s pgs-digest-state)
          (if (and (eq status :read) (< 1 k)
                   (<= (+ off 64 (fn-ewp-demand s)) (len fn-octets)))
              (fn-ews-span-spec (1- k) (+ off 64) s fn-octets pgs-digest-state fn-ew-buffer)
            (mv status s pgs-digest-state fn-ew-buffer)))))))

; ---------------------------------------------------------------------------
; Lemmas: the buffer offset BASE is a slice of the buffer.
(defun fn-ews-nth-take-ind (i d x)
  (if (zp i) (list d x) (fn-ews-nth-take-ind (1- i) (1- d) (cdr x))))
(defthm fn-ews-nth-take
  (implies (and (natp i) (natp d) (< i d))
           (equal (nth i (take d x)) (nth i x)))
  :hints (("Goal" :induct (fn-ews-nth-take-ind i d x) :in-theory (enable take)
           :expand ((take d x)))))
(defthm fn-ews-nth-nthcdr
  (implies (and (natp i) (natp base))
           (equal (nth i (nthcdr base x)) (nth (+ base i) x)))
  :hints (("Goal" :induct (nthcdr base x))))
(defthm fn-ews-nthcdr-nil (equal (nthcdr n nil) nil))
(defthm fn-ews-len-take
  (implies (and (natp d) (<= d (len x))) (equal (len (take d x)) d))
  :hints (("Goal" :in-theory (enable take) :induct (take d x))))
(defthm fn-ews-len-nthcdr
  (implies (natp base) (equal (len (nthcdr base x)) (nfix (- (len x) base))))
  :hints (("Goal" :induct (nthcdr base x))))
(defthm fn-ews-len-slice
  (implies (and (natp base) (natp d) (<= (+ base d) (len st)))
           (equal (len (take d (nthcdr base st))) d))
  :hints (("Goal" :in-theory (disable take))))
(defthm fn-ews-b3x-byte-shift
  (implies (and (natp base) (natp i) (natp d) (<= (+ base d) (len st)))
           (equal (fn-b3x-byte i d nil 0 base st)
                  (fn-b3x-byte i d nil 0 0 (take d (nthcdr base st)))))
  :hints (("Goal" :in-theory (enable fn-b3x-byte fn-octets-get)))
  :rule-classes nil)
(defun fn-ews-kp-ind (k p) (if (zp k) p (fn-ews-kp-ind (1- k) (+ p 4))))
(defthm fn-ews-b3x-words-shift
  (implies (and (natp base) (natp p) (natp d) (<= (+ base d) (len st)))
           (equal (fn-b3x-words k p d nil 0 base st)
                  (fn-b3x-words k p d nil 0 0 (take d (nthcdr base st)))))
  :hints (("Goal" :induct (fn-ews-kp-ind k p)
           :in-theory (enable fn-b3x-words fn-b3x-word))
          ("Subgoal *1/2"
           :use ((:instance fn-ews-b3x-byte-shift (i p)) (:instance fn-ews-b3x-byte-shift (i (+ p 1)))
                 (:instance fn-ews-b3x-byte-shift (i (+ p 2))) (:instance fn-ews-b3x-byte-shift (i (+ p 3))))))
  :rule-classes nil)
(defun fn-ews-copy-ind (src2 src count dst st buf)
  (declare (xargs :measure (nfix count)))
  (if (zp count) (list buf src)
    (fn-ews-copy-ind (1+ src2) (1+ src) (1- count) (1+ dst) st
       (cons (update-nth dst (nth src2 st) (car buf)) (cdr buf)))))
(defthm fn-ews-copy-shift-gen
  (implies (and (natp base) (natp src) (natp count) (natp dst) (natp d)
                (equal src2 (+ base src))
                (<= (+ src count) d) (<= (+ base d) (len st)))
           (equal (fn-ewb-copy src2 count dst st buf)
                  (fn-ewb-copy src count dst (take d (nthcdr base st)) buf)))
  :hints (("Goal" :induct (fn-ews-copy-ind src2 src count dst st buf)
           :in-theory (enable fn-octets-get fn-ewb-copy)))
  :rule-classes nil)
(defthm fn-ews-capture-at-shift
  (implies (and (natp base) (<= (+ base (fn-ewp-demand s)) (len st)))
           (equal (fn-ewb-capture-at base s st buf)
                  (fn-ewb-capture s (take (fn-ewp-demand s) (nthcdr base st)) buf)))
  :hints (("Goal" :in-theory (e/d (fn-ewb-capture-at fn-ewb-capture) (fn-ewp-window-span fn-ewb-copy))
           :use (fn-ewp-window-span-bounds
                 (:instance fn-ews-copy-shift-gen (src2 (+ base (car (fn-ewp-window-span s)))) (src (car (fn-ewp-window-span s)))
                    (count (cadr (fn-ewp-window-span s))) (dst (caddr (fn-ewp-window-span s)))
                    (d (fn-ewp-demand s))))))
  :rule-classes nil)
(defthm fn-ews-tick-len3
  (and (true-listp (fn-ews-tick s pgs-digest-state)) (equal (len (fn-ews-tick s pgs-digest-state)) 3))
  :hints (("Goal" :in-theory (enable fn-ews-tick))))
(defthm fn-ews-len3-triple
  (implies (and (true-listp x) (equal (len x) 3))
           (equal (list (mv-nth 0 x) (mv-nth 1 x) (mv-nth 2 x)) x))
  :hints (("Goal" :in-theory (enable mv-nth) :expand ((len x) (len (cdr x)) (len (cddr x))))))
(defthm fn-ews-tick-is-triple
  (equal (list (mv-nth 0 (fn-ews-tick s h)) (mv-nth 1 (fn-ews-tick s h)) (mv-nth 2 (fn-ews-tick s h)))
         (fn-ews-tick s h))
  :hints (("Goal" :use ((:instance fn-ews-len3-triple (x (fn-ews-tick s h))) (:instance fn-ews-tick-len3 (pgs-digest-state h)))
           :in-theory (disable fn-ews-len3-triple fn-ews-tick-len3 fn-ews-tick))))
(defthm fn-ews-tick-is-triple-car
  (equal (list (car (fn-ews-tick s h)) (mv-nth 1 (fn-ews-tick s h)) (mv-nth 2 (fn-ews-tick s h)))
         (fn-ews-tick s h))
  :hints (("Goal" :use fn-ews-tick-is-triple :in-theory (disable fn-ews-tick-is-triple fn-ews-tick))))

; ---------------------------------------------------------------------------
; STATEMENTS (each :rule-classes nil)

; A tick that answers anything but :continue is a fixed point of tick.
(defthm fn-ews-tick-past-stop-is-fixed
  (implies (not (equal (mv-nth 0 (fn-ews-tick s pgs-digest-state)) :continue))
           (equal (fn-ews-tick (mv-nth 1 (fn-ews-tick s pgs-digest-state))
                               (mv-nth 2 (fn-ews-tick s pgs-digest-state)))
                  (fn-ews-tick s pgs-digest-state)))
  :hints (("Goal" :in-theory (enable fn-ews-tick fn-ewp-with-phase-pos fn-ewp-state)))
  :rule-classes nil)

(defthm fn-ews-tick-past-stop-rw
  (implies (not (equal (mv-nth 0 (fn-ews-tick s pgs-digest-state)) :continue))
           (equal (fn-ews-tick (mv-nth 1 (fn-ews-tick s pgs-digest-state))
                               (mv-nth 2 (fn-ews-tick s pgs-digest-state)))
                  (fn-ews-tick s pgs-digest-state)))
  :hints (("Goal" :use fn-ews-tick-past-stop-is-fixed)))

(defthm fn-ews-tick-n-past-stop
  (implies (and (posp m) (not (equal (mv-nth 0 (fn-ews-tick s pgs-digest-state)) :continue)))
           (equal (fn-ews-tick-n m (mv-nth 1 (fn-ews-tick s pgs-digest-state)) (mv-nth 2 (fn-ews-tick s pgs-digest-state)))
                  (fn-ews-tick s pgs-digest-state)))
  :hints (("Goal" :induct (fn-ews-tick-n m s pgs-digest-state)
           :in-theory (disable fn-ews-tick))))

; TICK-RUN is N ticks: same verdict, same stream state, same digest state.
(defthm fn-ews-tick-run-is-iterated-tick
  (implies (posp n)
           (equal (fn-ews-tick-run n s pgs-digest-state)
                  (fn-ews-tick-n n s pgs-digest-state)))
  :hints (("Goal" :induct (fn-ews-tick-run n s pgs-digest-state)
           :in-theory (disable fn-ews-tick)))
  :rule-classes nil)

; Fuel exhaustion yields a consistent :continue and the next run resumes it:
; two runs are one run of the summed fuel.
(defthm fn-ews-tick-run-resumes
  (implies (and (natp a) (natp b)
                (equal (mv-nth 0 (fn-ews-tick-run a s pgs-digest-state)) :continue))
           (equal (fn-ews-tick-run b (mv-nth 1 (fn-ews-tick-run a s pgs-digest-state))
                                     (mv-nth 2 (fn-ews-tick-run a s pgs-digest-state)))
                  (fn-ews-tick-run (+ a b) s pgs-digest-state)))
  :hints (("Goal" :induct (fn-ews-tick-run a s pgs-digest-state)
           :in-theory (enable fn-ews-tick-run)))
  :rule-classes nil)

; The host's tick is the block quantum of ticks.
(defthm fn-ews-tick-to-io-is-iterated-tick
  (equal (fn-ews-tick-to-io s pgs-digest-state)
         (fn-ews-tick-n *fn-ews-block-tick-fuel* s pgs-digest-state))
  :hints (("Goal" :in-theory (enable fn-ews-tick-to-io)
           :use (:instance fn-ews-tick-run-is-iterated-tick (n *fn-ews-block-tick-fuel*))))
  :rule-classes nil)

; The span's effect is the stream's effect for its first block, widened.
(defthm fn-ews-span-effect-extends-block-effect
  (implies (fn-ews-span-effect s pgs-digest-state)
           (and (equal (update-nth 5 (fn-ewp-demand s) (fn-ews-span-effect s pgs-digest-state))
                       (fn-ews-effect s pgs-digest-state))
                (<= (fn-ewp-demand s) (fn-ews-span-demand s))
                (<= (fn-ews-span-demand s) (fn-profile-limit :read-span-octets))))
  :hints (("Goal" :in-theory (e/d (fn-ews-span-effect fn-ews-span-demand fn-ewp-demand fn-ewp-effect fn-ews-effect) (nfix))))
  :rule-classes nil)

; The block step at BASE is the stream's block step on the 64 octets there.
(defthm fn-ews-read-block-is-fn-ews-read-on-slice
  (implies (and (natp base) (equal (nth 0 s) :scan)
                (<= (+ base (fn-ewp-demand s)) (len fn-octets)))
           (equal (fn-ews-read-block base effect s fn-octets pgs-digest-state fn-ew-buffer)
                  (fn-ews-read effect :ok s (take (fn-ewp-demand s) (nthcdr base fn-octets))
                               pgs-digest-state fn-ew-buffer)))
  :hints (("Goal" :in-theory (e/d (fn-ews-read-block fn-ews-read)
                                  (fn-ewp-demand fn-ewb-capture-at fn-ewb-capture fn-ewp-complete-read take fn-b3x-words))
           :use ((:instance fn-ews-capture-at-shift (st fn-octets) (buf fn-ew-buffer))
                 (:instance fn-ews-b3x-words-shift (k 16) (p 0) (d (fn-ewp-demand s)) (st fn-octets))
                 (:instance fn-ews-len-slice (d (fn-ewp-demand s)) (st fn-octets))
                 fn-ewp-demand-bounded)))
  :rule-classes nil)

(defthm fn-ews-read-block-rw
  (implies (and (natp base) (equal (nth 0 s) :scan)
                (<= (+ base (fn-ewp-demand s)) (len fn-octets)))
           (equal (fn-ews-read-block base effect s fn-octets pgs-digest-state fn-ew-buffer)
                  (fn-ews-read effect :ok s (take (fn-ewp-demand s) (nthcdr base fn-octets))
                               pgs-digest-state fn-ew-buffer)))
  :hints (("Goal" :use fn-ews-read-block-is-fn-ews-read-on-slice)))
(defthm fn-ews-read-block-not-scan
  (implies (not (equal (nth 0 s) :scan))
           (equal (fn-ews-read-block base effect s fn-octets pgs-digest-state fn-ew-buffer)
                  (list :stale s pgs-digest-state fn-ew-buffer)))
  :hints (("Goal" :in-theory (enable fn-ews-read-block))))
(defthm fn-ews-tick-run-rw
  (implies (posp n)
           (equal (fn-ews-tick-run n s pgs-digest-state) (fn-ews-tick-n n s pgs-digest-state)))
  :hints (("Goal" :use fn-ews-tick-run-is-iterated-tick)))

; THE EQUATION: the span loop is K iterations of the stream's block step
; and ticks; same final digest state, same captured buffer, same verdict
; (including :state on an invalid digest and :stale).
(defthm fn-ews-span-loop-is-iterated-block-step
  (implies (and (natp base) (<= (+ base (fn-ewp-demand s)) (len fn-octets)))
           (equal (fn-ews-span-loop k base s fn-octets pgs-digest-state fn-ew-buffer)
                  (fn-ews-span-spec k base s fn-octets pgs-digest-state fn-ew-buffer)))
  :hints (("Goal" :induct (fn-ews-span-loop k base s fn-octets pgs-digest-state fn-ew-buffer)
           :in-theory (disable fn-ewp-demand take nthcdr len fn-ews-read-block fn-ews-read
                               fn-ews-tick-n fn-ews-tick-run fn-ews-effect)
           :expand ((fn-ews-span-loop k base s fn-octets pgs-digest-state fn-ew-buffer)
                    (fn-ews-span-spec k base s fn-octets pgs-digest-state fn-ew-buffer))))
  :rule-classes nil)

; The entry: stale and failed completions change nothing the stream's do not.
(defthm fn-ews-read-span-stale-preserves-all-effects
  (implies (or (not (fn-ews-span-effect s pgs-digest-state))
               (not (equal effect (fn-ews-span-effect s pgs-digest-state))))
           (equal (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
                  (list :stale s pgs-digest-state fn-ew-buffer)))
  :hints (("Goal" :in-theory (enable fn-ews-read-span)))
  :rule-classes nil)

(defthm fn-ews-read-span-failed-read-is-a-read-failure
  (implies (and (fn-ews-span-effect s pgs-digest-state)
                (equal effect (fn-ews-span-effect s pgs-digest-state))
                (or (not (equal io-status :ok))
                    (not (equal (len fn-octets) (fn-ews-span-demand s)))))
           (equal (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
                  (list :read (fn-ewp-with-phase-pos :read (nth 7 s) s)
                        pgs-digest-state fn-ew-buffer)))
  :hints (("Goal" :in-theory (enable fn-ews-read-span)))
  :rule-classes nil)

(defthm fn-ews-span-demand-covers-block
  (implies (fn-ews-span-effect s pgs-digest-state)
           (<= (fn-ewp-demand s) (fn-ews-span-demand s)))
  :hints (("Goal" :use fn-ews-span-effect-extends-block-effect)))

(defthm fn-ews-read-span-scan-is-iterated-block-step
  (implies (and (fn-ews-span-effect s pgs-digest-state)
                (equal effect (fn-ews-span-effect s pgs-digest-state))
                (equal io-status :ok)
                (equal (len fn-octets) (fn-ews-span-demand s))
                (equal (nth 0 s) :scan))
           (equal (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
                  (fn-ews-span-spec (ceiling (fn-ews-span-demand s) 64) 0 s fn-octets
                                    pgs-digest-state fn-ew-buffer)))
  :hints (("Goal" :in-theory (e/d (fn-ews-read-span) (fn-ews-span-loop fn-ews-span-spec fn-ews-span-demand fn-ews-span-effect))
           :use ((:instance fn-ews-span-loop-is-iterated-block-step (k (ceiling (fn-ews-span-demand s) 64)) (base 0))
                 fn-ews-span-demand-covers-block)))
  :rule-classes nil)

(defthm fn-ews-read-span-trailer-is-the-stream-read
  (implies (and (fn-ews-span-effect s pgs-digest-state)
                (equal effect (fn-ews-span-effect s pgs-digest-state))
                (equal (nth 0 s) :trailer))
           (equal (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
                  (fn-ews-read (fn-ews-effect s pgs-digest-state) io-status s fn-octets
                               pgs-digest-state fn-ew-buffer)))
  :hints (("Goal" :in-theory (e/d (fn-ews-read-span fn-ews-span-effect fn-ews-read fn-ews-span-demand fn-ewp-demand) (fn-ews-effect))
           :do-not-induct t))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; The publication keystone for the entry the host calls.
(defthm fn-ews-tick-no-new-publication
  (implies (not (fn-ewp-publication s))
           (not (fn-ewp-publication (mv-nth 1 (fn-ews-tick s pgs-digest-state)))))
  :hints (("Goal" :in-theory (enable fn-ews-tick fn-ewp-publication fn-ewp-with-phase-pos fn-ewp-state))))
(defthm fn-ews-tick-n-no-new-publication
  (implies (not (fn-ewp-publication s))
           (not (fn-ewp-publication (mv-nth 1 (fn-ews-tick-n n s pgs-digest-state)))))
  :hints (("Goal" :in-theory (e/d (fn-ews-tick-n) (fn-ews-tick)) :induct (fn-ews-tick-n n s pgs-digest-state))))
(defthm fn-ews-read-scan-no-publication
  (implies (and (not (fn-ewp-publication s)) (equal (nth 0 s) :scan))
           (not (fn-ewp-publication (mv-nth 1 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer)))))
  :hints (("Goal" :use fn-ews-read-publication-requires-core-integrity :in-theory (disable fn-ews-read fn-ewp-publication))))
(defthm fn-ews-span-spec-no-publication
  (implies (not (fn-ewp-publication s))
           (not (fn-ewp-publication (mv-nth 1 (fn-ews-span-spec k off s fn-octets pgs-digest-state fn-ew-buffer)))))
  :hints (("Goal" :in-theory (e/d (fn-ews-span-spec) (fn-ews-tick-n fn-ews-read fn-ewp-publication))
           :induct (fn-ews-span-spec k off s fn-octets pgs-digest-state fn-ew-buffer))))
(defthm fn-ews-span-effect-phase
  (implies (fn-ews-span-effect s pgs-digest-state)
           (or (equal (nth 0 s) :scan) (equal (nth 0 s) :trailer)))
  :hints (("Goal" :in-theory (e/d (fn-ews-span-effect fn-ews-effect fn-ewp-effect fn-ewp-demand) (fn-ews-span-demand))))
  :rule-classes nil)
(defthm fn-ews-read-span-scan-no-publication
  (implies (and (fn-ews-span-effect s pgs-digest-state)
                (equal effect (fn-ews-span-effect s pgs-digest-state))
                (equal (nth 0 s) :scan)
                (not (fn-ewp-publication s)))
           (not (fn-ewp-publication (mv-nth 1 (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer)))))
  :hints (("Goal" :do-not-induct t :cases ((and (equal io-status :ok) (equal (len fn-octets) (fn-ews-span-demand s))))
           :in-theory (e/d (fn-ewp-publication) (fn-ews-read-span fn-ews-span-spec fn-ews-span-effect fn-ews-span-demand fn-ews-span-spec-no-publication))
           :use (fn-ews-read-span-failed-read-is-a-read-failure fn-ews-read-span-scan-is-iterated-block-step
                 (:instance fn-ews-span-spec-no-publication (k (ceiling (fn-ews-span-demand s) 64)) (off 0))))))

; A window is published only by the trailer read, only with the digest of the
; consumed prefix equal to the committed one: fn-ews-read's keystone for the
; entry the host actually calls.
(defthm fn-ews-read-span-publication-requires-core-integrity
  (implies
    (and (not (fn-ewp-publication s))
         (fn-ewp-publication
           (mv-nth 1 (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer))))
    (and (equal (nth 0 s) :trailer)
         (equal (pgs-dc-mode pgs-digest-state) :done)
         (equal (nth 7 s) (nth 3 s))
         (equal io-status :ok)
         (equal (fn-octets-len fn-octets) 32)
         (equal (fn-bch-pack (fn-ews-read-trailer 32 0 fn-octets)) (nth 6 s))
         (equal (pgs-dcb-result-octets pgs-digest-state) (fn-ews-read-trailer 32 0 fn-octets))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ews-read-span fn-ewp-publication fn-ews-span-effect fn-ews-read fn-ews-effect)
           :cases ((and (fn-ews-span-effect s pgs-digest-state) (equal effect (fn-ews-span-effect s pgs-digest-state))))
           :use (fn-ews-read-span-stale-preserves-all-effects fn-ews-span-effect-phase
                 fn-ews-read-span-scan-no-publication
                 fn-ews-read-span-trailer-is-the-stream-read
                 (:instance fn-ews-read-publication-requires-core-integrity (effect (fn-ews-effect s pgs-digest-state))))))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; Guards: the host calls fn-ews-tick-run and fn-ews-read-span.
(defthm fn-ews-tick-true-listp-s
  (implies (true-listp s) (true-listp (mv-nth 1 (fn-ews-tick s pgs-digest-state))))
  :hints (("Goal" :in-theory (enable fn-ews-tick fn-ewp-with-phase-pos fn-ewp-state))))
(verify-guards fn-ews-tick-run)
(verify-guards fn-ews-tick-to-io)
(verify-guards fn-ews-read-block
  :hints (("Goal" :in-theory (enable fn-ews-effect fn-ews-boundp fn-ewp-demand) :use fn-ewp-demand-bounded)))
(defthm fn-ews-tick-run-true-listp-s
  (implies (true-listp s) (true-listp (mv-nth 1 (fn-ews-tick-run n s pgs-digest-state))))
  :hints (("Goal" :in-theory (enable fn-ews-tick-run) :induct (fn-ews-tick-run n s pgs-digest-state))))
(defthm fn-ews-read-block-true-listp-s
  (implies (true-listp s) (true-listp (mv-nth 1 (fn-ews-read-block base effect s fn-octets pgs-digest-state fn-ew-buffer))))
  :hints (("Goal" :in-theory (enable fn-ews-read-block fn-ewp-with-phase-pos fn-ewp-state fn-ewp-complete-read))))
(in-theory (disable fn-ews-tick-run-rw fn-ews-read-block-rw fn-ews-read-block-not-scan))
(verify-guards fn-ews-span-loop
  :hints (("Goal" :in-theory (disable fn-ews-read-block fn-ews-tick-run fn-ewp-demand fn-ews-effect
                                      fn-ewp-complete-read fn-ewp-with-phase-pos))))
(verify-guards fn-ews-read-span
  :hints (("Goal" :in-theory (disable fn-ews-span-effect fn-ewp-demand fn-ews-span-demand fn-ews-read fn-ews-span-loop)
           :use fn-ews-span-demand-covers-block)))
(in-theory (disable fn-ews-span-demand fn-ews-span-effect fn-ewb-capture-at fn-ews-read-block
                    fn-ews-tick-run fn-ews-tick-n fn-ews-tick-to-io fn-ews-span-loop fn-ews-read-span))
