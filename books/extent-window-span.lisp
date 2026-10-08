; Span-granular driving of the verified-window stream.
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
; STATEMENTS (each :rule-classes nil)

; A tick that answers anything but :continue is a fixed point of tick.
(defthm fn-ews-tick-past-stop-is-fixed
  (implies (not (equal (mv-nth 0 (fn-ews-tick s pgs-digest-state)) :continue))
           (equal (fn-ews-tick (mv-nth 1 (fn-ews-tick s pgs-digest-state))
                               (mv-nth 2 (fn-ews-tick s pgs-digest-state)))
                  (fn-ews-tick s pgs-digest-state)))
  :rule-classes nil)

; TICK-RUN is N ticks: same verdict, same stream state, same digest state.
(defthm fn-ews-tick-run-is-iterated-tick
  (implies (posp n)
           (equal (fn-ews-tick-run n s pgs-digest-state)
                  (fn-ews-tick-n n s pgs-digest-state)))
  :rule-classes nil)

; The span's effect is the stream's effect for its first block, widened.
(defthm fn-ews-span-effect-extends-block-effect
  (implies (fn-ews-span-effect s pgs-digest-state)
           (and (equal (update-nth 5 (fn-ewp-demand s) (fn-ews-span-effect s pgs-digest-state))
                       (fn-ews-effect s pgs-digest-state))
                (<= (fn-ewp-demand s) (fn-ews-span-demand s))
                (<= (fn-ews-span-demand s) (fn-profile-limit :read-span-octets))))
  :rule-classes nil)

; The block step at BASE is the stream's block step on the 64 octets there.
(defthm fn-ews-read-block-is-fn-ews-read-on-slice
  (implies (and (natp base) (equal (nth 0 s) :scan)
                (<= (+ base (fn-ewp-demand s)) (len fn-octets)))
           (equal (fn-ews-read-block base effect s fn-octets pgs-digest-state fn-ew-buffer)
                  (fn-ews-read effect :ok s (take (fn-ewp-demand s) (nthcdr base fn-octets))
                               pgs-digest-state fn-ew-buffer)))
  :rule-classes nil)

; THE EQUATION: the span loop is K iterations of the stream's block step
; and ticks; same final digest state, same captured buffer, same verdict
; (including :state on an invalid digest and :stale).
(defthm fn-ews-span-loop-is-iterated-block-step
  (implies (and (natp base) (<= (+ base (fn-ewp-demand s)) (len fn-octets)))
           (equal (fn-ews-span-loop k base s fn-octets pgs-digest-state fn-ew-buffer)
                  (fn-ews-span-spec k base s fn-octets pgs-digest-state fn-ew-buffer)))
  :rule-classes nil)

; The entry: stale and failed completions change nothing the stream's do not.
(defthm fn-ews-read-span-stale-preserves-all-effects
  (implies (or (not (fn-ews-span-effect s pgs-digest-state))
               (not (equal effect (fn-ews-span-effect s pgs-digest-state))))
           (equal (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
                  (list :stale s pgs-digest-state fn-ew-buffer)))
  :rule-classes nil)

(defthm fn-ews-read-span-failed-read-is-a-read-failure
  (implies (and (fn-ews-span-effect s pgs-digest-state)
                (equal effect (fn-ews-span-effect s pgs-digest-state))
                (or (not (equal io-status :ok))
                    (not (equal (len fn-octets) (fn-ews-span-demand s)))))
           (equal (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
                  (list :read (fn-ewp-with-phase-pos :read (nth 7 s) s)
                        pgs-digest-state fn-ew-buffer)))
  :rule-classes nil)

(defthm fn-ews-read-span-scan-is-iterated-block-step
  (implies (and (fn-ews-span-effect s pgs-digest-state)
                (equal effect (fn-ews-span-effect s pgs-digest-state))
                (equal io-status :ok)
                (equal (len fn-octets) (fn-ews-span-demand s))
                (equal (nth 0 s) :scan))
           (equal (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
                  (fn-ews-span-spec (ceiling (fn-ews-span-demand s) 64) 0 s fn-octets
                                    pgs-digest-state fn-ew-buffer)))
  :rule-classes nil)

(defthm fn-ews-read-span-trailer-is-the-stream-read
  (implies (and (fn-ews-span-effect s pgs-digest-state)
                (equal effect (fn-ews-span-effect s pgs-digest-state))
                (not (equal (nth 0 s) :scan)))
           (equal (fn-ews-read-span effect io-status s fn-octets pgs-digest-state fn-ew-buffer)
                  (fn-ews-read (fn-ews-effect s pgs-digest-state) io-status s fn-octets
                               pgs-digest-state fn-ew-buffer)))
  :rule-classes nil)
