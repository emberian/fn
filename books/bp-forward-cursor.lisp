; The forward round as a bounded, resumable cursor over held transit
; (planning/design/bp-2026-10-04.md section 2.7; PRF-1311).
;
; The host's :forward service class (host/native/bp-node.lisp, the service
; lambda of fnn-bp-session-loop) asks fn-bpfc-turn once per turn.  The
; logical model stays fn-bpsched-forward-entry over fn-bpnp-forward-plan
; (books/bp-session-scheduler, books/bp-node-forward-plan): a sweep run to
; completion from the head answers exactly their choice
; (fn-bpfc-run-is-the-plan-choice), one turn examines at most QUANTUM rows
; (fn-bpfc-turn-advances-at-most-quantum), and resuming after a yield is the
; same as never having yielded (fn-bpfc-turn-after-a-yield-is-the-larger-turn).
; Work per turn is bounded in route decisions and allocation (D27); the
; position skip over the oldest-first order is a pointer walk, as
; fn-bpnjc-drop's is for the contact round, until the held set is indexed.
(in-package "ACL2")
(include-book "bp-node-forward-plan")
(include-book "bp-session-scheduler")

; One scan step over the oldest-first suffix ROWS, at absolute position POS,
; with the peers SEEN already planned this sweep and the peers BUSY on an
; open session.  The row condition is fn-bpnp-forward-plan-rows' own; BUSY
; is fn-bpsched-forward-entry's.  Answer: (WORD ENTRY POS' SEEN').
(defun fn-bpfc-scan (rows table seen busy quantum pos)
  (declare (xargs :guard (and (true-listp busy) (natp quantum) (natp pos))
                  :measure (acl2-count rows)))
  (cond ((atom rows) (list :drained nil pos seen))
        ((zp quantum) (list :yield nil pos seen))
        (t (let* ((h (car rows))
                  (peer (fn-bpn-nth 11 h))
                  (choice (fn-bprt-outbound-choice (fn-bpnp-held-dest h) table)))
             (if (and (equal (fn-bpn-nth 12 h) '(:forward-pending))
                      (null (fn-bpn-nth 14 h))
                      (fn-bpp-eidp peer)
                      (not (member-equal peer (fix-true-list seen)))
                      (equal (fn-bprt-nth 0 choice) :hop))
                 (if (member-equal peer busy)
                     (fn-bpfc-scan (cdr rows) table (cons peer (fix-true-list seen))
                                   busy (1- quantum) (1+ pos))
                   (list :entry
                         (list peer (fn-bprt-nth 1 choice) (fn-bprt-nth 2 choice)
                               (fn-bprt-nth 3 choice))
                         (1+ pos) (cons peer (fix-true-list seen))))
               (fn-bpfc-scan (cdr rows) table seen busy (1- quantum) (1+ pos)))))))

(defun fn-bpfc-cursor (pos seen)
  (declare (xargs :guard t))
  (list :bpfc pos seen))
(defun fn-bpfc-pos (cursor)
  (declare (xargs :guard t))
  (nfix (fn-bpn-nth 1 cursor)))
(defun fn-bpfc-seen (cursor)
  (declare (xargs :guard t))
  (fix-true-list (fn-bpn-nth 2 cursor)))
(defun fn-bpfc-initial ()
  (declare (xargs :guard t))
  (fn-bpfc-cursor 0 nil))

; The oldest-first order fn-bpnp-forward-plan walks (it reverses HELD).
(defun fn-bpfc-ordered (held)
  (declare (xargs :guard (true-listp held)))
  (reverse held))

(defthm fn-bpfc-ordered-true-listp
  (implies (true-listp held) (true-listp (fn-bpfc-ordered held))))

; One turn: (:entry (PEER HOP EID PORT) CURSOR'), (:yield CURSOR') or
; (:drained).
(defun fn-bpfc-turn (cursor held table busy quantum)
  (declare (xargs :guard (and (true-listp held) (true-listp busy) (posp quantum))))
  (let* ((pos (fn-bpfc-pos cursor))
         (answer (fn-bpfc-scan (nthcdr pos (fn-bpfc-ordered held)) table
                               (fn-bpfc-seen cursor) busy quantum pos)))
    (case (car answer)
      (:entry (list :entry (second answer)
                    (fn-bpfc-cursor (third answer) (fourth answer))))
      (:yield (list :yield (fn-bpfc-cursor (third answer) (fourth answer))))
      (otherwise (list :drained)))))

; Turns to the first answer that is not a yield, at most FUEL resumptions.
(defun fn-bpfc-run (cursor held table busy quantum fuel)
  (declare (xargs :guard (and (true-listp held) (true-listp busy) (posp quantum) (natp fuel))
                  :measure (nfix fuel)))
  (let ((answer (fn-bpfc-turn cursor held table busy quantum)))
    (if (and (equal (car answer) :yield) (not (zp fuel)))
        (fn-bpfc-run (second answer) held table busy quantum (1- fuel))
      answer)))

;; The route condition, the destination and the row slots are opaque to every
;; proof below, as they are to bp-node-forward-plan's.
; ---------------------------------------------------------------------------
; K1: one turn examines at most QUANTUM rows.  Each examined row is one
; fn-bprt-outbound-choice, so the position advance is the decision count.

(defthm fn-bpfc-scan-advances-at-most-quantum
  (implies (natp pos)
           (<= (third (fn-bpfc-scan rows table seen busy quantum pos))
               (+ pos (nfix quantum))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

(defthm fn-bpfc-scan-advances-from-pos
  (implies (natp pos)
           (<= pos (third (fn-bpfc-scan rows table seen busy quantum pos))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

(defthm fn-bpfc-scan-position-is-natp
  (implies (natp pos)
           (natp (third (fn-bpfc-scan rows table seen busy quantum pos))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

(defthm fn-bpfc-scan-seen-is-true-listp
  (implies (true-listp seen)
           (true-listp (fourth (fn-bpfc-scan rows table seen busy quantum pos))))
  :hints (("Goal" :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

(defthm fn-bpfc-turn-advances-at-most-quantum
  (implies (member-equal (car (fn-bpfc-turn cursor held table busy quantum))
                         '(:entry :yield))
           (let ((next (if (equal (car (fn-bpfc-turn cursor held table busy quantum)) :entry)
                           (third (fn-bpfc-turn cursor held table busy quantum))
                         (second (fn-bpfc-turn cursor held table busy quantum)))))
             (and (<= (fn-bpfc-pos cursor) (fn-bpfc-pos next))
                  (<= (fn-bpfc-pos next) (+ (fn-bpfc-pos cursor) (nfix quantum))))))
  :hints (("Goal" :in-theory (disable fn-bpfc-scan fn-bpfc-ordered))))

; ---------------------------------------------------------------------------
; K3: resuming after a yield is the same as never having yielded.

(defthm fn-bpfc-scan-of-nfix-quantum
  (equal (fn-bpfc-scan rows table seen busy (nfix quantum) pos)
         (fn-bpfc-scan rows table seen busy quantum pos))
  :hints (("Goal" :expand ((fn-bpfc-scan rows table seen busy (nfix quantum) pos)
                           (fn-bpfc-scan rows table seen busy quantum pos))
                  :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

(defthm fn-bpfc-scan-resumes-after-a-yield
  (implies (equal (car (fn-bpfc-scan rows table seen busy q1 pos)) :yield)
           (equal (fn-bpfc-scan (nthcdr (nfix q1) rows) table
                                (fourth (fn-bpfc-scan rows table seen busy q1 pos))
                                busy q2
                                (third (fn-bpfc-scan rows table seen busy q1 pos)))
                  (fn-bpfc-scan rows table seen busy (+ (nfix q1) (nfix q2)) pos)))
  :hints (("Goal" :induct (fn-bpfc-scan rows table seen busy q1 pos)
                  :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

; A yield is exactly QUANTUM rows past POS.
(defthm fn-bpfc-scan-yield-position
  (implies (and (natp pos)
                (equal (car (fn-bpfc-scan rows table seen busy quantum pos)) :yield))
           (equal (third (fn-bpfc-scan rows table seen busy quantum pos))
                  (+ pos (nfix quantum))))
  :hints (("Goal" :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

(local (defthm fn-bpfc-nthcdr-of-nthcdr
  (implies (and (natp a) (natp b))
           (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x)))))

(defthm fn-bpfc-turn-after-a-yield-is-the-larger-turn
  (implies (and (natp q1) (natp q2)
                (equal (car (fn-bpfc-turn cursor held table busy q1)) :yield))
           (equal (fn-bpfc-turn (second (fn-bpfc-turn cursor held table busy q1))
                                held table busy q2)
                  (fn-bpfc-turn cursor held table busy (+ q1 q2))))
  :hints (("Goal" :in-theory (disable fn-bpfc-scan fn-bpfc-ordered
                                      fn-bpfc-scan-resumes-after-a-yield)
                  :use ((:instance fn-bpfc-scan-resumes-after-a-yield
                         (rows (nthcdr (fn-bpfc-pos cursor) (fn-bpfc-ordered held)))
                         (seen (fn-bpfc-seen cursor))
                         (pos (fn-bpfc-pos cursor)))))))

; ---------------------------------------------------------------------------
; K2: a sweep run to completion from the head is the plan's choice.

; Two quanta stepped down together, for the larger-quantum lemma.
(local (defun fn-bpfc-scan-2q-ind (rows table seen busy q1 q2 pos)
  (declare (xargs :measure (acl2-count rows)))
  (cond ((atom rows) (list table seen busy q1 q2 pos))
        ((or (zp q1) (zp q2)) nil)
        (t (let* ((h (car rows))
                  (peer (fn-bpn-nth 11 h))
                  (choice (fn-bprt-outbound-choice (fn-bpnp-held-dest h) table)))
             (if (and (equal (fn-bpn-nth 12 h) '(:forward-pending))
                      (null (fn-bpn-nth 14 h))
                      (fn-bpp-eidp peer)
                      (not (member-equal peer (fix-true-list seen)))
                      (equal (fn-bprt-nth 0 choice) :hop))
                 (if (member-equal peer busy)
                     (fn-bpfc-scan-2q-ind (cdr rows) table (cons peer (fix-true-list seen))
                                          busy (1- q1) (1- q2) (1+ pos))
                   nil)
               (fn-bpfc-scan-2q-ind (cdr rows) table seen busy (1- q1) (1- q2) (1+ pos))))))))

; A scan that does not yield is the same under any larger quantum.
(defthm fn-bpfc-scan-with-more-quantum-agrees
  (implies (and (not (equal (car (fn-bpfc-scan rows table seen busy q1 pos)) :yield))
                (<= (nfix q1) (nfix q2)))
           (equal (fn-bpfc-scan rows table seen busy q2 pos)
                  (fn-bpfc-scan rows table seen busy q1 pos)))
  :hints (("Goal" :induct (fn-bpfc-scan-2q-ind rows table seen busy q1 q2 pos)
                  :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

; A scan whose quantum covers the suffix never yields.
(defthm fn-bpfc-scan-covering-never-yields
  (implies (<= (len rows) (nfix quantum))
           (not (equal (car (fn-bpfc-scan rows table seen busy quantum pos)) :yield)))
  :hints (("Goal" :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

; A covering scan selects what the plan and the scheduler's busy filter select.
(defthm fn-bpfc-scan-covering-is-the-plan-choice
  (implies (<= (len rows) (nfix quantum))
           (let ((e (fn-bpsched-forward-entry (fn-bpnp-forward-plan-rows rows table seen) busy)))
             (and (equal (car (fn-bpfc-scan rows table seen busy quantum pos))
                         (if e :entry :drained))
                  (equal (second (fn-bpfc-scan rows table seen busy quantum pos)) e))))
  :hints (("Goal" :induct (fn-bpfc-scan rows table seen busy quantum pos)
                  :in-theory (disable fn-bprt-outbound-choice fn-bpnp-held-dest
                                      fn-bpn-nth fn-bpp-eidp fn-bprt-nth))))

(defthm fn-bpfc-turn-with-more-quantum-agrees
  (implies (and (not (equal (car (fn-bpfc-turn cursor held table busy q1)) :yield))
                (natp q1) (natp q2) (<= q1 q2))
           (equal (fn-bpfc-turn cursor held table busy q2)
                  (fn-bpfc-turn cursor held table busy q1)))
  :hints (("Goal" :in-theory (disable fn-bpfc-scan fn-bpfc-ordered
                                      fn-bpfc-scan-with-more-quantum-agrees)
                  :use ((:instance fn-bpfc-scan-with-more-quantum-agrees
                         (rows (nthcdr (fn-bpfc-pos cursor) (fn-bpfc-ordered held)))
                         (seen (fn-bpfc-seen cursor))
                         (pos (fn-bpfc-pos cursor)))))))

; FUEL resumptions of quantum Q are one turn of quantum Q * (FUEL + 1).
(defthm fn-bpfc-run-is-one-large-turn
  (implies (and (posp quantum) (natp fuel))
           (equal (fn-bpfc-run cursor held table busy quantum fuel)
                  (fn-bpfc-turn cursor held table busy (* quantum (+ 1 fuel)))))
  :hints (("Goal" :induct (fn-bpfc-run cursor held table busy quantum fuel)
                  :in-theory (disable fn-bpfc-turn fn-bpfc-turn-with-more-quantum-agrees
                                      fn-bpfc-turn-after-a-yield-is-the-larger-turn))
          ("Subgoal *1/1" :use ((:instance fn-bpfc-turn-after-a-yield-is-the-larger-turn
                                 (q1 quantum) (q2 (* quantum fuel)))))
          ("Subgoal *1/2" :use ((:instance fn-bpfc-turn-with-more-quantum-agrees
                                 (q1 quantum) (q2 (* quantum (+ 1 fuel))))))))

(local (defthm fn-bpfc-covering-quantum
  (implies (and (posp q) (natp n))
           (<= n (+ q (* q n))))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear))

(defthm fn-bpfc-run-is-the-plan-choice
  (implies (and (true-listp held) (posp quantum))
           (let ((run (fn-bpfc-run (fn-bpfc-initial) held table busy quantum (len held)))
                 (e (fn-bpsched-forward-entry (fn-bpnp-forward-plan held table) busy)))
             (and (equal (car run) (if e :entry :drained))
                  (implies e (equal (second run) e)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable fn-bpfc-scan fn-bpsched-forward-entry fn-bpnp-forward-plan-rows
                                      fn-bpfc-scan-covering-is-the-plan-choice)
                  :use ((:instance fn-bpfc-scan-covering-is-the-plan-choice
                         (rows (fn-bpfc-ordered held)) (seen nil) (pos 0)
                         (quantum (* quantum (+ 1 (len held)))))))))
