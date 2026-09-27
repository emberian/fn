; PRF-245: fragment reassembly as a RESUMABLE step bounded in octets per
; step (RFC 9171 section 5.9; D27: bound work per scheduling step, never
; data).
;
; `fn-bpfw-reassemble' (books/bp-fragment-sweep.lisp) sweeps the positions
; 0..total-1 of a family in one call: for a 10 MiB family that is one step
; of 10 MiB.  The sweep's state is already explicit -- the active extents'
; unconsumed suffixes, the queue of sorted fragments not yet admitted, the
; position, the positions left and the emitted cells -- so it can stop after
; any number of positions and resume from that state.
;
; `fn-bpfr-step' runs at most QUANTUM positions (it emits at most QUANTUM
; octets) and returns the state.  `fn-bpfr-start' is the state before the
; first position; `fn-bpfr-finish' the outcome of a finished state.
;
; KEYSTONE fn-bpfr-step-resumes: the sweep from any state equals the sweep
; from the state one bounded step leaves; so any schedule of steps, of any
; quanta, reaches the one reassembly (fn-bpfr-run-is-reassemble:
; running steps of QUANTUM to completion is `fn-bpfw-reassemble', hence
; `fn-bpfw-spec', the uncapped RFC 9171 reference).
; fn-bpfr-step-is-bounded: one step consumes at most QUANTUM positions and
; emits exactly min(QUANTUM, left) cells.
;
; Host: NONE YET.  The node's family plan (bp-node-fragment-family) still
; calls the whole reassembly inside one foundation step; carrying this state
; across steps is the integration boundary (planning/evidence/
; bp-fragments-10mib-2026-09-27.md).  The cells are still an octet list:
; assembly into the Store's arena by extents waits for PKT-585.
(in-package "ACL2")
(include-book "bp-fragment-sweep")

; The sweep state: (active queue position left cells), CELLS reversed.
(defun fn-bpfr-state (active queue i n acc)
  (declare (xargs :guard t))
  (list active queue i n acc))

(defun fn-bpfr-step (active queue i n acc quantum)
  (declare (xargs :guard (and (true-list-listp active)
                              (fn-bpfw-fragment-listp queue)
                              (natp i) (natp n) (true-listp acc)
                              (natp quantum))
                  :measure (nfix n) :verify-guards nil))
  (if (or (zp n) (zp quantum))
      (fn-bpfr-state active queue i n acc)
    (mv-let (active queue) (fn-bpfw-admit active queue i)
      (fn-bpfr-step (fn-bpfw-advance active) queue (+ 1 i) (- n 1)
                    (cons (fn-bpfw-head-cell active) acc)
                    (- quantum 1)))))

(verify-guards fn-bpfr-step
  :hints (("Goal" :use ((:instance fn-bpfw-admit-true-list-list))
           :in-theory (disable fn-bpfw-admit fn-bpfw-advance
                               fn-bpfw-admit-true-list-list
                               fn-bpfw-head-cell fn-bpfw-fragmentp))))

(defun fn-bpfr-resume (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpfw-sweep-acc (nth 0 s) (nth 1 s) (nth 2 s) (nth 3 s) (nth 4 s)))

; KEYSTONE.  One bounded step changes nothing about the sweep's result.
(defthm fn-bpfr-step-resumes
  (equal (fn-bpfr-resume (fn-bpfr-step active queue i n acc quantum))
         (fn-bpfw-sweep-acc active queue i n acc))
  :hints (("Goal" :induct (fn-bpfr-step active queue i n acc quantum)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-bpfr-step fn-bpfr-resume fn-bpfr-state
                         fn-bpfw-sweep-acc car-cons cdr-cons
                         (:executable-counterpart zp) nth-0-cons
                         nth-add1)))
          ("Subgoal *1/1" :expand ((fn-bpfw-sweep-acc active queue i n acc)
                                   (nth 1 (list active queue i n acc))
                                   (nth 2 (list active queue i n acc))
                                   (nth 3 (list active queue i n acc))
                                   (nth 4 (list active queue i n acc))))))

; The bound: exactly min(QUANTUM, left) positions consumed and cells emitted.
(defthm fn-bpfr-step-is-bounded
  (implies (and (natp n) (natp quantum))
           (let ((s (fn-bpfr-step active queue i n acc quantum)))
             (and (equal (nth 3 s) (- n (min n quantum)))
                  (equal (len (nth 4 s)) (+ (len acc) (min n quantum))))))
  :hints (("Goal" :induct (fn-bpfr-step active queue i n acc quantum)
           :in-theory (e/d (fn-bpfr-state)
                           (fn-bpfw-admit fn-bpfw-advance fn-bpfw-head-cell
                            mod floor)))))

; A finished state's cells are the sweep's.
(defthm fn-bpfr-finished-state-is-the-sweep
  (implies (zp (nth 3 s))
           (equal (fn-bpfr-resume s) (reverse (nth 4 s))))
  :hints (("Goal" :in-theory (enable fn-bpfr-resume))))

(defthm fn-bpfr-step-state-shape
  (let ((s (fn-bpfr-step active queue i n acc quantum)))
    (and (true-listp s) (equal (len s) 5)))
  :hints (("Goal" :induct (fn-bpfr-step active queue i n acc quantum)
           :in-theory (disable fn-bpfw-admit fn-bpfw-advance
                               fn-bpfw-head-cell))))

(defthm fn-bpfr-step-advances
  (implies (and (not (zp n)) (not (zp quantum)))
           (< (nfix (nth 3 (fn-bpfr-step active queue i n acc quantum)))
              n))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-bpfr-step active queue i n acc quantum)
           :in-theory (disable fn-bpfw-admit fn-bpfw-advance
                               fn-bpfw-head-cell))))

; Running steps of QUANTUM to the end.
(defun fn-bpfr-run (s quantum)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix (nth 3 s))))
  (if (or (zp (nth 3 s)) (zp quantum))
      s
    (fn-bpfr-run (fn-bpfr-step (nth 0 s) (nth 1 s) (nth 2 s) (nth 3 s)
                               (nth 4 s) quantum)
                 quantum)))

(defthm fn-bpfr-run-resumes
  (equal (fn-bpfr-resume (fn-bpfr-run s quantum)) (fn-bpfr-resume s))
  :hints (("Goal" :induct (fn-bpfr-run s quantum)
           :in-theory (e/d (fn-bpfr-resume) (fn-bpfr-step)))
          ("Subgoal *1/2" :use ((:instance fn-bpfr-step-resumes
                                           (active (nth 0 s)) (queue (nth 1 s))
                                           (i (nth 2 s)) (n (nth 3 s))
                                           (acc (nth 4 s))))
           :in-theory (e/d (fn-bpfr-resume)
                           (fn-bpfr-step fn-bpfr-step-resumes)))))

; Run to completion leaves no position (for a positive quantum).
(defthm fn-bpfr-run-finishes
  (implies (posp quantum)
           (zp (nth 3 (fn-bpfr-run s quantum))))
  :hints (("Goal" :induct (fn-bpfr-run s quantum)
           :in-theory (disable fn-bpfr-step))))

; The state before the first position, and the outcome of a finished one:
; the reassembler's own sort and outcome function around the sweep.
(defun fn-bpfr-start (fs total)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpfr-state nil (fn-bpfw-sort fs) 0 total nil))

(defun fn-bpfr-finish (fs total s)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-bpfw-inputsp fs total))
      (list :invalid :bounds)
    (fn-bpfw-outcome (fn-bpfr-resume s))))

; KEYSTONE.  Steps of any positive QUANTUM, run to completion from the start,
; finish with the reassembler's outcome: the uncapped reference's.
(defthm fn-bpfr-run-is-reassemble
  (implies (posp quantum)
           (and (zp (nth 3 (fn-bpfr-run (fn-bpfr-start fs total) quantum)))
                (equal (fn-bpfr-finish
                        fs total (fn-bpfr-run (fn-bpfr-start fs total) quantum))
                       (fn-bpfw-reassemble fs total))
                (equal (fn-bpfr-finish
                        fs total (fn-bpfr-run (fn-bpfr-start fs total) quantum))
                       (fn-bpfw-spec fs total))))
  :hints (("Goal" :use ((:instance fn-bpfr-run-resumes
                                   (s (fn-bpfr-start fs total)))
                        (:instance fn-bpfr-run-finishes
                                   (s (fn-bpfr-start fs total)))
                        (:instance fn-bpfw-reassemble-is-spec))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-bpfr-finish fn-bpfr-start fn-bpfr-state
                         fn-bpfw-reassemble car-cons cdr-cons nth-0-cons
                         nth-add1 (:executable-counterpart zp)
                         (:executable-counterpart binary-+)
                         (:executable-counterpart posp)))
           :expand ((fn-bpfr-resume (list nil (fn-bpfw-sort fs) 0 total nil))))))
