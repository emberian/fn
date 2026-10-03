; fn: the record log route's remaining process-death cuts as model programs
; (lane log-2, 2026-09-27; the coordinator's "every process-death cut is a
; model crash point" for commit-onto-log's :log-reserve route).
;
; On a format-9 store the host's member step keeps the per-file route's cut
; names where the file route had its programs (host/native/io.lisp):
;
;   fn-lg-reserve-program   fnn-log-reserve      frontier-reserved
;   fn-lg-order-program     fnn-log-publish      record-completing (after,
;                           for a batch of one, fn-lg-append-program and
;                           fn-lg-fence-program through
;                           fnn-log-commit-open-batch)
;   fn-lg-open-program      fnn-recover-log      P-LOG-RECOVER's two cuts, then
;                           recover-replayed and the three recovery barriers
;                           (journal/, root, parent), each followed by
;                           recover-barrier
;
; tools/native_program_check.py reads each log-route arm's host steps
; (fnn-log-pwrite, fnn-log-fdatasync, the barrier thunks, the cuts) in order
; against these programs (tests/campaign/native_cuts.py LOG_ROUTE_ARMS).
; The theorems: the state at every cut is R-related to the kernel the host
; holds there, so a process death at the cut is a crash of a related state:
; books/store-log-kernel.lisp fn-lgk-crash-of-related-state-is-a-prefix
; (and, with the route's link, fn-olr-crash-reads-a-prefix-of-the-history).
(in-package "ACL2")
(include-book "store-log-route")
(include-book "store-log-programs")

(defun fn-lg-reserve-program ()
  (declare (xargs :guard t))
  (list (list :cut "frontier-reserved")))

(defun fn-lg-order-program ()
  (declare (xargs :guard t))
  (list (list :cut "record-completing")))

; The recovery barriers fence objects the log's byte model does not hold
; (journal/, the root, its parent): no step of fn-lg-step changes the segment
; or the kernel for them.  Three, not five (lane open-barriers, 2026-09-27):
; the config file's and the segment's second fence are gone.  What each
; remaining barrier is for, and that the three-barrier open is the five-
; barrier open at every cut, is books/store-log-open-barriers.lisp
; (fn-lgob-three-barrier-open-is-the-five-at-every-cut and one ground
; counterexample per omitted barrier).
(defun fn-lg-open-program ()
  (declare (xargs :guard t))
  (list (list :write-at :segment :tail)
        (list :cut "log-truncated")
        (list :fence :segment :tail)
        (list :cut "log-recovered")
        (list :cut "recover-replayed")
        (list :fence :journal)
        (list :cut "recover-barrier")
        (list :fence :root)
        (list :cut "recover-barrier")
        (list :fence :parent)
        (list :cut "recover-barrier")))

(defun fn-lg-open-suffix ()
  (declare (xargs :guard t))
  (nthcdr 4 (fn-lg-open-program)))

(defthm fn-lg-open-program-is-recover-then-the-suffix-by-definition
  (equal (fn-lg-open-program) (append (fn-lg-recover-program) (fn-lg-open-suffix))))

; A process death at frontier-reserved: the kernel caught up to the owner's
; allocation (fn-olr-consume-to), nothing written: related.
(defthm fn-lg-reserve-program-keeps-the-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lg-all-relp (fn-lg-run bs (fn-olr-consume-to ks txid) (fn-lg-reserve-program)
                                      nil ino)
                           ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgk-relp fn-olr-consume-to))))

; A process death at record-completing: the record joined the open batch
; (fn-olr-take), nothing written for it yet inside a batch quantum (a batch
; of one ran fn-lg-append-program and fn-lg-fence-program first, whose
; states are related by their own theorems): related.
(defthm fn-lg-order-program-keeps-the-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max) (fn-lg-recordp record max))
           (fn-lg-all-relp (fn-lg-run bs (cadr (fn-olr-take ks record txid count octets
                                                            bmax omax unit))
                                      (fn-lg-order-program) nil ino)
                           ino genesis max))
  :hints (("Goal" :use ((:instance fn-olr-take-preserves-relation))
           :in-theory (disable fn-lgk-relp fn-olr-take fn-olr-take-preserves-relation
                               fn-lg-recordp))))

; Every process-death cut after P-LOG-RECOVER (recover-replayed and the three
; barriers' cuts): from the relation P-LOG-RECOVER establishes
; (fn-lg-recover-program-establishes-the-relation), every state of the open's
; suffix is related.  The suffix holds no segment step since lane
; open-barriers (the segment's second fence is gone), so every state of it is
; the recovered one: the hypothesis "nothing in flight" the five-barrier
; statement carried is redundant for this suffix and was removed after this
; weakened theorem was proved.
(defthm fn-lg-open-suffix-keeps-the-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lg-all-relp (fn-lg-run bs ks (fn-lg-open-suffix) nil ino) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-lgk-relp fn-bs-durable-content)))))

; -----------------------------------------------------------------------------
; The served open at every cut (lane host-model, 2026-10-03; P10's keystone).
;
; planning/current.md's P10 used to cite fn-bs-recover-program-keeps-relation-
; at-every-cut (books/byte-store-k0-recovery.lisp), a theorem over the
; PER-FILE recovery program, which no image opens any more (every store an
; image opens is format 9: books/store-profile-open.lisp; books/byte-store-
; programs.lisp says so at P-RECOVER).  The served open is fnn-recover-log
; (host/native/io.lisp), whose program is fn-lg-open-program above.  Its six
; cuts: log-truncated and log-recovered (the recover program's; LOG_CUTS in
; tests/campaign/native_cuts.py), then recover-replayed and the three
; recover-barrier sites (RECOVERY_CUTS; the table's fifth coordinate,
; recovery-stage-unlinked, is fn-bs-recover-stage-cleanup-program's, run
; after this program, and is outside this theorem).  This is the one theorem
; over the WHOLE open program: from the recovered kernel the recover program
; completes with log-recovered related (fn-lg-recover-program-establishes-
; the-relation), and every state of the suffix -- recover-replayed and the
; three barriers, each with its cut -- is related (fn-lg-open-suffix-keeps-
; the-relation).  The owner's carried invariant at the end of the open is
; fn-lgoc-recover-installs-invariant (books/owner-log-ocl.lisp), the host's
; bridge (host/owner-host.lisp fn-owner-recover-extended).
;
; NOT covered here, by design, each named: (1) the state at log-truncated
; (the tail write before its fence), which the recover theorem does not
; relate; (2) recovery-stage-unlinked, the stage-cleanup program's cut; (3)
; fnn-log-complete-rotation (host/native/io.lisp), which a writable open runs
; BEFORE this program with no cut and no model step (Codex r72 F1; lane
; SWEEP-STORE's fix): until it has a program of its own the open's model
; starts at the recovered kernel, after it.

; A run that completed every step of STEPS (each step answered :ok), and
; the state such a run ends in.
(defun fn-lg-run-completep (bs ks steps ino)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count steps)))
  (if (consp steps)
      (mv-let (r bs1 ks1)
        (fn-lg-step bs ks (car steps) :ok ino)
        (and (equal r :ok)
             (fn-lg-run-completep bs1 ks1 (cdr steps) ino)))
    t))

(defun fn-lg-run-final (bs ks steps ino)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count steps)))
  (if (consp steps)
      (mv-let (r bs1 ks1)
        (fn-lg-step bs ks (car steps) :ok ino)
        (declare (ignore r))
        (fn-lg-run-final bs1 ks1 (cdr steps) ino))
    (cons bs ks)))

(local
 (defthm fn-lg-run-of-consp-steps-is-consp
   (implies (consp steps)
            (consp (fn-lg-run bs ks steps outcomes ino)))
   :hints (("Goal" :expand ((fn-lg-run bs ks steps outcomes ino))
            :in-theory (disable fn-lg-step)))))

; A completed run of A followed by B is A's run, then B's from A's final state.
(defthm fn-lg-run-of-append-when-complete
  (implies (fn-lg-run-completep bs ks a ino)
           (equal (fn-lg-run bs ks (append a b) nil ino)
                  (append (fn-lg-run bs ks a nil ino)
                          (fn-lg-run (car (fn-lg-run-final bs ks a ino))
                                     (cdr (fn-lg-run-final bs ks a ino))
                                     b nil ino))))
  :hints (("Goal" :induct (fn-lg-run-completep bs ks a ino)
           :in-theory (e/d (fn-lg-run fn-lg-run-completep fn-lg-run-final)
                           (fn-lg-step)))))

; ... and A's last state is that final state.
(defthm fn-lg-run-last-when-complete
  (implies (and (consp a) (fn-lg-run-completep bs ks a ino))
           (equal (car (last (fn-lg-run bs ks a nil ino)))
                  (fn-lg-run-final bs ks a ino)))
  :hints (("Goal" :induct (fn-lg-run-completep bs ks a ino)
           :in-theory (e/d (fn-lg-run fn-lg-run-completep fn-lg-run-final)
                           (fn-lg-step)))))

; A cut step answers :ok unconditionally (fn-lg-step's last arm).
(defun fn-lg-cut-stepp (step)
  (declare (xargs :guard t))
  (and (consp step) (equal (car step) :cut)))

(local
 (defthm fn-lg-step-of-a-cut-is-ok
   (implies (fn-lg-cut-stepp step)
            (equal (mv-nth 0 (fn-lg-step bs ks step outcome ino)) :ok))
   :hints (("Goal" :in-theory (enable fn-lg-step)))))

(local
 (defthm fn-lg-last-of-a-single-step
   (implies (not (consp (cdr steps)))
            (equal (last steps) steps))))

(local
 (defthm fn-lg-len-one-is-a-single-step
   (implies (and (consp steps) (equal (len steps) 1))
            (not (consp (cdr steps))))
   :hints (("Goal" :expand ((len steps) (len (cdr steps)))))))

(local
 (defthm fn-lg-step-of-a-cut-is-ok-car
   (implies (fn-lg-cut-stepp step)
            (equal (car (fn-lg-step bs ks step outcome ino)) :ok))
   :hints (("Goal" :in-theory (enable fn-lg-step)))))

; A run with as many states as steps, whose last step is a cut, completed
; every step: a refused step ends the run early, except a last one, which
; cannot be refused when it is a cut.
(defthm fn-lg-full-length-run-ending-in-a-cut-is-complete
  (implies (and (consp steps)
                (fn-lg-cut-stepp (car (last steps)))
                (equal (len (fn-lg-run bs ks steps nil ino)) (len steps)))
           (fn-lg-run-completep bs ks steps ino))
  :hints (("Goal" :induct (fn-lg-run-completep bs ks steps ino)
           :in-theory (e/d (fn-lg-run fn-lg-run-completep)
                           (fn-lg-step fn-lg-cut-stepp fn-lg-chunk-len)))))

(local
 (defthm fn-lg-nthcdr-of-the-length-of-the-prefix
   (implies (equal (len a) (nfix n))
            (equal (nthcdr n (append a b)) b))))

(local
 (defthm fn-lg-recover-program-shape
   (and (equal (len (fn-lg-recover-program)) 4)
        (consp (fn-lg-recover-program))
        (fn-lg-cut-stepp (car (last (fn-lg-recover-program)))))))

; KEYSTONE (P10).  The served open, from the recovered kernel: the recover
; program completes (its four states; log-recovered is related), and every
; state of the suffix -- recover-replayed and the three recovery barriers,
; each followed by its cut -- is related: a process death at any of those
; coordinates is a crash of a related state.
(defthm fn-lg-open-program-keeps-the-relation-at-every-cut
  (let* ((ks (fn-lg-recovered-kernel bs ino genesis max floor))
         (recover (fn-lg-run bs ks (fn-lg-recover-program) nil ino))
         (recovered (fn-lg-run-final bs ks (fn-lg-recover-program) ino))
         (run (fn-lg-run bs ks (fn-lg-open-program) nil ino)))
    (implies (and (posp (fn-bs-unit bs)) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp (fn-bs-durable-content bs ino))
                  (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)
                  (fn-frame-digestp genesis)
                  (fn-assume-log-sole-pending-writer bs ino)
                  (not (fn-bs-ops-for-ino (fn-bs-pending bs) ino)))
             (and (equal (len recover) 4)
                  (equal (car (last recover)) recovered)
                  (fn-lgk-relp (car recovered) (cdr recovered) ino genesis max)
                  (equal run
                         (append recover
                                 (fn-lg-run (car recovered) (cdr recovered)
                                            (fn-lg-open-suffix) nil ino)))
                  (fn-lg-all-relp (nthcdr 4 run) ino genesis max))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lg-recover-program-establishes-the-relation)
                 (:instance fn-lg-full-length-run-ending-in-a-cut-is-complete
                            (ks (fn-lg-recovered-kernel bs ino genesis max floor))
                            (steps (fn-lg-recover-program)))
                 (:instance fn-lg-run-of-append-when-complete
                            (ks (fn-lg-recovered-kernel bs ino genesis max floor))
                            (a (fn-lg-recover-program)) (b (fn-lg-open-suffix)))
                 (:instance fn-lg-run-last-when-complete
                            (ks (fn-lg-recovered-kernel bs ino genesis max floor))
                            (a (fn-lg-recover-program)))
                 (:instance fn-lg-open-suffix-keeps-the-relation
                            (bs (car (fn-lg-run-final bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                      (fn-lg-recover-program) ino)))
                            (ks (cdr (fn-lg-run-final bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                      (fn-lg-recover-program) ino)))))
           :in-theory (e/d (fn-lg-open-program-is-recover-then-the-suffix-by-definition)
                           (fn-lg-run fn-lg-run-completep fn-lg-run-final fn-lg-recovered-kernel
                            fn-lgk-relp fn-lg-all-relp fn-lg-recover-program fn-lg-open-suffix
                            fn-lg-open-program fn-lg-run-of-append-when-complete
                            fn-lg-run-last-when-complete
                            fn-lg-full-length-run-ending-in-a-cut-is-complete
                            fn-lg-recover-program-establishes-the-relation
                            fn-lg-open-suffix-keeps-the-relation last nthcdr append len
                            (:e fn-lg-open-program) (:e fn-lg-recover-program)
                            (:e fn-lg-open-suffix))))))
