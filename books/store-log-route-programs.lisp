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
;   fn-lg-open-program      fnn-recover-log      after P-LOG-RECOVER-COPY
;                           (books/store-log-recover-copy.lisp fn-lgrc-program,
;                           its four cuts): recover-replayed and the three
;                           recovery barriers (journal/, root, parent), each
;                           followed by recover-barrier
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
  (list (list :cut "recover-replayed")
        (list :fence :journal)
        (list :cut "recover-barrier")
        (list :fence :root)
        (list :cut "recover-barrier")
        (list :fence :parent)
        (list :cut "recover-barrier")))

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

; KEYSTONE (P10's log-model half).  Every process-death cut of the open
; after its copy (recover-replayed and the three barriers' cuts): from a
; related state every state of the program is related.  The program holds no
; segment step, so every state of it is the one it starts from.  The copy's
; half (P-LOG-RECOVER-COPY reaches a related state; every cut of it keeps the
; acknowledged prefix in every crash image) and the composition are
; books/store-log-recover-copy.lisp fn-lgrc-open-keeps-the-relation-at-every-cut.
(defthm fn-lg-open-program-keeps-the-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lg-all-relp (fn-lg-run bs ks (fn-lg-open-program) nil ino) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-lgk-relp fn-bs-durable-content)))))
