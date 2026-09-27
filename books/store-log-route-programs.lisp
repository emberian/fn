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
;                           recover-replayed and the five recovery barriers
;                           (config, segment, journal/, root, parent), each
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

; The barriers other than the segment's fence objects the log's byte model
; does not hold (the config file, journal/, the root, its parent): no step
; of fn-lg-step changes the segment or the kernel for them.
(defun fn-lg-open-program ()
  (declare (xargs :guard t))
  (list (list :write-at :segment :tail)
        (list :cut "log-truncated")
        (list :fence :segment :tail)
        (list :cut "log-recovered")
        (list :cut "recover-replayed")
        (list :fence :config)
        (list :cut "recover-barrier")
        (list :fence :segment :tail)
        (list :cut "recover-barrier")
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

(local
 (defthm fn-lgrp-relp-committed-true-listp
   (implies (fn-lgk-relp bs ks ino genesis max) (true-listp (nth 1 ks)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                                   (fn-lg-scan fn-lg-scan-last fn-lg-log fn-bs-durable-content))))))

; Every process-death cut after P-LOG-RECOVER (recover-replayed and the five
; barriers' cuts): from the relation P-LOG-RECOVER establishes
; (fn-lg-recover-program-establishes-the-relation; nothing in flight), every
; state of the open's suffix is related.
(defthm fn-lg-open-suffix-keeps-the-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max) (not (fn-lgk-inflight ks)))
           (fn-lg-all-relp (fn-lg-run bs ks (fn-lg-open-suffix) nil ino) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lg-fence-program-keeps-the-relation)
                 (:instance fn-lgrp-relp-committed-true-listp)
                 (:instance fn-lgk-relp-when-fields-agree
                            (bs (fn-bs-fence-file bs ino)) (ks (fn-lgk-fence ks (fn-bs-unit bs)))
                            (k2 ks))
                 (:instance fn-lgk-relp-forward))
           :in-theory (e/d (fn-bs-fsync-file fn-lgk-fence)
                           (fn-lgk-relp fn-bs-fence-file fn-bs-durable-content
                            fn-lg-fence-program-keeps-the-relation fn-lgk-relp-forward
                            fn-lgrp-relp-committed-true-listp)))))
