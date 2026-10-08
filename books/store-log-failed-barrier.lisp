; fn: after a failed log barrier the store recovers the committed records and
; a PREFIX of the batch in flight, stated of the kernel the host holds
; (PRF-255; the host-path restatement of owner-batch's T7, whose layer no
; host line calls).
;
; The host's failed barrier (host/native/io.lisp fnn-log-fence, fnn-log-fence-
; sync and the segment-extension paths) sets its concrete kernel to
; fn-lgc-fence-failed of it: faulted, the batch in flight and the count of
; acknowledged records kept.  Every member in flight is answered uncertain.
; What the next open then reads is the store the failed fsync left, which is a
; crash image of the environment's selection (books/owner-batch.lisp
; fn-owb-failed-fence-is-the-crash-image and -image-admissible): the kernel
; recovered from it holds the committed records followed by a prefix of the
; batch in flight (fn-owb-recovered-kernel-after-a-failed-fence, from
; books/store-log-crash.lisp's batch-crash prefix lemma under the platform
; tear hypothesis fn-lg-platform-tears-p, A-CRYPTO-TRAILER).  So an uncertain
; member is recovered whole and in order or not at all; nothing the batch did
; not hold appears, and no acknowledged record is lost.
;
; The keystone's subject is fn-lgc-fence-failed, the function the host calls;
; the host's kernel is the abstraction of a logical kernel at every point of
; its run (fn-lgc-run-refines-the-kernel).
(in-package "ACL2")
(include-book "store-log-kernel-concrete")
(include-book "owner-batch")

(defthm fn-lgc-failed-barrier-recovers-a-prefix
  (let* ((c (fn-lgc-fence-failed (fn-lgc-of ks)))
         (bs1 (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))))
         (ks2 (fn-lgk-recover (fn-bs-durable-content bs1 ino) genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (consp (fn-lgc-inflight (fn-lgc-of ks)))
                  (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
                  (fn-lg-platform-tears-p (nthcdr (fn-lgc-frontier c) (fn-bs-durable-content bs1 ino))
                                          (fn-lgc-inflight c) (fn-lgc-last c) (fn-bs-unit bs)))
             (and (equal (fn-lgc-phase c) :fault)
                  (equal (fn-lgc-acked c) (fn-lgk-acked ks))
                  (equal (fn-lgk-committed ks2)
                         (append (fn-lgk-committed ks)
                                 (nthcdr (fn-lgc-count c) (fn-lgk-committed ks2))))
                  (fn-lg-prefixp (nthcdr (fn-lgc-count c) (fn-lgk-committed ks2))
                                 (fn-lgc-inflight c)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-owb-recovered-kernel-after-a-failed-fence))
           :in-theory (e/d (fn-lgc-fence-failed fn-lgc-of fn-lgc-make fn-lgc-count fn-lgc-last
                            fn-lgc-frontier fn-lgc-inflight fn-lgc-acked fn-lgc-phase)
                           (fn-owb-recovered-kernel-after-a-failed-fence fn-lgk-recover
                            fn-lgk-relp fn-bs-crash-choicesp fn-bs-fsync-file
                            fn-lg-platform-tears-p fn-lg-prefixp)))))
