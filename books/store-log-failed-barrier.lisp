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

; The no-flight case recovers exactly the old committed records. Any
; selector list still writes only the appended units; admissibility is
; needed for physical-state well-formedness, not this prefix conclusion.
; These local proofs discharge both redundant premises before strengthening.
(encapsulate ()
(local (include-book "arithmetic/top" :dir :system))
(local (defthm owb-no-flight-image
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks))))
    (equal (fn-bs-durable-content
             (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))) ino)
           (fn-bs-durable-content bs ino)))
  :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-bs-fsync-file fn-bs-durable-content) (fn-lgk-content-okp))))))

(local (defthm owb-related-scan
  (implies (fn-lgk-relp bs ks ino genesis max)
    (equal (car (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
           (fn-lgk-committed ks)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lg-scan-of-complete-append
                    (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                    (x (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                    (prev genesis) (unit (fn-bs-unit bs))))
           :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                           (fn-lg-scan fn-lg-scan-last fn-lgk-committed fn-lgk-frontier
                            fn-lgk-last fn-bs-take fn-lg-log mod))))))

(local (defthm owb-nthcdr-len
 (implies (true-listp x) (equal (nthcdr (len x) x) nil))
 :hints (("Goal" :induct (len x)))))

(local (defthm owb-no-flight-conclusion
 (implies (and (fn-lgk-relp bs ks ino genesis max)
               (not (consp (fn-lgk-inflight ks))))
  (let* ((c (fn-lgc-fence-failed (fn-lgc-of ks)))
         (bs1 (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))))
         (ks2 (fn-lgk-recover (fn-bs-durable-content bs1 ino) genesis (fn-bs-unit bs) max next-txid)))
    (and (equal (fn-lgc-phase c) :fault)
         (equal (fn-lgc-acked c) (fn-lgk-acked ks))
         (equal (fn-lgk-committed ks2)
                (append (fn-lgk-committed ks)
                        (nthcdr (fn-lgc-count c) (fn-lgk-committed ks2))))
         (fn-lg-prefixp (nthcdr (fn-lgc-count c) (fn-lgk-committed ks2))
                        (fn-lgc-inflight c)))))
 :hints (("Goal"
          :use (owb-no-flight-image owb-related-scan)
          :in-theory
          (e/d (fn-lgc-of fn-lgc-fence-failed fn-lgc-make fn-lgc-phase fn-lgc-acked
                fn-lgc-count fn-lgc-inflight fn-lgk-recover fn-lgk-relp fn-lgk-content-okp)
               (fn-bs-fsync-file fn-lg-scan fn-lg-scan-last fn-lgk-inflight
                fn-lgk-last fn-lgk-frontier fn-lg-log mod
                fn-lgc-fence-failed-refines owb-no-flight-image owb-related-scan))))))

(local (defthm owb-select-one
 (implies (equal ops (list (list :write ino f w)))
  (equal (fn-bs-crash-select (fn-bs-ops-for-ino ops ino) choices unit)
         (fn-bs-tear-write (list :write ino f w) (car choices) 0 unit)))
 :hints (("Goal" :in-theory (e/d (fn-bs-ops-for-ino fn-bs-crash-select) (fn-bs-tear-write))))))

(local (defthm owb-any-choice-image
 (implies (and (posp (fn-bs-unit s)) (natp k) ino (true-listp d) (true-listp w)
               (equal (len d) (* k (fn-bs-unit s)))
               (equal (fn-bs-durable-content s ino) (append d z))
               (equal (fn-bs-pending s) (list (list :write ino (len d) w))))
  (equal (fn-bs-durable-content
           (mv-nth 1 (fn-bs-fsync-file s ino (cons :eio choices))) ino)
         (append d (fn-lg-apply-to z (fn-lg-pieces ino 0 w (car choices) (fn-bs-unit s))))))
 :hints (("Goal" :do-not-induct t :do-not '(eliminate-destructors generalize)
          :in-theory (e/d (fn-bs-fsync-file fn-bs-durable-content fn-bs-apply-ops-inodes-are-apply-writes)
                         (fn-lg-tear-write-is-pieces fn-lg-apply-to-past-prefix
                          fn-lg-pieces fn-lg-pieces-shift fn-lg-apply-to fn-bs-tear-write fn-bs-crash-select fn-bs-ops-for-ino))
          :use ((:instance owb-select-one (ops (fn-bs-pending s)) (f (len d)) (unit (fn-bs-unit s)))
                (:instance fn-lg-tear-write-is-pieces (unit (fn-bs-unit s)) (i 0) (sels (car choices)))
                (:instance fn-lg-apply-to-past-prefix (s 0) (unit (fn-bs-unit s)) (sels (car choices))))))))

(local (defthm owb-any-choice-verdict
 (let* ((image (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))))
        (content (fn-bs-durable-content image ino)))
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (consp (fn-lgk-inflight ks))
                (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) content)
                                        (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
   (fn-lg-crash-verdictp (fn-lg-scan content genesis (fn-bs-unit bs) max)
                        (fn-lgk-committed ks) (fn-lgk-frontier ks)
                        (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)
          :use (fn-lgk-relp-gives-the-tear-hypotheses
                (:instance fn-lg-log-true-listp (records (fn-lgk-inflight ks))
                  (prev (fn-lgk-last ks)) (unit (fn-bs-unit bs)))
                (:instance owb-any-choice-image
                  (s bs) (k (floor (fn-lgk-frontier ks) (fn-bs-unit bs)))
                  (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                  (z (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                  (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
                (:instance fn-lgc-tail-verdict
                  (unit (fn-bs-unit bs))
                  (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                  (z (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                  (c (fn-bs-durable-content (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))) ino))
                  (sels (car choices)) (committed (fn-lgk-committed ks))
                  (batch (fn-lgk-inflight ks)) (last (fn-lgk-last ks)))
                (:instance fn-lg-no-forgery-under-a-crypto-trailer
                  (x (nthcdr (fn-lgk-frontier ks)
                     (fn-bs-durable-content (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))) ino)))
                  (batch (fn-lgk-inflight ks)) (prev (fn-lgk-last ks)) (unit (fn-bs-unit bs))))))))

(defthm fn-lgc-failed-barrier-recovers-a-prefix
  (let* ((c (fn-lgc-fence-failed (fn-lgc-of ks)))
         (bs1 (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))))
         (ks2 (fn-lgk-recover (fn-bs-durable-content bs1 ino) genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
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
           :cases ((consp (fn-lgk-inflight ks)))
           :use (owb-any-choice-verdict owb-no-flight-conclusion)
           :in-theory (e/d (fn-lg-crash-verdictp fn-lgk-recover
                            fn-lgc-fence-failed fn-lgc-of fn-lgc-make fn-lgc-count fn-lgc-last
                            fn-lgc-frontier fn-lgc-inflight fn-lgc-acked fn-lgc-phase)
                           (fn-lgc-fence-failed-refines fn-lgk-relp fn-lg-scan
                            fn-bs-fsync-file fn-lg-platform-tears-p fn-lg-prefixp
                            owb-no-flight-conclusion)))))

)
