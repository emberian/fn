; fn: the STORE INSTANCE of the recovery refinement and of the checkpoint
; reserve (lane recovery-refinement, 2026-10-01; specs/recovery-refinement.md
; sections 1 and 4).  Prefix fn-rrs-.
;
; books/recovery-refinement.lisp proves the composition over the image
; medium's interface (the constrained fn-rr-medium-*); this book discharges
; the interface with the store's functions, the ones
; host/store-node-host.lisp calls at open: fn-sco-capture, fn-sco-open,
; fn-cpo-open-observed and fn-sco-select (books/store-checkpoint-open.lisp),
; by functional instantiation.  The constraints are the keystones
; fn-sn-recover-from-checkpoint-equals-full-recover (PRF-083) and
; fn-sco-select-bounds-the-suffix, cited by name.
;
; The decode.  The log's records are octet lists (fn-lg-recordp); the open's
; are the events fn-srs-decode makes of them (host fn-store-decode-records,
; books/store-recover-stream.lisp), one event per record or :bad, and
; fn-srs-decode-of-append splits a concatenation.  The keystone is stated
; over the log's records with the capture taken of their decode; a decode
; that is :bad is refused by both opens (the store instance's hypothesis
; names it).
;
; STATUS (2026-10-01): WRITTEN, NOT ADMITTED.  Its include chain reaches the
; node tower, which is red at dev 896c48c16 (books/store-events-carried.lisp
; fn-evc-consumer-shape, books/store-node-traces.lisp
; fn-snt-record-directory-preserves-relation: stage 0's record-shape revert,
; design section 5), so no REPL could load it; nothing below is a claim
; until that tower is green and this book certifies.  The registry rows
; PRF-1212 and PRF-1213 say so.
;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(in-package "ACL2")
(include-book "recovery-refinement")
(include-book "checkpoint-reserve")
(include-book "store-checkpoint-open")
(include-book "store-recover-stream")
(include-book "owner-checkpoint-writer")

; -----------------------------------------------------------------------------
; 1. The medium's interface, discharged by the store's open.

; The composed open the host runs, over the store's functions.
(defun fn-rrs-open (status s ckpt configs frontier records k)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car (fn-sco-select status s (len records) k)) :checkpoint)
      (fn-sco-open ckpt configs frontier (nthcdr s records))
    (fn-cpo-open-observed configs frontier records)))

(defthm fn-rrs-open-is-the-full-open-of-the-recovered-records
  (implies (equal ckpt (fn-sco-capture configs (take s records)))
           (equal (fn-rrs-open status s ckpt configs frontier records k)
                  (fn-cpo-open-observed configs frontier records)))
  :hints (("Goal"
           :use ((:functional-instance
                  fn-rr-open-is-the-full-open-of-the-recovered-records
                  (fn-rr-medium-capture fn-sco-capture)
                  (fn-rr-medium-open fn-sco-open)
                  (fn-rr-medium-full-open fn-cpo-open-observed)
                  (fn-rr-medium-select fn-sco-select)
                  (fn-rr-open fn-rrs-open)))
           :in-theory (union-theories '(fn-rrs-open)
                                      (theory 'minimal-theory)))
          ("Subgoal 2" :use ((:instance fn-sco-select-bounds-the-suffix
                                        (sequence s) (count count))))))

; -----------------------------------------------------------------------------
; 2. THE KEYSTONE over the store: the log's records decoded, the capture of
;    the decode's prefix.

(defthm fn-rrs-recovery-refines-a-prefix-with-every-acknowledged-record
  (let* ((recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid))
         (events (fn-srs-decode recovered)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (fn-bs-crash-imagep bs image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
                  (not (equal events :bad))
                  (natp s)
                  (<= s (len (fn-lgk-committed ks)))
                  (equal ckpt (fn-sco-capture configs (take s events))))
             (and (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks)
                                               (fn-lgk-inflight ks))
                  (equal (fn-rrs-open status s ckpt configs frontier events k)
                         (fn-cpo-open-observed configs frontier events))
                  (implies (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                           (member-equal r recovered)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rr-log-crash-image-recovers-a-tree-sequence-member)
                 (:instance fn-rr-acknowledged-record-is-in-every-tree-sequence-member
                            (recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                                max next-txid))
                            (inflight (fn-lgk-inflight ks)))
                 (:instance fn-rrs-open-is-the-full-open-of-the-recovered-records
                            (records (fn-srs-decode
                                      (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                               max next-txid)))))
           :in-theory (union-theories '(fn-rr-tree-sequence-memberp)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 3. The reserve over the profile's budget and the decision.

; The reserve is two capture budgets.
(defthm fn-rrs-reserve-is-two-capture-budgets
  (equal (fn-ckr-reserve-octets (fn-bs-profile-max-history-octets profile)
                                (fn-bs-profile-max-record-octets profile))
         (* 2 (fn-ock-capture-budget profile)))
  :hints (("Goal" :in-theory (enable fn-ckr-reserve-octets fn-ock-capture-budget))))

; Under a funded reserve (the free octets the host observed cover the
; maintenance reserve and one budget, the new generation), an estimate
; within the budget is planned, never deferred :exceeds-space.
(defthm fn-rrs-funded-reserve-never-defers-for-space
  (implies (and (natp estimate) (natp budget) (natp free)
                (<= estimate budget)
                (<= (+ budget (fn-smr-reserve-octets)) free))
           (equal (fn-ockp-decide estimate budget free) (list :plan estimate)))
  :hints (("Goal" :in-theory (enable fn-ockp-decide fn-ockp-space))))
