; fn: the STORE INSTANCE of the recovery refinement and of the checkpoint
; reserve (lane recovery-refinement, 2026-10-01; specs/recovery-refinement.md
; sections 1 and 4).  Prefix fn-rrs-.
;
; books/recovery-refinement.lisp proves the composition over the image
; medium's interface (the constrained fn-rr-medium-*); this book is to
; discharge the interface with the store's functions, the ones
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
; STATUS (2026-10-07): ADMITTED (lane s-pck-2; a Makefile root).  The
; interface's three constraints are discharged by the store's open:
; fn-sn-recover-from-checkpoint-equals-full-recover (PRF-083), the select
; bound (fn-rrs-select-bounds, from fn-sco-select-bounds-the-suffix), and the
; holding constraint fn-rrs-full-open-holds-its-records, from
; fn-cpo-open-success-exact-image (the opened files carry exactly the
; observed journal).  The functional instance and the keystone below are
; proved.  What stays MODEL-LEVEL is stated under THE HOST'S OPEN.
;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
;
; THE HOST'S OPEN (the Codex review of 2d1b10ed7, F1): host/native/io.lisp
; fnn-recover-log calls fn-rii-sco-extend-open
; (books/replay-identity-index.lisp) or fn-sfi-extend-open
; (books/store-finalize-incremental.lisp), not fn-sco-open directly; the
; instance below is stated over fn-sco-open, and a named equation of the
; composed fn-rrs-open to the host-called open is part of the pending
; subject, so the claim is MODEL-LEVEL until both land.
(in-package "ACL2")
(include-book "recovery-refinement")
(include-book "checkpoint-reserve")
(include-book "store-checkpoint-open")
(include-book "store-recover-stream")
(include-book "owner-checkpoint-writer")
(include-book "store-node-files-selector")

; -----------------------------------------------------------------------------
; 1. The medium's interface, to be discharged by the store's open.

; The composed open this instance MODELS over the store's functions (not
; what the host calls: fnn-recover-log reaches fn-rii-sco-extend-open /
; fn-sfi-extend-open; the equation to them is the pending subject).
(defun fn-rrs-open (status s ckpt configs frontier records k)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car (fn-sco-select status s (len records) k)) :checkpoint)
      (fn-sco-open ckpt configs frontier (nthcdr s records))
    (fn-cpo-open-observed configs frontier records)))

; A successful open (fn-sn-open-okp) holds a record when the opened Store's
; files carry it among their records (fn-sf-records of fn-sn-files: the
; open builds them from the replayed events, fn-sf-make :recovering).  The
; interface's third constraint over these two is fn-rrs-full-open-holds-its-
; records below: a successful fn-cpo-open-observed of
; EVENTS holds every member of EVENTS.
(defun fn-rrs-open-okp (result)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-open-okp result))
(defun fn-rrs-holds (result r)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal r (fn-sf-records (fn-sn-files (fn-sn-open-state result)))))

; The interface's third constraint over the store's open: a successful
; fn-cpo-open-observed of EVENTS holds every member of EVENTS.  The opened
; Store's files carry exactly the observed journal
; (fn-cpo-open-success-exact-image, books/config-observed.lisp).
(defthm fn-rrs-full-open-holds-its-records
  (implies (and (member-equal r records)
                (fn-rrs-open-okp (fn-cpo-open-observed configs frontier records)))
           (fn-rrs-holds (fn-cpo-open-observed configs frontier records) r))
  :hints (("Goal"
           :use ((:instance fn-cpo-open-success-exact-image (events records)))
           :in-theory (e/d (fn-rrs-open-okp fn-rrs-holds)
                           (fn-cpo-open-observed fn-sn-open-okp)))))

; The interface's select constraint, as a rewrite rule over the store's
; selection (fn-sco-select-bounds-the-suffix, books/store-checkpoint-open.lisp,
; is rule-classes nil).
(defthm fn-rrs-select-bounds
  (implies (equal (car (fn-sco-select status s count k)) :checkpoint)
           (and (natp s) (natp count) (<= s count)))
  :hints (("Goal" :use ((:instance fn-sco-select-bounds-the-suffix
                                   (sequence s))))))

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
                  (fn-rr-medium-open-okp fn-rrs-open-okp)
                  (fn-rr-medium-holds fn-rrs-holds)
                  (fn-rr-open fn-rrs-open)))
           :in-theory (union-theories '(fn-rrs-open fn-rrs-full-open-holds-its-records
                                        fn-sn-recover-from-checkpoint-equals-full-recover
                                        fn-rrs-select-bounds)
                                      (theory 'minimal-theory)))))

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
                           (member-equal r recovered))
                  ; a successful open holds every decoded event (the instance's
                  ; holding obligation, through the composed open); that the
                  ; acknowledged record's own event is among EVENTS is the
                  ; decode's position theorem, part of the pending subject
                  (implies (and (fn-rrs-open-okp
                                 (fn-rrs-open status s ckpt configs frontier events k))
                                (member-equal e events))
                           (fn-rrs-holds (fn-rrs-open status s ckpt configs frontier events k)
                                         e)))))
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
                                                               max next-txid))))
                 (:instance fn-rrs-full-open-holds-its-records
                            (records (fn-srs-decode
                                      (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                               max next-txid)))
                            (r e)))
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
