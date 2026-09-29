; fn: the owner transitions the host calls answer their own outcome (lane
; host-decisions-2, 2026-09-27; packet A of
; planning/evidence/host-decisions-2026-09-27.md).
;
; Before this book, ten host lines (host/owner-host.lisp) decided the answer
; word of an owner transition by comparing the owner before and after the
; ACL2 call: an unchanged Store was :refused, a changed one :prepared (the
; article, retention, identity, consumer and topic prepares); an unchanged
; owner core was :refused, a changed one :begun or :declared; and the
; reservation refusal and the known abort answered from a before/after
; comparison plus two phase reads.  The word is a fact about the transition
; ACL2 computed, so ACL2 answers it: each entry below returns (mv WORD NEXT),
; NEXT the configured owner the host installs (the same value the host
; installed before) and WORD the transition's own outcome:
;
;   * a Store prepare is :prepared exactly when it staged a record: the
;     reservation (phase :reserved) now holds a staged candidate (phase
;     :record-staged), `fn-pout-stagedp';
;   * the reservation refusal is :refused exactly when the Store's own gate
;     `fn-sn-refuse-reservation-enabledp' holds, the known abort :aborted
;     exactly when `fn-sn-known-abort-enabledp' holds; otherwise :fault;
;   * :begin and :declare-group answer from their gates
;     (`fn-pout-begin-admitsp', `fn-pout-declare-group-admitsp'), each the
;     test of the owner transition, named by an -unfolds theorem.
;
; The keystones say each word equals the comparison the host made (so the
; host's behaviour is unchanged) with no hypothesis, except :begin, whose
; comparison could not see a begin at the connection identifier NIL (the
; host's identifiers are naturals).  A prepare is pure: no outcome here is
; uncertain.
;
; This book shares the prefix `fn-pout-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "owner-identity-served")

; -----------------------------------------------------------------------------
; The Store's staging outcome.

(defun fn-pout-stagedp (before after)
  (declare (xargs :guard t))
  (and (equal (fn-sf-phase (fn-sn-files before)) :reserved)
       (equal (fn-sf-phase (fn-sn-files after)) :record-staged)))

(defthm fn-pout-stagedp-is-a-change
  (implies (fn-pout-stagedp before after)
           (not (equal after before)))
  :rule-classes nil)

; Every Store prepare the owner entries run returns its Store or stages.
(defthm fn-pout-sn-prepares-stage-or-keep
  (and (or (equal (fn-sn-prepare-retention s e) s)
           (fn-pout-stagedp s (fn-sn-prepare-retention s e)))
       (or (equal (fn-sn-prepare-consumer s e) s)
           (fn-pout-stagedp s (fn-sn-prepare-consumer s e)))
       (or (equal (fn-sn-prepare-topic s e) s)
           (fn-pout-stagedp s (fn-sn-prepare-topic s e)))
       (or (equal (fn-ccar-sn-prepare-identity s e) s)
           (fn-pout-stagedp s (fn-ccar-sn-prepare-identity s e)))
       (or (equal (fn-prc-spc-prepare s e view carry) s)
           (fn-pout-stagedp s (fn-prc-spc-prepare s e view carry))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-pout-stagedp fn-sn-prepare-retention fn-sn-prepare-consumer
                               fn-sn-prepare-topic fn-ccar-sn-prepare-identity
                               fn-prc-spc-prepare fn-cstp-sn-update-fields))))

; The Store of the configured owner (fn-sbud-oc-store) after each owner prepare
; is the owner's Store or the Store prepare over it.
(defthm fn-pout-store-of-psrv-prepare
  (or (equal (fn-sbud-oc-store (fn-psrv-prepare oc record budget carry))
             (fn-sbud-oc-store oc))
      (equal (fn-sbud-oc-store (fn-psrv-prepare oc record budget carry))
             (fn-prc-spc-prepare (fn-sbud-oc-store oc) record
                                 (fn-own-view (fn-ocfg-owner oc)) carry)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-psrv-prepare fn-prc-sbud-prepare fn-prc-opc-prepare
                               fn-prc-opc-owner-prepare fn-sbud-oc-store fn-ocfg-with-owner
                               fn-ocfg-owner-of-fn-ocfg-make fn-own-refresh-keeps-fields
                               fn-own-store-of-fn-own-make))))

(defthm fn-pout-store-of-oiis-prepare-identity
  (let ((s (fn-sbud-oc-store oc)))
    (or (equal (fn-sbud-oc-store (fn-oiis-prepare-identity oc w h)) s)
        (equal (fn-sbud-oc-store (fn-oiis-prepare-identity oc w h))
               (fn-ccar-sn-prepare-identity
                s (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) h)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-oiis-prepare-identity-unfolds fn-oii-ocfg-prepare-identity
                               fn-psrv-ccar-ocfg-prepare-identity-is-owner-with-store
                               fn-lgoc-store-of-owner-with-store fn-sbud-oc-store))))

(defthm fn-pout-store-of-psrv-prepare-topic
  (or (equal (fn-sbud-oc-store (fn-psrv-prepare-topic oc e)) (fn-sbud-oc-store oc))
      (equal (fn-sbud-oc-store (fn-psrv-prepare-topic oc e))
             (fn-sn-prepare-topic (fn-sbud-oc-store oc) e)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-psrv-prepare-topic-cases fn-lgoc-store-of-owner-with-store
                               fn-sbud-oc-store))))

(defthm fn-pout-store-of-store-step
  (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :store ev) fn-arena))
         (fn-snrt-step (fn-sbud-oc-store oc) ev))
  :hints (("Goal" :in-theory '(fn-psrv-store-step-is-owner-with-store
                               fn-lgoc-store-of-owner-with-store fn-sbud-oc-store))))

; -----------------------------------------------------------------------------
; THE ENTRIES THE HOST CALLS.  Each returns (mv WORD NEXT).

; host/owner-host.lisp fn-owner-prepare and fn-owner-prepare-buffer: the
; article prepare (prepare-served's fn-psrv-prepare) and its word: :prepared
; when it staged the row, else fn-psrv-refusal-kind (:refused, or
; :unaffordable at the budget).
(defun fn-pout-prepare-article (oc record budget carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-pidx-view-okp (fn-own-view (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))))
  (let ((next (fn-psrv-prepare oc record budget carry)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          (fn-psrv-refusal-kind oc record budget))
        next)))

; The identity prepare's refusal word over the row interned at handle H:
; :article-numbers-exhausted when the row's groups are served but their
; numbers would pass RFC 3977 section 6's bound, else :refused
; (books/owner-prepare-served.lisp fn-psrv-identity-refusal-kind).
(defun fn-pout-identity-refusal-kind (oc w h)
  ; The store's keyring is read: the owner's store is a store-node state
  ; (fn-pout-prepare-identity's guard, carried by the host).
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc)) (natp h))
                  :verify-guards nil))
  (let ((s (fn-sbud-oc-store oc)))
    (fn-psrv-identity-refusal-kind
     oc (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) h))))
(verify-guards fn-pout-identity-refusal-kind
  :hints (("Goal" :in-theory (enable fn-sn-statep))))

(defthm fn-pout-identity-refusal-kind-is-a-refusal
  (and (not (equal (fn-pout-identity-refusal-kind oc w h) :prepared))
       (member-equal (fn-pout-identity-refusal-kind oc w h)
                     '(:refused :article-numbers-exhausted)))
  :hints (("Goal" :in-theory '(fn-pout-identity-refusal-kind fn-psrv-identity-refusal-kind
                               member-equal (:executable-counterpart equal)))))

(in-theory (disable fn-pout-identity-refusal-kind))

; host/owner-host.lisp fn-owner-prepare-identity: the identity prepare
; (fn-oiis-prepare-identity over the row interned at handle H).
(defun fn-pout-prepare-identity (oc w h)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc)) (natp h))
                  :verify-guards nil))
  (let ((next (fn-oiis-prepare-identity oc w h)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          (fn-pout-identity-refusal-kind oc w h))
        next)))

; host/owner-host.lisp fn-owner-prepare-topic.
;
; The six callers of fn-ocfg-step below are guard-verified (lane depth-debt-6,
; row K2): each sends a literal event, so fn-ocfg-eventp opens to t, and the
; store state their guards state is fn-ocfg-step's.  fn-pout-prepare-identity
; waits on fn-oiis-prepare-identity (books/owner-identity-served),
; still :ideal.
(defun fn-pout-prepare-topic (oc e)
  (declare (xargs :guard (fn-sn-statep (fn-sbud-oc-store oc))))
  (let ((next (fn-psrv-prepare-topic oc e)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          :refused)
        next)))

; host/owner-host.lisp fn-owner-prepare-retention and
; fn-owner-prepare-consumer: the configured owner's (:store (:prepare-retention
; E)) and (:store (:prepare-consumer E)).
(defun fn-pout-prepare-retention (oc e fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil))
  (let ((next (fn-ocfg-step oc (list :store (list :prepare-retention e)) fn-arena)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          :refused)
        next)))
(verify-guards fn-pout-prepare-retention)

(defun fn-pout-prepare-consumer (oc e fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil))
  (let ((next (fn-ocfg-step oc (list :store (list :prepare-consumer e)) fn-arena)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          :refused)
        next)))
(verify-guards fn-pout-prepare-consumer)

; host/owner-host.lisp fn-owner-refuse-reservation: the configured owner's
; (:store (:refuse-reservation TXID)) at the reservation's txid, :refused
; exactly when the Store's gate holds.
(defun fn-pout-refuse-reservation (oc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil))
  (let ((txid (1- (fn-sf-frontier (fn-sn-files (fn-sbud-oc-store oc))))))
    (mv (if (fn-sn-refuse-reservation-enabledp (fn-sbud-oc-store oc) txid)
            :refused
          :fault)
        (fn-ocfg-step oc (list :store (list :refuse-reservation txid)) fn-arena))))
(verify-guards fn-pout-refuse-reservation)

; host/owner-host.lisp fn-owner-known-abort: (:store (:known-abort)),
; :aborted exactly when the Store's gate holds.
(defun fn-pout-known-abort (oc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil))
  (mv (if (fn-sn-known-abort-enabledp (fn-sbud-oc-store oc)) :aborted :fault)
      (fn-ocfg-step oc (list :store (list :known-abort)) fn-arena)))
(verify-guards fn-pout-known-abort)

; host/owner-host.lisp fn-owner-begin: (:begin ID), whose test is this gate
; (fn-pout-begin-unfolds).
(defun fn-pout-begin-admitsp (oc id)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (and (not (fn-ocfg-staged oc))
         (null (fn-own-pending o))
         (fn-own-find-conn id (fn-own-conns o))
         (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready))))

(defun fn-pout-begin (oc id fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil))
  (mv (if (fn-pout-begin-admitsp oc id) :begun :refused)
      (fn-ocfg-step oc (list :begin id) fn-arena)))
(verify-guards fn-pout-begin)

; host/owner-host.lisp fn-owner-declare-group: (:declare-group NAME), whose
; test is this gate (fn-pout-declare-group-unfolds).
(defun fn-pout-declare-group-admitsp (oc name)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (and (stringp name)
         (fn-clock-observationp (fn-own-clock o))
         (not (member-equal name (fn-own-replay-facts (fn-own-facts o)))))))

(defun fn-pout-declare-group (oc name fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil))
  (mv (if (fn-pout-declare-group-admitsp oc name) :declared :refused)
      (fn-ocfg-step oc (list :declare-group name) fn-arena)))
(verify-guards fn-pout-declare-group)

; -----------------------------------------------------------------------------
; KEYSTONES: each word is the answer the host's comparison gave (behaviour
; unchanged), and NEXT is the owner the host installed.

(defthm fn-pout-prepare-article-answers-the-store-change
  (let ((r (fn-pout-prepare-article oc record budget carry)))
    (and (equal (mv-nth 1 r) (fn-psrv-prepare oc record budget carry))
         (equal (mv-nth 0 r)
                (if (equal (fn-sbud-oc-store (mv-nth 1 r)) (fn-sbud-oc-store oc))
                    (fn-psrv-refusal-kind oc record budget)
                  :prepared))))
  :hints (("Goal"
           :use (fn-pout-store-of-psrv-prepare
                 (:instance fn-pout-sn-prepares-stage-or-keep
                            (s (fn-sbud-oc-store oc)) (e record)
                            (view (fn-own-view (fn-ocfg-owner oc))))
                 (:instance fn-pout-stagedp-is-a-change
                            (before (fn-sbud-oc-store oc))
                            (after (fn-sbud-oc-store (fn-psrv-prepare oc record budget carry)))))
           :in-theory '(fn-pout-prepare-article mv-nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))

(defthm fn-pout-prepare-identity-answers-the-store-change
  (let ((r (fn-pout-prepare-identity oc w h)))
    (and (equal (mv-nth 1 r) (fn-oiis-prepare-identity oc w h))
         (equal (mv-nth 0 r)
                (if (equal (fn-sbud-oc-store (mv-nth 1 r)) (fn-sbud-oc-store oc))
                    (fn-pout-identity-refusal-kind oc w h)
                  :prepared))))
  :hints (("Goal"
           :use (fn-pout-store-of-oiis-prepare-identity
                 (:instance fn-pout-sn-prepares-stage-or-keep
                            (s (fn-sbud-oc-store oc))
                            (e (fn-oii-identity-row w (fn-sn-keyring (fn-sbud-oc-store oc))
                                                    (fn-sn-keyring-generation (fn-sbud-oc-store oc))
                                                    h)))
                 (:instance fn-pout-stagedp-is-a-change
                            (before (fn-sbud-oc-store oc))
                            (after (fn-sbud-oc-store (fn-oiis-prepare-identity oc w h)))))
           :in-theory '(fn-pout-prepare-identity mv-nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))

(defthm fn-pout-prepare-topic-answers-the-store-change
  (let ((r (fn-pout-prepare-topic oc e)))
    (and (equal (mv-nth 1 r) (fn-psrv-prepare-topic oc e))
         (equal (mv-nth 0 r)
                (if (equal (fn-sbud-oc-store (mv-nth 1 r)) (fn-sbud-oc-store oc))
                    :refused
                  :prepared))))
  :hints (("Goal"
           :use (fn-pout-store-of-psrv-prepare-topic
                 (:instance fn-pout-sn-prepares-stage-or-keep (s (fn-sbud-oc-store oc)))
                 (:instance fn-pout-stagedp-is-a-change
                            (before (fn-sbud-oc-store oc))
                            (after (fn-sbud-oc-store (fn-psrv-prepare-topic oc e)))))
           :in-theory '(fn-pout-prepare-topic mv-nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))

(defthm fn-pout-prepare-retention-answers-the-store-change
  (let ((r (fn-pout-prepare-retention oc e fn-arena)))
    (and (equal (mv-nth 1 r)
                (fn-ocfg-step oc (list :store (list :prepare-retention e)) fn-arena))
         (equal (mv-nth 0 r)
                (if (equal (fn-sbud-oc-store (mv-nth 1 r)) (fn-sbud-oc-store oc))
                    :refused
                  :prepared))))
  :hints (("Goal"
           :use ((:instance fn-pout-sn-prepares-stage-or-keep (s (fn-sbud-oc-store oc)))
                 (:instance fn-pout-stagedp-is-a-change
                            (before (fn-sbud-oc-store oc))
                            (after (fn-sn-prepare-retention (fn-sbud-oc-store oc) e))))
           :in-theory '(fn-pout-prepare-retention fn-pout-store-of-store-step fn-snrt-step
                        mv-nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))

(defthm fn-pout-prepare-consumer-answers-the-store-change
  (let ((r (fn-pout-prepare-consumer oc e fn-arena)))
    (and (equal (mv-nth 1 r)
                (fn-ocfg-step oc (list :store (list :prepare-consumer e)) fn-arena))
         (equal (mv-nth 0 r)
                (if (equal (fn-sbud-oc-store (mv-nth 1 r)) (fn-sbud-oc-store oc))
                    :refused
                  :prepared))))
  :hints (("Goal"
           :use ((:instance fn-pout-sn-prepares-stage-or-keep (s (fn-sbud-oc-store oc)))
                 (:instance fn-pout-stagedp-is-a-change
                            (before (fn-sbud-oc-store oc))
                            (after (fn-sn-prepare-consumer (fn-sbud-oc-store oc) e))))
           :in-theory '(fn-pout-prepare-consumer fn-pout-store-of-store-step fn-snrt-step
                        mv-nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))
(defthm fn-pout-refuse-reservation-answers-the-host-test
  (let* ((s (fn-sbud-oc-store oc))
         (r (fn-pout-refuse-reservation oc fn-arena))
         (next (fn-sbud-oc-store (mv-nth 1 r))))
    (and (equal (mv-nth 1 r)
                (fn-ocfg-step oc (list :store (list :refuse-reservation
                                                    (1- (fn-sf-frontier (fn-sn-files s)))))
                              fn-arena))
         (equal (mv-nth 0 r)
                (if (and (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                         (not (equal next s))
                         (equal (fn-sf-phase (fn-sn-files next)) :ready))
                    :refused
                  :fault))))
  :hints (("Goal"
           :use ((:instance fn-sn-refuse-reservation-disabled-is-no-op
                            (s (fn-sbud-oc-store oc))
                            (txid (1- (fn-sf-frontier (fn-sn-files (fn-sbud-oc-store oc))))))
                 (:instance fn-sn-refuse-reservation-is-exact-advance
                            (s (fn-sbud-oc-store oc))
                            (txid (1- (fn-sf-frontier (fn-sn-files (fn-sbud-oc-store oc)))))))
           :in-theory '(fn-pout-refuse-reservation fn-pout-store-of-store-step fn-snrt-step
                        fn-sn-refuse-reservation-enabledp
                        mv-nth car-cons cdr-cons (:executable-counterpart zp)
                        (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))

(defthm fn-pout-known-abort-reaches-ready
  (implies (fn-sn-known-abort-enabledp s)
           (equal (fn-sf-phase (fn-sn-files (fn-sn-known-abort s))) :ready))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sn-known-abort-files-reaches-ready (files (fn-sn-files s)))
                 (:instance fn-cstp-sn-statep-files (st s)))
           :in-theory '(fn-sn-known-abort fn-sn-known-abort-enabledp fn-cstp-sn-update-fields))))

(defthm fn-pout-known-abort-answers-the-host-test
  (let* ((s (fn-sbud-oc-store oc))
         (r (fn-pout-known-abort oc fn-arena))
         (next (fn-sbud-oc-store (mv-nth 1 r))))
    (and (equal (mv-nth 1 r) (fn-ocfg-step oc (list :store (list :known-abort)) fn-arena))
         (equal (mv-nth 0 r)
                (if (and (member-equal (fn-sf-phase (fn-sn-files s))
                                       '(:record-staged :record-data-durable))
                         (not (equal next s))
                         (equal (fn-sf-phase (fn-sn-files next)) :ready))
                    :aborted
                  :fault))))
  :hints (("Goal"
           :use ((:instance fn-sn-known-abort-disabled-is-no-op (s (fn-sbud-oc-store oc)))
                 (:instance fn-pout-known-abort-reaches-ready (s (fn-sbud-oc-store oc))))
           :in-theory '(fn-pout-known-abort fn-pout-store-of-store-step fn-snrt-step
                        fn-sn-known-abort-enabledp member-equal
                        mv-nth car-cons cdr-cons (:executable-counterpart zp)
                        (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))

(defthm fn-pout-begin-unfolds
  (equal (fn-ocfg-owner (fn-ocfg-step oc (list :begin id) fn-arena))
         (let ((o (fn-ocfg-owner oc)))
           (if (fn-pout-begin-admitsp oc id)
               (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                            (fn-own-next-id o) (fn-own-max-conns o) id
                            (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                            (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                            (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))
             o)))
  :hints (("Goal" :in-theory '(fn-ocfg-step fn-ocfg-pass fn-own-step fn-own-begin
                               fn-pout-begin-admitsp fn-ocfg-with-owner
                               fn-ocfg-owner-of-fn-ocfg-make car-cons cdr-cons
                               (:executable-counterpart equal)))))

(defthm fn-pout-begin-answers-the-host-test
  (implies id
           (let ((r (fn-pout-begin oc id fn-arena)))
             (and (equal (mv-nth 1 r) (fn-ocfg-step oc (list :begin id) fn-arena))
                  (equal (mv-nth 0 r)
                         (if (equal (fn-ocfg-owner (mv-nth 1 r)) (fn-ocfg-owner oc))
                             :refused
                           :begun)))))
  :hints (("Goal"
           :in-theory '(fn-pout-begin fn-pout-begin-unfolds fn-pout-begin-admitsp
                        fn-own-pending-of-fn-own-make
                        mv-nth car-cons cdr-cons (:executable-counterpart zp)
                        (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))

(defthm fn-pout-declare-group-unfolds
  (equal (fn-ocfg-owner (fn-ocfg-step oc (list :declare-group name) fn-arena))
         (let ((o (fn-ocfg-owner oc)))
           (if (fn-pout-declare-group-admitsp oc name)
               (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                            (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                            (fn-own-ledger-field o) (fn-own-clock o)
                            (fn-ag-append (fn-own-facts o)
                                          (list (fn-own-group-fact-make name (fn-own-clock o))))
                            (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                            (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))
             o)))
  :hints (("Goal" :in-theory '(fn-ocfg-step fn-ocfg-pass fn-own-step fn-own-declare-group
                               fn-pout-declare-group-admitsp fn-ocfg-with-owner
                               fn-ocfg-owner-of-fn-ocfg-make car-cons cdr-cons
                               (:executable-counterpart equal)))))

(local
 (defthm fn-pout-append-singleton-grows
   (not (equal (append x (list y)) x))))

(local
 (defthm fn-pout-grown-facts-are-another-owner
   (not (equal (fn-own-make store view conns next-id max-conns pending ledger clock
                            (append (fn-own-facts o) (list g))
                            config queue inflight feeds node-secret refused)
               o))
   :hints (("Goal" :use ((:instance fn-own-facts-of-fn-own-make
                                    (facts (append (fn-own-facts o) (list g)))))
            :in-theory '(fn-pout-append-singleton-grows)))))

(defthm fn-pout-declare-group-answers-the-host-test
  (let ((r (fn-pout-declare-group oc name fn-arena)))
    (and (equal (mv-nth 1 r) (fn-ocfg-step oc (list :declare-group name) fn-arena))
         (equal (mv-nth 0 r)
                (if (equal (fn-ocfg-owner (mv-nth 1 r)) (fn-ocfg-owner oc))
                    :refused
                  :declared))))
  :hints (("Goal"
           :in-theory '(fn-pout-declare-group fn-pout-declare-group-unfolds
                        fn-ag-append fn-pout-grown-facts-are-another-owner
                        mv-nth car-cons cdr-cons (:executable-counterpart zp)
                        (:executable-counterpart binary-+) (:executable-counterpart unary--)
                        (:executable-counterpart equal)))))

; The article entry's NEXT is the owner's budgeted prepare wherever the row's
; groups are served (the bridge of planning/current-view.json P9: the host
; calls fn-pout-prepare-article; prepare-served's
; fn-psrv-prepare-is-sbud-prepare-when-served equates fn-psrv-prepare, whose
; value NEXT is, with fn-sbud-prepare under the carried indexes).
(defthm fn-pout-prepare-article-is-sbud-prepare-when-served
  (implies (and (fn-psrv-event-servedp (fn-ocfg-config oc) record)
                (fn-psrv-event-numberedp oc record)
                (fn-prc-carryp carry)
                (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc)))
                (fn-scar-view-indexedp (fn-ocfg-owner oc)))
           (equal (mv-nth 1 (fn-pout-prepare-article oc record budget carry))
                  (fn-sbud-prepare oc record budget)))
  :hints (("Goal" :use (fn-pout-prepare-article-answers-the-store-change
                        fn-psrv-prepare-is-sbud-prepare-when-served)
           :in-theory nil)))
