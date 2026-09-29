;; fn: the Store's derived event index, carried from the host's open across
;; every owner transition the host installs (PRF-144; lane
;; signed-history-index-2, 2026-09-26).
;
; The maintained relation is fn-ceis-indexedp
; (books/history-columns-relation.lisp (the retired index's invariants were deleted)): the Store's derived
; event index is the index of its committed history, in every phase.  The
; BP receiver's Message-ID lookups read that index
; (books/bp-native-app-fast.lisp, fn-bpaj-indexed-records-are-the-walk) and
; so does the consumer poll (books/consumer-owner-index-invariants.lisp).
; It is never evaluated on a served path.  This book:
;
;   ESTABLISHES it at the host's open.  host/owner-host.lisp
;   fn-owner-recover-extended installs fn-ock-recover-extended of the
;   extended checkpoint (books/owner-checkpoint-open.lisp), on both paths
;   (fn-owner-recover, fn-owner-recover-from-checkpoint,
;   fn-owner-recover-from-store-open); that owner is fn-ock-install over
;   fn-cpo-open-observed (fn-owner-recover-from-checkpoint-equals-full-recover),
;   whose opened Store carries fn-cei-build of the history it read
;   (fn-osi-cpo-open-observed-is-indexed).  The store-only model reopen
;   fn-sn-open-observed (fn-own-reopen) and fn-sn-initial establish it too.
;
;   PRESERVES it across every owner the host installs: fn-osi-host-step
;   names each of them with the ACL2 function host/owner-host.lisp calls
;   (fn-owner-step's fn-ocfg-step, fn-owner-io's fn-rcon-ocfg-io, the carried
;   prepares, completion, finish and outcome, the publication, the profile
;   and posting configuration, the feed table, the connection events, the
;   carried read, the exposure open and the clock).  Only the kernel's
;   (:store (:crash ...)) event breaks it (the crash image's index is empty
;   while its history is not), and the host never issues it: a crash is the
;   death of the process, whose next owner is the open above.  The model's
;   own restart (:reopen) re-establishes it (fn-osi-own-reopen-is-indexed).
;
; KEYSTONE fn-osi-live-owner-store-is-indexed: the Store of every owner the
; host reaches from its open by the installed transitions is indexed.  That
; is the Store host/native/bp-app.lisp fnn-bpapp-accept-locked binds
; (fnn-bpapp-bind-owner-store -> host/bp-native-app-host.lisp
; fn-owner-app-bind-receipt-store: (fn-own-store (fn-ocfg-owner oc)) of the
; installed owner) before every fn-bprj-request-action ->
; fn-bpaj-dispatch-fast, so PRF-132's keystones (restated below over that
; owner) carry no index premise.

(in-package "ACL2")
(include-book "owner-offer-indexed")
(include-book "owner-checkpoint-open")
(include-book "records-concrete-owner")
(include-book "owner-served-bound")
(include-book "public-exposure")
(include-book "owner-open-carried")
(include-book "store-node-resolution")
(include-book "store-files-traces")
(include-book "bp-signed-binding")
(include-book "post-identity-index")

; The owner field laws this book reads (withdrawn at owner-invariants'
; export with its vocabulary).
(local (in-theory (enable fn-own-refresh-keeps-fields
                          fn-own-connection-events-keep-store-bound-and-ledger)))

; -----------------------------------------------------------------------------
; The Store transitions the owner reaches that the invariants book does not
; include: the resolution events and the carried identity prepare.  Each
; keeps the history and the index.







; The store-only kernel crash is the one Store transition that breaks the
; relation; the host never issues it (see the head of this book).
(defun fn-osi-host-store-eventp (event)
  (declare (xargs :guard t))
  (not (and (consp event) (equal (car event) :crash))))



; -----------------------------------------------------------------------------
; Establishment



(defthm fn-osi-observed-seed-is-replaying
  (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-seed groups capacity
                                                        frontier records)))
         :replaying)
  :hints (("Goal" :in-theory (e/d (fn-sn-observed-seed)
                                  (fn-node-initial-state)))))



(defthm fn-osi-own-start-store
  (equal (fn-own-store (fn-own-start store max-conns)) store)
  :hints (("Goal" :in-theory (e/d (fn-own-start fn-own-refresh-keeps-fields
                                   fn-own-store-of-fn-own-make)
                                  (fn-own-refresh fn-own-store fn-own-make
                                   fn-own-view-make-visible fn-midx-build
                                   fn-gidx-build fn-own-prefix-archive
                                   fn-ctl-visible-state)))))

; The owner the host installs at open, on either path, or :fault.


(defthm fn-osi-ock-install-requires-an-ok-open
  (implies (not (equal (fn-ock-install replayed opened max-conns) :fault))
           (equal (fn-sn-open-kind opened) :ok))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ock-install)
                                  (fn-own-start fn-own-configure
                                   fn-oag-post-config)))))

; The open the host runs (host/owner-host.lisp fn-owner-recover-extended,
; on both paths: the extended checkpoint of a prefix of the history, over
; the records after it), and the owner the host holds after the installed
; transitions EVS.  Abbreviations for the statements below.
(defun fn-osi-open (configs prefix suffix frontier max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ock-recover-extended
   (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
   configs frontier max-conns))

; A refused open is :fault, whose owner has the empty Store, whose empty
; index is the index of its empty history.


; KEYSTONE (establishment): the owner host/owner-host.lisp
; fn-owner-recover-extended installs, on either path, has an indexed Store.
; No hypothesis.


; -----------------------------------------------------------------------------
; The carried article prepare's Store step keeps the history and the index.



; -----------------------------------------------------------------------------
; The raw owner.  Only the :store, :complete and :reopen events of
; fn-own-step move the Store (as books/owner-invariants.lisp's local
; fn-own-step-store-of-other-events says); every other event keeps it.

; Owner transitions the configured owner reaches outside fn-own-step.
(defthm fn-osi-own-keeps-store-outside-step
  (and (equal (fn-own-store (cdr (fn-own-advance-result o id))) (fn-own-store o))
       (equal (fn-own-store (fn-own-reader-context o id cfg)) (fn-own-store o))
       (equal (fn-own-store (cdr (fn-own-open-peer o peer cfg acfg)))
              (fn-own-store o))
       (equal (fn-own-store (cdr (fn-own-fault o id))) (fn-own-store o))
       (equal (fn-own-store (fn-own-with-feeds o feeds)) (fn-own-store o))
       (equal (fn-own-store (fn-own-configure o config)) (fn-own-store o))
       (equal (fn-own-store (cdr (fn-own-transit-outcome o id kind reason word)))
              (fn-own-store o))
       (equal (fn-own-store (cdr (fn-acar-own-outcome o id word)))
              (fn-own-store o)))
  :hints (("Goal" :in-theory (e/d (fn-own-advance-result fn-own-reader-context
                                   fn-own-open-peer fn-own-fault
                                   fn-own-with-feeds fn-own-configure
                                   fn-own-transit-outcome fn-acar-own-outcome
                                   fn-acar-own-advance-result
                                   fn-own-invariants-vocabulary
                                   fn-own-set-conns fn-own-enqueue)
                                  (fn-served-step fn-served-dispatch
                                   fn-served-post-outcome fn-served-open
                                   fn-own-conn-boundedp fn-own-outcome-completion
                                   fn-own-find-conn-id fn-own-refresh)))))

(defthm fn-osi-own-step-store-of-other-events
  (implies (not (member-equal (car event) '(:store :complete :reopen)))
           (equal (fn-own-store (fn-own-step o event fn-arena)) (fn-own-store o)))
  :hints (("Goal" :in-theory (e/d (fn-own-step fn-own-invariants-vocabulary
                                   fn-own-feed-reply fn-own-tick fn-own-tick-peer
                                   fn-own-feed-connect fn-own-feed-lost
                                   fn-own-feed-recover fn-own-feeds-reconfigure
                                   fn-own-with-feeds fn-own-control-submit
                                   fn-own-operator-submit fn-own-bp-transit-submit
                                   fn-own-control-outcome fn-own-bp-transit-outcome
                                   fn-own-enqueue fn-own-set-conns
                                   fn-own-transit-outcome)
                                  (fn-served-step fn-served-dispatch
                                   fn-served-post-outcome fn-served-open
                                   fn-own-conn-boundedp fn-own-outcome-completion
                                   fn-own-find-conn-id)))))





; The model's restart re-establishes the relation whatever the old Store.


; The owner events the host issues: every one but the kernel crash.
(defun fn-osi-host-own-eventp (event)
  (declare (xargs :guard t))
  (not (and (consp event) (equal (car event) :store)
            (consp (cdr event))
            (not (fn-osi-host-store-eventp (cadr event))))))

(defthm fn-osi-own-step-of-store-changing-events
  (and (implies (equal (car event) :store)
                (equal (fn-own-step o event fn-arena) (fn-own-store-step o (cadr event))))
       (implies (equal (car event) :complete)
                (equal (fn-own-step o event fn-arena) (fn-own-complete o)))
       (implies (equal (car event) :reopen)
                (equal (fn-own-step o event fn-arena)
                       (fn-own-reopen o (cadr event) (caddr event)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-own-step))))





; -----------------------------------------------------------------------------
; The configured owner.

; The configured read arms take the owner from the full read (fn-own-read-full
; and fn-own-read-step-full, with their REPINNED flag: NNT-042); fn-own-read
; and fn-own-read-step are that result's projections, and the store facts
; over them lift to the full reads.
(defthm fn-osi-own-read-full-keeps-store
  (equal (fn-own-store (car (cdr (fn-own-read-full o id octets fn-arena))))
         (fn-own-store o))
  :hints (("Goal" :use ((:instance fn-own-connection-events-keep-store-bound-and-ledger))
           :in-theory (e/d (fn-own-read)
                           (fn-own-read-full fn-own-read-step-full
                            fn-own-connection-events-keep-store-bound-and-ledger)))))

(defthm fn-osi-own-read-step-full-keeps-store
  (equal (fn-own-store (car (cdr (fn-own-read-step-full o id event fn-arena))))
         (fn-own-store o))
  :hints (("Goal" :use ((:instance fn-own-connection-events-keep-store-bound-and-ledger))
           :in-theory (e/d (fn-own-read-step)
                           (fn-own-read-full fn-own-read-step-full
                            fn-own-connection-events-keep-store-bound-and-ledger)))))



(defthm fn-osi-ocfg-with-owner-store
  (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-with-owner oc owner)))
         (fn-own-store owner))
  :hints (("Goal" :in-theory (enable fn-ocfg-with-owner))))





;; PRF-191: the prepare fn-owner-prepare-buffer installs since
;; books/post-identity-index.lisp.  It keeps the index with no hypothesis on
;; the view: whichever node its duplicate test yields, the Store it returns
;; is the one it was given or that Store with the record staged.




;; The view trie (fn-scar-view-indexedp, books/owner-offer-indexed.lisp) is
;; kept alike: only the refresh changes the view.
(defthm fn-osi-pidx-prepare-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp
            (fn-ocfg-owner (fn-pidx-sbud-prepare oc record budget))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-pidx-sbud-prepare
                                   fn-pidx-opc-prepare fn-pidx-opc-owner-prepare
                                   fn-ocfg-with-owner)
                                  (fn-midx-correspondencep fn-own-refresh
                                   fn-pidx-spc-prepare
                                   fn-sbud-admitp fn-sbud-used fn-sbud-count)))))









(defthm fn-osi-ocfg-open-keeps-store
  (and (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocfg-open-peer oc peer acfg))))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocfg-read-step oc id event fn-arena))))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocfg-fault oc id))))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-observe oc obs)))
              (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open fn-ocfg-open-peer
                                   fn-ocfg-read-step fn-ocfg-fault
                                   fn-ocfg-observe fn-ocfg-with-owner
                                   fn-ocfg-with-read-owner)
                                  (fn-own-open fn-own-open-peer
                                   fn-own-reader-context fn-own-read-step
                                   fn-own-read-step-full
                                   fn-own-fault fn-own-observe)))))

(defthm fn-osi-exp-at-one
  (equal (fn-exp-at 1 (cons a (cons b c))) b)
  :hints (("Goal" :expand ((fn-exp-at 1 (cons a (cons b c)))
                           (fn-exp-at 0 (cons b c))))))

(defthm fn-osi-exp-open-keeps-store
  (equal (fn-own-store (fn-ocfg-owner
                        (fn-exp-open-ocfg
                         (fn-exp-open oc st limits auth peer address now))))
         (fn-own-store (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-exp-open fn-exp-open-ocfg fn-osi-exp-at-one
                                fn-osi-ocfg-open-keeps-store)
                              (theory 'minimal-theory)))))

(defthm fn-osi-ocar-exp-open-keeps-store
  (equal (fn-own-store (fn-ocfg-owner
                        (fn-exp-open-ocfg
                         (fn-ocar-exp-open oc st limits auth peer address now))))
         (fn-own-store (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-ocar-exp-open fn-exp-open-ocfg fn-osi-exp-at-one
                                fn-osi-ocfg-open-keeps-store
                                fn-ocar-ocfg-open-keeps-store)
                              (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The host's owner transitions, one arm per owner host/owner-host.lisp
; installs (fn-owner-install-ocfg or fn-owner-replace-core), with the ACL2
; function it installs:
;
;   :step            fn-owner-step, fn-owner-refuse-reservation, -begin, ...  fn-ocfg-step
;   :io              fn-owner-io                              fn-rcon-ocfg-io
;   :prepare         fn-owner-prepare                         fn-pcar-sbud-prepare
;   :prepare-buffer  fn-owner-prepare-buffer (PRF-191)        fn-pidx-sbud-prepare
;   :prepare-identity fn-owner-prepare-identity               fn-ccar-ocfg-prepare-identity
;   :complete        fn-owner-finish                          fn-ccar-ocfg-complete
;   :finish          fn-owner-finish-submission               fn-ccar-own-finish
;                    (installs its cdr, fn-ccar-own-complete: the word alone reads the arena)
;   :publish         fn-owner-reconfigure-complete            fn-ocl-publish
;   :configure       fn-owner-posting-configure               fn-own-configure
;   :profile         fn-owner-install-profile                 fn-osb-install
;   :feeds           fn-owner-feed-install-port-result        fn-own-with-feeds
;   :transit-outcome fn-owner-transit-outcome                 fn-own-transit-outcome
;   :outcome         the served POST outcome                  fn-acar-own-outcome
;   :open-peer       fn-owner-open-peer                       fn-ocfg-open-peer
;   :read-step       fn-owner-tls-established                 fn-ocfg-read-step
;   :open            fn-owner-open                            fn-ocar-ocfg-open
;   :exposure-open   fn-owner-exposure-open                   fn-ocar-exp-open
;
; The two open arms are the carried opens (books/owner-open-carried.lisp),
; equal to fn-ocfg-open and fn-exp-open under fn-ocl-relation.
;   :read            fn-owner-chunk-span-at                   fn-scar-ocfg-read-tls-prefix
;   :fault           fn-owner-fault                           fn-ocfg-fault
;   :observe         fn-owner-observe                         fn-ocfg-observe
;
; The :step arm admits every owner event but the kernel crash
; (fn-osi-host-own-eventp), a superset of the events the host sends.
(defun fn-osi-host-step (oc ev fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((a (cadr ev)) (b (caddr ev)) (c (cadddr ev)))
    (case (car ev)
      (:step (if (fn-osi-host-own-eventp a) (fn-ocfg-step oc a fn-arena) oc))
      (:io (fn-rcon-ocfg-io oc a b))
      (:prepare (fn-pcar-sbud-prepare oc a b))
      (:prepare-buffer (fn-pidx-sbud-prepare oc a b))
      (:prepare-identity (fn-ccar-ocfg-prepare-identity oc a))
      (:complete (fn-ccar-ocfg-complete oc))
      (:finish (if (fn-ocfg-staged oc) oc
                 (fn-ocfg-with-owner
                  oc (fn-ccar-own-complete (fn-ocfg-owner oc)))))
      (:publish (mv-let (verdict next) (fn-ocl-publish oc a b)
                  (declare (ignore verdict))
                  next))
      (:configure (fn-ocfg-with-owner oc (fn-own-configure (fn-ocfg-owner oc) a)))
      (:profile (mv-let (verdict next) (fn-osb-install (fn-ocfg-owner oc) a)
                  (declare (ignore verdict))
                  (fn-ocfg-with-owner oc next)))
      (:feeds (fn-ocfg-with-owner oc (fn-own-with-feeds (fn-ocfg-owner oc) a)))
      (:transit-outcome
       (fn-ocfg-with-owner
        oc (cdr (fn-own-transit-outcome (fn-ocfg-owner oc) a b c
                                        (car (cddddr ev))))))
      (:outcome (fn-ocfg-with-owner
                 oc (cdr (fn-acar-own-outcome (fn-ocfg-owner oc) a b))))
      (:open-peer (cdr (fn-ocfg-open-peer oc a b)))
      (:read-step (cdr (fn-ocfg-read-step oc a b fn-arena)))
      (:open (cdr (fn-ocar-ocfg-open oc a)))
      (:exposure-open
       (fn-exp-open-ocfg (fn-ocar-exp-open oc a b c (car (cddddr ev))
                                      (cadr (cddddr ev))
                                      (caddr (cddddr ev)))))
      (:read (fn-own-tls-result-owner (fn-scar-ocfg-read-tls-prefix oc a b fn-arena)))
      (:fault (cdr (fn-ocfg-fault oc a)))
      (:observe (fn-ocfg-observe oc a))
      (otherwise oc))))

(defun fn-osi-host-run (oc evs fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp evs)
      (fn-osi-host-run (fn-osi-host-step oc (car evs) fn-arena) (cdr evs) fn-arena)
    oc))

(defthm fn-osi-osb-install-keeps-store
  (equal (fn-own-store (mv-nth 1 (fn-osb-install o profile))) (fn-own-store o))
  :hints (("Goal" :in-theory (e/d (fn-osb-install)
                                  (fn-bs-profile-admittedp fn-osb-config
                                   fn-own-configure)))))





(defun fn-osi-live-owner (configs prefix suffix frontier max-conns evs fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-osi-host-run (fn-osi-open configs prefix suffix frontier max-conns) evs fn-arena))

(defun fn-osi-live-store (configs prefix suffix frontier max-conns evs fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-own-store (fn-ocfg-owner (fn-osi-live-owner configs prefix suffix
                                                  frontier max-conns evs fn-arena))))

; KEYSTONE (PRF-144): the Store of every owner the host reaches from its
; open, by any sequence of the owners it installs, is indexed.  No
; hypothesis.  This is the Store fnn-bpapp-accept-locked binds before each
; dispatch.


; -----------------------------------------------------------------------------
; PRF-132, restated over the Store the host dispatches over.  host/native/
; bp-app.lisp fnn-bpapp-accept-locked binds the installed owner's Store
; (fn-owner-app-bind-receipt-store) and asks fn-bprj-request-action ->
; fn-bpaj-dispatch-fast before every step; that Store is
; (fn-osi-live-store ...) of the open and the transitions the host has
; installed since.  The index premise of books/bp-signed-binding.lisp's
; refinement lemmas is discharged by fn-osi-live-owner-store-is-indexed; no
; conclusion changes.

; KEYSTONE: once the live Store's history holds an article record (plain or
; signed; after the records flip, the held row it retains) with the
; Message-ID the dispatcher reads, the dispatcher never answers (:submit).


; KEYSTONE: whatever the dispatcher binds over the live Store is the wire
; form, read through the arena, of the held row an event of that Store's own
; history retains as its article, for the request's Message-ID, accepted by
; the receiver's Store check; a composite row whose article record decodes
; binds its verdict to that article.


; The fast/checked equalities over the live Store: the Store record check,
; the direct and transit Message-ID lookups (the direct one the receipt
; hosts call, PRF-220) and the dispatcher they compose into are the
; checked walks over the history.


;; PRF-220: the premise of the Store check is carried, never evaluated on
;; a request.  host/owner-host.lisp fn-owner-store is
;; (fn-own-store (fn-ocfg-owner (f-get-global 'fn-owner state))), the configured
;; owner the host installs; fn-ocl-relation holds of it from open and every
;; transition keeps it (books/config-owner-live.lisp,
;; fn-ocl-open-, -close-, -observe-, -read-preserves-historical-relation and
;; the advance/complete twins), and its Store conjunct fn-cst-relation
;; conjoins fn-sn-statep.
(defthm fn-bpaj-ocl-relation-carries-sn-statep
  (implies (fn-ocl-relation oc)
           (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation fn-cst-relation)
                                  (fn-sn-statep)))))

;; KEYSTONE (PRF-220) for host/bp-native-app-host.lisp fn-owner-app-submit,
;; fn-owner-app-record and host/bp-receipt-journal-host.lisp fn-bprj-apply,
;; fn-bprj-preflight, fn-bprj-request-action: over the configured owner's
;; Store, under its carried relation and index, the Store check the host runs
;; (no whole-node or whole-store recognizer, no history walk) is the
;; receiver's checked Store predicate.








(in-theory (disable fn-osi-open fn-osi-live-owner fn-osi-live-store
                    fn-osi-host-step fn-osi-host-run))
