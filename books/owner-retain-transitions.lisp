; Actual host-called retention carry transitions.
; The owner installer is one global put (W9's obligation view is parked:
; books/owner-obligation-state.lisp). Raw owner dispatch stays disabled.
(in-package "ACL2")
(include-book "owner-state-accessors")
(include-book "owner-retain-state")
(include-book "owner-obligation-state")
(include-book "identity-retain-carried")
(include-book "owner-connection-state")
(include-book "owner-reader-view")
(include-book "owner-readers-transitions")

(defthm fn-owner-retain-carry-of-install-ocfg
  (equal (fn-owner-retain-carry (fn-owner-install-ocfg oc state))
         (fn-owner-retain-carry state))
  :hints (("Goal" :in-theory (e/d (fn-owner-install-ocfg)
                                  (put-global)))))

; Entry guards read the owner after the carry global changes.  These
; exact frame/availability facts avoid reopening the whole state writer.
(defthm fn-owner-ocfg-of-retain-carry-put
  (equal (fn-owner-ocfg (fn-owner-retain-carry-put carry state))
         (fn-owner-ocfg state))
  :hints (("Goal" :in-theory (enable fn-owner-ocfg
                                    fn-owner-retain-carry-put))))

(defthm fn-owner-bound-of-retain-carry-put
  (equal (boundp-global 'fn-owner (fn-owner-retain-carry-put carry state))
         (boundp-global 'fn-owner state))
  :hints (("Goal" :in-theory (enable fn-owner-retain-carry-put))))

(defthm fn-owner-bound-of-install-ocfg
  (boundp-global 'fn-owner (fn-owner-install-ocfg oc state))
  :hints (("Goal" :in-theory (enable fn-owner-install-ocfg))))

(defthm fn-owner-ocfg-of-install-ocfg
  (equal (fn-owner-ocfg (fn-owner-install-ocfg oc state)) oc)
  :hints (("Goal" :in-theory (enable fn-owner-ocfg))))

(defthm fn-owner-ocfg-of-other-global-put
  (implies (not (equal key 'fn-owner))
           (equal (fn-owner-ocfg (f-put-global key value state))
                  (fn-owner-ocfg state)))
  :hints (("Goal" :in-theory (enable fn-owner-ocfg))))

(defthm fn-owner-bound-of-other-global-put
  (implies (not (equal key 'fn-owner))
           (equal (boundp-global 'fn-owner (f-put-global key value state))
                  (boundp-global 'fn-owner state))))

; Proof-only carried entry-state invariant. Never called by native serving
; code or used as an executable guard: it names the maintained relation.
(defun fn-captured-view-follows-files (view files)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-own-view-shapep view)
       (natp (fn-own-view-version view))
       (natp (fn-own-view-frontier view))
       (natp (fn-sf-frontier files))
       (<= (fn-own-view-version view) (len (fn-sf-records files)))
       (<= (fn-own-view-frontier view) (fn-sf-frontier files))))
(defun fn-captured-views-follow-files (views files)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp views)
      (and (fn-captured-view-follows-files (car views) files)
           (fn-captured-views-follow-files (cdr views) files))
    (null views)))
; Bounds plus the existing complete configured-owner relation at each captured view.
(defun fn-captured-view-follows-ocfg (view oc)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-captured-view-follows-files view (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
       (fn-ocl-relation (fn-ocfg-with-view oc view))))
(defun fn-captured-views-follow-ocfg (views oc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp views)
      (and (fn-captured-view-follows-ocfg (car views) oc)
           (fn-captured-views-follow-ocfg (cdr views) oc))
    (null views)))
(defun fn-owner-captured-view-follows-store (state)
  (declare (xargs :stobjs state :guard t :verify-guards nil))
  (and (boundp-global 'fn-owner state)
       (fn-captured-views-follow-ocfg
        (fn-owner-reader-views state)
        (fn-owner-ocfg state))))

(defun fn-owner-retain-statep (state)
  (declare (xargs :stobjs state :guard t :verify-guards nil))
  (and (boundp-global 'fn-owner state)
       (fn-lgoc-invariantp (fn-owner-ocfg state))
       (fn-prc-carryp (fn-owner-retain-carry state))
       (fn-owner-captured-view-follows-store state)))

; Captured reader frames: globals, install, carry refresh, and identity prepare.
(defthm fn-owner-reader-views-of-other-global-put
  (implies (not (equal key 'fn-owner-reader-views))
           (equal (fn-owner-reader-views (f-put-global key value state))
                  (fn-owner-reader-views state)))
  :hints (("Goal" :in-theory '(fn-owner-reader-views
                               fn-ost-readers-of-other-global-put))))
(defthm fn-owner-reader-views-of-install-ocfg
  (equal (fn-owner-reader-views (fn-owner-install-ocfg oc state))
         (fn-owner-reader-views state))
  :hints (("Goal" :in-theory '(fn-owner-install-ocfg
                               fn-owner-reader-views-of-other-global-put))))
(defthm fn-owner-reader-views-of-retain-carry-put
  (equal (fn-owner-reader-views (fn-owner-retain-carry-put carry state))
         (fn-owner-reader-views state))
  :hints (("Goal" :in-theory '(fn-owner-retain-carry-put
                               fn-owner-reader-views-of-other-global-put))))
(defthm fn-owner-captured-view-of-other-global-put
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-reader-views)))
           (equal (fn-owner-captured-view-follows-store
                   (f-put-global key value state))
                  (fn-owner-captured-view-follows-store state)))
  :hints (("Goal" :in-theory '(fn-owner-captured-view-follows-store
                               fn-owner-reader-views-of-other-global-put
                               fn-owner-ocfg-of-other-global-put
                               fn-owner-bound-of-other-global-put))))
(defthm fn-owner-captured-view-of-retain-carry-put
  (equal (fn-owner-captured-view-follows-store
          (fn-owner-retain-carry-put carry state))
         (fn-owner-captured-view-follows-store state))
  :hints (("Goal" :in-theory '(fn-owner-retain-carry-put
                               fn-owner-captured-view-of-other-global-put))))
(defthm fn-owner-captured-view-of-install-ocfg
  (equal (fn-owner-captured-view-follows-store
          (fn-owner-install-ocfg oc state))
         (fn-captured-views-follow-ocfg (fn-owner-reader-views state) oc))
  :hints (("Goal" :in-theory '(fn-owner-captured-view-follows-store
                               fn-owner-reader-views-of-install-ocfg
                               fn-owner-ocfg-of-install-ocfg
                               fn-owner-bound-of-install-ocfg))))
(local
 (defthm fn-k1-true-list-fix-of-true-listp
  (implies (true-listp xs) (equal (true-list-fix xs) xs))
  :hints (("Goal" :induct (true-listp xs)
            :in-theory (enable true-listp true-list-fix)))))
(defthm fn-k1-captured-view-transport-same-history
  (implies
   (and (fn-lgoc-invariantp oc0)
        (fn-lgoc-invariantp oc)
        (fn-captured-view-follows-ocfg view oc0)
        (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
               (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0)))))
        (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
               (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0))))
        (equal (fn-ocfg-config oc) (fn-ocfg-config oc0))
        (equal (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
               (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))))
   (fn-captured-view-follows-ocfg view oc))
  :hints
  (("Goal"
    :use ((:instance fn-ocl-relation-of-a-view-captured-before-appends
           (oc0 (fn-ocfg-with-view oc0 view)) (extra nil))
          (:instance fn-lgoc-invariant-statep (oc oc0))
          (:instance fn-cstp-sn-statep-files
           (st (fn-own-store (fn-ocfg-owner oc0))))
          (:instance fn-sf-state-records-are-true-list
           (s (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))))
    :in-theory '(fn-captured-view-follows-ocfg fn-captured-view-follows-files
                 fn-lgoc-invariantp fn-ocfg-with-view-keeps-the-rest
                 fn-lgt-append-nil fn-k1-true-list-fix-of-true-listp))))
(local
 (defthm fn-k1-ccar-identity-keeps-frontier
  (equal (fn-sf-frontier (fn-sn-files (fn-ccar-sn-prepare-identity s e)))
         (fn-sf-frontier (fn-sn-files s)))
  :hints (("Goal"
    :use ((:instance fn-psrv-pcar-stage-record-staged
            (files (fn-sn-files s))))
    :in-theory '(fn-ccar-sn-prepare-identity fn-cstp-sn-update-fields)))))
(local
 (defthm fn-k1-config-of-with-owner
  (equal (fn-ocfg-config (fn-ocfg-with-owner oc owner)) (fn-ocfg-config oc))
  :hints (("Goal" :in-theory '(fn-ocfg-with-owner fn-ocfg-config-of-fn-ocfg-make)))))
(defthm fn-k1-oiis-keeps-durable-context
  (let* ((next (fn-oiis-prepare-identity oc w h))
         (old (fn-own-store (fn-ocfg-owner oc)))
         (new (fn-own-store (fn-ocfg-owner next))))
    (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
         (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
         (equal (fn-sn-config-history new) (fn-sn-config-history old))
         (equal (fn-ocfg-config next) (fn-ocfg-config oc))))
  :hints (("Goal" :in-theory
    '(fn-oiis-prepare-identity fn-psrv-prepare-identity
      fn-psrv-ccar-ocfg-prepare-identity-is-owner-with-store
      fn-lgoc-store-of-owner-with-store
      fn-psrv-deferred-prepare-keeps-histories
      fn-k1-ccar-identity-keeps-frontier
      fn-k1-config-of-with-owner))))
(defthm fn-k1-captured-view-of-oiis-prepare-identity
  (implies (and (fn-lgoc-invariantp oc)
                (fn-captured-view-follows-ocfg view oc))
           (fn-captured-view-follows-ocfg view (fn-oiis-prepare-identity oc w h)))
  :hints (("Goal"
   :use ((:instance fn-k1-captured-view-transport-same-history
           (oc0 oc) (oc (fn-oiis-prepare-identity oc w h))))
   :in-theory '(fn-oiis-prepare-identity-preserves-invariant
                fn-k1-oiis-keeps-durable-context))))
(defthm fn-k1-captured-views-of-oiis-prepare-identity
  (implies (and (fn-lgoc-invariantp oc)
                (fn-captured-views-follow-ocfg views oc))
           (fn-captured-views-follow-ocfg views (fn-oiis-prepare-identity oc w h)))
  :hints (("Goal" :induct (fn-captured-views-follow-ocfg views oc)
           :in-theory '(fn-captured-views-follow-ocfg
                        fn-k1-captured-view-of-oiis-prepare-identity))))


(defthm fn-owner-retain-statep-implies-entry-guard
  (implies (fn-owner-retain-statep state)
           (and (boundp-global 'fn-owner state)
                (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                (fn-prc-carryp (fn-owner-retain-carry state))))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep fn-sbud-oc-store
                               fn-lgoc-invariant-statep))))

(defun fn-owner-prepare-identity (event fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                              (fn-prc-carryp (fn-owner-retain-carry state)))
                  :guard-hints (("Goal" :in-theory (enable fn-sn-statep fn-sbud-oc-store fn-arena-count-is-len)))))
  (let ((s (fn-owner-store state)))
    (if (not (or (fn-stxk-p event) (fn-stxa-p event)))
        (value :invalid)
      ;; fn-oiis-prepare-identity (books/owner-identity-served.lisp): the
      ;; owner's identity prepare over the ROW the intern makes of EVENT at
      ;; the arena's count (signed-post: fn-oii-identity-row, KEYSTONE
      ;; fn-oii-ocfg-prepare-identity-is-intern-then-step), when the row's
      ;; article groups are served (prepare-served's test over the row --
      ;; over the wire event it answered t for every composite; KEYSTONE
      ;; fn-oiis-prepare-identity-preserves-invariant), and the owner
      ;; unchanged otherwise.
      ;; fn-pout-prepare-identity (books/owner-prepare-outcome.lisp) answers
      ;; its word (KEYSTONE fn-pout-prepare-identity-answers-the-store-change).
      ;; served-costs-4 (Q5b): the prepare the host calls is
      ;; fn-irc-pout-prepare-identity (books/identity-retain-carried.lisp)
      ;; with the carried obligation-id trie brought to the Store node's
      ;; ledger, as the article prepare above: the gate's record application
      ;; answers the retention admission from the trie instead of scanning
      ;; every pin and release (KEYSTONE
      ;; fn-irc-pout-prepare-identity-of-refresh-is-pout: its word and owner
      ;; are fn-pout-prepare-identity's for every carry the host holds).
      (let ((carry (fn-prc-refresh (fn-owner-retain-carry state)
                                   (fn-node-retention (fn-sn-node s)))))
      (mv-let (word next)
        (fn-irc-pout-prepare-identity (fn-owner-ocfg state) event
                                      (fn-arena-count fn-arena) carry)
      (let* ((row (fn-oii-identity-row event (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                       (fn-arena-count fn-arena)))
             (state (fn-owner-retain-carry-put carry state))
             (state (fn-owner-install-ocfg next state)))
        (cond ((not (equal word :prepared)) (value word))
              ((fn-oii-identity-sealsp event)
               ; The catalog (signed-post's red, catalog-columns): the article
               ; this event serves and its held row -- the row itself for a
               ; plain record, the held row inside the composite for a signed
               ; one -- kept for the catalog's prepare after the host's seal
               ; (fn-owner-cat-prepare-sealed), completed by
               ; fn-owner-finish-identity (T4 then T2, as a POST).
               (let ((state (f-put-global
                             'fn-owner-cat-candidate
                             (if (fn-hstxa-p row)
                                 (cons (fn-replay-composite-record event) (fn-hstxa-held row))
                               (cons event row))
                             state)))
                 (value (list :seal (fn-oii-identity-payload event)))))
              (t (value :prepared)))))))))

(defthm fn-owner-prepare-identity-preserves-retain-carry
  (implies (fn-prc-carryp (fn-owner-retain-carry state))
           (fn-prc-carryp
            (fn-owner-retain-carry
             (mv-nth 2 (fn-owner-prepare-identity event fn-arena state)))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-prepare-identity mv-nth nth endp zp car-cons cdr-cons
              (:executable-counterpart zp)
              (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-retain-carry-of-put
              fn-owner-retain-carry-of-other-global-put
              fn-owner-retain-carry-of-install-ocfg
              fn-prc-carryp-of-refresh)
            (theory 'minimal-theory)))))

(defthm fn-owner-prepare-identity-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep
            (mv-nth 2 (fn-owner-prepare-identity event fn-arena state))))
  :hints (("Goal" :in-theory
           '(fn-owner-retain-statep fn-owner-prepare-identity
             fn-pout-prepare-identity mv-nth nth endp zp car-cons cdr-cons
             fn-owner-bound-of-retain-carry-put
             fn-owner-bound-of-install-ocfg fn-owner-bound-of-other-global-put
             fn-owner-ocfg-of-retain-carry-put fn-owner-ocfg-of-install-ocfg
             fn-owner-ocfg-of-other-global-put
             fn-owner-retain-carry-of-put
             fn-owner-retain-carry-of-other-global-put
             fn-owner-retain-carry-of-install-ocfg
             fn-prc-carryp-of-refresh
             fn-irc-pout-prepare-identity-of-refresh-is-pout
             fn-oiis-prepare-identity-preserves-invariant
             fn-owner-captured-view-follows-store
             fn-owner-reader-views-of-other-global-put
             fn-owner-reader-views-of-retain-carry-put
             fn-owner-reader-views-of-install-ocfg
             fn-k1-captured-views-of-oiis-prepare-identity))))

(defun fn-owner-finish-synced (fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                              (fn-prc-carryp (fn-owner-retain-carry state)))
                  :guard-hints (("Goal" :in-theory (e/d (fn-sbud-oc-store) (boundp-global))))))
  (let* ((before (fn-owner-core state))
         (before-files (fn-sn-files (fn-own-store before)))
         ;; served-costs-4 (Q5b): the completion the host calls is
         ;; fn-irc-rix-ocfg-complete (books/identity-retain-carried.lisp),
         ;; its gate and finish applying an identity, consumer or topic
         ;; record through the carried obligation-id trie brought to the
         ;; Store node's ledger (boundary fn-irc-rix-ocfg-complete-is-rix,
         ;; then derived composition
         ;; fn-irc-rix-ocfg-complete-of-refresh-is-ocfg-step-complete-by-definition).
         (carry (fn-prc-refresh (fn-owner-retain-carry state)
                                (fn-node-retention
                                 (fn-sn-node (fn-own-store before)))))
         (state (fn-owner-retain-carry-put carry state))
         (state (fn-owner-install-ocfg
                 (fn-irc-rix-ocfg-complete (fn-owner-ocfg state) fn-hist carry)
                 state))
         (after (fn-owner-core state))
         (after-files (fn-sn-files (fn-own-store after))))
    (if (and (equal (fn-sf-phase before-files) :completing)
             (equal (fn-sf-phase after-files) :ready)
             (equal (fn-own-ledger-count after)
                    (1+ (fn-own-ledger-count before))))
        (value :durable)
      (value :fault))))

(defthm fn-owner-finish-synced-preserves-retain-carry
  (implies (fn-prc-carryp (fn-owner-retain-carry state))
           (fn-prc-carryp
            (fn-owner-retain-carry
             (mv-nth 2 (fn-owner-finish-synced fn-hist state)))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-finish-synced mv-nth nth endp zp car-cons cdr-cons
              (:executable-counterpart zp)
              (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-retain-carry-of-put
              fn-owner-retain-carry-of-install-ocfg
              fn-prc-carryp-of-refresh)
            (theory 'minimal-theory)))))

(in-theory (disable fn-owner-retain-statep fn-owner-prepare-identity fn-owner-finish-synced))

; Establish the captured-view premise at initial reader installation and
; the first capture from the actual recovery/start working-view producer.
(local
(defthm fn-one-world-b-start-store
 (equal (fn-own-store (fn-own-start store max-conns)) store)
 :hints (("Goal" :in-theory '(fn-own-start fn-own-refresh-keeps-fields
                             fn-own-store-of-fn-own-make)))))

(local
(defthm fn-one-world-b-started-view-follows-files
 (implies (natp (fn-sf-frontier (fn-sn-files store)))
  (fn-captured-view-follows-files
   (fn-own-view (fn-own-start store max-conns)) (fn-sn-files store)))
 :hints (("Goal" :in-theory
  (union-theories '(fn-captured-view-follows-files fn-own-start fn-own-refresh
                    fn-own-store-of-fn-own-make fn-own-view-of-fn-own-make
                    fn-own-view-fields-of-make-visible natp (:type-prescription len))
                  (theory 'minimal-theory))))))

(defthm fn-one-world-b-initial-readers-follow-ocfg
 (fn-captured-views-follow-ocfg (fn-ordr-views (fn-ordr-initial)) oc)
 :hints (("Goal" :in-theory (enable fn-ordr-initial fn-captured-views-follow-ocfg))))

(defthm fn-one-world-b-started-view-follows-ocfg
 (let ((oc (fn-ocfg-make (fn-own-start store max-conns) config pins staged)))
  (implies (fn-lgoc-invariantp oc)
   (fn-captured-view-follows-ocfg (fn-own-view (fn-ocfg-owner oc)) oc)))
 :hints (("Goal"
  :use ((:instance fn-ocl-relation-of-a-view-captured-before-appends
                   (oc0 (fn-ocfg-make (fn-own-start store max-conns) config pins staged)) (oc (fn-ocfg-make (fn-own-start store max-conns) config pins staged)) (extra nil))
        (:instance fn-lgoc-invariant-statep
         (oc (fn-ocfg-make (fn-own-start store max-conns) config pins staged))))
  :in-theory (union-theories
   '(fn-captured-view-follows-ocfg fn-lgoc-invariantp
     fn-one-world-b-started-view-follows-files fn-one-world-b-start-store
     fn-ocfg-owner-of-fn-ocfg-make fn-lgoc-invariant-statep
     fn-cstp-sn-statep-files fn-snt-typed-frontier-natural
     fn-sf-state-records-are-true-list append-to-nil)
   (theory 'minimal-theory)))))

(defthm fn-one-world-b-start-capture-establishes-follows-ocfg
 (let ((oc (fn-ocfg-make (fn-own-start store max-conns) config pins staged)))
  (implies (fn-lgoc-invariantp oc)
   (fn-captured-views-follow-ocfg
    (fn-ordr-views
     (fn-ordr-capture (fn-ordr-initial) :start
                     (fn-own-view (fn-ocfg-owner oc)))) oc)))

 :hints (("Goal" :use (fn-one-world-b-started-view-follows-ocfg)
  :in-theory (union-theories
   '(car-cons cdr-cons fn-ordr-initial fn-ordr-capture fn-ocv-capture fn-ordr-put
     fn-ordr-views fn-ordr-make fn-captured-views-follow-ocfg
     fn-ocfg-owner-of-fn-ocfg-make)
   (theory 'minimal-theory)))))
