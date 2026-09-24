; fn: the live reconfiguration as the host calls it.
;
; Two decisions the host used to make move here.
;
;   `fn-ocl-request-deltas' is the delta list for one `create' or `retire'
;   group request.  host/owner-host.lisp `fn-owner-reconfigure' calls it;
;   before, the host built the list itself (`fn-owner-config-deltas') under a
;   comment that said ACL2 did.
;
;   `fn-ocl-publish' is the whole completion the host performs after the
;   configuration journal reported the staged record durable: refuse when
;   nothing is staged or the durable generation is not the staged one,
;   complete through `fn-ocl-complete', and install the posting
;   configuration of the published generation.  host/owner-host.lisp
;   `fn-owner-reconfigure-complete' calls it and installs its second value
;   unconditionally; before, the host sequenced `fn-ocl-complete' and
;   `fn-own-configure' itself, and the headline theorem was stated over
;   `fn-ocfg-step (:complete)', which the host never called.
;
; This book shares the prefix `fn-ocl-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "config-owner-live")
(include-book "owner-agent")

(defun fn-ocl-request-deltas (kind name)
  (declare (xargs :guard t))
  (cond ((equal kind :create-group)
         (list (fn-cfg-create-group name *fn-cfg-default-policy-id*)))
        ((equal kind :remove-group) (list (fn-cfg-remove-group name)))
        (t nil)))

(defun fn-ocl-publish (oc generation max-octets)
  ; (mv verdict next).  VERDICT is :durable, :refused or :recovery-required;
  ; NEXT is the configured owner the host installs.  On :refused and
  ; :recovery-required NEXT is OC itself: the durable record that could not
  ; be installed is a recovery event, and the host fences and reopens.
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (let ((record (fn-ocfg-staged oc)))
    (if (or (not record)
            (not (equal (fn-cfg-record-generation record) generation)))
        (mv :refused oc)
      (let ((next (fn-ocl-complete oc)))
        (if (fn-ocfg-staged next)
            (mv :recovery-required oc)
          (mv :durable
              (fn-ocfg-with-owner
               next
               (fn-own-configure
                (fn-ocfg-owner next)
                (fn-oag-post-config (fn-ocfg-config next) max-octets)))))))))

(in-theory (disable fn-ocl-request-deltas fn-ocl-publish))

; -----------------------------------------------------------------------------
; The request delta.

; A group request's delta list is one typed delta that names the requested
; group and no other.  Hypothesis: the request kind is one of the two.
(defthm fn-ocl-request-deltas-name-only-the-requested-group
  (implies (member-equal kind '(:create-group :remove-group))
           (let ((deltas (fn-ocl-request-deltas kind name)))
             (and (consp deltas)
                  (equal (len deltas) 1)
                  (implies (fn-cfg-labelp name) (fn-cfg-delta-listp deltas))
                  (fn-ocfg-deltas-touch-groupp deltas name)
                  (implies (not (equal other name))
                           (not (fn-ocfg-deltas-touch-groupp deltas other))))))
  :hints (("Goal" :in-theory (enable fn-ocl-request-deltas
                                     fn-cfg-create-group fn-cfg-remove-group
                                     fn-cfg-delta-listp fn-cfg-deltap
                                     fn-ocfg-deltas-touch-groupp
                                     fn-ocfg-delta-names-group))))

; KEYSTONE (request).  A GROUP REQUEST NEVER STAGES OVER A READER STANDING IN
; THAT GROUP.  If an open connection's reader session has selected NAME, the
; request for NAME is refused at staging: the owner is unchanged and nothing
; is staged for `fn-ocl-publish' to complete.  Hypotheses: some connection in
; the owner's table has NAME as its reader group.  Any request kind: a kind
; that is not a group kind has no delta, and staging refuses an empty delta
; list; and a connection with no group selected (NAME nil) asks for a delta
; naming no label, which staging refuses as untyped.
(defthm fn-ocl-reader-in-a-touched-group-pins-it
  (implies (and (member-equal conn conns)
                (equal (fn-nntp-session-group
                        (fn-auth-reader-session (fn-own-conn-session conn)))
                       name)
                name
                (fn-ocfg-deltas-touch-groupp deltas name))
           (fn-ocfg-group-pinned-by-readerp deltas conns))
  :hints (("Goal" :in-theory (enable fn-ocfg-group-pinned-by-readerp))))

(local
 (defthm fn-ocl-request-deltas-without-a-name-are-untyped
   (not (and (consp (fn-ocl-request-deltas kind nil))
             (fn-cfg-delta-listp (fn-ocl-request-deltas kind nil))))
   :hints (("Goal" :in-theory (enable fn-ocl-request-deltas fn-cfg-create-group
                                      fn-cfg-remove-group)))))

(local
 (defthm fn-ocl-request-over-a-reader-is-untyped-or-pinned
   (implies (and (member-equal conn conns)
                 (equal (fn-nntp-session-group
                         (fn-auth-reader-session (fn-own-conn-session conn)))
                        name))
            (or (not (consp (fn-ocl-request-deltas kind name)))
                (not (fn-cfg-delta-listp (fn-ocl-request-deltas kind name)))
                (fn-ocfg-group-pinned-by-readerp
                 (fn-ocl-request-deltas kind name) conns)))
   :rule-classes nil
   :hints (("Goal"
            :cases ((and name (member-equal kind '(:create-group :remove-group))))
            :use ((:instance fn-ocl-reader-in-a-touched-group-pins-it
                             (deltas (fn-ocl-request-deltas kind name)))
                  (:instance fn-ocl-request-deltas-name-only-the-requested-group
                             (other name))
                  (:instance fn-ocl-request-deltas-without-a-name-are-untyped))
            :in-theory (e/d (fn-ocl-request-deltas)
                            (fn-ocl-reader-in-a-touched-group-pins-it
                             fn-ocl-request-deltas-name-only-the-requested-group
                             fn-ocl-request-deltas-without-a-name-are-untyped
                             fn-ocfg-group-pinned-by-readerp fn-cfg-delta-listp
                             fn-nntp-session-group fn-cfg-create-group
                             fn-cfg-remove-group))))))

(defthm fn-ocl-request-refused-over-a-reader-in-the-group
  (implies (and (member-equal conn (fn-own-conns (fn-ocfg-owner oc)))
                (equal (fn-nntp-session-group
                        (fn-auth-reader-session (fn-own-conn-session conn)))
                       name))
           (equal (fn-ocfg-step oc (list :reconfigure id
                                         (fn-ocl-request-deltas kind name)))
                  oc))
  :hints (("Goal"
           :use ((:instance fn-ocl-request-over-a-reader-is-untyped-or-pinned
                            (conns (fn-own-conns (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocfg-step fn-ocfg-reconfigure fn-ocfg-reconfig-okp)
                           (fn-nntp-session-group fn-ocfg-group-pinned-by-readerp
                            fn-ocl-request-deltas
                            fn-ocfg-live-cnode fn-ocfg-reconfig-record
                            fn-cnode-record-acceptablep fn-cfg-delta-listp)))))

; -----------------------------------------------------------------------------
; Publication.

; What `fn-ocl-complete' publishes on success is what the installed store's
; configuration history replays to.
(defthm fn-ocl-complete-success-publishes-the-store-configuration
  (implies (and (fn-ocfg-staged oc)
                (not (fn-ocfg-staged (fn-ocl-complete oc))))
           (equal (fn-ocfg-config (fn-ocl-complete oc))
                  (fn-ocl-store-config
                   (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc))))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-complete fn-ocl-owner-with-store
                                   fn-own-refresh-keeps-fields)
                                  (fn-cpo-configure-durable fn-ocl-store-config)))))

(defthm fn-ocl-publish-leaves-connections-and-pins
  (and (equal (fn-own-conns
       (fn-ocfg-owner (mv-nth 1 (fn-ocl-publish oc generation max-octets))))
      (fn-own-conns (fn-ocfg-owner oc)))
       (equal (fn-ocfg-pins (mv-nth 1 (fn-ocl-publish oc generation max-octets)))
              (fn-ocfg-pins oc)))
  :hints (("Goal" :in-theory (enable fn-ocl-publish fn-ocfg-with-owner
                                     fn-own-configure))))

; KEYSTONE (headline 1, over the called path).  NO READER OBSERVES A HALF
; CHANGE.  The host's live reconfiguration is `(:reconfigure other deltas)'
; through `fn-ocfg-step' (host/owner-host.lisp `fn-owner-reconfigure-deltas')
; followed by `fn-ocl-publish' (`fn-owner-reconfigure-complete').  Across the
; two, every open connection's record and every configuration pin are exactly
; as they were, hence each connection's served table; staging moves neither
; the owner nor the live configuration; and publication either changes
; nothing (:refused, :recovery-required) or, on :durable, completes exactly
; the record whose generation the durable write named: the store's
; configuration history gains that WHOLE record, the live configuration is
; what that history replays to, nothing stays staged, and the posting
; configuration new connections pin is the published generation's.  No
; hypothesis: the refusal that used to be a host line (nothing staged, or a
; different generation) is `fn-ocl-publish''s first arm.
(defthm fn-ocl-no-reader-observes-a-half-change
  (let* ((staged (fn-ocfg-step oc (list :reconfigure other deltas)))
         (record (fn-ocfg-staged staged))
         (result (fn-ocl-publish staged generation max-octets))
         (verdict (mv-nth 0 result))
         (published (mv-nth 1 result)))
    (and (equal (fn-own-conns (fn-ocfg-owner staged))
                (fn-own-conns (fn-ocfg-owner oc)))
         (equal (fn-ocfg-pins staged) (fn-ocfg-pins oc))
         (equal (fn-ocfg-config staged) (fn-ocfg-config oc))
         (equal (fn-own-conns (fn-ocfg-owner published))
                (fn-own-conns (fn-ocfg-owner oc)))
         (equal (fn-ocfg-pins published) (fn-ocfg-pins oc))
         (equal (fn-ocfg-served published id) (fn-ocfg-served oc id))
         (if (equal verdict :durable)
             (and (equal (fn-cfg-record-generation record) generation)
                  (not (fn-ocfg-staged published))
                  (equal (fn-sn-config-history
                          (fn-own-store (fn-ocfg-owner published)))
                         (append (fn-sn-config-history
                                  (fn-own-store (fn-ocfg-owner oc)))
                                 (list record)))
                  (equal (fn-ocfg-config published)
                         (fn-ocl-store-config
                          (fn-own-store (fn-ocfg-owner published))))
                  (equal (fn-own-config (fn-ocfg-owner published))
                         (fn-oag-post-config (fn-ocfg-config published)
                                             max-octets)))
           (equal published staged))))
  :hints (("Goal"
           :use ((:instance fn-ocl-success-appends-exact-config-history
                            (oc (fn-ocfg-step oc (list :reconfigure other deltas))))
                 (:instance fn-ocl-staged-complete-keeps-connections
                            (oc (fn-ocfg-step oc (list :reconfigure other deltas))))
                 (:instance fn-ocl-complete-success-publishes-the-store-configuration
                            (oc (fn-ocfg-step oc (list :reconfigure other deltas)))))
           :in-theory (e/d (fn-ocl-publish fn-ocfg-step fn-ocfg-reconfigure
                            fn-ocfg-with-owner
                            fn-own-configure fn-ocfg-served fn-ocfg-conn-config)
                           (fn-ocl-complete fn-ocfg-reconfig-okp
                            fn-ocfg-reconfig-record fn-oag-post-config
                            fn-ocl-store-config
                            fn-ocl-success-appends-exact-config-history
                            fn-ocl-staged-complete-keeps-connections
                            fn-ocl-complete-success-publishes-the-store-configuration)))))

;; -----------------------------------------------------------------------------
; What the published configuration IS.  The physical replay the host calls
; at open (`fn-cpr-replay', host/owner-host.lisp `fn-owner-recover') and that
; `fn-ocl-complete' installs moves the configuration only at configuration
; records, each by `fn-cfg-apply-record' of the whole record; Store events
; never move it.  So a successful replay's configuration is the fold of
; `fn-cfg-apply-record' over the configuration history.

(defun fn-ocl-config-fold (cfg configs)
  (declare (xargs :verify-guards nil))
  (if (consp configs)
      (fn-ocl-config-fold (fn-cfg-apply-record cfg (car configs)) (cdr configs))
    cfg))

(local
 (defthm fn-ocl-config-of-applied-config
   (implies (and (fn-cnode-statep cn)
                 (fn-cnode-record-acceptablep cn record ceiling))
            (equal (fn-cnode-config (fn-cnode-apply-config cn record ceiling))
                   (fn-cfg-apply-record (fn-cnode-config cn) record)))
   :hints (("Goal" :in-theory (enable fn-cnode-apply-config)))))

(local
 (defthm fn-ocl-statep-is-consp
   (implies (fn-cnode-statep cn) (consp cn))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cnode-statep)))))

(defthm fn-ocl-cpr-loop-configuration-is-the-record-fold
  (implies (equal (fn-replay-result-kind
                   (fn-cpr-loop cn configs events config-sequence event-sequence))
                  :ok)
           (equal (fn-cnode-config
                   (fn-replay-result-node
                    (fn-cpr-loop cn configs events config-sequence event-sequence)))
                  (fn-ocl-config-fold (fn-cnode-config cn) configs)))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events config-sequence
                                       event-sequence)
           :in-theory (e/d (fn-cpr-loop fn-ocl-config-fold)
                           (fn-cnode-statep fn-cnode-apply-config
                            fn-cnode-record-acceptablep fn-cpr-apply-event
                            fn-cfg-apply-record fn-replay-advance-txid
                            fn-replay-advance-okp fn-store-event-p
                            fn-cfg-recordp)))))

(defthm fn-ocl-config-fold-of-one-more-record
  (equal (fn-ocl-config-fold cfg (append configs (list record)))
         (fn-cfg-apply-record (fn-ocl-config-fold cfg configs) record))
  :hints (("Goal" :in-theory (enable fn-ocl-config-fold))))

(local
 (defthm fn-ocl-append-one-is-longer
   (not (equal (append x (list y)) x))))

(local
 (defthm fn-ocl-durable-history-change-replays-ok
   (implies (not (equal (fn-sn-config-history (fn-cpo-configure-durable st record))
                        (fn-sn-config-history st)))
            (equal (fn-replay-result-kind
                    (fn-cpr-replay (append (fn-sn-config-history st) (list record))
                                   (fn-sf-records (fn-sn-files st))))
                   :ok))
   :hints (("Goal" :in-theory (e/d (fn-cpo-configure-durable fn-cpo-install)
                                   (fn-cpo-history-relation fn-cpr-replay))))))

; KEYSTONE (the whole record, over the called path).  When `fn-ocl-publish'
; answers :durable, the live configuration it installs is
; `fn-cfg-apply-record' of the live configuration and the WHOLE staged record:
; never a prefix of its deltas, never another generation.  Hypothesis: the
; owner's live configuration is what its store's durable history replays to
; (`fn-ocl-config-historyp', a conjunct of `fn-ocl-relation', which
; `fn-ocl-complete-preserves-full-historical-relation' carries across every
; completion).
(defthm fn-ocl-publish-installs-the-whole-staged-record
  (implies (and (equal (mv-nth 0 (fn-ocl-publish oc generation max-octets)) :durable)
                (fn-ocl-config-historyp oc))
           (equal (fn-ocfg-config (mv-nth 1 (fn-ocl-publish oc generation max-octets)))
                  (fn-cfg-apply-record (fn-ocfg-config oc) (fn-ocfg-staged oc))))
  :hints (("Goal"
           :use ((:instance fn-ocl-complete-success-publishes-the-store-configuration)
                 (:instance fn-ocl-success-appends-exact-config-history)
                 (:instance fn-ocl-staged-complete-keeps-store-events)
                 (:instance fn-ocl-durable-history-change-replays-ok
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-ocl-complete-success-install-exact-store))
           :in-theory (e/d (fn-ocl-publish fn-ocfg-with-owner fn-own-configure
                            fn-ocl-config-historyp fn-ocl-store-config fn-cpr-replay)
                           (fn-ocl-complete fn-cpo-configure-durable fn-cpr-loop
                            fn-cfg-apply-record fn-oag-post-config
                            fn-ocl-durable-history-change-replays-ok
                            fn-ocl-complete-success-publishes-the-store-configuration
                            fn-ocl-success-appends-exact-config-history
                            fn-ocl-staged-complete-keeps-store-events
                            fn-ocl-complete-success-install-exact-store)))))

; The equation to the model event.  On :durable, `fn-ocl-publish' agrees with
; `fn-ocfg-step (:complete)' on everything a reader holds: the pins, hence
; every served table, the connection records, and the empty stage.  The two
; differ in the owner's store and posting configuration and in the live
; configuration's formula (`fn-ocl-store-config' of the store history against
; `fn-ocfg-published-config' of the configuration), which is why the headline
; above is stated over `fn-ocl-publish' and not transferred through this.
; Hypothesis: the verdict is :durable (otherwise `(:complete)' with nothing
; staged is the article completion `fn-own-complete').
(defthm fn-ocl-publish-agrees-with-ocfg-complete-on-readers
  (implies (equal (mv-nth 0 (fn-ocl-publish oc generation max-octets)) :durable)
           (let ((published (mv-nth 1 (fn-ocl-publish oc generation max-octets)))
                 (model (fn-ocfg-step oc (list :complete))))
             (and (equal (fn-ocfg-pins published) (fn-ocfg-pins model))
                  (equal (fn-ocfg-served published id) (fn-ocfg-served model id))
                  (equal (fn-own-conns (fn-ocfg-owner published))
                         (fn-own-conns (fn-ocfg-owner model)))
                  (equal (fn-ocfg-staged published) (fn-ocfg-staged model)))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-publish fn-ocfg-step fn-ocfg-complete
                                   fn-ocfg-with-owner
                                   fn-own-configure fn-ocfg-served fn-ocfg-conn-config)
                                  (fn-ocl-complete fn-oag-post-config)))))
