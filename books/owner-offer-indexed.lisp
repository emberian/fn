;; fn: the owner's view trie, carried across every owner transition.
;
; books/peer-offer-indexed.lisp answers the IHAVE/CHECK history test from a
; trie when that trie corresponds (fn-midx-correspondencep) to the article
; list it is keyed to.  The owner passes its committed view's trie and
; articles (books/owner-served-carried.lisp fn-scar-own-read-tls-prefix), so
; the premise the host call needs is fn-scar-view-indexedp of the owner.
; fn-own-relation already carries it (fn-own-view-okp); this book carries it
; for the configured owner the host runs: it holds at fn-own-start and every
; transition the host installs keeps it -- each fn-ocfg-step event
; (fn-oix-ocfg-step-keeps-view-indexed), and the owners host/owner-host.lisp
; installs directly: fn-ocfg-observe, the carried read, fn-ocfg-open,
; -open-peer, -read-step and -fault, the carried prepare, finish and outcome
; (fn-pcar-sbud-prepare, fn-ccar-own-finish, fn-acar-own-outcome),
; fn-own-transit-outcome, fn-own-configure, fn-own-with-feeds and
; fn-ocl-publish.  It is never evaluated on a served path.
;
; The only transition that changes the trie is fn-own-refresh, which the
; commit arms (complete, advance, reopen, the writer outcomes) call; there
; the work is fn-midx-refresh-preserves-correspondence (books/msgid-index.lisp):
; a single acceptance extends the trie by one path copy, a discontinuous
; recovery rebuilds it.  Every other arm keeps the view.

(in-package "ACL2")
(include-book "owner-served-carried")
(include-book "owner-config-observe")
(include-book "owner-commit-carried")
(include-book "owner-prepare-carried")
(include-book "owner-advance-carried")
(include-book "config-owner-publish")

; The keystone of maintenance: a refresh keeps the view trie keyed to the
; view's articles, whichever of its three branches it takes.
(defthm fn-oix-refresh-keeps-correspondence
  (implies (fn-midx-correspondencep
            (fn-own-view-index (fn-own-view o))
            (fn-state-articles (fn-own-view-archive (fn-own-view o))))
           (fn-midx-correspondencep
            (fn-own-view-index (fn-own-view (fn-own-refresh o)))
            (fn-state-articles (fn-own-view-archive (fn-own-view (fn-own-refresh o))))))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh)
                                  (fn-midx-refresh fn-midx-correspondencep
                                   fn-gidx-build)))))

(defthm fn-oix-refresh-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-refresh o)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp)
                                  (fn-own-refresh fn-midx-correspondencep)))))

; The base case: the owner the host starts.
(defthm fn-oix-own-start-is-view-indexed
  (fn-scar-view-indexedp (fn-own-start store max-conns))
  :hints (("Goal" :in-theory (e/d (fn-own-start fn-scar-view-indexedp
                                   fn-midx-correspondencep)
                                  (fn-own-refresh fn-midx-build fn-gidx-build
                                   fn-own-prefix-archive)))))

(defthm fn-oix-helpers-keep-view-unfolds
  (and (equal (fn-own-view (fn-own-enqueue o sub)) (fn-own-view o))
       (equal (fn-own-view (fn-own-set-conns o conns)) (fn-own-view o))
       (equal (fn-own-view (fn-own-with-feeds o feeds)) (fn-own-view o)))
  :hints (("Goal" :in-theory (enable fn-own-enqueue fn-own-set-conns
                                     fn-own-with-feeds))))

; -----------------------------------------------------------------------------
; One lemma per owner transition.

(defthm fn-oix-advance-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-advance o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-advance )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-close-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-close o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-close )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-open-peer-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-open-peer o a b c))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-open-peer )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-open-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-open o a))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-open )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-reader-context-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-reader-context o a b)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-reader-context )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-read-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-read o a b))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-read fn-own-finish-read fn-own-set-conns fn-own-enqueue)
                                  (fn-midx-correspondencep fn-own-refresh fn-served-step)))))

(defthm fn-oix-read-step-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-read-step o a b))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-read-step fn-own-finish-read fn-own-set-conns fn-own-enqueue)
                                  (fn-midx-correspondencep fn-own-refresh fn-served-dispatch)))))

(defthm fn-oix-fault-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-fault o a))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-fault )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-reopen-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-reopen o a b)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-reopen )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-begin-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-begin o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-begin )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-store-step-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-store-step o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-store-step )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-observe-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-observe o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-observe )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-declare-group-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-declare-group o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-declare-group )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-configure-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-configure o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-configure )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-take-submission-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-take-submission o)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-take-submission )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-control-submit-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-control-submit o a b c)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-control-submit )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-bp-transit-submit-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-bp-transit-submit o a b c d e f)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-bp-transit-submit )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-operator-submit-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-operator-submit o a b c)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-operator-submit )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-outcome-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-outcome o a b))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-outcome )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-control-outcome-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-control-outcome o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-control-outcome )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-bp-transit-outcome-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-bp-transit-outcome o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-bp-transit-outcome )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-transit-outcome-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-transit-outcome o a b c d))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-transit-outcome )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-feeds-reconfigure-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-feeds-reconfigure o a)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-feeds-reconfigure )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-feed-connect-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-feed-connect o a b)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-feed-connect )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-feed-lost-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-feed-lost o a b)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-feed-lost )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-feed-recover-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-feed-recover o a b)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-feed-recover )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-tick-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-tick o a))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-tick )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-tick-peer-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-tick-peer o a b))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-tick-peer )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-feed-reply-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-feed-reply o a b c))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-feed-reply )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-advance-result-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-advance-result o a))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-advance-result )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-complete-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-complete o)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-complete )
                                  (fn-midx-correspondencep fn-own-refresh )))))

(defthm fn-oix-own-step-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-step o ev)))
  :hints (("Goal" :in-theory (e/d (fn-own-step)
                                  (fn-scar-view-indexedp fn-own-advance fn-own-advance-result fn-own-begin fn-own-bp-transit-outcome fn-own-bp-transit-submit fn-own-close fn-own-complete fn-own-configure fn-own-control-outcome fn-own-control-submit fn-own-declare-group fn-own-fault fn-own-feed-connect fn-own-feed-lost fn-own-feed-recover fn-own-feed-reply fn-own-feeds-reconfigure fn-own-observe fn-own-open fn-own-open-peer fn-own-operator-submit fn-own-outcome fn-own-read fn-own-read-step fn-own-reader-context fn-own-reopen fn-own-store-step fn-own-take-submission fn-own-tick fn-own-tick-peer fn-own-transit-outcome)))))

; PRESERVATION over every event the host drives through fn-owner-step.
(defthm fn-oix-ocfg-step-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp (fn-ocfg-owner (fn-ocfg-step oc event))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step fn-ocfg-open fn-ocfg-advance
                                   fn-ocfg-close fn-ocfg-read fn-ocfg-read-step
                                   fn-ocfg-open-peer fn-ocfg-fault
                                   fn-ocfg-reconfigure fn-ocfg-complete
                                   fn-ocfg-pass fn-ocfg-with-owner
                                   fn-ocfg-with-read-owner)
                                  (fn-scar-view-indexedp fn-own-advance fn-own-advance-result fn-own-begin fn-own-bp-transit-outcome fn-own-bp-transit-submit fn-own-close fn-own-complete fn-own-configure fn-own-control-outcome fn-own-control-submit fn-own-declare-group fn-own-fault fn-own-feed-connect fn-own-feed-lost fn-own-feed-recover fn-own-feed-reply fn-own-feeds-reconfigure fn-own-observe fn-own-open fn-own-open-peer fn-own-operator-submit fn-own-outcome fn-own-read fn-own-read-step fn-own-reader-context fn-own-reopen fn-own-store-step fn-own-take-submission fn-own-tick fn-own-tick-peer fn-own-transit-outcome)))))

; host/owner-host.lisp fn-owner-observe installs fn-ocfg-observe.
(defthm fn-oix-ocfg-observe-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp (fn-ocfg-owner (fn-ocfg-observe oc obs))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-observe fn-scar-view-indexedp)
                                  (fn-midx-correspondencep fn-own-refresh)))))

; host/owner-host.lisp fn-owner-chunk installs the carried read's owner.
(defthm fn-oix-scar-read-keeps-view
  (equal (fn-own-view
          (fn-ocfg-owner
           (fn-own-tls-result-owner (fn-scar-ocfg-read-tls-prefix oc id octets))))
         (fn-own-view (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (e/d (fn-scar-ocfg-read-tls-prefix
                                   fn-scar-own-read-tls-prefix
                                   fn-scar-finish-read
                                   fn-ocfg-with-read-owner fn-own-tls-make-result
                                   fn-own-tls-result-owner fn-own-set-conns
                                   fn-own-enqueue)
                                  (fn-scar-step-counted-fast
                                   fn-scar-conn-boundedp)))))

(defthm fn-oix-scar-read-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp
            (fn-ocfg-owner
             (fn-own-tls-result-owner (fn-scar-ocfg-read-tls-prefix oc id octets)))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp)
                                  (fn-scar-ocfg-read-tls-prefix
                                   fn-midx-correspondencep)))))

; -----------------------------------------------------------------------------
; The owners host/owner-host.lisp installs without going through fn-ocfg-step.

(defthm fn-oix-ocfg-with-owner-is-view-indexed
  (implies (fn-scar-view-indexedp owner)
           (fn-scar-view-indexedp (fn-ocfg-owner (fn-ocfg-with-owner oc owner))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-with-owner) (fn-scar-view-indexedp)))))

(defthm fn-oix-ocfg-open-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open)
                                  (fn-scar-view-indexedp fn-own-open
                                   fn-own-reader-context)))))

(defthm fn-oix-ocfg-open-peer-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp (fn-ocfg-owner (cdr (fn-ocfg-open-peer oc peer acfg)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open-peer fn-ocfg-with-owner)
                                  (fn-scar-view-indexedp fn-own-open-peer)))))

(defthm fn-oix-ocfg-read-step-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp (fn-ocfg-owner (cdr (fn-ocfg-read-step oc id event)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-read-step fn-ocfg-with-read-owner)
                                  (fn-scar-view-indexedp fn-own-read-step)))))

(defthm fn-oix-ocfg-fault-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp (fn-ocfg-owner (cdr (fn-ocfg-fault oc id)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-fault)
                                  (fn-scar-view-indexedp fn-own-fault)))))

(defthm fn-oix-with-feeds-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-own-with-feeds o feeds)))
  :hints (("Goal" :in-theory (enable fn-scar-view-indexedp))))

(defthm fn-oix-finish-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-own-finish o cfg))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-own-finish)
                                  (fn-midx-correspondencep fn-own-refresh)))))

(defthm fn-oix-ccar-own-finish-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-ccar-own-finish o cfg))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-ccar-own-finish)
                                  (fn-midx-correspondencep fn-own-refresh)))))

(defthm fn-oix-acar-advance-result-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-acar-own-advance-result o id))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-acar-own-advance-result)
                                  (fn-midx-correspondencep fn-own-refresh)))))

(defthm fn-oix-acar-own-outcome-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-acar-own-outcome o id word))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-acar-own-outcome)
                                  (fn-midx-correspondencep fn-own-refresh)))))

(defthm fn-oix-pcar-sbud-prepare-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp (fn-ocfg-owner (fn-pcar-sbud-prepare oc record budget))))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-sbud-prepare fn-opc-prepare
                                   fn-opc-owner-prepare fn-ocfg-with-owner)
                                  (fn-midx-correspondencep fn-own-refresh
                                   fn-sbud-admitp fn-sbud-used)))))

(defthm fn-oix-ocl-owner-with-store-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (fn-ocl-owner-with-store o st)))
  :hints (("Goal" :in-theory (e/d (fn-scar-view-indexedp fn-ocl-owner-with-store)
                                  (fn-midx-correspondencep fn-own-refresh)))))

(defthm fn-oix-ocl-publish-keeps-view-indexed
  (implies (fn-scar-view-indexedp (fn-ocfg-owner oc))
           (fn-scar-view-indexedp
            (fn-ocfg-owner (mv-nth 1 (fn-ocl-publish oc generation max-octets)))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-publish fn-ocfg-with-owner fn-ocl-complete)
                                  (fn-scar-view-indexedp fn-own-configure
                                   fn-ocl-owner-with-store fn-own-complete)))))
