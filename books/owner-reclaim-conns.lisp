; fn -- Q16 (a) (PRF-939): the connections the installing pass re-pins
; satisfy the configured owner relation's connection clause over the
; rebuilt Store.
;
; The swap (host/owner-host.lisp fn-owner-orcp-swap) installs
; fn-orcp-swapped-ocfg: the rebuilt owner's Store and view, every live
; connection re-pinned to that view (fn-orcp-repin-conn, as GROUP moves a
; pin) and its configuration pin moved to the rebuilt configuration (as
; fn-ocfg-advance moves one).  It installs only when fn-orcp-swap-decision
; answers :swap, which requires fn-orcp-swap-admissiblep.  The rebuilt
; owner is the full open's (fn-orcp-rebuild-is-the-full-open), which
; satisfies fn-ocl-relation (fn-orec-recover-installs-ocl-relation).  Each
; re-pinned connection then has its history (fn-ocl-conn-historyp) by
; fn-ocl-unchanged-view-new-pin-is-historical: the same Store and view, the
; view's pin, the rebuilt configuration's pin, bounded by its domain.

(in-package "ACL2")
(include-book "owner-reclaim-pass")
(include-book "owner-recover-ocl")
(include-book "config-owner-live-open")

; Every re-pinned connection reads the view it was re-pinned to.
(defthm fn-orcn-repin-conn-at-view
  (let ((c (fn-orcp-repin-conn o conn)))
    (and (fn-own-conn-shapep c)
         (equal (fn-own-conn-id c) (fn-own-conn-id conn))
         (equal (fn-own-conn-version c) (fn-own-view-version (fn-own-view o)))
         (equal (fn-own-conn-frontier c) (fn-own-view-frontier (fn-own-view o)))
         (equal (fn-own-conn-archive c) (fn-own-view-archive (fn-own-view o)))))
  :hints (("Goal" :in-theory (e/d (fn-orcp-repin-conn fn-served-repin fn-own-served-conn)
                                  (fn-own-conn-make-group-indexed fn-own-conn-shapep
                                   fn-served-repin-session))
                  :use ((:instance fn-own-view-live-fields (view (fn-own-view o)))))))

(defthm fn-orcn-member-of-repin-conns
  (implies (member-equal c (fn-orcp-repin-conns o conns))
           (and (fn-own-conn-shapep c)
                (equal (fn-own-conn-version c) (fn-own-view-version (fn-own-view o)))
                (equal (fn-own-conn-frontier c) (fn-own-view-frontier (fn-own-view o)))
                (equal (fn-own-conn-archive c) (fn-own-view-archive (fn-own-view o)))))
  :hints (("Goal" :induct (fn-orcp-repin-conns o conns)
                  :in-theory (e/d (fn-orcp-repin-conns) (fn-orcp-repin-conn)))))

; The pins the swap installs name every connection at CFG.
(defthm fn-orcn-pin-find-of-pins-at
  (implies (member-equal c conns)
           (equal (cdr (fn-ocfg-pin-find (fn-own-conn-id c) (fn-orcp-pins-at conns cfg)))
                  cfg))
  :hints (("Goal" :induct (fn-orcp-pins-at conns cfg)
                  :in-theory (enable fn-orcp-pins-at fn-ocfg-pin-find))))

(defthm fn-orcn-bounded-member
  (implies (and (fn-orcp-conns-boundedp conns domain)
                (member-equal c conns))
           (fn-own-conn-boundedp c domain))
  :hints (("Goal" :induct (fn-orcp-conns-boundedp conns domain)
                  :in-theory (e/d (fn-orcp-conns-boundedp) (fn-own-conn-boundedp)))))

(defthm fn-orcn-swap-base-view
  (equal (fn-own-view (fn-orcp-swap-base live rebuilt))
         (fn-own-view rebuilt))
  :hints (("Goal" :in-theory (enable fn-orcp-swap-base))))

(defthm fn-orcn-swapped-owner-conns
  (equal (fn-own-conns (fn-orcp-swapped-owner live rebuilt))
         (fn-orcp-repin-conns (fn-orcp-swap-base live rebuilt) (fn-own-conns live)))
  :hints (("Goal" :in-theory (e/d (fn-orcp-swapped-owner fn-own-set-conns)
                                  (fn-orcp-repin-conns fn-orcp-swap-base)))))

(defthm fn-orcn-swapped-ocfg-fields
  (let ((next (fn-orcp-swapped-ocfg live-oc rebuilt-oc)))
    (and (equal (fn-own-store (fn-ocfg-owner next))
                (fn-own-store (fn-ocfg-owner rebuilt-oc)))
         (equal (fn-own-view (fn-ocfg-owner next))
                (fn-own-view (fn-ocfg-owner rebuilt-oc)))
         (equal (fn-own-conns (fn-ocfg-owner next))
                (fn-orcp-repin-conns (fn-orcp-swap-base (fn-ocfg-owner live-oc)
                                                        (fn-ocfg-owner rebuilt-oc))
                                     (fn-own-conns (fn-ocfg-owner live-oc))))
         (equal (fn-ocfg-pins next)
                (fn-orcp-pins-at (fn-own-conns (fn-ocfg-owner next))
                                 (fn-ocfg-config rebuilt-oc)))))
  :hints (("Goal" :in-theory (e/d (fn-orcp-swapped-ocfg fn-orcp-swapped-owner
                                   fn-orcp-swap-base fn-own-set-conns)
                                  (fn-orcp-repin-conns fn-orcp-pins-at)))))

(in-theory (disable fn-orcp-swapped-ocfg))

; One connection of the swapped owner has its history.
(defthm fn-orcn-swapped-conn-has-history
  (implies (and (fn-ocl-relation rebuilt-oc)
                (fn-orcp-swap-admissiblep live-oc rebuilt-oc)
                (member-equal c (fn-own-conns (fn-ocfg-owner
                                               (fn-orcp-swapped-ocfg live-oc rebuilt-oc)))))
           (fn-ocl-conn-historyp (fn-orcp-swapped-ocfg live-oc rebuilt-oc) c))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-ocl-unchanged-view-new-pin-is-historical
                            (oc rebuilt-oc)
                            (next (fn-orcp-swapped-ocfg live-oc rebuilt-oc))
                            (conn c))
                 (:instance fn-orcn-member-of-repin-conns
                            (o (fn-orcp-swap-base (fn-ocfg-owner live-oc)
                                                  (fn-ocfg-owner rebuilt-oc)))
                            (conns (fn-own-conns (fn-ocfg-owner live-oc))))
                 (:instance fn-orcn-pin-find-of-pins-at
                            (conns (fn-own-conns (fn-ocfg-owner
                                                  (fn-orcp-swapped-ocfg live-oc rebuilt-oc))))
                            (cfg (fn-ocfg-config rebuilt-oc)))
                 (:instance fn-orcn-bounded-member
                            (conns (fn-own-conns (fn-ocfg-owner
                                                  (fn-orcp-swapped-ocfg live-oc rebuilt-oc))))
                            (domain (fn-cnode-domain-of (fn-ocfg-config rebuilt-oc)))))
           :in-theory (e/d (fn-orcp-swap-admissiblep fn-ocfg-conn-config)
                           (fn-ocl-relation fn-ocl-conn-historyp fn-own-conn-boundedp
                            fn-orcp-repin-conns fn-orcp-pins-at fn-ocfg-pin-find
                            fn-orcp-conns-boundedp fn-orcp-swapped-owner
                            fn-orcp-swap-base)))))

(defthm fn-orcn-swapped-conns-have-history-sublist
  (implies (and (fn-ocl-relation rebuilt-oc)
                (fn-orcp-swap-admissiblep live-oc rebuilt-oc)
                (true-listp xs)
                (subsetp-equal xs (fn-own-conns (fn-ocfg-owner
                                                 (fn-orcp-swapped-ocfg live-oc rebuilt-oc)))))
           (fn-ocl-conns-historyp (fn-orcp-swapped-ocfg live-oc rebuilt-oc) xs))
  :hints (("Goal" :induct (len xs)
                  :in-theory (e/d (fn-ocl-conns-historyp subsetp-equal)
                                  (fn-ocl-relation fn-ocl-conn-historyp
                                   fn-orcp-swap-admissiblep)))
          ("Subgoal *1/1" :use ((:instance fn-orcn-swapped-conn-has-history (c (car xs)))))))

(local
 (defthm fn-orcn-subsetp-cons
   (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(local
 (defthm fn-orcn-subsetp-refl
   (subsetp-equal x x)))

(defthm fn-orcn-true-listp-repin-conns
  (true-listp (fn-orcp-repin-conns o conns))
  :hints (("Goal" :in-theory (enable fn-orcp-repin-conns))))

; KEYSTONE.  Over the configuration the swap installs, every connection of
; the swapped owner has its history (fn-ocl-conns-historyp, the connection
; clause of fn-ocl-relation), when the rebuilt owner satisfies the relation
; and the swap was admitted.
(defthm fn-orcn-swapped-conns-have-history
  (implies (and (fn-ocl-relation rebuilt-oc)
                (fn-orcp-swap-admissiblep live-oc rebuilt-oc))
           (let ((next (fn-orcp-swapped-ocfg live-oc rebuilt-oc)))
             (fn-ocl-conns-historyp next (fn-own-conns (fn-ocfg-owner next)))))
  :hints (("Goal" :use ((:instance fn-orcn-swapped-conns-have-history-sublist
                                   (xs (fn-own-conns (fn-ocfg-owner
                                                      (fn-orcp-swapped-ocfg live-oc rebuilt-oc))))))
                  :in-theory (e/d (fn-orcn-subsetp-refl)
                                  (fn-orcn-swapped-conns-have-history-sublist
                                   fn-ocl-relation fn-ocl-conns-historyp
                                   fn-orcp-swap-admissiblep)))))

; The rebuilt owner the pass swaps in satisfies the relation: it is the full
; open's (fn-orcp-rebuild-is-the-full-open), and a full open that installs
; satisfies fn-ocl-relation (fn-orec-recover-installs-ocl-relation).
(defthm fn-orcn-rebuilt-owner-has-ocl-relation
  (let ((rebuilt-oc (cadr (fn-orcp-rebuild rows configs frontier max-conns))))
    (implies (not (equal rebuilt-oc :fault))
             (fn-ocl-relation rebuilt-oc)))
  :hints (("Goal" :use (fn-orcp-rebuild-is-the-full-open
                        (:instance fn-orec-recover-installs-ocl-relation
                                   (events rows)))
                  :in-theory (e/d (fn-ock-recover-full fn-ock-install)
                                  (fn-orcp-rebuild fn-ocl-relation fn-cpr-replay
                                   fn-cpo-open-observed fn-own-configure fn-own-start
                                   fn-oag-post-config fn-scar-view-indexedp)))))

;; The admitted swap's rebuild installed.
(defthm fn-orcn-admitted-swap-rebuild-installed
  (implies (equal (fn-orcp-swap-decision word live-oc rebuilt-oc) :swap)
           (and (fn-orcp-swap-admissiblep live-oc rebuilt-oc)
                (not (equal rebuilt-oc :fault))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-orcp-swap-decision fn-orcp-swap-admissiblep)
                                  (fn-orcp-conns-boundedp fn-orcp-swapped-owner)))))

; KEYSTONE (composed).  The configuration the swap installs over the pass's
; rebuild: when fn-orcp-swap-decision answered :swap (the host installs
; only then), every connection of the swapped owner has its history over
; the rebuilt Store.
(defthm fn-orcn-swap-over-the-rebuild-keeps-conn-histories
  (let ((rebuilt-oc (cadr (fn-orcp-rebuild rows configs frontier max-conns))))
    (implies (equal (fn-orcp-swap-decision word live-oc rebuilt-oc) :swap)
             (let ((next (fn-orcp-swapped-ocfg live-oc rebuilt-oc)))
               (fn-ocl-conns-historyp next (fn-own-conns (fn-ocfg-owner next))))))
  :hints (("Goal" :use (fn-orcn-rebuilt-owner-has-ocl-relation
                        (:instance fn-orcn-admitted-swap-rebuild-installed
                                   (rebuilt-oc (cadr (fn-orcp-rebuild rows configs
                                                                      frontier max-conns))))
                        (:instance fn-orcn-swapped-conns-have-history
                                   (rebuilt-oc (cadr (fn-orcp-rebuild rows configs
                                                                      frontier max-conns)))))
                  :in-theory (union-theories '(car-cons cdr-cons)
                                             (theory 'minimal-theory)))))
