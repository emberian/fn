; fn: an access tightening reaches every open connection at its next command
; (ACCESS-REVOKE-PINNED; coordinator ruling 2026-10-04, specs/
; reconfiguration.md 2.3 "Readers").
;
; Before: a connection's READ rule (its login's access row, moderation-queue
; hiding) was read from the configuration the connection pinned at open, and
; nothing moved that pin's access -- not a reconfiguration, not ADVANCE, not
; GROUP (fn-ocfg-with-read-owner moves the pin TABLE's generation; the
; connection's injection configuration stayed).  A revoked reader's open
; socket kept listing the revoked group and answered 223 for its articles.
;
; Now books/owner.lisp `fn-own-served-conn' serves the pin with the live
; configuration's access beside it (books/group-access.lisp
; `fn-gac-config-with-live'), and books/nntp-auth.lisp `fn-auth-access-text'
; decides every command by the pinned rule AND the live rule of the login the
; session has at that command.  So:
;   * what the live rule refuses, no command of any connection is served
;     (fn-own-served-conn-refuses-what-the-live-rule-refuses);
;   * what the pin refuses stays refused: a widening never reaches an open
;     connection (fn-own-served-conn-refuses-what-the-pin-refuses);
;   * the rule is the login's at each command, so an AUTHINFO pipelined ahead
;     of a retrieval in the same socket read is decided by that login's live
;     rule (tests/acl2/served-access-revoke-tests.lisp, the pipelined witness).
; The per-command cost is one more rule lookup and one comparison of two rule
; texts; nothing walks the catalog or the group table to decide it.
;
; Scope.  The conclusion is about the view a command is answered from
; (`fn-auth-view-archive' of the served configuration), for any session and
; any archive, so it holds at every event of a read, including after AUTHINFO
; and after a GROUP re-pin.  That the host's read answers from exactly that
; view is PRF-1328 (books/served-available-access.lisp,
; fn-av-scr-auth-delegate-restricted-is-reference and the read-level
; equations), over the served connection this book's keystone is about.

(in-package "ACL2")
(include-book "owner-tls-prefix")
(include-book "served-available-access")

(local (in-theory (disable (tau-system))))

; The live rule of LOGIN in configuration CFG, as fn-oag-post-config installs
; it in the owner (fn-own-config): its access row and its queue hiding.
(defun fn-sar-live-rule (cfg login)
  (declare (xargs :guard t))
  (fn-auth-rule-text (fn-gac-listing-table (fn-inj-config-listing cfg))
                     (fn-inj-config-closed cfg) login 1))

(defthm fn-sar-served-config
  (equal (fn-served-conn-config (fn-own-served-conn o conn session))
         (fn-gac-config-with-live (fn-own-conn-config conn) (fn-own-config o)))
  :hints (("Goal" :in-theory (enable fn-own-served-conn))))

; The served configuration's READ text, unfolded: the pinned rule and the
; live rule, intersected.
(defthm fn-sar-access-text-of-config-with-live
  (equal (fn-auth-access-text as (fn-gac-config-with-live pinned live) 1)
         (fn-gac-and-text
          (fn-auth-rule-text (fn-gac-listing-table (fn-inj-config-listing pinned))
                             (fn-inj-config-closed pinned)
                             (fn-auth-access-login as) 1)
          (fn-sar-live-rule live (fn-auth-access-login as))))
  :hints (("Goal" :in-theory (e/d (fn-auth-access-text fn-sar-live-rule fn-gac-live-access)
                                  (fn-auth-rule-text fn-gac-and-text)))))

(local
 (defthm fn-sar-text-refuses-live
   (implies (and (fn-sar-live-rule live (fn-auth-access-login as))
                 (not (fn-gac-readablep (fn-sar-live-rule live (fn-auth-access-login as)) g)))
            (and (fn-auth-access-text as (fn-gac-config-with-live pinned live) 1)
                 (not (fn-gac-readablep
                       (fn-auth-access-text as (fn-gac-config-with-live pinned live) 1) g))))
   :hints (("Goal" :in-theory (disable fn-sar-live-rule fn-auth-rule-text fn-gac-and-text
                                       fn-gac-readablep)))))

(local
 (defthm fn-sar-text-refuses-pin
   (let ((tp (fn-auth-rule-text (fn-gac-listing-table (fn-inj-config-listing pinned))
                                (fn-inj-config-closed pinned)
                                (fn-auth-access-login as) 1)))
     (implies (and tp (not (fn-gac-readablep tp g)))
              (and (fn-auth-access-text as (fn-gac-config-with-live pinned live) 1)
                   (not (fn-gac-readablep
                         (fn-auth-access-text as (fn-gac-config-with-live pinned live) 1) g)))))
   :hints (("Goal" :in-theory (disable fn-sar-live-rule fn-auth-rule-text fn-gac-and-text
                                       fn-gac-readablep)))))

;; KEYSTONE (ACCESS-REVOKE-PINNED).  After any reconfiguration, the view any
;; command of any open connection is answered from holds no group the LIVE
;; rule of that command's login refuses, and no article filed in one: GROUP
;; answers as for a group the node does not carry, every Message-ID form as
;; for an absent article.  O is the owner after the reconfiguration
;; (fn-own-config o is the configuration it published), CONN any of its
;; connections however long ago it pinned, AS the session at the command and
;; ARCHIVE the archive the command reads (the pin, or the view a GROUP
;; re-pinned it to).
(defthm fn-own-served-conn-refuses-what-the-live-rule-refuses
  (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
        (live (fn-sar-live-rule (fn-own-config o) (fn-auth-access-login as))))
    (implies (and (fn-nntp-session-projected (fn-auth-reader-session as))
                  live
                  (not (fn-gac-readablep live g)))
             (and (not (member-equal g (fn-state-groups
                                        (fn-auth-view-archive as c archive))))
                  (not (fn-auth-arts-name-groupp
                        g (fn-state-articles (fn-auth-view-archive as c archive)))))))
  :hints (("Goal" :in-theory (disable fn-sar-live-rule fn-auth-view-archive
                                      fn-gac-readablep fn-own-served-conn
                                      fn-auth-view-excludes-unreadable-groups-on-any-connection)
           :use ((:instance fn-sar-text-refuses-live
                            (pinned (fn-own-conn-config conn)) (live (fn-own-config o)))
                 (:instance fn-auth-view-excludes-unreadable-groups-on-any-connection
                            (config (fn-gac-config-with-live (fn-own-conn-config conn)
                                                             (fn-own-config o))))))))

;; And the pin still binds: a widening never reaches an open connection.
(defthm fn-own-served-conn-refuses-what-the-pin-refuses
  (let ((c (fn-served-conn-config (fn-own-served-conn o conn session)))
        (pin (fn-auth-rule-text
              (fn-gac-listing-table (fn-inj-config-listing (fn-own-conn-config conn)))
              (fn-inj-config-closed (fn-own-conn-config conn))
              (fn-auth-access-login as) 1)))
    (implies (and (fn-nntp-session-projected (fn-auth-reader-session as))
                  pin
                  (not (fn-gac-readablep pin g)))
             (and (not (member-equal g (fn-state-groups
                                        (fn-auth-view-archive as c archive))))
                  (not (fn-auth-arts-name-groupp
                        g (fn-state-articles (fn-auth-view-archive as c archive)))))))
  :hints (("Goal" :in-theory (disable fn-sar-live-rule fn-auth-view-archive fn-auth-rule-text
                                      fn-gac-readablep fn-own-served-conn
                                      fn-auth-view-excludes-unreadable-groups-on-any-connection)
           :use ((:instance fn-sar-text-refuses-pin
                            (pinned (fn-own-conn-config conn)) (live (fn-own-config o)))
                 (:instance fn-auth-view-excludes-unreadable-groups-on-any-connection
                            (config (fn-gac-config-with-live (fn-own-conn-config conn)
                                                             (fn-own-config o))))))))

;; When the live configuration grants the login what its pin grants, the
;; served rule IS the pinned one: a reconfiguration that does not touch the
;; session's access changes nothing it is served.
(defthm fn-own-served-conn-rule-is-the-pin-when-access-is-unchanged
  (implies (and (not (consp (fn-gac-listing-live
                              (fn-inj-config-listing (fn-own-conn-config conn)))))
                (equal (fn-sar-live-rule (fn-own-config o) (fn-auth-access-login as))
                  (fn-auth-rule-text
                   (fn-gac-listing-table (fn-inj-config-listing (fn-own-conn-config conn)))
                   (fn-inj-config-closed (fn-own-conn-config conn))
                   (fn-auth-access-login as) 1)))
           (equal (fn-auth-access-text
                   as (fn-served-conn-config (fn-own-served-conn o conn session)) 1)
                  (fn-auth-access-text as (fn-own-conn-config conn) 1)))
  :hints (("Goal" :in-theory (e/d (fn-gac-and-text)
                                  (fn-auth-access-text fn-auth-rule-text fn-sar-live-rule
                                   fn-own-served-conn))
           :expand ((fn-auth-access-text as (fn-own-conn-config conn) 1)))))
