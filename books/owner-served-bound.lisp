; fn: the served article bound the owner installs from its Store profile (PKT-103).
;
; Recovery installs each owner's posting configuration with the record
; codec's payload ceiling as its article bound (host/owner-host.lisp
; fn-owner-post-config: *fn-record-max-payload*, 4,261,412,864 octets),
; because the profile is not yet decoded there.  Only the operator run's
; control start (fn-owner-posting-configure) replaced it with the profile's
; A, so the developer `owner run' served every connection with the codec
; ceiling: a 40 KiB article on a store whose A is 32,768 passed the wire
; and was refused later with the unnamed "441 posting failed".
;
; The bound is now installed where the profile is: `fn-osb-install' is what
; host/owner-host.lisp `fn-owner-install-profile' calls, on every run path
; (host/native/owner.lisp fnn-owner-install, after recovery and before any
; connection opens).  It keeps the posting bit, the agent and the served
; groups and sets the article bound to the profile's A, which
; `fn-own-body-limit' hands every connection the owner opens afterwards
; (books/owner.lisp fn-own-open), so the wire closes an article past A with
; `:body-overlimit' and the reply names the size.

(in-package "ACL2")
(include-book "owner")
(include-book "store-budget-naming")

(defun fn-osb-config (cfg profile)
  "CFG with its article bound replaced by PROFILE's payload bound."
  (declare (xargs :guard t))
  (fn-inj-make-config (fn-inj-config-allow cfg)
                      (fn-inj-config-agent cfg)
                      (fn-inj-config-groups cfg)
                      (fn-sbud-payload-bound profile)))

(defun fn-osb-install (o profile)
  "(mv VERDICT OWNER): :installed and O with the served bound of PROFILE, or
:refused and O unchanged when PROFILE is not one a store may be served under."
  (declare (xargs :guard t))
  (if (fn-bs-profile-admittedp profile)
      (mv :installed (fn-own-configure o (fn-osb-config (fn-own-config o) profile)))
    (mv :refused o)))

(local
 (defthm fn-osb-own-config-of-configure
   (equal (fn-own-config (fn-own-configure o config)) config)
   :hints (("Goal" :in-theory (enable fn-own-configure fn-own-config fn-own-make)))))

(local
 (defthm fn-osb-admitted-article-bound
   (implies (fn-bs-profile-admittedp profile)
            (and (<= 1 (fn-bs-profile-max-article-octets profile))
                 (<= (fn-bs-profile-max-article-octets profile)
                     *fn-record-max-payload*)
                 (integerp (fn-bs-profile-max-article-octets profile))))
   :hints (("Goal" :use ((:instance fn-bs-profile-validp-codecs-accept
                                    (values profile) (kind 0)))
            :in-theory (union-theories
                        '((:type-prescription fn-bs-profile-max-article-octets))
                        (theory 'minimal-theory))))))

; KEYSTONE.  After an admitted profile is installed, every connection the
; owner opens reads the profile's A as its article bound: the served bound
; is the operator's, never the codec ceiling.
(defthm fn-osb-install-serves-the-profile-bound
  (implies (fn-bs-profile-admittedp profile)
           (and (equal (mv-nth 0 (fn-osb-install o profile)) :installed)
                (equal (fn-own-body-limit (mv-nth 1 (fn-osb-install o profile)))
                       (fn-bs-profile-max-article-octets profile))))
  :hints (("Goal" :in-theory (e/d (fn-sbud-payload-bound fn-own-body-limit)
                                  (fn-bs-profile-admittedp
                                   fn-bs-profile-max-article-octets
                                   fn-own-configure fn-own-config)))))

; Nothing else of the posting configuration moves: the posting bit, the
; injecting agent and the served groups are the ones recovery installed.
(defthm fn-osb-install-keeps-the-posting-configuration
  (let ((next (fn-own-config (mv-nth 1 (fn-osb-install o profile))))
        (cfg (fn-own-config o)))
    (and (equal (fn-inj-config-allow next) (fn-inj-config-allow cfg))
         (equal (fn-inj-config-agent next) (fn-inj-config-agent cfg))
         (equal (fn-inj-config-groups next) (fn-inj-config-groups cfg))))
  :hints (("Goal" :in-theory (disable fn-bs-profile-admittedp fn-sbud-payload-bound
                                      fn-own-configure fn-own-config))))

; A well-formed posting configuration stays one (the bound is within
; *fn-article-max-octets*, the record codec's payload ceiling).
(defthm fn-osb-install-keeps-configp
  (implies (fn-inj-configp (fn-own-config o))
           (fn-inj-configp (fn-own-config (mv-nth 1 (fn-osb-install o profile)))))
  :hints (("Goal" :in-theory (e/d (fn-sbud-payload-bound fn-inj-configp)
                                  (fn-bs-profile-admittedp
                                   fn-bs-profile-max-article-octets
                                   fn-own-configure fn-own-config)))))

; A profile that is not admitted installs nothing.
(defthm fn-osb-install-refuses-unadmitted-by-definition
  (implies (not (fn-bs-profile-admittedp profile))
           (equal (fn-osb-install o profile) (mv :refused o)))
  :hints (("Goal" :in-theory (union-theories '(fn-osb-install)
                                             (theory 'minimal-theory)))))
