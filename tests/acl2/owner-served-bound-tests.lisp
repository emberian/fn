; Witnesses and teeth for books/owner-served-bound.lisp: the served article
; bound installed with the Store profile.  The subject is fn-osb-install,
; which host/owner-host.lisp fn-owner-install-profile calls (from
; host/native/owner.lisp fnn-owner-install, on every run path).

(in-package "ACL2")
(include-book "../../books/owner-served-bound")
(include-book "std/testing/must-fail" :dir :system)

(defun osbt-text (s) (fn-record-string-octets s))

; The owner recovery leaves: the posting configuration with the record
; codec's payload ceiling as its bound (host/owner-host.lisp
; fn-owner-post-config).
(defconst *osbt-recovered-config*
  (fn-inj-make-config t (osbt-text "hbox.ember.software")
                      (list (osbt-text "fn.test")) *fn-record-max-payload*))
(defconst *osbt-owner* (fn-own-configure nil *osbt-recovered-config*))
(assert-event (fn-inj-configp *osbt-recovered-config*))
(assert-event (equal (fn-own-body-limit *osbt-owner*) 4261412864))

; The development profile (A = 32,768): after the install every connection
; the owner opens reads 32,768, so a 40 KiB article is closed at the wire.
(assert-event (fn-bs-profile-admittedp *fn-bs-profile-development*))
(assert-event
 (mv-let (verdict next) (fn-osb-install *osbt-owner* *fn-bs-profile-development*)
   (and (equal verdict :installed)
        (equal (fn-own-body-limit next) 32768)
        (fn-inj-configp (fn-own-config next))
        (equal (fn-inj-config-agent (fn-own-config next))
               (osbt-text "hbox.ember.software")))))
; An operator profile (the D27 defaults) with A = 65,536: the bound follows the profile.
(defconst *osbt-large*
  (fn-bs-profile-resolve (list :default (list (cons *fn-bs-pf-max-article-octets* 65536)))
                         nil))
(assert-event (fn-bs-profile-admittedp *osbt-large*))
(assert-event
 (mv-let (verdict next) (fn-osb-install *osbt-owner* *osbt-large*)
   (and (equal verdict :installed)
        (equal (fn-own-body-limit next) 65536))))

; Teeth.  Without the admission hypothesis the keystone fails: a value that
; is not a profile installs nothing and the codec ceiling stays.
(assert-event
 (mv-let (verdict next) (fn-osb-install *osbt-owner* nil)
   (and (equal verdict :refused)
        (equal (fn-own-body-limit next) 4261412864))))
(must-fail
 (defthm osbt-serves-the-profile-bound-without-admission
   (and (equal (mv-nth 0 (fn-osb-install o profile)) :installed)
        (equal (fn-own-body-limit (mv-nth 1 (fn-osb-install o profile)))
               (fn-bs-profile-max-article-octets profile)))
   :hints (("Goal" :in-theory (e/d (fn-sbud-payload-bound fn-own-body-limit)
                                   (fn-bs-profile-admittedp
                                    fn-bs-profile-max-article-octets
                                    fn-own-configure fn-own-config))))))
; Without a well-formed configuration before, none after: the agent is the
; configuration's, and a malformed one stays malformed.
(assert-event
 (mv-let (verdict next) (fn-osb-install (fn-own-configure nil nil)
                                        *fn-bs-profile-development*)
   (and (equal verdict :installed)
        (not (fn-inj-configp (fn-own-config next))))))
(must-fail
 (defthm osbt-keeps-configp-without-configp
   (fn-inj-configp (fn-own-config (mv-nth 1 (fn-osb-install o profile))))
   :hints (("Goal" :in-theory (e/d (fn-sbud-payload-bound fn-inj-configp)
                                   (fn-bs-profile-admittedp
                                    fn-bs-profile-max-article-octets
                                    fn-own-configure fn-own-config))))))
