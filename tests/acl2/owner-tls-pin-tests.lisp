; The host's one-pass TLS read carries the same historical verdict and
; Message-ID index as the ordinary owner read.  This uses a real accepted
; composite Store event and two readers opened on opposite sides of it.
(in-package "ACL2")
(include-book "owner-verdict-tests")
(include-book "../../books/owner-tls-prefix")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (fn-wire-statep
  (fn-own-conn-wire
   (fn-own-find-conn 2 (fn-own-conns *ov-reader-b*)))))
(defconst *otp-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record*)))
(defconst *otp-tls-b* (fn-ocfg-read-tls-prefix
                       (fn-ocfg-make *ov-reader-b* *otp-config* nil nil)
                       2 *ov-hdr*))
(defconst *otp-full-b* (fn-ocfg-read
                        (fn-ocfg-make *ov-reader-b* *otp-config* nil nil)
                        2 *ov-hdr*))
(assert-event (equal (fn-own-tls-result-effects *otp-tls-b*)
                     (car *otp-full-b*)))
(assert-event (equal (fn-own-tls-result-owner *otp-tls-b*)
                     (cdr *otp-full-b*)))
(assert-event
 (equal (fn-served-reply-octets (fn-own-tls-result-effects *otp-tls-b*))
        (fn-served-reply-octets (car *ov-read-b*))))

; Dropping the verdict pin used to turn the actual HDR into a 430.  This
; executable counterexample prevents the six-argument compatibility
; constructor from being substituted back into the TLS path.
(defconst *otp-conn-b*
  (fn-own-find-conn 2 (fn-own-conns *ov-reader-b*)))
(defconst *otp-unpinned*
  (fn-served-make-conn
   (fn-own-conn-wire *otp-conn-b*)
   (fn-own-conn-live-session *ov-reader-b* *otp-conn-b*)
   (fn-own-conn-archive *otp-conn-b*)
   (fn-own-conn-config *otp-conn-b*)
   (fn-own-conn-observation *otp-conn-b*)
   (fn-own-clock *ov-reader-b*)))
(assert-event
 (not (equal (fn-served-result-effects
              (fn-served-step *otp-unpinned* *ov-hdr*))
             (fn-own-tls-result-effects *otp-tls-b*))))
(must-fail
 (defthm otp-dropping-verdict-pin-is-equivalent
   (equal (fn-served-result-effects
           (fn-served-step *otp-unpinned* *ov-hdr*))
          (fn-own-tls-result-effects *otp-tls-b*))))
