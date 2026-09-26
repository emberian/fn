; Fold invariants for the host-called served port.  A no-posting credential
; does not forbid an independently authorized peer transfer, so the property
; here distinguishes local injection from transit submission.
(in-package "ACL2")
(include-book "nntp-auth-invariants")

(local
 (defthm fn-auth-fold-authinfo-keeps-the-config
   (equal (fn-auth-session-config
           (fn-post-result-session (fn-auth-authinfo as args)))
          (fn-auth-session-config as))
   :hints (("Goal"
            :in-theory
            (e/d (fn-auth-authinfo fn-auth-bind-principal-peer
                   fn-auth-with-base)
                 (fn-auth-single fn-auth-find-cred fn-auth-checkp
                  fn-auth-token-argp fn-nntp-keywordp
                  fn-auth-principal-match fn-node-statep))))))

(local
 (defthm fn-auth-fold-starttls-keeps-the-config
   (equal (fn-auth-session-config
           (fn-post-result-session (fn-auth-starttls as args)))
          (fn-auth-session-config as))
   :hints (("Goal"
            :in-theory
            (e/d (fn-auth-starttls fn-auth-clear-principal-peer
                   fn-auth-with-base)
                 (fn-auth-single fn-auth-principal-rolep))))))

(local
 (defthm fn-auth-fold-command-keeps-the-config
   (implies (fn-auth-command as config keyword args)
            (equal (fn-auth-session-config
                    (fn-post-result-session
                     (fn-auth-command as config keyword args)))
                   (fn-auth-session-config as)))
   :hints (("Goal"
            :in-theory
            (e/d (fn-auth-command)
                 (fn-auth-authinfo fn-auth-starttls fn-auth-single
                  fn-auth-gatedp fn-auth-postingp fn-nntp-keywordp
                  fn-nntp-keyword-tokenp fn-nntp-multi
                  fn-auth-capability-lines-for-peer fn-auth-peer-record
                  fn-inj-config-allow))))))

(defthm fn-auth-step-pinned-preserves-the-config
  (equal (fn-auth-session-config
          (fn-post-result-session
           (fn-auth-step-pinned as archive index verdicts config observation
                                injection wire-event)))
         (fn-auth-session-config as))
  :hints (("Goal"
           :do-not-induct t
           :in-theory
           (e/d (fn-auth-step-pinned fn-auth-delegate-pinned
                  fn-auth-tls-eventp fn-auth-tls-established fn-auth-with-base)
                (fn-peer-step-pinned fn-auth-command fn-auth-authinfo
                 fn-auth-starttls fn-auth-sessionp fn-nntp-tokenize
                 fn-nntp-command-inputp fn-nntp-keyword-tokenp
                 fn-nntp-command-arguments-at-mostp)))))

(defthm fn-post-step-pinned-without-awaiting-submits-nothing
  (implies (not (fn-post-session-awaiting ps))
           (not (fn-post-result-submission
                 (fn-nntp-post-step-pinned
                  ps archive index verdicts config observation injection
                  wire-event))))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-post-step-pinned fn-nntp-post-step)
                           (fn-nntp-step-pinned
                            fn-post-offeredp)))))

(defthm fn-post-step-pinned-starts-awaiting-only-on-offer
  (implies (and (fn-post-sessionp ps)
                (not (fn-post-session-awaiting ps))
                (fn-post-session-awaiting
                 (fn-post-result-session
                  (fn-nntp-post-step-pinned
                   ps archive index verdicts config observation injection
                   wire-event))))
           (fn-post-offeredp
            (fn-post-result-effects
             (fn-nntp-post-step-pinned
              ps archive index verdicts config observation injection
              wire-event))))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-post-step-pinned)
                           (fn-nntp-step-pinned fn-nntp-post-step
                            fn-post-offeredp)))))

(defthm fn-auth-fold-single-has-no-offer
  (not (fn-post-offeredp
        (fn-nntp-result-effects (fn-nntp-single session text))))
  :hints (("Goal" :in-theory (enable fn-nntp-single fn-post-offeredp
                                      fn-nntp-reply-effect
                                      fn-nntp-begin-article-effect))))

(defthm fn-auth-fold-multi-has-no-offer
  (not (fn-post-offeredp
        (fn-nntp-result-effects (fn-nntp-multi session initial lines))))
  :hints (("Goal" :in-theory (enable fn-nntp-multi fn-post-offeredp
                                      fn-nntp-reply-effect
                                      fn-nntp-begin-article-effect))))

(defthm fn-auth-fold-multi-octets-has-no-offer
  (not (fn-post-offeredp
        (fn-nntp-result-effects
         (fn-nntp-multi-octets session initial lines))))
  :hints (("Goal" :in-theory (enable fn-nntp-multi-octets
                                      fn-post-offeredp
                                      fn-nntp-reply-effect
                                      fn-nntp-begin-article-effect))))

(defthm fn-auth-fold-session-command-offers-only-post
  (implies (not (fn-nntp-keywordp keyword "POST"))
           (not (fn-post-offeredp
                 (fn-nntp-result-effects
                  (fn-nntp-session-command session env keyword args)))))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-session-command fn-post-offeredp
                            fn-nntp-capabilities fn-nntp-help
                            fn-nntp-mode-response fn-nntp-date-response
                            fn-nntp-single fn-nntp-reply-effect)
                           (fn-nntp-keywordp fn-nntp-capability-lines
                            fn-nntp-multi
                            fn-nntp-crlf)))))

(defthm fn-auth-fold-archive-command-has-no-offer
  (not (fn-post-offeredp
        (fn-nntp-result-effects
         (fn-nntp-archive-command session archive env keyword args))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory
           (e/d (fn-nntp-archive-command fn-post-offeredp
                  fn-nntp-reply-effect
                  fn-nntp-group-result fn-nntp-listgroup-command
                  fn-nntp-listgroup-result
                  fn-nntp-list-command fn-nntp-list-response
                  fn-nntp-list-counts-command fn-nntp-list-counts
                  fn-nntp-list-active fn-nntp-list-active-times
                  fn-nntp-list-active-or-newsgroups
                  fn-nntp-list-newsgroups
                  fn-nntp-list-filtered-response
                  fn-nntp-list-unmaintained-response
                  fn-nntp-list-overview-fmt
                  fn-nntp-list-headers
                  fn-nntp-next-or-last
                  fn-nntp-retrieval fn-nntp-number-retrieval
                  fn-nntp-msgid-retrieval fn-nntp-article-response
                  fn-nntp-current-retrieval
                  fn-nntp-over-response fn-nntp-over-range
                  fn-nntp-over-msgid fn-nntp-over-current
                  fn-nntp-xover-response fn-nntp-xover-range
                  fn-nntp-hdr-response fn-nntp-hdr-command
                  fn-nntp-hdr-current fn-nntp-hdr-range fn-nntp-hdr-msgid
                  fn-nntp-xhdr-response fn-nntp-xpat-response
                  fn-nntp-xpat-range fn-nntp-xpat-msgid
                  fn-nntp-newgroups-response fn-nntp-newnews-response)
                (fn-nntp-single fn-nntp-multi fn-nntp-multi-octets
                 fn-nntp-keywordp fn-nntp-stuff-lines
                 fn-nntp-crlf fn-nntp-string-octets)))))

(defthm fn-auth-fold-gidx-list-counts-has-no-offer
  (not (fn-post-offeredp
        (fn-nntp-result-effects
         (fn-gidx-list-counts-command session archive buckets args))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-gidx-list-counts-command)
                           (fn-gidx-counts-lines fn-post-offeredp
                            fn-nntp-filter-groups-by-wildmat fn-wildmat-parse
                            fn-nntp-single fn-nntp-multi)))))

(defthm fn-auth-fold-control-hdr-response-has-no-offer
  (not (fn-post-offeredp
        (fn-nntp-result-effects
         (fn-nntp-control-hdr-response session archive index verdicts args))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-control-hdr-response fn-post-offeredp
                                   fn-nntp-reply-effect)
                                  (fn-nntp-single fn-nntp-multi
                                   fn-ctl-control-item fn-ctl-served-status
                                   fn-ctl-served-held fn-nntp-string-octets
                                   fn-nntp-control-cleanp fn-nntp-hdr-line
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-ctl-pin-withdrawn fn-ctl-pin-ws
                                   fn-nntp-token-string fn-ctl-target-octets
                                   fn-octet-listp)))))

(defthm fn-auth-fold-enrollment-hdr-response-has-no-offer
  (not (fn-post-offeredp
        (fn-nntp-result-effects
         (fn-nntp-enrollment-hdr-response session archive index verdicts args))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-enrollment-hdr-response fn-post-offeredp
                                   fn-nntp-reply-effect)
                                  (fn-nntp-single fn-nntp-multi
                                   fn-enr-item fn-stx-reader-lookup fn-midx-lookup
                                   fn-nntp-hdr-line
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-nntp-token-string fn-octet-listp)))))

(defthm fn-auth-fold-archive-command-pinned-has-no-offer
  (not (fn-post-offeredp
        (fn-nntp-result-effects
         (fn-nntp-archive-command-pinned
          session archive index verdicts env keyword args))))
  :hints (("Goal" :do-not-induct t
           :in-theory
           (e/d (fn-nntp-archive-command-pinned
                  fn-nntp-msgid-retrieval-indexed
                  fn-nntp-verdict-hdr-response fn-post-offeredp
                  fn-nntp-reply-effect fn-nntp-article-response
                  fn-nntp-withdrawn-reply)
                (fn-nntp-single fn-nntp-multi fn-nntp-multi-octets
                 fn-nntp-archive-command fn-nntp-keywordp
                 fn-nntp-stuff-lines fn-nntp-crlf)))))

(defthm fn-auth-fold-command-pinned-offers-only-post
  (implies (not (fn-nntp-keywordp (car tokens) "POST"))
           (not (fn-post-offeredp
                 (fn-nntp-result-effects
                  (fn-nntp-command-pinned session archive index verdicts
                                          env tokens)))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-command-pinned)
                (fn-nntp-session-command
                 fn-nntp-archive-command-pinned fn-post-offeredp
                 fn-nntp-keywordp fn-nntp-archive-keywordp)))))

(defthm fn-auth-fold-command-pinned-offer-has-keyword
  (implies
   (fn-post-offeredp
    (fn-nntp-result-effects
     (fn-nntp-command-pinned session archive index verdicts env tokens)))
   (fn-nntp-keyword-tokenp (car tokens)))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-command-pinned)
                (fn-nntp-session-command fn-nntp-archive-command-pinned
                 fn-nntp-keywordp fn-nntp-archive-keywordp
                 fn-post-offeredp)))))

(defthm fn-auth-fold-reader-offer-has-a-post-command-origin
  (implies
   (fn-post-offeredp
    (fn-nntp-result-effects
     (fn-nntp-step-pinned session archive index verdicts env wire-event)))
   (and (consp wire-event)
        (equal (car wire-event) :command)
        (consp (cdr wire-event))
        (null (cddr wire-event))
        (fn-nntp-command-inputp (cadr wire-event))
        (consp (fn-nntp-tokenize (cadr wire-event)))
        (fn-nntp-keyword-tokenp
         (car (fn-nntp-tokenize (cadr wire-event))))
        (fn-nntp-command-arguments-at-mostp
         (fn-nntp-tokenize (cadr wire-event)))
        (fn-nntp-keywordp
         (car (fn-nntp-tokenize (cadr wire-event))) "POST")))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-step-pinned)
                (fn-nntp-command-pinned fn-post-offeredp
                 fn-nntp-tokenize fn-nntp-keywordp
                 fn-nntp-command-inputp fn-nntp-single)))))

(defthm fn-auth-fold-post-awaiting-implies-reader-offer
  (implies
   (and (fn-post-sessionp ps)
        (not (fn-post-session-awaiting ps))
        (fn-post-session-awaiting
         (fn-post-result-session
          (fn-nntp-post-step-pinned
           ps archive index verdicts config observation injection
           wire-event))))
   (fn-post-offeredp
    (fn-nntp-result-effects
     (fn-nntp-step-pinned
      (fn-post-session-base ps) archive index verdicts
      (fn-nntp-env observation nil (and (fn-inj-config-allow config) t))
      wire-event))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-post-step-pinned)
                (fn-nntp-step-pinned fn-post-offeredp
                 fn-nntp-post-step)))))

(defthm fn-auth-fold-post-step-starts-awaiting-only-on-post
  (implies
   (and (fn-post-sessionp ps)
        (not (fn-post-session-awaiting ps))
        (fn-post-session-awaiting
         (fn-post-result-session
          (fn-nntp-post-step-pinned
           ps archive index verdicts config observation injection
           wire-event))))
   (and (consp wire-event)
        (equal (car wire-event) :command)
        (consp (cdr wire-event))
        (null (cddr wire-event))
        (fn-nntp-command-inputp (cadr wire-event))
        (consp (fn-nntp-tokenize (cadr wire-event)))
        (fn-nntp-keyword-tokenp
         (car (fn-nntp-tokenize (cadr wire-event))))
        (fn-nntp-command-arguments-at-mostp
         (fn-nntp-tokenize (cadr wire-event)))
        (fn-nntp-keywordp
         (car (fn-nntp-tokenize (cadr wire-event))) "POST")))
  :hints (("Goal"
           :use ((:instance fn-auth-fold-reader-offer-has-a-post-command-origin
                            (session (fn-post-session-base ps))
                            (env (fn-nntp-env
                                  observation nil
                                  (and (fn-inj-config-allow config) t)))))
           :in-theory (disable fn-nntp-post-step-pinned
                               fn-nntp-step-pinned fn-post-offeredp))))

(defthm fn-auth-fold-peer-command-keeps-reader-session
  (implies (fn-peer-command ps keyword args)
           (equal (fn-peer-reader-session
                   (fn-post-result-session
                    (fn-peer-command ps keyword args)))
                  (fn-peer-reader-session ps)))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-command fn-peer-with-transfer)
                (fn-peer-decide-offer fn-peer-single
                 fn-peer-echo-reply fn-peer-capability-lines
                 fn-nntp-keywordp fn-nntp-multi)))))

(defthm fn-auth-fold-peer-command-keeps-post-awaiting
  (implies (fn-peer-command ps keyword args)
           (equal (fn-post-session-awaiting
                   (fn-peer-session-base
                    (fn-post-result-session
                     (fn-peer-command ps keyword args))))
                  (fn-post-session-awaiting (fn-peer-session-base ps))))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-command fn-peer-with-transfer)
                (fn-peer-decide-offer fn-peer-single
                 fn-peer-echo-reply fn-peer-capability-lines
                 fn-nntp-keywordp fn-nntp-multi)))))

(defthm fn-auth-fold-peer-transfer-keeps-reader-session
  (implies (and (fn-peer-sessionp ps)
                (fn-peer-session-peer ps)
                (equal (fn-nntp-session-openp
                        (fn-peer-reader-session ps)) t)
                (fn-peer-session-transfer ps))
           (equal
            (fn-peer-reader-session
             (fn-post-result-session
              (fn-peer-step ps archive config observation injection
                            wire-event)))
            (fn-peer-reader-session ps)))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-step fn-peer-with-transfer)
                (fn-peer-delegate fn-peer-command
                 fn-post-body-octets fn-peer-make-submission
                 fn-nntp-keywordp fn-nntp-tokenize)))))

(defthm fn-auth-fold-peer-transfer-keeps-post-awaiting
  (implies (and (fn-peer-sessionp ps)
                (fn-peer-session-peer ps)
                (equal (fn-nntp-session-openp
                        (fn-peer-reader-session ps)) t)
                (fn-peer-session-transfer ps))
           (equal
            (fn-post-session-awaiting
             (fn-peer-session-base
              (fn-post-result-session
               (fn-peer-step ps archive config observation injection
                             wire-event))))
            (fn-post-session-awaiting (fn-peer-session-base ps))))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-step fn-peer-with-transfer)
                (fn-peer-delegate fn-peer-command
                 fn-post-body-octets fn-peer-make-submission
                 fn-nntp-keywordp fn-nntp-tokenize)))))

(defthm fn-auth-fold-peer-delegate-starts-post-awaiting-only-on-post
  (implies
   (and (fn-peer-sessionp ps)
        (not (fn-post-session-awaiting (fn-peer-session-base ps)))
        (fn-post-session-awaiting
         (fn-peer-session-base
          (fn-post-result-session
           (fn-peer-delegate-pinned
            ps archive index verdicts config observation injection
            wire-event)))))
   (and (consp wire-event)
        (equal (car wire-event) :command)
        (consp (cdr wire-event))
        (null (cddr wire-event))
        (fn-nntp-command-inputp (cadr wire-event))
        (consp (fn-nntp-tokenize (cadr wire-event)))
        (fn-nntp-keyword-tokenp
         (car (fn-nntp-tokenize (cadr wire-event))))
        (fn-nntp-command-arguments-at-mostp
         (fn-nntp-tokenize (cadr wire-event)))
        (fn-nntp-keywordp
         (car (fn-nntp-tokenize (cadr wire-event))) "POST")))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-delegate-pinned fn-peer-with-base)
                (fn-nntp-post-step-pinned fn-nntp-step-pinned
                 fn-nntp-keywordp fn-nntp-tokenize))
           :use ((:instance fn-auth-fold-post-step-starts-awaiting-only-on-post
                            (ps (fn-peer-session-base ps)))))))

(defthm fn-auth-fold-peer-step-starts-post-awaiting-only-on-post
  (implies
   (and (fn-peer-sessionp ps)
        (not (fn-post-session-awaiting (fn-peer-session-base ps)))
        (fn-post-session-awaiting
         (fn-peer-session-base
          (fn-post-result-session
           (fn-peer-step-pinned
            ps archive index verdicts config observation injection
            wire-event)))))
   (and (consp wire-event)
        (equal (car wire-event) :command)
        (consp (cdr wire-event))
        (null (cddr wire-event))
        (fn-nntp-command-inputp (cadr wire-event))
        (consp (fn-nntp-tokenize (cadr wire-event)))
        (fn-nntp-keyword-tokenp
         (car (fn-nntp-tokenize (cadr wire-event))))
        (fn-nntp-command-arguments-at-mostp
         (fn-nntp-tokenize (cadr wire-event)))
        (fn-nntp-keywordp
         (car (fn-nntp-tokenize (cadr wire-event))) "POST")))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-step-pinned)
                (fn-peer-delegate-pinned fn-peer-step fn-peer-command
                 fn-nntp-tokenize fn-nntp-keywordp))
           :use ((:instance fn-auth-fold-peer-delegate-starts-post-awaiting-only-on-post)
                 (:instance fn-auth-fold-peer-transfer-keeps-post-awaiting)
                 (:instance fn-auth-fold-peer-command-keeps-post-awaiting
                            (keyword (car (fn-nntp-tokenize (cadr wire-event))))
                            (args (cdr (fn-nntp-tokenize (cadr wire-event)))))))))

(defthm fn-auth-fold-auth-delegate-starts-post-awaiting-only-on-post
  (implies
   (and (fn-auth-sessionp as)
        (not (fn-post-session-awaiting
              (fn-peer-session-base (fn-auth-session-base as))))
        (fn-post-session-awaiting
         (fn-peer-session-base
          (fn-auth-session-base
           (fn-post-result-session
            (fn-auth-delegate-pinned
             as archive index verdicts config observation injection
             wire-event))))))
   (fn-served-post-command-eventp wire-event))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-delegate-pinned fn-auth-with-base
                            fn-served-post-command-eventp fn-auth-sessionp)
                           (fn-peer-step-pinned fn-nntp-tokenize
                            fn-nntp-keywordp))
           :use ((:instance fn-auth-fold-peer-step-starts-post-awaiting-only-on-post
                            (ps (fn-auth-session-base as)))))))

(defun fn-auth-fold-post-awaiting (as)
  (declare (xargs :guard t))
  (fn-post-session-awaiting
   (fn-peer-session-base (fn-auth-session-base as))))

; PRF-164: XREDEEM keeps the base session (fn-auth-xredeem-keeps-the-config-
; base-and-subject), hence the POST state under it.
(local
 (defthm fn-auth-fold-xredeem-keeps-post-awaiting
   (equal (fn-auth-fold-post-awaiting
           (fn-post-result-session (fn-auth-xredeem as args)))
          (fn-auth-fold-post-awaiting as))
   :hints (("Goal" :in-theory (enable fn-auth-fold-post-awaiting)))))

(local
 (defthm fn-auth-fold-authinfo-keeps-post-awaiting
   (equal (fn-auth-fold-post-awaiting
           (fn-post-result-session (fn-auth-authinfo as args)))
          (fn-auth-fold-post-awaiting as))
   :hints (("Goal" :in-theory
            (e/d (fn-auth-authinfo fn-auth-bind-principal-peer
                   fn-auth-with-base fn-auth-fold-post-awaiting)
                 (fn-auth-single fn-auth-find-cred fn-auth-checkp
                  fn-auth-token-argp fn-nntp-keywordp
                  fn-auth-principal-match fn-node-statep))))))

(local
 (defthm fn-auth-fold-starttls-keeps-post-awaiting
   (equal (fn-auth-fold-post-awaiting
           (fn-post-result-session (fn-auth-starttls as args)))
          (fn-auth-fold-post-awaiting as))
   :hints (("Goal" :in-theory
            (e/d (fn-auth-starttls fn-auth-clear-principal-peer
                   fn-auth-with-base fn-auth-fold-post-awaiting)
                 (fn-auth-single fn-auth-principal-rolep))))))

(local
 (defthm fn-auth-fold-command-keeps-post-awaiting
   (implies (fn-auth-command as config keyword args)
            (equal (fn-auth-fold-post-awaiting
                    (fn-post-result-session
                     (fn-auth-command as config keyword args)))
                   (fn-auth-fold-post-awaiting as)))
   :hints (("Goal" :in-theory
            (e/d (fn-auth-command)
                 (fn-auth-authinfo fn-auth-starttls fn-auth-single
                  fn-auth-fold-post-awaiting
                  fn-auth-gatedp fn-auth-postingp fn-nntp-keywordp
                  fn-nntp-keyword-tokenp fn-nntp-multi
                  fn-auth-capability-lines-for-peer fn-auth-peer-record
                  fn-inj-config-allow))))))

(defthm fn-auth-fold-auth-step-starts-post-awaiting-only-on-post
  (implies
   (and (fn-auth-sessionp as)
        (not (fn-auth-fold-post-awaiting as))
        (fn-auth-fold-post-awaiting
         (fn-post-result-session
          (fn-auth-step-pinned
           as archive index verdicts config observation injection
           wire-event))))
   (fn-served-post-command-eventp wire-event))
  :hints (("Goal"
           :in-theory
           (e/d (fn-auth-step-pinned fn-auth-tls-eventp
                  fn-auth-tls-established
                  fn-auth-fold-post-awaiting)
                (fn-auth-delegate-pinned fn-auth-command
                 fn-auth-authinfo fn-auth-starttls
                 fn-nntp-tokenize
                 fn-nntp-keywordp fn-nntp-command-inputp
                 fn-nntp-keyword-tokenp
                 fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-auth-fold-auth-delegate-starts-post-awaiting-only-on-post)
                 (:instance fn-auth-fold-command-keeps-post-awaiting
                            (keyword (car (fn-nntp-tokenize (cadr wire-event))))
                            (args (cdr (fn-nntp-tokenize (cadr wire-event)))))))))

(defthm fn-auth-fold-auth-step-no-posters-preserves-no-post-awaiting
  (implies
   (and (fn-auth-sessionp as)
        (fn-auth-config-no-postersp (fn-auth-session-config as))
        (not (fn-auth-fold-post-awaiting as)))
   (not
    (fn-auth-fold-post-awaiting
     (fn-post-result-session
      (fn-auth-step-pinned
       as archive index verdicts config observation injection
       wire-event)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-tls-eventp
                            fn-auth-tls-established
                            fn-auth-fold-post-awaiting
                            fn-served-post-command-eventp)
                           (fn-auth-delegate-pinned fn-auth-command
                            fn-auth-postingp fn-nntp-tokenize))
           :use ((:instance fn-auth-fold-auth-step-starts-post-awaiting-only-on-post)
                 (:instance fn-auth-no-posters-means-no-posting)
                 (:instance fn-auth-step-pinned-post-without-permission-is-not-offered
                            (line (cadr wire-event)))))))

(defthm fn-auth-fold-peer-delegate-no-local-submission
  (implies
   (not (fn-post-session-awaiting (fn-peer-session-base ps)))
   (not (fn-post-result-submission
         (fn-peer-delegate-pinned
          ps archive index verdicts config observation injection
          wire-event))))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-delegate-pinned)
                (fn-nntp-post-step-pinned)))))

(defthm fn-auth-fold-peer-command-no-submission
  (not (fn-post-result-submission (fn-peer-command ps keyword args)))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-command)
                (fn-peer-decide-offer fn-peer-single
                 fn-peer-echo-reply fn-peer-capability-lines
                 fn-nntp-keywordp fn-nntp-multi)))))

(defthm fn-auth-fold-peer-transfer-no-local-submission
  (implies (and (fn-peer-sessionp ps)
                (fn-peer-session-peer ps)
                (equal (fn-nntp-session-openp
                        (fn-peer-reader-session ps)) t)
                (fn-peer-session-transfer ps))
           (not (fn-inj-injectedp
                 (fn-post-result-submission
                  (fn-peer-step ps archive config observation injection
                                wire-event)))))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-step fn-peer-make-submission
                  fn-inj-injectedp fn-inj-decision-status fn-inj-nth
                  fn-inj-car)
                (fn-peer-delegate fn-peer-command
                 fn-post-body-octets
                 fn-nntp-keywordp fn-nntp-tokenize)))))

(defthm fn-auth-fold-peer-step-no-local-submission
  (implies
   (and (fn-peer-sessionp ps)
        (not (fn-post-session-awaiting (fn-peer-session-base ps))))
   (not (fn-inj-injectedp
         (fn-post-result-submission
          (fn-peer-step-pinned
           ps archive index verdicts config observation injection
           wire-event)))))
  :hints (("Goal" :in-theory
           (e/d (fn-peer-step-pinned)
                (fn-peer-delegate-pinned fn-peer-step
                 fn-peer-command fn-nntp-tokenize
                 fn-nntp-keywordp))
           :use ((:instance fn-auth-fold-peer-transfer-no-local-submission)
                 (:instance fn-auth-fold-peer-command-no-submission
                            (keyword (car (fn-nntp-tokenize (cadr wire-event))))
                            (args (cdr (fn-nntp-tokenize (cadr wire-event)))))))))

(local
 (defthm fn-auth-fold-starttls-no-submission
   (not (fn-post-result-submission (fn-auth-starttls as args)))
   :hints (("Goal" :in-theory
            (e/d (fn-auth-starttls)
                 (fn-auth-clear-principal-peer fn-auth-single))))))

(defthm fn-auth-fold-auth-command-no-submission
  (not (fn-post-result-submission
        (fn-auth-command as config keyword args)))
  :hints (("Goal" :in-theory
           (e/d (fn-auth-command)
                (fn-auth-authinfo fn-auth-starttls fn-auth-single
                 fn-auth-gatedp fn-auth-postingp fn-nntp-keywordp
                 fn-nntp-keyword-tokenp fn-nntp-multi
                 fn-auth-capability-lines-for-peer fn-auth-peer-record
                 fn-inj-config-allow)))))

(defthm fn-auth-fold-auth-step-no-local-submission
  (implies
   (and (fn-auth-sessionp as)
        (not (fn-auth-fold-post-awaiting as)))
   (not (fn-inj-injectedp
         (fn-post-result-submission
          (fn-auth-step-pinned
           as archive index verdicts config observation injection
           wire-event)))))
  :hints (("Goal" :in-theory
           (e/d (fn-auth-step-pinned fn-auth-delegate-pinned
                  fn-auth-with-base fn-auth-fold-post-awaiting
                  fn-auth-tls-eventp fn-auth-tls-established
                  fn-auth-sessionp)
                (fn-peer-step-pinned fn-auth-command
                 fn-nntp-tokenize fn-nntp-keywordp))
           :use ((:instance fn-auth-fold-peer-step-no-local-submission
                            (ps (fn-auth-session-base as)))))))

(defun fn-auth-fold-safe-connp (conn)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-served-connp conn)
       (fn-auth-config-no-postersp
        (fn-auth-session-config (fn-served-conn-session conn)))
       (not (fn-auth-fold-post-awaiting
             (fn-served-conn-session conn)))))

(defun fn-auth-fold-no-local-effectsp (effects)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp effects)
      (and (not (and (consp (car effects))
                     (equal (caar effects) :submit)
                     (fn-inj-injectedp (cadar effects))))
           (fn-auth-fold-no-local-effectsp (cdr effects)))
    t))

(defthm fn-auth-fold-no-local-effectsp-of-append
  (equal (fn-auth-fold-no-local-effectsp (append left right))
         (and (fn-auth-fold-no-local-effectsp left)
              (fn-auth-fold-no-local-effectsp right))))

(defthm fn-auth-fold-nntp-effectsp-no-local-submission
  (implies (fn-auth-effectsp effects)
           (fn-auth-fold-no-local-effectsp effects))
  :hints (("Goal" :induct (fn-auth-fold-no-local-effectsp effects)
           :in-theory (e/d (fn-auth-effectsp fn-auth-effectp
                            fn-nntp-effectp fn-auth-fold-no-local-effectsp
                            fn-nntp-close-effect fn-nntp-begin-article-effect
                            fn-auth-starttls-effect)
                           (fn-nntp-replyp fn-octet-listp)))))

(defthm fn-auth-fold-dispatch-preserves-safe-connp
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-safe-connp
            (fn-served-result-conn (fn-served-dispatch conn event))))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-fold-safe-connp fn-served-dispatch)
                           (fn-served-connp fn-auth-step-pinned
                            fn-served-conn-pinned-index fn-gidx-pin-correspondencep
                            fn-gidx-pin-trie fn-gidx-pinp
                            fn-midx-correspondencep
                            fn-served-connp-is-group-correspondence
                            fn-served-connp-is-pinned-trie-correspondence
                            fn-auth-fold-post-awaiting
                            fn-auth-config-no-postersp
                            fn-wire-begin-article-with-line-limit))
           :use ((:instance fn-served-dispatch-preserves-connp)
                 (:instance fn-served-connp-is-consistent-session
                            (c conn))
                 (:instance fn-served-connp-is-group-correspondence (c conn))
                 (:instance fn-served-connp-is-pinned-trie-correspondence (c conn))
                 (:instance fn-auth-consistent-forward
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn)))
                 (:instance fn-auth-step-pinned-preserves-the-config
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))
                 (:instance fn-auth-fold-auth-step-no-posters-preserves-no-post-awaiting
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))))))

(defthm fn-auth-fold-dispatch-has-no-local-submission
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-no-local-effectsp
            (fn-served-result-effects (fn-served-dispatch conn event))))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-fold-safe-connp fn-served-dispatch
                            fn-served-submit-effect
                            fn-auth-fold-no-local-effectsp)
                           (fn-served-connp fn-auth-step-pinned
                            fn-served-conn-pinned-index fn-gidx-pin-correspondencep
                            fn-gidx-pin-trie fn-gidx-pinp
                            fn-midx-correspondencep
                            fn-served-connp-is-group-correspondence
                            fn-served-connp-is-pinned-trie-correspondence
                            fn-auth-fold-post-awaiting
                            fn-auth-effectsp fn-nntp-effectp
                            fn-wire-begin-article-with-line-limit))
           :use ((:instance fn-served-connp-is-consistent-session
                            (c conn))
                 (:instance fn-served-connp-is-group-correspondence (c conn))
                 (:instance fn-served-connp-is-pinned-trie-correspondence (c conn))
                 (:instance fn-auth-consistent-forward
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn)))
                 (:instance fn-auth-step-pinned-effects-well-formed
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))
                 (:instance fn-auth-fold-auth-step-no-local-submission
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))
                 (:instance fn-auth-fold-nntp-effectsp-no-local-submission
                            (effects
                             (fn-post-result-effects
                              (fn-auth-step-pinned
                               (fn-served-conn-session conn)
                               (fn-served-conn-archive conn)
                               (fn-served-conn-pinned-index conn)
                               (fn-served-conn-verdicts conn)
                               (fn-served-conn-config conn)
                               (fn-served-conn-observation conn)
                               (fn-served-conn-injection conn)
                               event))))))))

(defthm fn-auth-fold-dispatch-events-preserves-safe-connp
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-safe-connp
            (fn-served-result-conn
             (fn-served-dispatch-events conn events))))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events)
           :in-theory (disable fn-served-dispatch
                               fn-auth-fold-safe-connp))))

(defthm fn-auth-fold-dispatch-events-have-no-local-submission
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-no-local-effectsp
            (fn-served-result-effects
             (fn-served-dispatch-events conn events))))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events)
           :in-theory (disable fn-served-dispatch
                               fn-auth-fold-safe-connp
                               fn-auth-fold-no-local-effectsp))))

(defun fn-auth-fold-fed-conn (conn byte)
  (declare (xargs :guard t :verify-guards nil))
  (fn-served-make-conn-group-indexed
   (fn-wire-result-state
    (fn-wire-feed-byte (fn-served-conn-wire conn) byte))
   (fn-served-conn-session conn)
   (fn-served-conn-archive conn)
   (fn-served-conn-config conn)
   (fn-served-conn-observation conn)
   (fn-served-conn-injection conn)
   (fn-served-conn-verdicts conn)
   (fn-served-conn-index conn)
   (fn-served-conn-group-index conn) (fn-served-conn-control conn)))

(defthm fn-auth-fold-fed-conn-is-a-connection
  (implies (fn-served-connp conn)
           (fn-served-connp (fn-auth-fold-fed-conn conn byte)))
  :hints (("Goal" :in-theory
           (e/d (fn-auth-fold-fed-conn fn-served-connp)
                (fn-wire-feed-byte fn-wire-statep
                 fn-auth-session-consistentp)))))

(defthm fn-auth-fold-fed-conn-preserves-safe-connp
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-safe-connp
            (fn-auth-fold-fed-conn conn byte)))
  :hints (("Goal" :in-theory
           (e/d (fn-auth-fold-safe-connp fn-auth-fold-fed-conn)
                (fn-served-connp fn-wire-feed-byte
                 fn-auth-fold-post-awaiting
                 fn-auth-config-no-postersp))
           :use ((:instance fn-auth-fold-fed-conn-is-a-connection)))))

(defthm fn-auth-fold-feed-byte-preserves-safe-connp
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-safe-connp
            (fn-served-result-conn (fn-served-feed-byte conn byte))))
  :hints (("Goal" :in-theory
           (e/d (fn-served-feed-byte fn-auth-fold-fed-conn)
                (fn-wire-feed-byte fn-served-dispatch-events
                 fn-auth-fold-safe-connp))
           :use ((:instance fn-auth-fold-fed-conn-preserves-safe-connp)
                 (:instance fn-auth-fold-dispatch-events-preserves-safe-connp
                            (conn (fn-auth-fold-fed-conn conn byte))
                            (events
                             (fn-wire-result-events
                              (fn-wire-feed-byte
                               (fn-served-conn-wire conn) byte))))))))

(defthm fn-auth-fold-feed-byte-has-no-local-submission
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-no-local-effectsp
            (fn-served-result-effects (fn-served-feed-byte conn byte))))
  :hints (("Goal" :in-theory
           (e/d (fn-served-feed-byte fn-auth-fold-fed-conn)
                (fn-wire-feed-byte fn-served-dispatch-events
                 fn-auth-fold-safe-connp
                 fn-auth-fold-no-local-effectsp))
           :use ((:instance fn-auth-fold-fed-conn-preserves-safe-connp)
                 (:instance fn-auth-fold-dispatch-events-have-no-local-submission
                            (conn (fn-auth-fold-fed-conn conn byte))
                            (events
                             (fn-wire-result-events
                              (fn-wire-feed-byte
                               (fn-served-conn-wire conn) byte))))))))

(defthm fn-auth-fold-feed-preserves-safe-connp
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-safe-connp
            (fn-served-result-conn (fn-served-feed conn octets))))
  :hints (("Goal" :induct (fn-served-feed conn octets)
           :in-theory (e/d (fn-served-feed)
                           (fn-served-feed-byte
                            fn-auth-fold-safe-connp
                            fn-served-closed-wirep
                            fn-served-tls-handshakingp)))))

(defthm fn-auth-fold-feed-has-no-local-submission
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-no-local-effectsp
            (fn-served-result-effects (fn-served-feed conn octets))))
  :hints (("Goal" :induct (fn-served-feed conn octets)
           :in-theory (e/d (fn-served-feed)
                           (fn-served-feed-byte
                            fn-auth-fold-safe-connp
                            fn-auth-fold-no-local-effectsp
                            fn-served-closed-wirep
                            fn-served-tls-handshakingp)))))

(defthm fn-auth-fold-step-preserves-safe-connp
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-safe-connp
            (fn-served-result-conn (fn-served-step conn octets))))
  :hints (("Goal" :in-theory
           (e/d (fn-served-step)
                (fn-served-feed fn-auth-fold-safe-connp
                 fn-wire-statep fn-served-closed-wirep)))))

(defthm fn-auth-fold-step-has-no-local-submission
  (implies (fn-auth-fold-safe-connp conn)
           (fn-auth-fold-no-local-effectsp
            (fn-served-result-effects (fn-served-step conn octets))))
  :hints (("Goal" :in-theory
           (e/d (fn-served-step fn-nntp-close-effect
                  fn-auth-fold-no-local-effectsp)
                (fn-served-feed fn-auth-fold-safe-connp
                 fn-wire-statep fn-served-closed-wirep)))))

; The proof-only projections stay closed for downstream callers.  The two
; served-step facts above are the exported K2 interface.
(in-theory (disable fn-auth-fold-post-awaiting fn-auth-fold-safe-connp
                    fn-auth-fold-no-local-effectsp fn-auth-fold-fed-conn))
