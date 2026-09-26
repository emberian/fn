; fn: read-only groups (O2): the served POST gate and LIST ACTIVE's status
; field, one decision (PRF-196, NNT-040).
;
; RFC 3977 section 7.6.3 gives LIST ACTIVE a status field, "y" (posting
; permitted) or "n" (posting not permitted); RFC 6048 section 2.1 lists the
; further values, of which fn serves only "y" and "n" ("m" is P3, deferred;
; "x", "j" and "=" are not served).  A group's status is configuration: the
; operator's `group policy NAME n|y' publishes the delta
; (:set-group-status NAME STATUS 0 nil), code 21 (books/config.lisp), and
; `fn-cfg-closed-names' lists the live groups whose status is "n".  The
; owner installs that list in the posting configuration it hands every
; connection (books/owner-agent.lisp `fn-oag-post-config', the fifth field
; `fn-inj-config-closed'), so a connection answers from the configuration it
; pinned, like every other served answer.
;
; Two readers of that one list, both through `fn-nntp-closed-status':
;   LIST ACTIVE      books/nntp-responses.lisp `fn-nntp-list-status-response',
;                    over the environment books/nntp-post.lisp builds from
;                    the connection's configuration;
;   POST             `fn-gst-post-gate' below, called by
;                    books/nntp-post.lisp `fn-nntp-post-step' before the
;                    injection decision.  An ORDINARY article (no Control
;                    field) naming a closed group is refused 441 by name
;                    (`:group-read-only').  A control message (a cancel) is
;                    not a posting to the group and is not gated; a
;                    Supersedes article is ordinary and is gated.
; Relayed articles (IHAVE, TAKETHIS, BP) are not local postings and are not
; gated: RFC 6048 section 2.1.1 ("n" -- "local postings are not permitted";
; articles may still arrive from peers).  That is the RFC's meaning, not a
; stronger fn guarantee.

(in-package "ACL2")
(include-book "injection")
(include-book "control-classify")
(include-book "nntp-responses")

; (G) for the first G of GROUPS whose status under CLOSED is "n", or nil.
(defun fn-gst-first-closed (groups closed)
  (declare (xargs :guard t))
  (if (consp groups)
      (if (equal (fn-nntp-closed-status (car groups) closed) "n")
          (list (car groups))
        (fn-gst-first-closed (cdr groups) closed))
    nil))

; The gate: nil (pass to the injection decision), or (G), G the octets of
; the first closed group an ordinary SOURCE names.  The parse is bounded by the
; configuration's article bound exactly as the injection decision's is; a
; source it does not admit, or a configuration the decision refuses
; (:config-invalid), passes, and the decision refuses it by its own reason.
(defun fn-gst-post-gate (source config)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-inj-configp)))))
  (let ((closed (fn-inj-config-closed config)))
    (if (or (not (consp closed))
            (not (fn-inj-configp config))
            (not (fn-cbor-at-mostp source (fn-inj-config-max-octets config))))
        nil
      (let ((parsed (fn-article-parse source)))
        (if (not (fn-article-result-okp parsed))
            nil
          (let ((article (fn-article-result-article parsed)))
            (if (not (and (true-listp article) (fn-article-syntax-p article)))
                nil
              (if (not (equal (fn-ctl-classify-fields
                               (fn-article-fields article))
                              :ordinary))
                  nil
                (let ((check (fn-af-proto-article-check article)))
                  (if (fn-inj-proto-reason check)
                      nil
                    (fn-gst-first-closed (fn-inj-nth 2 check)
                                         closed)))))))))))

; The groups an ordinary, admitted SOURCE names (the injection's own parse),
; or nil.
(defun fn-gst-named-groups (source config)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-inj-configp)))))
  (if (or (not (fn-inj-configp config))
          (not (fn-cbor-at-mostp source (fn-inj-config-max-octets config))))
      nil
    (let ((parsed (fn-article-parse source)))
      (if (not (fn-article-result-okp parsed))
          nil
        (let ((article (fn-article-result-article parsed)))
          (if (not (and (true-listp article) (fn-article-syntax-p article)))
              nil
            (if (not (equal (fn-ctl-classify-fields (fn-article-fields article))
                            :ordinary))
                nil
              (let ((check (fn-af-proto-article-check article)))
                (if (fn-inj-proto-reason check)
                    nil
                  (fn-inj-nth 2 check))))))))))

(defun fn-gst-some-closedp (groups closed)
  (declare (xargs :guard t))
  (if (consp groups)
      (or (equal (fn-nntp-closed-status (car groups) closed) "n")
          (fn-gst-some-closedp (cdr groups) closed))
    nil))

(local
 (defthm fn-gst-first-closed-iff-some-closed
   (iff (fn-gst-first-closed groups closed)
        (fn-gst-some-closedp groups closed))
   :hints (("Goal" :in-theory (enable fn-nntp-closed-status)))))

(local
 (defthm fn-gst-some-closedp-of-no-closed
   (implies (not (consp closed))
            (not (fn-gst-some-closedp groups closed)))
   :hints (("Goal" :in-theory (enable fn-nntp-closed-status
                                      fn-nntp-closed-memberp)))))

; KEYSTONE (O2, PRF-196).  The gate refuses exactly when the article names a
; group whose LIST ACTIVE status, under the same configuration, is "n":
; the status field a reader lists (`fn-nntp-closed-status' of the
; configuration's closed list, which the served LIST ACTIVE renders:
; `fn-gst-list-active-line-status' below) and the gate the POST path runs
; are one decision.  Subject: `fn-gst-post-gate', called by
; books/nntp-post.lisp `fn-nntp-post-step'.
(defthm fn-gst-post-gate-refuses-exactly-a-listed-n-group
  (iff (fn-gst-post-gate source config)
       (fn-gst-some-closedp (fn-gst-named-groups source config)
                            (fn-inj-config-closed config)))
  :hints (("Goal" :in-theory (disable fn-article-parse fn-article-syntax-p
                                      fn-ctl-classify-fields
                                      fn-af-proto-article-check
                                      fn-cbor-at-mostp fn-inj-proto-reason
                                      fn-inj-configp))))

; The first closed group the gate names is a group the article names, and
; its listed status is "n".
(defthm fn-gst-first-closed-is-named-and-listed-n
  (implies (fn-gst-first-closed groups closed)
           (and (member-equal (car (fn-gst-first-closed groups closed)) groups)
                (equal (fn-nntp-closed-status
                        (car (fn-gst-first-closed groups closed)) closed)
                       "n"))))

(deftheory fn-gst-vocabulary
  '((:d fn-gst-first-closed) (:d fn-gst-post-gate) (:d fn-gst-named-groups)
    (:d fn-gst-some-closedp)))
(in-theory (disable fn-gst-vocabulary))
