; fn: the inbound transit machine (specs/peering.md section 2): IHAVE
; (RFC 3977 section 6.3.2), CHECK and TAKETHIS (RFC 4644 sections 2.4, 2.5),
; MODE STREAM (RFC 4644 section 2.3), composed over the POST-composed reader
; step exactly as books/nntp-post.lisp composes POST over the reader
; dispatcher.
;
;   offer      fn-peer-decide-offer: what the Message-ID and the connection
;              decide (RFC 5537 sections 3.3, 3.6 step 3); answered at once
;              from the pinned node snapshot (RFC 4644 section 2.4.2: CHECK
;              answers are advisory)
;   transfer   fn-peer-decide-transfer: every check of RFC 5537 section 3.6
;              steps 1 to 4 and section 3.7 steps 1 to 3, one cond arm each,
;              in the RFC's order, each arm naming its reason
;   acceptance fn-peer-transfer: on :want, exactly one fn-node-prepare on the
;              arguments computed here (fn-peer-injection-arguments); the
;              durable completion arrives later through the store, as for
;              POST, and the reply is fn-peer-transit-outcome's
;
; A relaying agent MUST NOT alter anything but Path and Xref (RFC 5537
; section 3.6), so the injecting-agent step of books/injection.lisp is not
; called: the received octets are stored exactly (D01) and the Path prepend
; is rendered on the way out from the (:peer-transit ...) provenance.  What
; POST and transit share is everything from fn-node-prepare down.
;
; The identity strings (obligation id, subject) are the host's under
; A-CRYPTO, as for POST: fn-frame-digest is constrained and unattached, so
; ACL2 cannot evaluate fn-id-obligation-of; they enter fn-peer-transfer as
; arguments and fn-peer-injection-arguments bundles them.  The transaction
; generation is the store's and enters the same way.
;
; RFC 5537 section 3.6 step 2 (a date more than 24 hours in the future) is
; OPEN: the tree has no certified RFC 5322 date-time reader
; (fn-inj-date-decode reads back only the injector's own rendering), so the
; reasons :date-future and :no-clock are reserved and no arm emits them; the
; clock argument is carried for that arm.  :date-cutoff is reserved for D13
; and unreachable by design; :unknown-group is reserved (an unknown group is
; not a refusal by itself, section 2.2).

(in-package "ACL2")
(include-book "node-config")
(include-book "nntp-post")
(include-book "peer-config")

(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary fn-nntp-vocabulary
                          fn-nntp-post-vocabulary fn-cfg-vocabulary
                          fn-cfg-peer-vocabulary fn-path-vocabulary)))
(local (in-theory (enable fn-inj-nth fn-inj-car fn-inj-cdr)))

; -----------------------------------------------------------------------------
; Decisions: a closed enumeration

(defconst *fn-peer-decisions* '(:want :have :defer :refuse))
(defconst *fn-peer-reasons*
  '(:not-a-peer :no-inbound :message-id-syntax :history :staged :busy :fenced
    :inflight-limit :capacity :out-of-scope :loop :no-date :date-future :no-clock
    :proto-article :oversize :unknown-group :date-cutoff))

(defun fn-peer-decision-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)))
(defun fn-peer-decision-kind (d)
  (declare (xargs :guard t))
  (fn-ag-car d))
(defun fn-peer-decision-reason (d)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr d)))
(defun fn-peer-decision (kind reason)
  (declare (xargs :guard t))
  (list kind reason))

(defthm fn-peer-decision-shapep-of-fn-peer-decision
  (fn-peer-decision-shapep (fn-peer-decision kind reason)))
(defthm fn-peer-decision-kind-of-fn-peer-decision
  (equal (fn-peer-decision-kind (fn-peer-decision kind reason)) kind))
(defthm fn-peer-decision-reason-of-fn-peer-decision
  (equal (fn-peer-decision-reason (fn-peer-decision kind reason)) reason))
(defthm fn-peer-decision-shapep-forward-shape
  (implies (fn-peer-decision-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-peer-decision-shapep) (:d fn-peer-decision-kind)
                    (:d fn-peer-decision-reason) (:d fn-peer-decision)))

(defun fn-peer-decisionp (d)
  (declare (xargs :guard t))
  (and (fn-peer-decision-shapep d)
       (member-equal (fn-peer-decision-kind d) *fn-peer-decisions*)
       (or (null (fn-peer-decision-reason d))
           (member-equal (fn-peer-decision-reason d) *fn-peer-reasons*))))

(defun fn-peer-reason-text (reason)
  ; The typed reason, in the reply text, so an operator can re-feed after the
  ; cause is removed (specs/peering.md section 2.2).
  (declare (xargs :guard t))
  (cond ((equal reason :not-a-peer) "not a peer")
        ((equal reason :no-inbound) "no inbound feed configured")
        ((equal reason :message-id-syntax) "message-id syntax")
        ((equal reason :history) "duplicate")
        ((equal reason :staged) "the same article is being accepted")
        ((equal reason :busy) "another article is being accepted")
        ((equal reason :fenced) "recovery pending")
        ((equal reason :inflight-limit) "too many offers outstanding")
        ((equal reason :capacity) "capacity")
        ((equal reason :out-of-scope) "no newsgroup accepted from this peer")
        ((equal reason :loop) "path loop")
        ((equal reason :no-date) "no Injection-Date or Date")
        ((equal reason :proto-article) "not a valid article")
        ((equal reason :oversize) "article exceeds the configured size")
        (t "refused")))

; -----------------------------------------------------------------------------
; History (section 2.5): the store plus its bindings, no cutoff, no pruning

(defun fn-peer-history-hasp (msgid node)
  (declare (xargs :guard t))
  (or (fn-acceptedp msgid (fn-state-articles (fn-node-acceptance node)))
      (consp (fn-node-find-binding msgid (fn-node-bindings node)))))

(defun fn-peer-stagedp (msgid node)
  (declare (xargs :guard t))
  (and (consp (fn-node-stage node))
       (equal (fn-node-stage-msgid (fn-node-stage node)) msgid)))

; -----------------------------------------------------------------------------
; Scope, evidence, the local identity

(defun fn-peer-wildmat-matchp (wildmat-text name-octets)
  (declare (xargs :guard t))
  (let ((r (fn-wildmat-match (fn-record-string-octets wildmat-text) name-octets)))
    (and (fn-wildmat-result-okp r) (fn-wildmat-result-value r))))

; The sublist of the article's Newsgroups names that match the peer's
; accept-groups and are live at the current generation: those, and only
; those, become the local memberships.  Strings, as fn-node-prepare takes.
(defun fn-peer-scope-groups (groups record cfg)
  (declare (xargs :guard t))
  (if (consp groups)
      (let ((name (fn-record-octets-string (car groups)))
            (rest (fn-peer-scope-groups (cdr groups) record cfg)))
        (if (and (fn-peer-wildmat-matchp (fn-cfg-peer-inbound-groups record)
                                         (car groups))
                 (fn-cfg-group-livep (fn-cfg-value cfg) (fn-cfg-generation cfg)
                                     name)
                 (not (member-equal name rest)))
            (cons name rest)
          rest))
    nil))

; The provenance, as the retention ledger's evidence string.  The structured
; (:transit peer kind msgid octets) submission is what the served path
; carries; this is its rendering into the one slot the article record has.
(defun fn-peer-evidence (peer cfg)
  (declare (xargs :guard t) (ignorable cfg))
  (if (stringp peer)
      (string-append "peer-transit:" peer)
    "peer-transit:"))

(defun fn-peer-local-identity (cfg)
  ; The node's own <path-identity>: the policy slot "path-identity".
  (declare (xargs :guard t))
  (fn-record-string-octets (fn-cfg-policy (fn-cfg-value cfg) "path-identity")))

(defun fn-peer-probe-obligation-id (msgid)
  (declare (xargs :guard t))
  (string-append "peer-probe:" (fn-record-octets-string msgid)))

(defun fn-peer-probe-subject ()
  (declare (xargs :guard t))
  "peer-probe")

; -----------------------------------------------------------------------------
; Offer-time decision: only what the Message-ID and the connection decide

(defun fn-peer-decide-offer (node cfg peer session msgid clock inflight)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil)
           (ignorable session clock))
  (let ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
    (cond ((not record) (fn-peer-decision :refuse :not-a-peer))
          ((null (fn-cfg-peer-inbound record))
           (fn-peer-decision :refuse :no-inbound))
          ((not (fn-af-message-idp msgid))
           (fn-peer-decision :refuse :message-id-syntax))
          ((fn-peer-history-hasp (fn-record-octets-string msgid) node)
           (fn-peer-decision :have :history))
          ((fn-peer-stagedp (fn-record-octets-string msgid) node)
           (fn-peer-decision :defer :staged))
          ((equal (fn-state-fenced (fn-node-acceptance node)) t)
           (fn-peer-decision :defer :fenced))
          ((<= (fn-cfg-peer-inbound-max-inflight record) (nfix inflight))
           (fn-peer-decision :defer :inflight-limit))
          ; The minimum charge: this can only under-refuse; the exact check
          ; is at transfer.  Local policy: capacity at offer time defers.
          ((not (fn-retain-admissiblep (fn-node-retention node)
                                       (fn-peer-probe-obligation-id msgid)
                                       (fn-peer-probe-subject) :archive
                                       (fn-peer-evidence peer cfg)
                                       (fn-charge-for-payload 0)))
           (fn-peer-decision :defer :capacity))
          (t (fn-peer-decision :want nil)))))

; -----------------------------------------------------------------------------
; Transfer-time decision: the whole article is here

(defun fn-peer-check-msgid (check)
  (declare (xargs :guard t))
  (fn-inj-nth 1 check))
(defun fn-peer-check-groups (check)
  (declare (xargs :guard t))
  (fn-inj-nth 2 check))

(defun fn-peer-decide-transfer (node cfg peer msgid octets clock id subject)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil)
           (ignorable clock))
  (let* ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
         (parsed (fn-article-parse octets))
         (article (if (and (fn-article-result-okp parsed)
                           (true-listp parsed))
                      (fn-article-result-article parsed)
                    nil))
         (okp (and article (fn-article-syntax-p article)))
         (check (if okp (fn-af-proto-article-check article) nil)))
    (cond ((not record) (fn-peer-decision :refuse :not-a-peer))
          ((null (fn-cfg-peer-inbound record))
           (fn-peer-decision :refuse :no-inbound))
          ((not (fn-af-message-idp msgid))
           (fn-peer-decision :refuse :message-id-syntax))
          ((< (fn-cfg-peer-inbound-max-octets record) (len octets))
           (fn-peer-decision :refuse :oversize))
          ((not okp) (fn-peer-decision :refuse :proto-article))
          ; 3.6 step 1: Newsgroups, Message-ID, and Injection-Date or Date.
          ; The proto-article check permits a missing Message-ID for POST;
          ; transit requires it, and requires it to equal the offered one.
          ((not (equal (fn-af-status-kind check) :ok))
           (fn-peer-decision :refuse :proto-article))
          ((not (fn-af-message-id-equalp (fn-peer-check-msgid check) msgid))
           (fn-peer-decision :refuse :message-id-syntax))
          ((not (fn-path-date-presentp article))
           (fn-peer-decision :refuse :no-date))
          ; 3.6 step 2 (date-future): OPEN, see the header.
          ; 3.6 step 3 / 3.7 step 3: already accepted.  Re-checked here
          ; because the offer may be stale (RFC 4644 section 2.4.2).
          ((fn-peer-history-hasp (fn-record-octets-string msgid) node)
           (fn-peer-decision :have :history))
          ; Loop: our own path identity already in Path (section 2.3).
          ((fn-path-names-p (fn-af-path-field-value article)
                            (fn-peer-local-identity cfg))
           (fn-peer-decision :refuse :loop))
          ; Scope: at least one Newsgroups name accepted from this peer and
          ; live now.
          ((null (fn-peer-scope-groups (fn-peer-check-groups check) record cfg))
           (fn-peer-decision :refuse :out-of-scope))
          ((fn-peer-stagedp (fn-record-octets-string msgid) node)
           (fn-peer-decision :defer :staged))
          ((consp (fn-node-stage node)) (fn-peer-decision :defer :busy))
          ((equal (fn-state-fenced (fn-node-acceptance node)) t)
           (fn-peer-decision :defer :fenced))
          ; Local policy: capacity at transfer time, the bytes having
          ; arrived, is a refusal (RFC 3977 section 6.3.2.2 lists disc space).
          ((not (fn-retain-admissiblep (fn-node-retention node) id subject
                                       :archive (fn-peer-evidence peer cfg)
                                       (fn-charge-for-payload (len octets))))
           (fn-peer-decision :refuse :capacity))
          (t (fn-peer-decision :want nil)))))

; -----------------------------------------------------------------------------
; The transfer: the post path on arguments ACL2 computed from the octets

; The eight arguments after the node, in fn-node-prepare's order:
; (generation msgid payload groups obligation-id subject evidence charge).
(defun fn-peer-injection-arguments (node cfg peer msgid octets generation
                                         id subject)
  (declare (xargs :guard t :verify-guards nil) (ignorable node))
  (let* ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
         (parsed (fn-article-parse octets))
         (article (if (and (fn-article-result-okp parsed)
                           (true-listp parsed))
                      (fn-article-result-article parsed)
                    nil))
         (check (if (and article (fn-article-syntax-p article))
                    (fn-af-proto-article-check article)
                  nil)))
    (list generation
          (fn-record-octets-string msgid)
          octets
          (fn-peer-scope-groups (fn-peer-check-groups check) record cfg)
          id subject
          (fn-peer-evidence peer cfg)
          (fn-charge-for-payload (len octets)))))

; (mv node2 decision).  On :want it is exactly one fn-node-prepare; it never
; calls fn-accept-prepare directly and never touches retention itself.
(defun fn-peer-transfer (node cfg peer msgid octets clock generation id subject)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil))
  (let ((d (fn-peer-decide-transfer node cfg peer msgid octets clock id subject)))
    (if (not (equal (fn-peer-decision-kind d) :want))
        (mv node d)
      (let ((a (fn-peer-injection-arguments node cfg peer msgid octets
                                            generation id subject)))
        (mv (fn-node-prepare node (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                             (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a))
            d)))))

; -----------------------------------------------------------------------------
; The transit submission the served path carries to the owner

(defun fn-peer-submission-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5)))
(defun fn-peer-submission-peer (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr x)))
(defun fn-peer-submission-kind (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr x))))
(defun fn-peer-submission-msgid (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-peer-submission-octets (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-peer-make-submission (peer kind msgid octets)
  (declare (xargs :guard t))
  (list :transit peer kind msgid octets))

(defthm fn-peer-submission-shapep-of-fn-peer-make-submission
  (fn-peer-submission-shapep (fn-peer-make-submission peer kind msgid octets)))
(defthm fn-peer-submission-peer-of-fn-peer-make-submission
  (equal (fn-peer-submission-peer (fn-peer-make-submission peer kind msgid octets))
         peer))
(defthm fn-peer-submission-kind-of-fn-peer-make-submission
  (equal (fn-peer-submission-kind (fn-peer-make-submission peer kind msgid octets))
         kind))
(defthm fn-peer-submission-msgid-of-fn-peer-make-submission
  (equal (fn-peer-submission-msgid (fn-peer-make-submission peer kind msgid octets))
         msgid))
(defthm fn-peer-submission-octets-of-fn-peer-make-submission
  (equal (fn-peer-submission-octets (fn-peer-make-submission peer kind msgid octets))
         octets))
(defthm fn-peer-submission-shapep-forward-shape
  (implies (fn-peer-submission-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(defun fn-peer-submissionp (x)
  (declare (xargs :guard t))
  (and (fn-peer-submission-shapep x)
       (equal (fn-ag-car x) :transit)
       (stringp (fn-peer-submission-peer x))
       (or (equal (fn-peer-submission-kind x) :ihave)
           (equal (fn-peer-submission-kind x) :takethis))
       (fn-nntp-printable-tokenp (fn-peer-submission-msgid x))
       (fn-af-message-idp (fn-peer-submission-msgid x))))

(defthm fn-peer-submissionp-of-fn-peer-make-submission
  (equal (fn-peer-submissionp (fn-peer-make-submission peer kind msgid octets))
         (and (stringp peer)
              (or (equal kind :ihave) (equal kind :takethis))
              (fn-nntp-printable-tokenp msgid)
              (fn-af-message-idp msgid)))
  :hints (("Goal" :in-theory (enable fn-peer-make-submission
                                     fn-peer-submission-peer
                                     fn-peer-submission-kind
                                     fn-peer-submission-msgid
                                     fn-peer-submission-octets))))

; A transit submission is never an injected one: the two kinds stay distinct
; through the one :submit effect.
(defthm fn-peer-submission-is-not-injected
  (implies (fn-peer-submissionp x) (not (fn-inj-injectedp x)))
  :hints (("Goal" :in-theory (enable fn-inj-injectedp fn-inj-decision-status
                                     fn-peer-submission-shapep))))

(in-theory (disable (:d fn-peer-submission-shapep) (:d fn-peer-submission-peer)
                    (:d fn-peer-submission-kind) (:d fn-peer-submission-msgid)
                    (:d fn-peer-submission-octets) (:d fn-peer-make-submission)))

; -----------------------------------------------------------------------------
; The transit session: the posting session plus the peer, the transfer in
; progress, the outstanding offer count, and the pinned node and
; configuration the offer decision reads.  Opaque.

(defun fn-peer-session-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6)))
(defun fn-peer-session-base (x)
  (declare (xargs :guard t))
  (fn-ag-car x))
(defun fn-peer-session-peer (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr x)))
(defun fn-peer-session-transfer (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr x))))
(defun fn-peer-session-inflight (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-peer-session-node (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-peer-session-cfg (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(defun fn-peer-make-session (base peer transfer inflight node cfg)
  (declare (xargs :guard t))
  (list base peer transfer inflight node cfg))

(defthm fn-peer-session-shapep-of-fn-peer-make-session
  (fn-peer-session-shapep (fn-peer-make-session base peer transfer inflight node cfg)))
(defthm fn-peer-session-base-of-fn-peer-make-session
  (equal (fn-peer-session-base (fn-peer-make-session base peer transfer inflight node cfg))
         base))
(defthm fn-peer-session-peer-of-fn-peer-make-session
  (equal (fn-peer-session-peer (fn-peer-make-session base peer transfer inflight node cfg))
         peer))
(defthm fn-peer-session-transfer-of-fn-peer-make-session
  (equal (fn-peer-session-transfer (fn-peer-make-session base peer transfer inflight node cfg))
         transfer))
(defthm fn-peer-session-inflight-of-fn-peer-make-session
  (equal (fn-peer-session-inflight (fn-peer-make-session base peer transfer inflight node cfg))
         inflight))
(defthm fn-peer-session-node-of-fn-peer-make-session
  (equal (fn-peer-session-node (fn-peer-make-session base peer transfer inflight node cfg))
         node))
(defthm fn-peer-session-cfg-of-fn-peer-make-session
  (equal (fn-peer-session-cfg (fn-peer-make-session base peer transfer inflight node cfg))
         cfg))
(defthm fn-peer-session-shapep-forward-shape
  (implies (fn-peer-session-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-peer-session-shapep) (:d fn-peer-session-base)
                    (:d fn-peer-session-peer) (:d fn-peer-session-transfer)
                    (:d fn-peer-session-inflight) (:d fn-peer-session-node)
                    (:d fn-peer-session-cfg) (:d fn-peer-make-session)))

; nil | (:ihave msgid) | (:takethis msgid)
(defun fn-peer-transferp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (true-listp x) (equal (len x) 2)
           (or (equal (car x) :ihave) (equal (car x) :takethis))
           (fn-nntp-printable-tokenp (car (cdr x)))
           (fn-af-message-idp (car (cdr x))))))

(defun fn-peer-sessionp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-peer-session-shapep x)
       (fn-post-sessionp (fn-peer-session-base x))
       (or (null (fn-peer-session-peer x))
           (and (stringp (fn-peer-session-peer x))
                (fn-node-statep (fn-peer-session-node x))
                (fn-cfgp (fn-peer-session-cfg x))))
       (fn-peer-transferp (fn-peer-session-transfer x))
       (natp (fn-peer-session-inflight x))))

(defthm fn-peer-sessionp-forward-shape
  (implies (fn-peer-sessionp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(defun fn-peer-session-consistentp (x archive)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-peer-sessionp x)
       (fn-post-session-consistentp (fn-peer-session-base x) archive)))

; Opening: peer nil is a reader connection (the POST-composed session
; unchanged); a peer connection pins the node and configuration once, under
; their recognizers, here and nowhere per command.
(defun fn-peer-open-session (archive peer node cfg)
  (declare (xargs :guard t :verify-guards nil))
  (if (and peer (stringp peer) (fn-node-statep node) (fn-cfgp cfg))
      (fn-peer-make-session (fn-post-open-session archive) peer nil 0 node cfg)
    (fn-peer-make-session (fn-post-open-session archive) nil nil 0 nil nil)))

(defun fn-peer-with-base (ps base)
  (declare (xargs :guard t))
  (fn-peer-make-session base (fn-peer-session-peer ps)
                        (fn-peer-session-transfer ps)
                        (fn-peer-session-inflight ps)
                        (fn-peer-session-node ps) (fn-peer-session-cfg ps)))

(defun fn-peer-with-transfer (ps transfer inflight)
  (declare (xargs :guard t))
  (fn-peer-make-session (fn-peer-session-base ps) (fn-peer-session-peer ps)
                        transfer inflight
                        (fn-peer-session-node ps) (fn-peer-session-cfg ps)))

; -----------------------------------------------------------------------------
; Replies, exactly per RFC (the two tables of section 2.2)

(defun fn-peer-single (ps text)
  (declare (xargs :guard t))
  (fn-nntp-result-effects
   (fn-nntp-single (fn-post-session-base (fn-peer-session-base ps)) text)))

; A reply that echoes the offered Message-ID (RFC 4644: the first parameter
; MUST be the message-id), built over octets: the token came from the
; command line and is printable.
(defun fn-peer-echo-reply (code-text msgid)
  (declare (xargs :guard t))
  (list (fn-nntp-reply-effect
         (fn-nntp-crlf (append (fn-nntp-string-octets code-text) msgid)))))

(defun fn-peer-ihave-offer-line (d)
  ; 335 / 435 duplicate / 436 retry later / 435 not wanted
  (declare (xargs :guard t))
  (let ((kind (fn-peer-decision-kind d)))
    (cond ((equal kind :want) "335 send it; end with <CR-LF>.<CR-LF>")
          ((equal kind :have) "435 duplicate")
          ((equal kind :defer)
           (string-append "436 retry later; "
                          (fn-peer-reason-text (fn-peer-decision-reason d))))
          (t (string-append "435 not wanted; "
                            (fn-peer-reason-text (fn-peer-decision-reason d)))))))

(defun fn-peer-check-code (d)
  ; 238 / 438 / 431 / 438
  (declare (xargs :guard t))
  (let ((kind (fn-peer-decision-kind d)))
    (cond ((equal kind :want) "238 ")
          ((equal kind :defer) "431 ")
          (t "438 "))))

; After the article: (command, decision, completion) -> code -> effects.
; completion is the host's durable observation: :durable | :refused |
; :uncertain, or nil when the transfer was not :want and no attempt ran.
;
; The code classes, fixed by what the legacy sender does with them
; (innfeed, measured against INN 2.7.4 on hbox,
; planning/evidence/inn-lab-f4e8272-2026-09-20.md): 431, 436, 400, 480, 503
; and any unknown code are RETRIED; 437 and 439 are DROPPED for good.  So
; every fn "not now" (:defer at transfer -- busy, staged, fenced, capacity
; probe -- and an uncertain outcome) is 436 for IHAVE and for TAKETHIS,
; never a drop code and never 400-and-close (a 400 costs the peer a
; reconnect and its backoff for every pipelined article behind it); every
; :refuse and :have after the bytes is the drop code 437 / 439.  RFC 4644
; section 2.5 gives TAKETHIS only 239 / 439 and names 400 for a temporary
; error; 436 on TAKETHIS is fn's local policy for the reason above, and it is
; in the retry class of every sender that follows RFC 3977 section 6.3.2.2
; ("a lack of response ... treated the same as 436").  An uncertain outcome
; also closes: the node is fenced and serves nothing until recovery.
(defun fn-peer-transit-code (kind d completion)
  (declare (xargs :guard t))
  (let ((dk (fn-peer-decision-kind d)))
    (cond ((equal completion :durable) (if (equal kind :ihave) 235 239))
          ((equal completion :uncertain) 436)
          ((equal completion :refused) (if (equal kind :ihave) 437 439))
          ((equal dk :defer) 436)
          (t (if (equal kind :ihave) 437 439)))))

(defun fn-peer-transit-outcome-effects (ps submission d completion)
  (declare (xargs :guard t))
  (let* ((kind (fn-peer-submission-kind submission))
         (msgid (fn-peer-submission-msgid submission))
         (code (fn-peer-transit-code kind d completion))
         (reason (fn-peer-reason-text (fn-peer-decision-reason d))))
    (if (equal kind :ihave)
        (cond ((equal code 235) (fn-peer-single ps "235 article transferred OK"))
              ((equal completion :uncertain)
               (append (fn-peer-single ps "436 transfer failed; the outcome is uncertain")
                       (list (fn-nntp-close-effect))))
              ((equal completion :refused)
               (fn-peer-single ps "437 transfer rejected; refused by acceptance"))
              ((equal code 436)
               (fn-peer-single ps (string-append "436 retry later; " reason)))
              (t (fn-peer-single ps (string-append "437 transfer rejected; " reason))))
      (cond ((equal code 239) (fn-peer-echo-reply "239 " msgid))
            ((equal completion :uncertain)
             (append (fn-peer-echo-reply "436 " msgid)
                     (list (fn-nntp-close-effect))))
            ((equal code 436) (fn-peer-echo-reply "436 " msgid))
            (t (fn-peer-echo-reply "439 " msgid))))))

; The offer codes, the same two classes: :defer is 431 (CHECK) / 436 (IHAVE),
; :refuse and :have are 438 / 435, :want is 238 / 335.
(defun fn-peer-offer-code (kind d)
  (declare (xargs :guard t))
  (let ((dk (fn-peer-decision-kind d)))
    (cond ((equal dk :want) (if (equal kind :ihave) 335 238))
          ((equal dk :defer) (if (equal kind :ihave) 436 431))
          (t (if (equal kind :ihave) 435 438)))))

; The mapping, stated: a deferral or an uncertain outcome is never a drop
; code and never 400; a durable completion is the only way to a 2xx.
(defthm fn-peer-not-now-is-a-retry-code
  (and (implies (or (equal completion :uncertain)
                    (and (null completion)
                         (equal (fn-peer-decision-kind d) :defer)))
                (equal (fn-peer-transit-code kind d completion) 436))
       (implies (equal (fn-peer-decision-kind d) :defer)
                (member-equal (fn-peer-offer-code kind d) '(431 436)))
       (implies (not (equal completion :durable))
                (member-equal (fn-peer-transit-code kind d completion)
                              '(436 437 439)))
       (implies (equal completion :durable)
                (member-equal (fn-peer-transit-code kind d completion)
                              '(235 239)))))

; The host entry after the durable attempt: the connection is unchanged.
(defun fn-peer-transit-outcome (ps submission d completion)
  (declare (xargs :guard t))
  (fn-post-make-result ps (fn-peer-transit-outcome-effects ps submission d completion)
                       nil))

; -----------------------------------------------------------------------------
; The composed step

(defun fn-peer-capability-lines (record)
  ; RFC 3977 section 3.3.2: a label is advertised only for what is served.
  ; IHAVE and STREAMING are promised to a peer whose record has an inbound
  ; half; a feed-only peer sees the reader's list.
  (declare (xargs :guard t))
  (if (and record (fn-cfg-peer-inbound record))
      (append (fn-nntp-capability-lines)
              (list (fn-nntp-string-octets "IHAVE")
                    (fn-nntp-string-octets "STREAMING")))
    (fn-nntp-capability-lines)))

(defun fn-peer-delegate (ps archive config observation wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-nntp-post-step (fn-peer-session-base ps) archive config
                              observation wire-event)))
    (fn-post-make-result (fn-peer-with-base ps (fn-post-result-session r))
                         (fn-post-result-effects r)
                         (fn-post-result-submission r))))

(defun fn-peer-msgid-argp (args)
  (declare (xargs :guard t))
  (and (consp args) (null (cdr args))
       (fn-nntp-printable-tokenp (car args))
       (fn-af-message-idp (car args))))

(defun fn-peer-command (ps keyword args)
  ; The peer connection's transit commands.  Anything else is nil: delegate.
  (declare (xargs :guard (fn-peer-sessionp ps) :verify-guards nil))
  (let ((node (fn-peer-session-node ps))
        (cfg (fn-peer-session-cfg ps))
        (peer (fn-peer-session-peer ps))
        (inflight (fn-peer-session-inflight ps)))
    (cond
     ((fn-nntp-keywordp keyword "IHAVE")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps "501 syntax error") nil)
        (let ((d (fn-peer-decide-offer node cfg peer ps (car args) nil inflight)))
          (if (equal (fn-peer-decision-kind d) :want)
              (fn-post-make-result
               (fn-peer-with-transfer ps (list :ihave (car args)) inflight)
               (append (fn-peer-single ps (fn-peer-ihave-offer-line d))
                       (list (fn-nntp-begin-article-effect)))
               nil)
            (fn-post-make-result ps (fn-peer-single ps (fn-peer-ihave-offer-line d))
                                 nil)))))
     ((fn-nntp-keywordp keyword "CHECK")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps "501 syntax error") nil)
        (let ((d (fn-peer-decide-offer node cfg peer ps (car args) nil inflight)))
          (fn-post-make-result
           (if (equal (fn-peer-decision-kind d) :want)
               (fn-peer-with-transfer ps nil (+ 1 (nfix inflight)))
             ps)
           (fn-peer-echo-reply (fn-peer-check-code d) (car args))
           nil))))
     ((fn-nntp-keywordp keyword "TAKETHIS")
      ; The article always follows (RFC 4644 section 2.5.2); no decision
      ; until it has arrived.  Each TAKETHIS retires one outstanding 238.
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps "501 syntax error") nil)
        (fn-post-make-result
         (fn-peer-with-transfer ps (list :takethis (car args))
                                (nfix (- (nfix inflight) 1)))
         (list (fn-nntp-begin-article-effect))
         nil)))
     ((and (fn-nntp-keywordp keyword "MODE")
           (consp args) (null (cdr args))
           (fn-nntp-keywordp (car args) "STREAM"))
      ; RFC 4644 section 2.3: 203, stateless.
      (fn-post-make-result ps (fn-peer-single ps "203 streaming permitted") nil))
     ((and (fn-nntp-keywordp keyword "CAPABILITIES")
           (or (null args)
               (and (consp args) (null (cdr args))
                    (fn-nntp-keyword-tokenp (car args)))))
      (fn-post-make-result
       ps
       (fn-nntp-result-effects
        (fn-nntp-multi (fn-post-session-base (fn-peer-session-base ps))
                       "101 capability list follows"
                       (fn-peer-capability-lines
                        (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))))
       nil))
     (t nil))))

(defun fn-peer-step (ps archive config observation wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (fn-peer-sessionp ps)) (fn-post-make-result ps nil nil))
   ; A reader connection: the POST-composed step, unchanged.
   ((null (fn-peer-session-peer ps))
    (fn-peer-delegate ps archive config observation wire-event))
   ; A closed session serves nothing further.
   ((not (equal (fn-nntp-session-openp
                 (fn-post-session-base (fn-peer-session-base ps)))
                t))
    (fn-peer-delegate ps archive config observation wire-event))
   ; Awaiting the transit article: the body arrives as one (:article lines)
   ; event through the same wire article mode POST uses, and leaves as the
   ; submission the owner carries through fn-peer-transfer.
   ((fn-peer-session-transfer ps)
    (let ((transfer (fn-peer-session-transfer ps)))
      (if (and (consp wire-event)
               (equal (car wire-event) :article)
               (consp (cdr wire-event))
               (null (cdr (cdr wire-event))))
          (fn-post-make-result
           (fn-peer-with-transfer ps nil (fn-peer-session-inflight ps))
           nil
           (fn-peer-make-submission (fn-peer-session-peer ps)
                                    (car transfer) (car (cdr transfer))
                                    (fn-post-body-octets (car (cdr wire-event)))))
        ; The article was not received: RFC 3977 section 6.3.2.2 makes a
        ; lack of response a retry; the honest signal is the retry code and
        ; a close.
        (fn-post-make-result
         (fn-peer-with-transfer ps nil (fn-peer-session-inflight ps))
         (append (fn-peer-single
                  ps (if (equal (car transfer) :ihave)
                         "436 transfer failed; the article was not received"
                       "436 the article was not received; closing"))
                 (list (fn-nntp-close-effect)))
         nil))))
   ; A command line: the transit commands here, everything else delegated.
   ((and (consp wire-event)
         (equal (car wire-event) :command)
         (consp (cdr wire-event))
         (null (cdr (cdr wire-event)))
         (fn-nntp-command-inputp (car (cdr wire-event))))
    (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
      (if (and (consp tokens)
               (fn-nntp-keyword-tokenp (car tokens))
               (fn-nntp-command-arguments-at-mostp tokens))
          (let ((r (fn-peer-command ps (car tokens) (cdr tokens))))
            (if r r (fn-peer-delegate ps archive config observation wire-event)))
        (fn-peer-delegate ps archive config observation wire-event))))
   (t (fn-peer-delegate ps archive config observation wire-event))))

; -----------------------------------------------------------------------------
; What the composed step preserves and emits: the two facts the served fold
; (books/served.lisp) needs of fn-peer-step, stated as books/nntp-post.lisp
; states them of fn-nntp-post-step.

(local (defthm fn-peer-cbor-at-mostp-len
  (implies (fn-cbor-at-mostp xs bound) (<= (len xs) (nfix bound)))
  :rule-classes :linear))

(local (defthm fn-peer-message-id-len
  (implies (fn-af-message-idp msgid) (<= (len msgid) 250))
  :hints (("Goal" :in-theory (enable fn-af-message-idp)
           :use ((:instance fn-peer-cbor-at-mostp-len (xs msgid) (bound 250)))))
  :rule-classes :linear))

(local (defthm fn-peer-message-id-true-listp
  (implies (fn-af-message-idp msgid) (true-listp msgid))
  :hints (("Goal" :in-theory (enable fn-af-message-idp)))))

; An echoed reply is a typed effect: the token is printable (so response
; text), the code is a status prefix, and 4 + 250 + 2 fits the line.
(defthm fn-peer-echo-reply-effects-well-formed
  (implies (and (fn-nntp-printable-tokenp msgid)
                (fn-af-message-idp msgid)
                (member-equal code-text '("238 " "431 " "438 " "239 " "436 " "439 ")))
           (fn-nntp-effectsp (fn-peer-echo-reply code-text msgid)))
  :hints (("Goal" :in-theory (e/d (fn-peer-echo-reply fn-nntp-effectsp
                                   fn-nntp-effectp fn-nntp-reply-effect)
                                  (fn-nntp-replyp fn-nntp-crlf
                                   fn-nntp-initial-status-linep
                                   fn-nntp-response-textp
                                   fn-af-message-idp fn-nntp-printable-tokenp))
           :use ((:instance fn-nntp-replyp-of-single-line
                            (line (append (fn-nntp-string-octets code-text) msgid)))))))

(defthm fn-peer-single-effects-well-formed
  (implies (and (fn-nntp-response-textp (fn-nntp-string-octets text))
                (fn-nntp-initial-status-linep (fn-nntp-string-octets text))
                (<= (+ (len (fn-nntp-string-octets text)) 2)
                    *fn-nntp-max-response-octets*))
           (fn-nntp-effectsp (fn-peer-single ps text)))
  :hints (("Goal" :in-theory (e/d (fn-peer-single)
                                  (fn-nntp-single fn-nntp-effectsp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep)))))

(local (defthm fn-peer-effectsp-of-append
  (implies (and (fn-nntp-effectsp a) (fn-nntp-effectsp b))
           (fn-nntp-effectsp (append a b)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-effectsp) (fn-nntp-effectp))))))

(local (defthm fn-peer-close-effect-typed
  (fn-nntp-effectsp (list (fn-nntp-close-effect)))
  :hints (("Goal" :in-theory (enable fn-nntp-effectsp fn-nntp-effectp
                                     fn-nntp-close-effect)))))

(local (defthm fn-peer-begin-article-typed
  (fn-nntp-effectsp (list (fn-nntp-begin-article-effect)))
  :hints (("Goal" :in-theory (enable fn-nntp-effectsp fn-nntp-effectp
                                     fn-nntp-begin-article-effect)))))

(defthm fn-peer-transit-outcome-effects-well-formed
  (implies (fn-peer-submissionp submission)
           (fn-nntp-effectsp
            (fn-peer-transit-outcome-effects ps submission d completion)))
  :hints (("Goal" :in-theory (e/d (fn-peer-transit-outcome-effects
                                   fn-peer-transit-code
                                   fn-peer-reason-text fn-peer-submissionp)
                                  (fn-peer-single fn-peer-echo-reply
                                   fn-nntp-effectsp fn-nntp-response-textp
                                   fn-nntp-initial-status-linep
                                   fn-af-message-idp fn-nntp-printable-tokenp
                                   fn-peer-decision-kind
                                   fn-peer-decision-reason)))))

(defthm fn-peer-command-effects-well-formed
  (implies (and (fn-peer-sessionp ps)
                (fn-peer-command ps keyword args))
           (fn-nntp-effectsp (fn-post-result-effects (fn-peer-command ps keyword args))))
  :hints (("Goal" :in-theory (e/d (fn-peer-command fn-peer-ihave-offer-line
                                   fn-peer-check-code fn-peer-reason-text
                                   fn-peer-msgid-argp)
                                  (fn-peer-single fn-peer-echo-reply
                                   fn-nntp-effectsp fn-nntp-response-textp
                                   fn-nntp-initial-status-linep
                                   fn-af-message-idp fn-nntp-printable-tokenp
                                   fn-peer-decide-offer fn-peer-decision-kind
                                   fn-peer-decision-reason fn-nntp-keywordp
                                   fn-nntp-keyword-tokenp fn-peer-sessionp
                                   fn-nntp-multi fn-peer-capability-lines
                                   fn-cfg-peer-find fn-nntp-capability-lines))
           :use ((:instance fn-nntp-effects-multi
                            (session (fn-post-session-base (fn-peer-session-base ps)))
                            (initial "101 capability list follows")
                            (lines (fn-peer-capability-lines
                                    (fn-cfg-peer-find (fn-peer-session-peer ps)
                                                      (fn-cfg-peers (fn-cfg-value (fn-peer-session-cfg ps)))))))))))

(defthm fn-peer-step-effects-well-formed
  (implies (fn-peer-session-consistentp ps archive)
           (fn-nntp-effectsp
            (fn-post-result-effects
             (fn-peer-step ps archive config observation wire-event))))
  :hints (("Goal" :in-theory (e/d (fn-peer-step fn-peer-delegate
                                   fn-peer-session-consistentp)
                                  (fn-peer-command fn-nntp-post-step
                                   fn-peer-sessionp fn-nntp-effectsp
                                   fn-peer-single fn-nntp-response-textp
                                   fn-nntp-initial-status-linep
                                   fn-nntp-command-inputp fn-nntp-tokenize
                                   fn-nntp-keyword-tokenp
                                   fn-nntp-command-arguments-at-mostp
                                   fn-post-body-octets fn-nntp-session-openp
                                   fn-post-session-consistentp)))))

; The session stays consistent: the reader branches are
; fn-post-step-preserves-consistent-session under the base, and the transit
; branches touch only the transfer and inflight fields.
(defthm fn-peer-command-preserves-consistent-session
  (implies (and (fn-peer-session-consistentp ps archive)
                (fn-peer-command ps keyword args))
           (fn-peer-session-consistentp
            (fn-post-result-session (fn-peer-command ps keyword args)) archive))
  :hints (("Goal" :in-theory (e/d (fn-peer-command fn-peer-session-consistentp
                                   fn-peer-sessionp fn-peer-with-transfer
                                   fn-peer-msgid-argp fn-peer-transferp)
                                  (fn-peer-single fn-peer-echo-reply
                                   fn-peer-decide-offer fn-peer-decision-kind
                                   fn-nntp-keywordp fn-nntp-keyword-tokenp
                                   fn-nntp-multi fn-peer-capability-lines
                                   fn-cfg-peer-find fn-post-sessionp
                                   fn-post-session-consistentp
                                   fn-node-statep fn-cfgp
                                   fn-af-message-idp fn-nntp-printable-tokenp
                                   fn-peer-ihave-offer-line fn-peer-check-code)))))

(defthm fn-peer-step-preserves-consistent-session
  (implies (fn-peer-session-consistentp ps archive)
           (fn-peer-session-consistentp
            (fn-post-result-session
             (fn-peer-step ps archive config observation wire-event))
            archive))
  :hints (("Goal" :in-theory (e/d (fn-peer-step fn-peer-delegate
                                   fn-peer-with-base fn-peer-with-transfer)
                                  (fn-peer-command fn-nntp-post-step
                                   fn-peer-sessionp fn-peer-session-consistentp
                                   fn-nntp-command-inputp fn-nntp-tokenize
                                   fn-nntp-keyword-tokenp
                                   fn-nntp-command-arguments-at-mostp
                                   fn-post-body-octets fn-nntp-session-openp
                                   fn-post-session-consistentp
                                   fn-peer-command-preserves-consistent-session))
           :use ((:instance fn-peer-command-preserves-consistent-session
                            (keyword (car (fn-nntp-tokenize (car (cdr wire-event)))))
                            (args (cdr (fn-nntp-tokenize (car (cdr wire-event))))))
                 (:instance fn-post-step-preserves-consistent-session
                            (ps (fn-peer-session-base ps)))))
          ("Subgoal *1/1" :in-theory (enable fn-peer-session-consistentp fn-peer-sessionp
                                              fn-post-session-consistentp))))

; A submission the step emits is an injected article (a reader's POST) or a
; transit submission, never anything else: the one :submit effect stays typed.
(defthm fn-peer-step-submission-is-typed
  (implies (and (fn-peer-sessionp ps)
                (fn-post-result-submission
                 (fn-peer-step ps archive config observation wire-event)))
           (or (fn-inj-injectedp
                (fn-post-result-submission
                 (fn-peer-step ps archive config observation wire-event)))
               (fn-peer-submissionp
                (fn-post-result-submission
                 (fn-peer-step ps archive config observation wire-event)))))
  :hints (("Goal" :in-theory (e/d (fn-peer-step fn-peer-delegate fn-peer-command
                                   fn-peer-sessionp fn-peer-transferp
                                   fn-peer-msgid-argp)
                                  (fn-nntp-post-step fn-inj-injectedp
                                   fn-peer-submissionp fn-peer-single
                                   fn-peer-echo-reply fn-peer-decide-offer
                                   fn-peer-decision-kind fn-nntp-keywordp
                                   fn-nntp-keyword-tokenp fn-nntp-multi
                                   fn-peer-capability-lines fn-cfg-peer-find
                                   fn-post-sessionp fn-node-statep fn-cfgp
                                   fn-af-message-idp fn-nntp-printable-tokenp
                                   fn-nntp-command-inputp fn-nntp-tokenize
                                   fn-nntp-command-arguments-at-mostp
                                   fn-post-body-octets fn-nntp-session-openp
                                   fn-peer-ihave-offer-line fn-peer-check-code
                                   fn-post-submission-is-an-injected-article))
           :use ((:instance fn-post-submission-is-an-injected-article
                            (ps (fn-peer-session-base ps)))))))

(defthm fn-peer-open-session-is-consistent
  (fn-peer-session-consistentp (fn-peer-open-session archive peer node cfg) archive)
  :hints (("Goal" :in-theory (e/d (fn-peer-open-session fn-peer-session-consistentp
                                   fn-peer-sessionp fn-peer-transferp)
                                  (fn-post-open-session fn-post-session-consistentp
                                   fn-post-sessionp fn-node-statep fn-cfgp
                                   fn-post-open-session-is-consistent))
           :use ((:instance fn-post-open-session-is-consistent))
           :expand ((fn-post-session-consistentp (fn-post-open-session archive) archive)))))

; -----------------------------------------------------------------------------
; Export theory

(deftheory fn-peer-vocabulary
  '((:d fn-peer-decisionp) (:d fn-peer-reason-text) (:d fn-peer-history-hasp)
    (:d fn-peer-stagedp) (:d fn-peer-wildmat-matchp) (:d fn-peer-scope-groups)
    (:d fn-peer-evidence) (:d fn-peer-local-identity)
    (:d fn-peer-probe-obligation-id) (:d fn-peer-probe-subject)
    (:d fn-peer-decide-offer) (:d fn-peer-check-msgid) (:d fn-peer-check-groups)
    (:d fn-peer-decide-transfer) (:d fn-peer-injection-arguments)
    (:d fn-peer-transfer) (:d fn-peer-submissionp) (:d fn-peer-transferp)
    (:d fn-peer-sessionp) (:d fn-peer-session-consistentp)
    (:d fn-peer-open-session) (:d fn-peer-with-base) (:d fn-peer-with-transfer)
    (:d fn-peer-single) (:d fn-peer-echo-reply) (:d fn-peer-ihave-offer-line)
    (:d fn-peer-check-code) (:d fn-peer-transit-code) (:d fn-peer-offer-code)
    (:d fn-peer-transit-outcome-effects)
    (:d fn-peer-transit-outcome) (:d fn-peer-capability-lines)
    (:d fn-peer-delegate) (:d fn-peer-msgid-argp) (:d fn-peer-command)
    (:d fn-peer-step)))

(in-theory (disable fn-peer-vocabulary))
