; fn: the inbound transit machine (specs/peering.md section 2): IHAVE
; (RFC 3977 section 6.3.2), CHECK and TAKETHIS (RFC 4644 sections 2.4, 2.5),
; MODE STREAM (RFC 4644 section 2.3), composed over the POST-composed reader
; step exactly as books/nntp-post.lisp composes POST over the reader
; dispatcher.
;
;   offer      fn-peer-decide-offer: what the Message-ID and the connection
;              decide (RFC 5537 sections 3.3, 3.6 step 3), over the node the
;              session carries.  books/owner.lisp fn-own-conn-live-session
;              re-pins that node from the owner's own store before every
;              fn-own-read, so the answer is about the node as it is now.
;              RFC 4644 section 2.4.2 makes a CHECK answer advisory, which
;              permits a later refusal; it does not ask a server to forget
;              what it holds, and until w11/transit-correct this one did --
;              the node was the value fn-peer-open-session pinned at :open
;              and nothing replaced it, so a peer was told 335/238 for an
;              article it had delivered on that same connection
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
; fn-charge-for-payload: the retention charge a transit probe offers.
(include-book "identity")
(include-book "peer-config")
(include-book "provenance-codec")

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

; The provenance of a transit acceptance (specs/peering.md section 2.4).
;
; `fn-peer-transit-provenance' is the typed record: the peer name as the
; configuration knows it, the command that carried the bytes, the RFC 5537
; section 3.2.1 Path diagnostic the transfer decision computed, and the
; configuration generation the peer record was read at.
; `fn-peer-transit-evidence' is its wire form --- a STRING whose octets are
; the canonical encoding, so it fits the record grammar's evidence field
; unchanged and `fn-prov-of-wire' recovers the whole record after replay.
;
; `fn-peer-evidence' is UNCHANGED and is still what the decisions below and
; `fn-peer-injection-arguments' pass: it answers exactly the string this
; function answered before the typed record existed, and
; `fn-peer-evidence-is-the-legacy-rendering' (books/peer-inbound-invariants)
; is the equation.  Moving the transit path onto
; `fn-peer-transit-evidence' needs the transit command in scope, which means
; a `kind' formal on `fn-peer-decide-transfer', `fn-peer-transfer' and
; `fn-peer-injection-arguments' --- an arity change inside the K1/K2/K3
; statements, which this lane does not own.  It is the ASK on
; planning/deputies/BOARD.md and the open item in
; planning/lanes/HANDOFF-w10-provenance.md.
(defun fn-peer-transit-provenance (peer cfg kind diagnostic)
  (declare (xargs :guard t))
  (fn-prov-make-transit
   (if (stringp peer) peer "")
   (if (fn-prov-transit-kindp kind) kind :ihave)
   (if (fn-prov-diagnosticp diagnostic) diagnostic (fn-prov-diagnostic-match))
   (nfix (fn-cfg-generation cfg))))

(defun fn-peer-transit-evidence (peer cfg kind diagnostic)
  (declare (xargs :guard t))
  (let ((p (fn-peer-transit-provenance peer cfg kind diagnostic)))
    (if (fn-prov-durablep p) (fn-prov-wire p) (fn-prov-render p))))

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
         ; RFC 5537 section 3.6 step 1 is the RELAYING agent's check, and
         ; that is what this is. The injecting agent's check of section
         ; 3.4.1 refuses an article carrying Injection-Info, which every
         ; injected article carries, so applying it here refused EVERY offer
         ; of an article any node had posted -- `:refuse :proto-article` on
         ; the first transfer between two fn nodes, every time.
         (check (if okp (fn-af-relayed-article-check article) nil)))
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
         ; The relaying agent's check, as in `fn-peer-decide-transfer`: the
         ; memberships staged for a transit article come from its own
         ; Newsgroups, and an injected article is not a proto-article.
         (check (if (and article (fn-article-syntax-p article))
                    (fn-af-relayed-article-check article)
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

; The reader session under a transit session, named ONCE.  The served command
; chain is four records deep -- auth over peer over post over the reader
; session -- and all three base accessors are `car', so a walk that stops one
; level short is answered with a plausible value instead of an error.  Four
; such misses shipped on 2026-09-20 (see tools/session_depth.py, which reads
; this ladder out of the books and fails on a wrong depth).  This is a MACRO
; rather than a function on purpose: it expands to exactly the term every
; call site spells today, so naming the walk costs no theorem, no rule and no
; re-proof, and the next wrapper is one edit here instead of a sweep.
(defmacro fn-peer-reader-session (ps)
  `(fn-post-session-base (fn-peer-session-base ,ps)))

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
       (or (and (null (fn-peer-session-peer x))
                (or (and (null (fn-peer-session-node x))
                         (null (fn-peer-session-cfg x)))
                    (and (fn-node-statep (fn-peer-session-node x))
                         (fn-cfgp (fn-peer-session-cfg x)))))
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
  (if (and (or (null peer) (stringp peer)) (fn-node-statep node) (fn-cfgp cfg))
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

; Re-pin the node the offer decision reads.  `fn-peer-decide-offer' answers
; from the node the session carries, and only `fn-peer-open-session' ever set
; it, so every offer on a connection was decided against the node as it stood
; when the connection opened.  A peer that transferred an article and then
; offered it again on the SAME connection drew `335'/`238' -- K3's duplicate
; suppression, which is proved of `fn-peer-decide-offer', never saw the
; history it is about, because the node it was given did not have it yet.
; Measured on `tools/v0_matrix.py' at `6fb30ca': `V0-TRANSIT-DUPLICATE-AB/BA'
; `335' and `V0-TRANSIT-CHECK-DUP-AB/BA' `238' against `435'/`438'.
; `books/owner.lisp' (`fn-own-conn-live-session', called by `fn-own-read')
; applies this once per socket read from the owner's own store; the peer
; record stays pinned, because the owner holds no configuration to re-read.
(defun fn-peer-with-node (ps node)
  (declare (xargs :guard t))
  (fn-peer-make-session (fn-peer-session-base ps) (fn-peer-session-peer ps)
                        (fn-peer-session-transfer ps)
                        (fn-peer-session-inflight ps)
                        node (fn-peer-session-cfg ps)))

; -----------------------------------------------------------------------------
; Replies, exactly per RFC (the two tables of section 2.2)

(defun fn-peer-single (ps text)
  (declare (xargs :guard t))
  (fn-nntp-result-effects
   (fn-nntp-single (fn-peer-reader-session ps) text)))

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

(defun fn-peer-capability-lines (record postingp)
  ; RFC 3977 section 3.3.2: a label is advertised only for what is served.
  ; IHAVE and STREAMING are promised to a peer whose record has an inbound
  ; half; a feed-only peer sees the reader's list.  postingp is the pinned
  ; configuration's posting bit, which fn-nntp-capability-lines gates the
  ; POST label on; a transit connection carries no injection configuration
  ; (fn-peer-command reads only the session), so it passes nil and does not
  ; promise POST.
  (declare (xargs :guard t))
  (if (and record (fn-cfg-peer-inbound record))
      (append (fn-nntp-capability-lines postingp)
              (list (fn-nntp-string-octets "IHAVE")
                    (fn-nntp-string-octets "STREAMING")))
    (fn-nntp-capability-lines postingp)))

(defun fn-peer-delegate (ps archive config observation injection wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-nntp-post-step (fn-peer-session-base ps) archive config
                              observation injection wire-event)))
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
  ; The guard names what fn-peer-step has already established when it calls
  ; this: a peer connection, whose session pins a node and a configuration
  ; under their recognizers.  A reader connection never reaches here.
  (declare (xargs :guard (and (fn-peer-sessionp ps) (fn-peer-session-peer ps))
                  :verify-guards nil))
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
        (fn-nntp-multi (fn-peer-reader-session ps)
                       "101 capability list follows"
                       (fn-peer-capability-lines
                        (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))
                        nil)))
       nil))
     (t nil))))

(defun fn-peer-step (ps archive config observation injection wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (fn-peer-sessionp ps)) (fn-post-make-result ps nil nil))
   ; A reader connection: the POST-composed step, unchanged.
   ((null (fn-peer-session-peer ps))
    (fn-peer-delegate ps archive config observation injection wire-event))
   ; A closed session serves nothing further.
   ((not (equal (fn-nntp-session-openp (fn-peer-reader-session ps)) t))
    (fn-peer-delegate ps archive config observation injection wire-event))
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
            (if r r (fn-peer-delegate ps archive config observation injection wire-event)))
        (fn-peer-delegate ps archive config observation injection wire-event))))
   (t (fn-peer-delegate ps archive config observation injection wire-event))))

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

; The echoed line, in two halves, because the two facts want opposite
; theories: response text is closed under append (so the append stays
; closed), and the status-line prefix and the length want it open.  Both
; are :rule-classes nil and cited by :use, so nothing about append or
; about these recognizers leaves the book.

(local (defthm fn-peer-echo-line-is-response-text
  (implies (and (fn-nntp-printable-tokenp msgid)
                (true-listp msgid)
                (member-equal code-text
                              '("238 " "431 " "438 " "239 " "436 " "439 ")))
           (fn-nntp-response-textp
            (append (fn-nntp-string-octets code-text) msgid)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable (:d binary-append)
                                      (:d fn-nntp-string-octets)
                                      (:d fn-nntp-response-textp)
                                      (:d fn-nntp-printable-tokenp))
           :use ((:instance fn-nntp-response-text-of-append
                            (x (fn-nntp-string-octets code-text))
                            (y msgid))
                 (:instance fn-nntp-printable-token-is-response-text
                            (octets msgid)))))))

; RFC 3977 section 3.1: three decimal digits and a space, and the whole
; line with its CRLF inside 512 octets.  The code is a ground four-octet
; prefix and RFC 5536 section 3.1.3 bounds the Message-ID at 250, so the
; line is at most 256 octets: the bound is not tight and is not the
; interesting part.
(local (defthm fn-peer-echo-line-is-a-status-line
  (implies (and (fn-af-message-idp msgid)
                (member-equal code-text
                              '("238 " "431 " "438 " "239 " "436 " "439 ")))
           (and (fn-nntp-initial-status-linep
                 (append (fn-nntp-string-octets code-text) msgid))
                (<= (+ (len (append (fn-nntp-string-octets code-text) msgid)) 2)
                    *fn-nntp-max-response-octets*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-nntp-initial-status-linep
                                   fn-nntp-decimal-digitp)
                                  ((:d fn-af-message-idp)))))))

; An echoed reply is a typed effect: the token is printable (so response
; text), the code is a status prefix, and 4 + 250 + 2 fits the line.
(defthm fn-peer-echo-reply-effects-well-formed
  (implies (and (fn-nntp-printable-tokenp msgid)
                (fn-af-message-idp msgid)
                (member-equal code-text '("238 " "431 " "438 " "239 " "436 " "439 ")))
           (fn-nntp-effectsp (fn-peer-echo-reply code-text msgid)))
  :hints (("Goal" :in-theory (e/d (fn-peer-echo-reply fn-nntp-effectsp
                                   fn-nntp-effectp fn-nntp-reply-effect)
                                  ((:d fn-nntp-replyp) (:d fn-nntp-crlf)
                                   (:d fn-nntp-initial-status-linep)
                                   (:d fn-nntp-response-textp)
                                   (:d fn-af-message-idp)
                                   (:d fn-nntp-printable-tokenp)
                                   (:d binary-append)
                                   (:d fn-nntp-string-octets)))
           :use ((:instance fn-nntp-replyp-of-single-line
                            (line (append (fn-nntp-string-octets code-text) msgid)))
                 fn-peer-echo-line-is-response-text
                 fn-peer-echo-line-is-a-status-line))))

(defthm fn-peer-single-effects-well-formed
  (implies (and (fn-nntp-response-textp (fn-nntp-string-octets text))
                (fn-nntp-initial-status-linep (fn-nntp-string-octets text))
                (<= (+ (len (fn-nntp-string-octets text)) 2)
                    *fn-nntp-max-response-octets*))
           (fn-nntp-effectsp (fn-peer-single ps text)))
  ; fn-nntp-effects-single (books/nntp-effects.lisp) is the fact; it is
  ; stated over (fn-nntp-result-effects (fn-nntp-single ...)), so the
  ; accessor stays closed or the rule stops matching.
  :hints (("Goal" :in-theory (e/d (fn-peer-single)
                                  ((:d fn-nntp-result-effects)
                                   (:d fn-nntp-single) (:d fn-nntp-effectsp)
                                   (:d fn-nntp-response-textp)
                                   (:d fn-nntp-initial-status-linep))))))

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

; Every advertised label is response text: the reader's list is ground and
; IHAVE and STREAMING are two more ground lines.
(local (defthm fn-peer-capability-lines-is-block-text
  (fn-nntp-block-textp (fn-peer-capability-lines record postingp))
  :hints (("Goal" :in-theory (e/d (fn-peer-capability-lines
                                   fn-nntp-capability-lines
                                   fn-nntp-block-textp)
                                  ((:d fn-cfg-peer-inbound)))))))

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
                            (session (fn-peer-reader-session ps))
                            (initial "101 capability list follows")
                            (lines (fn-peer-capability-lines
                                    (fn-cfg-peer-find (fn-peer-session-peer ps)
                                                      (fn-cfg-peers (fn-cfg-value (fn-peer-session-cfg ps))))
                                    nil)))))))

(defthm fn-peer-step-effects-well-formed
  (implies (fn-peer-session-consistentp ps archive)
           (fn-nntp-effectsp
            (fn-post-result-effects
             (fn-peer-step ps archive config observation injection wire-event))))
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
; The two directions of the consistency predicate, so no proof below opens
; it: forward-chaining puts its two conjuncts in the context when it is a
; hypothesis, and the rewrite discharges it on a session just built.
; Exported, not local: books/served.lisp needs (fn-peer-sessionp x) from a
; consistent connection session to dismiss fn-peer-step's non-session
; branch.  Forward-chaining, so no rewrite rule about the recognizer
; leaves the book.
(defthm fn-peer-session-consistentp-forward
  (implies (fn-peer-session-consistentp x archive)
           (and (fn-peer-sessionp x)
                (fn-post-session-consistentp (fn-peer-session-base x) archive)
                (fn-post-sessionp (fn-peer-session-base x))
                (fn-peer-transferp (fn-peer-session-transfer x))
                (natp (fn-peer-session-inflight x))
                ; the peer half of the recognizer, as a conditional fact so
                ; a reader connection carries nothing about node or cfg
                (implies (fn-peer-session-peer x)
                         (and (stringp (fn-peer-session-peer x))
                              (fn-node-statep (fn-peer-session-node x))
                              (fn-cfgp (fn-peer-session-cfg x))))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-session-consistentp)
                                   (:d fn-peer-sessionp))
                                  ((:d fn-post-session-consistentp)
                                   (:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp))))))

(local (defthm fn-peer-session-consistentp-of-make-session
  (equal (fn-peer-session-consistentp
          (fn-peer-make-session base peer transfer inflight node cfg) archive)
         (and (fn-peer-sessionp
               (fn-peer-make-session base peer transfer inflight node cfg))
              (fn-post-session-consistentp base archive)
              t))
  :hints (("Goal" :in-theory (e/d (fn-peer-session-consistentp)
                                  ((:d fn-peer-sessionp)
                                   (:d fn-post-session-consistentp)))))))

; Withdrawn from here down: the two lemmas above are the only way into it,
; and the forward-chaining rule cannot trigger while it opens.
(local (in-theory (disable (:d fn-peer-session-consistentp))))

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

; The session recognizer in both directions, so the step proof never opens
; it: what a consistent session gives, and what rebuilding one with a new
; base needs.  fn-peer-step only ever replaces the base (fn-peer-with-base)
; or the transfer slot, so these two constructor rules cover it.
(local (defthm fn-post-session-consistentp-forward
  (implies (fn-post-session-consistentp x archive)
           (fn-post-sessionp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-post-session-consistentp))
                                  ((:d fn-post-sessionp)
                                   (:d fn-nntp-session-consistentp)))))))

; Exported with the two constructor rules below: books/owner.lisp reads a
; connection session's POST base and its slots without opening the
; recognizer.
(defthm fn-peer-sessionp-forward-fields
  (implies (fn-peer-sessionp x)
           (and (fn-post-sessionp (fn-peer-session-base x))
                (fn-peer-transferp (fn-peer-session-transfer x))
                (natp (fn-peer-session-inflight x))
                (implies (fn-peer-session-peer x)
                         (and (stringp (fn-peer-session-peer x))
                              (fn-node-statep (fn-peer-session-node x))
                              (fn-cfgp (fn-peer-session-cfg x))))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-sessionp))
                                  ((:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp))))))

; The reader case of `fn-peer-sessionp' is a null peer with a null node and a
; null configuration, which is what `fn-peer-open-session' builds (line 539);
; a null peer beside an arbitrary node and configuration is not a session, so
; the free `node' and `cfg' this lemma carried made it false rather than hard.
; The peer case, where the node and configuration are checked, is the sibling
; below.
(local (defthm fn-peer-sessionp-of-make-session-reader
  (implies (and (fn-post-sessionp base)
                (fn-peer-transferp transfer)
                (natp inflight))
           (fn-peer-sessionp
            (fn-peer-make-session base nil transfer inflight nil nil)))
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-sessionp))
                                  ((:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp)))))))

; And the configured reader: a null peer beside a checked node and
; configuration is the recognizer's second reader form.
(local (defthm fn-peer-sessionp-of-make-session-reader-configured
  (implies (and (fn-post-sessionp base)
                (fn-peer-transferp transfer)
                (natp inflight)
                (fn-node-statep node)
                (fn-cfgp cfg))
           (fn-peer-sessionp
            (fn-peer-make-session base nil transfer inflight node cfg)))
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-sessionp))
                                  ((:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp)))))))

; The other reader shape a step rebuilds: the node and configuration of a
; reader session it already has, whichever of the two reader forms that
; session is in.
(local (defthm fn-peer-sessionp-of-make-session-reader-from-session
  (implies (and (fn-post-sessionp base)
                (fn-peer-transferp transfer)
                (natp inflight)
                (fn-peer-sessionp ps)
                (not (fn-peer-session-peer ps)))
           (fn-peer-sessionp
            (fn-peer-make-session base nil transfer inflight
                                  (fn-peer-session-node ps)
                                  (fn-peer-session-cfg ps))))
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-sessionp))
                                  ((:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp)))))))

(local (defthm fn-peer-sessionp-of-make-session-peer
  (implies (and (fn-post-sessionp base)
                (stringp peer)
                (fn-node-statep node)
                (fn-cfgp cfg)
                (fn-peer-transferp transfer)
                (natp inflight))
           (fn-peer-sessionp
            (fn-peer-make-session base peer transfer inflight node cfg)))
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-sessionp))
                                  ((:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp)))))))

(local (in-theory (disable (:d fn-peer-sessionp))))

(defthm fn-peer-step-preserves-consistent-session
  (implies (fn-peer-session-consistentp ps archive)
           (fn-peer-session-consistentp
            (fn-post-result-session
             (fn-peer-step ps archive config observation injection wire-event))
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
                                   ; every sub-recognizer stays closed: the
                                   ; content is in the forward-chaining
                                   ; facts and the two constructor rules
                                   (:d fn-post-sessionp)
                                   (:d fn-nntp-session-consistentp)
                                   (:d fn-post-session-shapep)
                                   (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp)
                                   fn-peer-command-preserves-consistent-session))
           :use ((:instance fn-peer-command-preserves-consistent-session
                            (keyword (car (fn-nntp-tokenize (car (cdr wire-event)))))
                            (args (cdr (fn-nntp-tokenize (car (cdr wire-event))))))
                 (:instance fn-post-step-preserves-consistent-session
                            (ps (fn-peer-session-base ps)))
                 (:instance fn-post-session-consistentp-forward
                            (x (fn-post-result-session
                                (fn-nntp-post-step (fn-peer-session-base ps)
                                                   archive config observation
                                                   injection wire-event))))))
          ("Subgoal *1/1" :in-theory (enable fn-peer-session-consistentp fn-peer-sessionp
                                              fn-post-session-consistentp))))

; A submission the step emits is an injected article (a reader's POST) or a
; transit submission, never anything else: the one :submit effect stays typed.
(defthm fn-peer-step-submission-is-typed
  (implies (and (fn-peer-sessionp ps)
                (fn-post-result-submission
                 (fn-peer-step ps archive config observation injection wire-event)))
           (or (fn-inj-injectedp
                (fn-post-result-submission
                 (fn-peer-step ps archive config observation injection wire-event)))
               (fn-peer-submissionp
                (fn-post-result-submission
                 (fn-peer-step ps archive config observation injection wire-event)))))
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
  ; Only fn-peer-open-session opens: the constructor rules above carry the
  ; shape and the forward rule carries what the opened base gives.
  :hints (("Goal" :in-theory (e/d (fn-peer-open-session)
                                  ((:d fn-peer-session-consistentp)
                                   (:d fn-peer-sessionp) (:d fn-peer-transferp)
                                   (:d fn-post-open-session)
                                   (:d fn-post-session-consistentp)
                                   (:d fn-post-sessionp)
                                   (:d fn-node-statep) (:d fn-cfgp)
                                   fn-post-open-session-is-consistent))
           :use ((:instance fn-post-open-session-is-consistent)
                 (:instance fn-post-session-consistentp-forward
                            (x (fn-post-open-session archive)))))))

; Exported for books/owner.lisp (fn-own-advance): re-pinning a connection
; replaces only the POST base of its peer session and keeps the peer, the
; transfer, the inflight count and the pinned node and configuration, so
; the result is still a peer session.
(defthm fn-peer-session-base-of-fn-peer-with-base
  (equal (fn-peer-session-base (fn-peer-with-base ps base)) base)
  :hints (("Goal" :in-theory (enable (:d fn-peer-with-base)))))

(defthm fn-peer-sessionp-of-fn-peer-with-base
  (implies (and (fn-peer-sessionp ps) (fn-post-sessionp base))
           (fn-peer-sessionp (fn-peer-with-base ps base)))
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-sessionp) (:d fn-peer-with-base))
                                  ((:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp))))))

; Exported for books/owner.lisp (fn-own-conn-live-session): re-pinning the
; node replaces only that field.  The peer, the transfer, the inflight count
; and the pinned peer record are kept, so a connection stays the connection
; it was, and the recognizer is preserved exactly when the new node is a
; node state --- which the owner's own store is (fn-sn-statep).
(defthm fn-peer-session-base-of-fn-peer-with-node
  (equal (fn-peer-session-base (fn-peer-with-node ps node))
         (fn-peer-session-base ps))
  :hints (("Goal" :in-theory (enable (:d fn-peer-with-node)))))

(defthm fn-peer-session-peer-of-fn-peer-with-node
  (equal (fn-peer-session-peer (fn-peer-with-node ps node))
         (fn-peer-session-peer ps))
  :hints (("Goal" :in-theory (enable (:d fn-peer-with-node)))))

(defthm fn-peer-session-node-of-fn-peer-with-node
  (equal (fn-peer-session-node (fn-peer-with-node ps node)) node)
  :hints (("Goal" :in-theory (enable (:d fn-peer-with-node)))))

(defthm fn-peer-session-transfer-of-fn-peer-with-node
  (equal (fn-peer-session-transfer (fn-peer-with-node ps node))
         (fn-peer-session-transfer ps))
  :hints (("Goal" :in-theory (enable (:d fn-peer-with-node)))))

(defthm fn-peer-session-inflight-of-fn-peer-with-node
  (equal (fn-peer-session-inflight (fn-peer-with-node ps node))
         (fn-peer-session-inflight ps))
  :hints (("Goal" :in-theory (enable (:d fn-peer-with-node)))))

(defthm fn-peer-session-cfg-of-fn-peer-with-node
  (equal (fn-peer-session-cfg (fn-peer-with-node ps node))
         (fn-peer-session-cfg ps))
  :hints (("Goal" :in-theory (enable (:d fn-peer-with-node)))))

(defthm fn-peer-sessionp-of-fn-peer-with-node
  (implies (and (fn-peer-sessionp ps) (fn-node-statep node))
           (fn-peer-sessionp (fn-peer-with-node ps node)))
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-sessionp) (:d fn-peer-with-node))
                                  ((:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp))))))

(defthm fn-peer-session-consistentp-of-fn-peer-with-node
  (implies (and (fn-peer-session-consistentp ps archive) (fn-node-statep node))
           (fn-peer-session-consistentp (fn-peer-with-node ps node) archive))
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-session-consistentp))
                                  ((:d fn-peer-sessionp) (:d fn-peer-with-node)
                                   (:d fn-post-session-consistentp)
                                   (:d fn-node-statep))))))

; -----------------------------------------------------------------------------
; Guard verification of the served chain
;
; books/served.lisp guard-verifies fn-served-dispatch, which calls
; fn-peer-step, so these are not optional: an unverified fn-peer-step makes
; books/served uncertifiable and the served host unloadable.  The one
; non-trivial obligation is the node-statep-to-retain-statep bridge that
; fn-peer-decide-offer needs for fn-retain-admissiblep, and it is a
; conjunct of fn-node-statep.

(local (defthm fn-peer-node-statep-forward
  (implies (fn-node-statep node)
           (and (fn-statep (fn-node-acceptance node))
                (fn-retain-statep (fn-node-retention node))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-node-statep))
                                  ((:d fn-statep) (:d fn-retain-statep)
                                   (:d fn-node-state-shapep)
                                   (:d fn-node-binding-listp)))))))

(local (defthm fn-peer-transferp-forward
  (implies (and (fn-peer-transferp x) x)
           (and (consp x) (consp (cdr x))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-transferp))
                                  ((:d fn-nntp-printable-tokenp)
                                   (:d fn-af-message-idp)))))))

(verify-guards fn-peer-decide-offer
  ; The recognizers stay closed: the forward rule above supplies
  ; fn-retain-statep and the rest are guard t.
  :hints (("Goal" :in-theory (disable (:d fn-node-statep) (:d fn-statep)
                                      (:d fn-retain-statep)
                                      (:d fn-node-state-shapep)
                                      (:d fn-cfgp) (:d fn-cfg-peer-find)
                                      (:d fn-af-message-idp)
                                      (:d fn-peer-history-hasp)
                                      (:d fn-peer-stagedp)
                                      (:d fn-retain-admissiblep)
                                      (:d fn-peer-evidence)
                                      (:d fn-record-octets-string)
                                      ; the inbound accessors stay closed or
                                      ; fn-cfg-peerp-inbound-fields, which is
                                      ; stated over them, stops matching
                                      (:d fn-cfg-peer-inbound)
                                      (:d fn-cfg-peer-inbound-groups)
                                      (:d fn-cfg-peer-inbound-max-octets)
                                      (:d fn-cfg-peer-inbound-max-inflight)
                                      (:d fn-cfg-ag-car) (:d fn-cfg-ag-cdr)))))
(verify-guards fn-peer-sessionp)
; fn-peer-session-consistentp: OPEN, and not needed.  It calls
; fn-post-session-consistentp (books/nntp-post.lisp), which is itself
; :verify-guards nil; it is a specification predicate, not on the served
; executable path, so nothing guard-verified calls it.
(verify-guards fn-peer-open-session)
(verify-guards fn-peer-delegate)
(verify-guards fn-peer-command)
(verify-guards fn-peer-step)

; -----------------------------------------------------------------------------
; Export theory

(deftheory fn-peer-vocabulary
  '((:d fn-peer-decisionp) (:d fn-peer-reason-text) (:d fn-peer-history-hasp)
    (:d fn-peer-stagedp) (:d fn-peer-wildmat-matchp) (:d fn-peer-scope-groups)
    (:d fn-peer-transit-provenance) (:d fn-peer-transit-evidence)
    (:d fn-peer-evidence) (:d fn-peer-local-identity)
    (:d fn-peer-probe-obligation-id) (:d fn-peer-probe-subject)
    (:d fn-peer-decide-offer) (:d fn-peer-check-msgid) (:d fn-peer-check-groups)
    (:d fn-peer-decide-transfer) (:d fn-peer-injection-arguments)
    (:d fn-peer-transfer) (:d fn-peer-submissionp) (:d fn-peer-transferp)
    (:d fn-peer-sessionp) (:d fn-peer-session-consistentp)
    (:d fn-peer-open-session) (:d fn-peer-with-base) (:d fn-peer-with-transfer)
    (:d fn-peer-with-node)
    (:d fn-peer-single) (:d fn-peer-echo-reply) (:d fn-peer-ihave-offer-line)
    (:d fn-peer-check-code) (:d fn-peer-transit-code) (:d fn-peer-offer-code)
    (:d fn-peer-transit-outcome-effects)
    (:d fn-peer-transit-outcome) (:d fn-peer-capability-lines)
    (:d fn-peer-delegate) (:d fn-peer-msgid-argp) (:d fn-peer-command)
    (:d fn-peer-step)))

(in-theory (disable fn-peer-vocabulary))
