; fn: the operator's moderation verbs and withdrawal (PKT-657, PKT-575).
;
; `moderation approve ID --moderator LOGIN', `moderation reject ID
; --moderator LOGIN [--reason TEXT]' and `article withdraw ID --reason TEXT'
; reach the running owner as one FNCT request (kind 21; its reply is the
; reasoned reply, kind 18).  The owner decides here, over what it carries:
;
;   `fn-mvb-plan'   (:refused REASON), (:submit MSGID GROUPS OCTETS) or
;                   (:withdraw ARGV MSGID GROUPS OCTETS).  The host runs the
;                   named steps in order and stops at the first that does
;                   not accept: ARGV (when not nil) through the live
;                   administration path (the :withdraw-article row, config
;                   delta code 26, books/config.lisp), then the octets
;                   through the operator's submission (books/owner.lisp
;                   `fn-own-operator-submit', the (:operator-submit ...)
;                   event).  Host: host/owner-host.lisp
;                   `fn-owner-moderation-plan', called by
;                   host/native/control.lisp `fnn-owner-moderation-serialized'.
;
; Approve (RFC 5537 section 3.9 step 4): the held article is the envelope's
; body (books/moderation.lisp `fn-mod-forward': the proto-article with its
; Message-ID and Date lines); the moderator's article is that body with
; `Approved: LOGIN' first.  It is decided by `fn-post-gated-decision', the
; served POST's decision, under LOGIN's moderation view (the configuration
; `fn-auth-moderation-config' gives LOGIN's connection), and submitted only
; when that decision injects it and the operator path injects the same
; Message-ID into the same groups: the approval commits exactly what LOGIN's
; approval over NNTP commits.
;
; Reject and withdraw (PKT-575, CT3): the node withdraws TARGET under its own
; authority.  The configuration row (CAUSE TARGET REASON 1) is written first,
; then the node injects the article CAUSE, `Control: cancel TARGET', filed in
; `control.cancel' (NNT-010; the operator creates that group); the control machine's :node arm
; (books/control-authority.lisp `fn-ctl-withdrawal-plan') makes the record
; when the refresh first publishes CAUSE, and
; `fn-ctl-node-withdrawal-withdraws-exactly-its-target' says what it
; withdraws.  CAUSE is `<fn-withdraw.' then TARGET after its `<': a second
; withdrawal of the same target names the same cause, so a retry after a
; crash between the two steps finds the row and injects only the article.
;
; Prefix `fn-mvb-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "control-evidence")
(include-book "nntp-post")
(include-book "config-invariants")
(include-book "peer-authored-accept")
(include-book "nntp-session")      ; fn-nntp-article-bytes, fn-nntp-article-alpha

; -----------------------------------------------------------------------------
; Identities

(defconst *fn-mvb-withdraw-prefix* "<fn-withdraw.")

; The envelope Message-ID ID names: ID itself when it is an envelope's, else
; the envelope `fn-mod-forward' makes for a post whose Message-ID is ID.
(defun fn-mvb-envelope-id (id)
  (declare (xargs :guard t))
  (let ((o (fn-record-string-octets id)))
    (cond ((fn-cev-envelope-original id) id)
          ((and (consp o) (equal (car o) 60))
           (fn-record-octets-string (fn-mod-envelope-msgid o)))
          (t id))))

; The cause of the node's withdrawal of TARGET.
(defun fn-mvb-cause (target)
  (declare (xargs :guard t))
  (let ((o (fn-record-string-octets target)))
    (fn-record-octets-string
     (append (fn-record-string-octets *fn-mvb-withdraw-prefix*)
             (if (consp o) (cdr o) nil)))))

; -----------------------------------------------------------------------------
; Articles

; The octets after the first empty line (CR LF CR LF) of O, or :none.
(defun fn-mvb-after-blank (o)
  (declare (xargs :guard t))
  (cond ((not (consp o)) :none)
        ((and (equal (car o) 13)
              (consp (cdr o)) (equal (cadr o) 10)
              (consp (cddr o)) (equal (caddr o) 13)
              (consp (cdddr o)) (equal (cadddr o) 10))
         (cddddr o))
        (t (fn-mvb-after-blank (cdr o)))))

(defconst *fn-mvb-approved-field*
  '(65 112 112 114 111 118 101 100 58 32))                   ; "Approved: "

; The moderator's article: the held proto-article with `Approved: LOGIN'.
(defun fn-mvb-approved-article (login held)
  (declare (xargs :guard t))
  (fn-inj-append *fn-mvb-approved-field*
                 (fn-inj-append login (fn-inj-append *fn-inj-crlf* held))))

(defun fn-mvb-join-groups (groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (append (fn-record-string-octets (car groups))
              (if (consp (cdr groups))
                  (cons 44 (fn-mvb-join-groups (cdr groups)))
                nil))
    nil))

(defun fn-mvb-groups-octets (groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (cons (fn-record-string-octets (car groups))
            (fn-mvb-groups-octets (cdr groups)))
    nil))

(defconst *fn-mvb-from* '(70 114 111 109 58 32 111 112 101 114 97 116 111 114 64))
                                                           ; "From: operator@"
(defconst *fn-mvb-subject* '(83 117 98 106 101 99 116 58 32 99 109 115 103 32
                             99 97 110 99 101 108 32))    ; "Subject: cmsg cancel "
(defconst *fn-mvb-control* '(67 111 110 116 114 111 108 58 32 99 97 110 99 101
                             108 32))                     ; "Control: cancel "
(defconst *fn-mvb-newsgroups* '(78 101 119 115 103 114 111 117 112 115 58 32))
(defconst *fn-mvb-body*
  ; "Withdrawn by the operator of this node: "
  '(87 105 116 104 100 114 97 119 110 32 98 121 32 116 104 101 32 111 112 101
    114 97 116 111 114 32 111 102 32 116 104 105 115 32 110 111 100 101 58 32))

; The cause article (RFC 5537 section 5.3: a cancel control message).
(defun fn-mvb-cancel-article (agent cause target groups reason)
  (declare (xargs :guard t))
  (let ((tgt (fn-record-string-octets target)))
    (fn-mod-concat
     (list *fn-mvb-from* agent *fn-inj-crlf*
           *fn-mvb-newsgroups* (fn-mvb-join-groups groups) *fn-inj-crlf*
           *fn-mvb-subject* tgt *fn-inj-crlf*
           *fn-mvb-control* tgt *fn-inj-crlf*
           (fn-inj-message-id-line (fn-record-string-octets cause))
           *fn-inj-crlf*
           *fn-mvb-body* (fn-record-string-octets reason) *fn-inj-crlf*))))

;; -----------------------------------------------------------------------------
; Moderators

; Whether LOGIN (octets) is a moderator, under the owner's status list
; CLOSED, of a moderated group whose queue is Q (octets).
(defun fn-mvb-moderates-queue (login q closed)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (enable fn-nntp-moderated-entryp)))))
  (if (consp closed)
      (or (and (fn-nntp-moderated-entryp (car closed))
               (equal (car (car closed)) :moderated)
               (equal (fn-mod-entry-queue (car closed)) q)
               (member-equal login (true-list-fix
                                    (fn-mod-entry-moderators (car closed))))
               t)
          (fn-mvb-moderates-queue login q (cdr closed)))
    nil))

; ... of a group whose queue is one of GROUPS (the envelope's, strings).
(defun fn-mvb-moderates-some (login groups closed)
  (declare (xargs :guard t))
  (if (consp groups)
      (or (fn-mvb-moderates-queue login (fn-record-string-octets (car groups))
                                  closed)
          (fn-mvb-moderates-some login (cdr groups) closed))
    nil))

; LOGIN's connection configuration: CFG with the status list LOGIN's view
; has (`fn-auth-moderation-config', books/nntp-auth.lisp, for an
; authenticated LOGIN).
(defun fn-mvb-login-config (cfg login)
  (declare (xargs :guard t))
  (if (fn-inj-config-shapep cfg)
      (fn-inj-make-config-full
       (fn-inj-config-allow cfg) (fn-inj-config-agent cfg)
       (fn-inj-config-groups cfg)
       (fn-inj-post-bound (fn-inj-config-max-octets cfg)
                          (fn-inj-config-header-limits cfg))
       (fn-inj-config-listing cfg)
       (fn-mod-session-entries (fn-inj-config-closed cfg) login))
    cfg))

; -----------------------------------------------------------------------------
; The plan
;
; The decisions are over what the owner carries, passed explicitly: RAW the
; view's article list (every stored article, withdrawn or not), WS its
; withdrawal records, VERDICTS its verdicts, CFG the owner's posting
; configuration (its status list holds the moderated entries
; books/owner-agent.lisp installs), CLOCK the owner's clock, NODE the
; Store's node, ROWS the configuration's authorities rows.  `fn-mvb-plan'
; takes them from the owner (`fn-mvb-plan-unfolds').

; The envelope of ID among RAW with LOGIN a moderator of its group and the
; envelope held: (:envelope ARTICLE), or (:refused REASON).
(defun fn-mvb-held-envelope (raw ws verdicts closed login id)
  (declare (xargs :guard t))
  (let ((a (fn-cev-find-article (fn-mvb-envelope-id id) raw)))
    (cond ((not (consp a)) (list :refused :no-such-held-article))
          ((not (fn-mvb-moderates-some login (fn-article-groups a) closed))
           (list :refused :not-a-moderator))
          (t (let ((state (fn-cev-envelope-state a ws raw verdicts)))
               (cond ((equal state "held") (list :envelope a))
                     ((equal state "approved") (list :refused :already-approved))
                     (t (list :refused :already-rejected))))))))

; The held proto-article of envelope A: the body of its octets.  A is an
; archive article, whose payload position is an arena HANDLE since the
; records flip (books/store-intern.lisp); its octets are read through the
; arena (books/nntp-session.lisp fn-nntp-article-bytes, which passes a
; payload that is not a handle through), never parsed from the handle.  The
; arena is only read (flip-L6-2's rule).  Before lane matrix-reds this read
; the handle itself and every approve answered :envelope-malformed.
(defun fn-mvb-held-article (a fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-mvb-after-blank (fn-nntp-article-bytes a fn-arena)))

(defun fn-mvb-approve (raw ws verdicts cfg clock login id fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((e (fn-mvb-held-envelope raw ws verdicts (fn-inj-config-closed cfg)
                                 login id)))
    (if (not (equal (car e) :envelope))
        e
      (let ((held (fn-mvb-held-article (cadr e) fn-arena)))
        (if (not (consp held))
            (list :refused :envelope-malformed)
          (let* ((octets (fn-mvb-approved-article login held))
                 (d (fn-post-gated-decision
                     octets (fn-mvb-login-config cfg login) clock)))
            (if (not (fn-inj-injectedp d))
                (list :refused (fn-inj-decision-reason d))
              (let* ((msgid (fn-inj-decision-msgid d))
                     (groups (fn-inj-decision-groups d))
                     (op (fn-own-operator-decision cfg clock :absent msgid groups
                                                   octets)))
                (if (not (fn-inj-injectedp op))
                    (list :refused :operator-decision-refused)
                  (list :submit msgid groups octets))))))))))

; The cause is a cancel control message, so the owner files it in
; `control.cancel' (books/control-classify.lisp `fn-ctl-filing-group'),
; which the operator creates; its Newsgroups names that group.
(defconst *fn-mvb-cancel-groups* '("control.cancel"))

; The vector the live administration takes for the row (CAUSE TARGET REASON 1).
(defun fn-mvb-withdraw-argv (cause target reason)
  (declare (xargs :guard t))
  (list (fn-record-string-octets "article")
        (fn-record-string-octets "withdraw-record")
        (fn-record-string-octets cause)
        (fn-record-string-octets target)
        (fn-record-string-octets reason)))

; The node's withdrawal of TARGET (a string) with REASON (a string).
(defun fn-mvb-withdraw (raw cfg clock node rows target reason)
  (declare (xargs :guard t))
  (let* ((a (fn-cev-find-article target raw))
         (cause (fn-mvb-cause target))
         (row (fn-cfg-withdrawal-row rows cause)))
    (cond ((not (consp a)) (list :refused :no-such-article))
          ((not (and (fn-cfg-msgid-labelp target) (fn-cfg-msgid-labelp cause)
                     (not (equal cause target)) (fn-cfg-labelp reason)))
           (list :refused :withdrawal-unrepresentable))
          ((consp (fn-cev-find-article cause raw))
           (list :refused :already-withdrawn))
          ((and row (not (equal (fn-cfg-row-b row) target)))
           (list :refused :withdrawal-row-conflict))
          (t (let* ((msgid (fn-record-string-octets cause))
                    (octets (fn-mvb-cancel-article (fn-inj-config-agent cfg)
                                                   cause target
                                                   *fn-mvb-cancel-groups* reason))
                    (groups (fn-mvb-groups-octets *fn-mvb-cancel-groups*))
                    (filing (fn-pa-filing-plan
                             octets groups
                             (fn-state-groups (fn-node-acceptance node))))
                    (op (fn-own-operator-decision cfg clock :absent msgid groups
                                                  octets)))
               ; The commit files a control article in its filing group
               ; (NNT-010: the owner's commit gate, fn-owner-bound-commit-gate,
               ; commits only when the filing plan files the payload in
               ; exactly the submitted groups), and the operator path must
               ; inject it as planned: either refusal is the plan's, by its
               ; reason, before any row.
               (cond ((not (equal filing (list :file groups)))
                      (list :refused (if (equal (car filing) :refused)
                                         (cadr filing)
                                       :control-not-filed)))
                     ((not (fn-inj-injectedp op))
                      (list :refused (fn-inj-decision-reason op)))
                     (t (list :withdraw
                              (if row nil
                                (fn-mvb-withdraw-argv cause target reason))
                              msgid groups octets))))))))

(defconst *fn-mvb-rejected-reason* "rejected by the moderator")

(defun fn-mvb-reject-reason (reason)
  (declare (xargs :guard t))
  (if (equal reason "") *fn-mvb-rejected-reason* reason))

(defun fn-mvb-reject (raw ws verdicts cfg clock node rows login id reason)
  (declare (xargs :guard t))
  (let ((e (fn-mvb-held-envelope raw ws verdicts (fn-inj-config-closed cfg)
                                 login id)))
    (if (not (equal (car e) :envelope))
        e
      (fn-mvb-withdraw raw cfg clock node rows (fn-article-msgid (cadr e))
                       (fn-mvb-reject-reason reason)))))

; The operator decision a plan checks is the fresh one (STORED :absent): the
; plan reads the arena only for the held envelope's own octets (approve).  It is a pre-check: the host then
; runs the planned submission through the operator path, whose decision
; reads the stored octets (books/owner.lisp fn-own-operator-decision over
; books/owner-served-invariants.lisp fn-own-operator-stored-octets) and
; resubmits a stored injection as the duplicate it is (flip-L8-2).
;
; OP is :approve, :reject or :withdraw; LOGIN, ID and REASON are the
; request's octets; OC the owner and its configuration (books/owner-config).
(defun fn-mvb-plan (op login id reason oc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (v (fn-own-view o))
         (raw (fn-own-view-raw v))
         (ws (fn-own-view-withdrawals v))
         (verdicts (fn-own-view-verdicts v))
         (cfg (fn-own-config o))
         (rows (fn-cfg-authorities (fn-cfg-value (fn-ocfg-config oc))))
         (id (fn-record-octets-string id))
         (reason (fn-record-octets-string reason)))
    (cond ((equal op :approve)
           (fn-mvb-approve raw ws verdicts cfg (fn-own-clock o) login id fn-arena))
          ((equal op :reject)
           (fn-mvb-reject raw ws verdicts cfg (fn-own-clock o)
                          (fn-sn-node (fn-own-store o)) rows login id reason))
          ((equal op :withdraw)
           (fn-mvb-withdraw raw cfg (fn-own-clock o) (fn-sn-node (fn-own-store o))
                            rows id reason))
          (t (list :refused :moderation-request)))))

; -----------------------------------------------------------------------------
; The keystones

; The host calls `fn-mvb-plan' (host/owner-host.lisp fn-owner-moderation-
; plan); it is the three decisions below over what the owner carries.
(defthm fn-mvb-plan-unfolds
  (equal (fn-mvb-plan op login id reason oc fn-arena)
         (let* ((o (fn-ocfg-owner oc))
                (v (fn-own-view o))
                (cfg (fn-own-config o))
                (rows (fn-cfg-authorities (fn-cfg-value (fn-ocfg-config oc)))))
           (cond ((equal op :approve)
                  (fn-mvb-approve (fn-own-view-raw v) (fn-own-view-withdrawals v)
                                  (fn-own-view-verdicts v) cfg (fn-own-clock o) login
                                  (fn-record-octets-string id) fn-arena))
                 ((equal op :reject)
                  (fn-mvb-reject (fn-own-view-raw v) (fn-own-view-withdrawals v)
                                 (fn-own-view-verdicts v) cfg (fn-own-clock o)
                                 (fn-sn-node (fn-own-store o)) rows login
                                 (fn-record-octets-string id)
                                 (fn-record-octets-string reason)))
                 ((equal op :withdraw)
                  (fn-mvb-withdraw (fn-own-view-raw v) cfg (fn-own-clock o)
                                   (fn-sn-node (fn-own-store o)) rows
                                   (fn-record-octets-string id)
                                   (fn-record-octets-string reason)))
                 (t (list :refused :moderation-request)))))
  :hints (("Goal" :in-theory (disable fn-mvb-approve fn-mvb-reject fn-mvb-withdraw))))


; KEYSTONE (PKT-657; PRF-228).  APPROVE COMMITS EXACTLY THE HELD ARTICLE WITH
; APPROVED, AS LOGIN'S APPROVAL OVER NNTP WOULD.  A submission is planned
; only when LOGIN moderates a group the envelope queues for, the envelope is
; held (neither approved nor rejected), and the octets are the envelope's
; proto-article with `Approved: LOGIN' first; the served POST's decision
; (`fn-post-gated-decision') under LOGIN's moderation view injects them under
; the planned Message-ID and groups, and the operator path the host submits
; through (`fn-own-operator-decision', the (:operator-submit ...) event)
; injects the same octets under that Message-ID and those groups
; (books/owner-invariants.lisp
; `fn-own-operator-decision-is-an-injection-of-the-payload').  Subject:
; `fn-mvb-approve', called by `fn-mvb-plan'.
(defthm fn-mvb-approve-commits-the-held-article-approved
  (implies (equal (car (fn-mvb-approve raw ws verdicts cfg clock login id fn-arena))
                  :submit)
           (let* ((plan (fn-mvb-approve raw ws verdicts cfg clock login id fn-arena))
                  (a (fn-cev-find-article (fn-mvb-envelope-id id) raw))
                  (octets (fn-mvb-approved-article login (fn-mvb-held-article a fn-arena)))
                  (d (fn-post-gated-decision octets (fn-mvb-login-config cfg login)
                                             clock)))
             (and (fn-mvb-moderates-some login (fn-article-groups a)
                                         (fn-inj-config-closed cfg))
                  (equal (fn-cev-envelope-state a ws raw verdicts) "held")
                  (equal (cadddr plan) octets)
                  (fn-inj-injectedp d)
                  (equal (cadr plan) (fn-inj-decision-msgid d))
                  (equal (caddr plan) (fn-inj-decision-groups d))
                  (fn-inj-injectedp (fn-own-operator-decision
                                     cfg clock :absent (cadr plan) (caddr plan)
                                     octets)))))
  :hints (("Goal" :in-theory (disable fn-post-gated-decision fn-own-operator-decision fn-post-gated-decision-unfolds
                                      fn-mvb-moderates-some fn-cev-envelope-state
                                      fn-cev-find-article fn-mvb-approved-article
                                      fn-mvb-after-blank fn-mvb-login-config
                                      fn-mvb-envelope-id))))


; The representation boundary (PKT-657, lane matrix-reds), by definition:
; the ledger reads both sides as the same term, so it is cited as the
; bridge, not as a keystone.  The held proto-article the approval commits is the body of
; the envelope's OCTET MODEL (books/nntp-session.lisp fn-nntp-article-alpha:
; the archive article with its handle replaced by the bytes it names), the
; body the pre-flip plan parsed from the envelope's own payload.  With the
; keystone above: the approved octets are `Approved: LOGIN' and that body.
(defthm fn-mvb-held-article-is-the-model-body-by-definition
  (equal (fn-mvb-held-article a fn-arena)
         (fn-mvb-after-blank (fn-article-payload (fn-nntp-article-alpha a fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-article-alpha) (fn-nntp-article-bytes fn-mvb-after-blank)))))

; KEYSTONE (PKT-657; PRF-228).  ONLY A MODERATOR OF THE GROUP APPROVES OR
; REJECTS.  A LOGIN that moderates no group the envelope queues for is
; refused (by name, :not-a-moderator, when the envelope exists).
(defthm fn-mvb-only-a-moderator-approves-or-rejects
  (implies (not (fn-mvb-moderates-some
                 login (fn-article-groups (fn-cev-find-article (fn-mvb-envelope-id id) raw))
                 (fn-inj-config-closed cfg)))
           (and (equal (car (fn-mvb-approve raw ws verdicts cfg clock login id fn-arena))
                       :refused)
                (equal (car (fn-mvb-reject raw ws verdicts cfg clock node rows login id reason))
                       :refused)))
  :hints (("Goal" :in-theory (disable fn-post-gated-decision fn-own-operator-decision fn-post-gated-decision-unfolds
                                      fn-mvb-moderates-some fn-cev-envelope-state
                                      fn-cev-find-article fn-mvb-approved-article
                                      fn-mvb-after-blank fn-mvb-login-config
                                      fn-mvb-envelope-id fn-mvb-withdraw))))


; KEYSTONE (PKT-657; PRF-228).  REJECT IS THE NODE'S WITHDRAWAL OF EXACTLY
; THE HELD ENVELOPE, by a moderator of its group.
(defthm fn-mvb-reject-withdraws-the-held-envelope
  (implies (equal (car (fn-mvb-reject raw ws verdicts cfg clock node rows login id reason))
                  :withdraw)
           (let ((a (fn-cev-find-article (fn-mvb-envelope-id id) raw)))
             (and (fn-mvb-moderates-some login (fn-article-groups a)
                                         (fn-inj-config-closed cfg))
                  (equal (fn-cev-envelope-state a ws raw verdicts) "held")
                  (equal (fn-mvb-reject raw ws verdicts cfg clock node rows login id reason)
                         (fn-mvb-withdraw raw cfg clock node rows
                                          (fn-article-msgid a)
                                          (fn-mvb-reject-reason reason))))))
  :hints (("Goal" :in-theory (disable fn-mvb-moderates-some fn-cev-envelope-state
                                      fn-cev-find-article fn-mvb-envelope-id
                                      fn-mvb-withdraw))))


; KEYSTONE (PKT-575, CT3; PRF-196).  THE WITHDRAWAL NAMES EXACTLY ITS
; TARGET: a stored TARGET, the cause <fn-withdraw....> derived from it, the
; row's vector for (CAUSE TARGET REASON) when no row exists (else the
; existing row already names TARGET), and the cancel article
; `Control: cancel TARGET' under Message-ID CAUSE.
(defthm fn-mvb-withdraw-names-exactly-its-target
  (implies (equal (car (fn-mvb-withdraw raw cfg clock node rows target reason)) :withdraw)
           (let* ((plan (fn-mvb-withdraw raw cfg clock node rows target reason))
                  (a (fn-cev-find-article target raw))
                  (cause (fn-mvb-cause target)))
             (and (consp a)
                  (fn-cfg-msgid-labelp cause)
                  (fn-cfg-msgid-labelp target)
                  (not (equal cause target))
                  (equal (caddr plan) (fn-record-string-octets cause))
                  (equal (car (cddddr plan))
                         (fn-mvb-cancel-article (fn-inj-config-agent cfg) cause target
                                                *fn-mvb-cancel-groups* reason))
                  (equal (fn-pa-filing-plan (car (cddddr plan)) (cadddr plan)
                                            (fn-state-groups (fn-node-acceptance node)))
                         (list :file (cadddr plan)))
                  (fn-inj-injectedp (fn-own-operator-decision
                                     cfg clock :absent (caddr plan) (cadddr plan)
                                     (car (cddddr plan))))
                  (if (cadr plan)
                      (and (equal (cadr plan) (fn-mvb-withdraw-argv cause target reason))
                           (not (fn-cfg-withdrawal-row rows cause)))
                    (equal (fn-cfg-withdrawal-target rows cause) target)))))
  :hints (("Goal" :in-theory (disable fn-cev-find-article fn-mvb-cause
                                      fn-mvb-cancel-article fn-cfg-msgid-labelp
                                      fn-mvb-withdraw-argv fn-cfg-labelp
                                      fn-own-operator-decision fn-pa-filing-plan))))

; KEYSTONE (PKT-575, CT3; PRF-196).  After the planned row (admitted as
; `fn-cfg-withdraw-article-authorizes-the-cause' says), the configuration
; authorizes CAUSE for exactly TARGET: the antecedent of
; books/control-authority.lisp `fn-ctl-node-withdrawal-withdraws-exactly-its-
; target', which the refresh applies when it first publishes CAUSE (the
; configuration in force at CAUSE's txid holds the row, which the host
; publishes first).
(defthm fn-mvb-withdraw-makes-the-node-authorize-exactly-its-target
  (implies (equal (car (fn-mvb-withdraw raw cfg clock node (fn-cfg-authorities v) target reason))
                  :withdraw)
           (let* ((plan (fn-mvb-withdraw raw cfg clock node (fn-cfg-authorities v) target reason))
                  (cause (fn-mvb-cause target))
                  (v2 (if (cadr plan)
                          (fn-cfg-apply-delta v gen stamp
                                              (fn-cfg-withdraw-article cause target
                                                                       reason))
                        v)))
             (fn-ctl-node-authorizesp cause target (fn-cfg-make gen2 v2))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-withdraw-article-reason fn-cfg-withdraw-article)
                                  (fn-cev-find-article fn-mvb-cause
                                   fn-mvb-cancel-article fn-cfg-msgid-labelp
                                   fn-mvb-withdraw-argv fn-cfg-labelp
                                   fn-cfg-apply-delta fn-own-operator-decision
                                   fn-pa-filing-plan))
           :use ((:instance fn-cfg-withdraw-article-authorizes-the-cause
                            (cause (fn-mvb-cause target))
                            (c (fn-mvb-cause target)))))))
