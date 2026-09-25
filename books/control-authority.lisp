; fn: control authority (packet C2) and cancel as a withdrawal (packet C3).
;
; D29 (planning/decisions.md, 2026-09-25) and the design
; planning/design-2026-09-25-control-messages.md sections 2.1 to 2.5.  The
; instruction is the operator's grant, a configuration row this node holds
; (books/config.lisp, the `authorities' slot, delta kinds 11 and 12); a
; control article is signed evidence that a granted principal asked, and it
; acts only inside the grant.
;
;   `fn-ctl-authorize'          the authority decision: the control article's
;                               verdict is :verified HERE and a grant covers
;                               the verb and every group involved.
;   `fn-ctl-cancel-plan'        the decision recorded when a cancel commits:
;                               a withdrawal record bound to its cause (the
;                               cancel's Message-ID and verified principal),
;                               its target, its scope (the principal's cancel
;                               grants) and the configuration generation it was
;                               decided under; or a decline with its reason.
;   `fn-ctl-withdrawal-effect'  a pure function of that record and the
;                               TARGET's accepted group bindings and verdict:
;                               :author, :authority or (:decline REASON).  The
;                               target's declared groups in the cancel never
;                               enter, so naming a narrower list gains nothing.
;   `fn-ctl-visible-articles'   the articles a newly published reader view
;                               serves: every article except a target some
;                               withdrawal whose cause is in the SAME article
;                               list withdraws.  Retention, the duplicate
;                               history and the Store are not inputs and are
;                               not outputs: nothing here deletes a byte.
;
; Prefix `fn-ctl-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "config")
(include-book "control-classify")
(include-book "stx-verify")
(include-book "acceptance")

; -----------------------------------------------------------------------------
; Namespace coverage.  A pattern is a group name (covers exactly that group)
; or PREFIX.* (covers every group PREFIX.X, not PREFIX itself); compared as
; octets.

(defun fn-ctl-dotted-under-p (prefix group)
  (declare (xargs :guard t))
  (and (true-listp prefix) (true-listp group)
       (< (+ 1 (len prefix)) (len group))
       (equal (take (len prefix) group) prefix)
       (equal (nth (len prefix) group) 46)))

(defun fn-ctl-pattern-covers-p (pattern group)
  (declare (xargs :guard t))
  (let ((p (fn-record-string-octets pattern))
        (g (fn-record-string-octets group)))
    (or (and (stringp pattern) (stringp group) (equal p g))
        (let ((prefix (fn-cfg-namespace-prefix-octets p)))
          (and (stringp pattern) (stringp group) (consp prefix)
               (fn-ctl-dotted-under-p prefix g))))))

(defun fn-ctl-some-pattern-covers-p (patterns group)
  (declare (xargs :guard t))
  (if (consp patterns)
      (or (fn-ctl-pattern-covers-p (car patterns) group)
          (fn-ctl-some-pattern-covers-p (cdr patterns) group))
    nil))

; Every group in GROUPS is covered by some pattern.
(defun fn-ctl-covers-every-p (patterns groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (and (fn-ctl-some-pattern-covers-p patterns (car groups))
           (fn-ctl-covers-every-p patterns (cdr groups)))
    t))

; The first group no pattern covers, or nil.
(defun fn-ctl-first-uncovered (patterns groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (if (fn-ctl-some-pattern-covers-p patterns (car groups))
          (fn-ctl-first-uncovered patterns (cdr groups))
        (car groups))
    nil))

; -----------------------------------------------------------------------------
; Grants.  The namespaces PRINCIPAL-HEX holds VERB over, in row order.

(defun fn-ctl-grant-scope (principal verb rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (let ((rest (fn-ctl-grant-scope principal verb (cdr rows))))
        (if (and (equal (fn-cfg-row-b (car rows)) principal)
                 (equal (fn-cfg-row-c (car rows)) verb))
            (cons (fn-cfg-row-a (car rows)) rest)
          rest))
    nil))

(defun fn-ctl-holds-any-grant-p (principal rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (equal (fn-cfg-row-b (car rows)) principal)
          (fn-ctl-holds-any-grant-p principal (cdr rows)))
    nil))

; -----------------------------------------------------------------------------
; Verdicts.  A Store verdict is (TOKEN DETAIL GENERATION)
; (`fn-stx-make-verdict'); schema 1 writes the 32-octet principal as the
; detail of :verified and :carried.  The principal is spelled as the
; configuration spells it: 64 lowercase hex characters.

(defun fn-ctl-principal-detailp (detail)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp detail) (equal (len detail) 32)))

(defun fn-ctl-principal-hex (detail)
  (declare (xargs :guard t))
  (if (fn-ctl-principal-detailp detail)
      (fn-record-octets-string (fn-stx-hex-octets detail))
    nil))

; The principal this node itself verified, or nil.
(defun fn-ctl-verified-principal (verdict)
  (declare (xargs :guard t))
  (if (and (equal (fn-stx-verdict-token verdict) :verified)
           (fn-ctl-principal-detailp (fn-stx-verdict-detail verdict)))
      (fn-ctl-principal-hex (fn-stx-verdict-detail verdict))
    nil))

; The principal an article's stored verdict names: verified here, or carried
; (D23: the carrier names it, this node verified nothing).
(defun fn-ctl-named-principal (verdict)
  (declare (xargs :guard t))
  (if (and (member-equal (fn-stx-verdict-token verdict) '(:verified :carried))
           (fn-ctl-principal-detailp (fn-stx-verdict-detail verdict)))
      (fn-ctl-principal-hex (fn-stx-verdict-detail verdict))
    nil))

(defun fn-ctl-unverified-reason (verdict)
  (declare (xargs :guard t))
  (let ((token (fn-stx-verdict-token verdict)))
    (cond ((not verdict) :unsigned)
          ((equal token :carried) :carried)
          ((equal token :verified) :legacy-verdict)
          (t :unverified))))

; -----------------------------------------------------------------------------
; C2: the authority decision.
;
; VERDICT is the control article's stored verdict, VERB its verb as the
; configuration spells it ("cancel"), GROUPS every group the command reaches
; (for a cancel: the TARGET's accepted group bindings), ROWS the authorities
; slot of the configuration the decision is made under.  Returns
; (:execute VERB PRINCIPAL SCOPE) or (:decline REASON).

(defun fn-ctl-authorize (verdict verb groups rows)
  (declare (xargs :guard t))
  (let ((principal (fn-ctl-verified-principal verdict)))
    (if (not principal)
        (list :decline (fn-ctl-unverified-reason verdict))
      (let ((scope (fn-ctl-grant-scope principal verb rows)))
        (cond ((not (consp scope))
               (list :decline (if (fn-ctl-holds-any-grant-p principal rows)
                                  :verb-not-granted
                                :no-grant)))
              ((not (consp groups)) (list :decline :no-groups))
              ((not (fn-ctl-covers-every-p scope groups))
               (list :decline :outside-namespace))
              (t (list :execute verb principal scope)))))))

; -----------------------------------------------------------------------------
; C3: the cancel's target and the withdrawal record.

(defun fn-ctl-msgid-octetsp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) (< 2 (len xs))
       (equal (car xs) 60) (equal (car (last xs)) 62)))

; `cancel <msgid>': exactly one argument that is bracketed.
(defun fn-ctl-cancel-target (classified)
  (declare (xargs :guard t))
  (if (and (true-listp classified)
           (equal (len classified) 3)
           (eq (car classified) :control)
           (equal (cadr classified) '(99 97 110 99 101 108))
           (true-listp (caddr classified))
           (equal (len (caddr classified)) 1)
           (fn-ctl-msgid-octetsp (car (caddr classified))))
      (fn-record-octets-string (car (caddr classified)))
    nil))

; (:withdrawal TARGET CAUSE PRINCIPAL SCOPE GENERATION)
(defun fn-ctl-withdrawal-make (target cause principal scope generation)
  (declare (xargs :guard t))
  (list :withdrawal target cause principal scope generation))
(defun fn-ctl-withdrawalp (w)
  (declare (xargs :guard t))
  (and (true-listp w) (equal (len w) 6) (eq (car w) :withdrawal)))
;; A total positional accessor.
(defun fn-ctl-at (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (consp x)
      (if (zp (nfix n)) (car x) (fn-ctl-at (1- (nfix n)) (cdr x)))
    nil))
(defun fn-ctl-w-target (w) (declare (xargs :guard t)) (fn-ctl-at 1 w))
(defun fn-ctl-w-cause (w) (declare (xargs :guard t)) (fn-ctl-at 2 w))
(defun fn-ctl-w-principal (w) (declare (xargs :guard t)) (fn-ctl-at 3 w))
(defun fn-ctl-w-scope (w) (declare (xargs :guard t)) (fn-ctl-at 4 w))
(defun fn-ctl-w-generation (w) (declare (xargs :guard t)) (fn-ctl-at 5 w))

; The decision made when a withdrawing article commits, under the
; configuration CFG it commits under (generation and authorities slot).  It
; reads the withdrawing article only: its verdict (verified HERE), its
; Message-ID and its one TARGET (a cancel's argument or a Supersedes field,
; `fn-ctl-article-target').  It never reads the target article, which may
; not have arrived; the target enters at `fn-ctl-withdrawal-effect'.  The
; scope is the principal's cancel grants in CFG, possibly empty (then only
; the author basis can apply).  RFC 5537 section 5.4: a Supersedes field
; withdraws its target "exactly as a cancel would", under the same
; authentication, so the two share this decision.
(defun fn-ctl-withdrawal-plan (cause-msgid cause-verdict target cfg)
  (declare (xargs :guard t))
  (let ((principal (fn-ctl-verified-principal cause-verdict)))
    (cond ((not principal)
           (list :decline (fn-ctl-unverified-reason cause-verdict)))
          ((not target) (list :decline :no-target))
          ((equal target cause-msgid) (list :decline :self-target))
          (t (fn-ctl-withdrawal-make
              target cause-msgid principal
              (fn-ctl-grant-scope principal "cancel"
                                  (fn-cfg-authorities (fn-cfg-value cfg)))
              (fn-cfg-generation cfg))))))

(defun fn-ctl-cancel-plan (cause-msgid cause-verdict classified cfg)
  (declare (xargs :guard t))
  (fn-ctl-withdrawal-plan cause-msgid cause-verdict
                          (fn-ctl-cancel-target classified) cfg))

; ---------------------------------------------------------------------------
; Supersedes (RFC 5537 section 5.4; RFC 5536 section 3.2.12:
; Supersedes = SP msg-id).  An ordinary article (no Control field; the
; classifier makes Control beside Supersedes malformed) with exactly one
; Supersedes field whose value is one bracketed Message-ID names that
; target; anything else names none.  The superseding article itself is
; an ordinary article, filed in its Newsgroups.

(defun fn-ctl-supersedes-target (fields)
  (declare (xargs :guard t))
  (let ((sups (fn-ctl-fields-named *fn-ctl-supersedes-name* fields)))
    (if (and (consp sups) (atom (cdr sups))
             (true-listp (car sups)) (equal (len (car sups)) 3))
        (let ((words (fn-ctl-words
                      (fn-article-field-unfolded-value (car sups)))))
          (if (and (consp words) (atom (cdr words))
                   (fn-ctl-msgid-octetsp (car words)))
              (fn-record-octets-string (car words))
            nil))
      nil)))

; The target an article withdraws: a cancel's argument, or an ordinary
; article's Supersedes target; nil for every other article.
(defun fn-ctl-article-target (fields)
  (declare (xargs :guard t))
  (let ((classified (fn-ctl-classify-fields fields)))
    (cond ((fn-ctl-cancel-target classified))
          ((eq classified :ordinary) (fn-ctl-supersedes-target fields))
          (t nil))))

; Over received octets, one parse.
(defun fn-ctl-target-octets (received)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse received)))
    (if (fn-article-result-okp parsed)
        (let ((article (fn-article-result-article parsed)))
          (if (true-listp article)
              (fn-ctl-article-target (fn-article-fields article))
            nil))
      nil)))

; The effect of a withdrawal record on its target, from the target's
; accepted group bindings T-GROUPS and its stored verdict T-VERDICT.
;   :author     the target's verdict names the canceller (verified or
;               carried; a forgery carrying P's name is P's to withdraw);
;   :authority  the record's scope covers EVERY group the target is served
;               in (the conservative cross-post rule, D29);
;   (:decline REASON) otherwise.
(defun fn-ctl-withdrawal-effect (w t-groups t-verdict)
  (declare (xargs :guard t))
  (let ((named (fn-ctl-named-principal t-verdict))
        (scope (fn-ctl-w-scope w)))
    (cond ((not (fn-ctl-withdrawalp w)) (list :decline :no-record))
          ((and named (equal named (fn-ctl-w-principal w))) :author)
          ((not (consp scope)) (list :decline :no-grant))
          ((not (consp t-groups)) (list :decline :no-groups))
          ((not (fn-ctl-covers-every-p scope t-groups))
           (list :decline :outside-namespace))
          (t :authority))))

(defun fn-ctl-effect-withdrawsp (effect)
  (declare (xargs :guard t))
  (or (eq effect :author) (eq effect :authority)))

; -----------------------------------------------------------------------------
; The visible view.  ARTICLES is an acceptance archive's article list,
; WITHDRAWALS the records, VERDICTS the historical verdict pairs.  A record
; acts only when its cause is itself among ARTICLES: a view that does not
; contain the cancel is not changed by it.  So one monotone record list
; serves every pinned prefix, and a connection pinned before the cancel
; keeps its archive until it advances.

(defun fn-ctl-lookup-verdict (msgid verdicts)
  (declare (xargs :guard t))
  (if (consp verdicts)
      (if (and (consp (car verdicts)) (equal (car (car verdicts)) msgid))
          (cdr (car verdicts))
        (fn-ctl-lookup-verdict msgid (cdr verdicts)))
    nil))

(defun fn-ctl-has-msgid-p (msgid articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (or (and (consp (car articles))
               (equal (fn-article-msgid (car articles)) msgid))
          (fn-ctl-has-msgid-p msgid (cdr articles)))
    nil))

; Does some record withdraw ARTICLE within ARTICLES?
(defun fn-ctl-withdrawn-by-p (article withdrawals articles verdicts)
  (declare (xargs :guard t))
  (if (consp withdrawals)
      (let ((w (car withdrawals)))
        (or (and (fn-ctl-withdrawalp w)
                 (consp article)
                 (equal (fn-ctl-w-target w) (fn-article-msgid article))
                 (fn-ctl-has-msgid-p (fn-ctl-w-cause w) articles)
                 (fn-ctl-effect-withdrawsp
                  (fn-ctl-withdrawal-effect
                   w (fn-article-groups article)
                   (fn-ctl-lookup-verdict (fn-article-msgid article)
                                          verdicts))))
            (fn-ctl-withdrawn-by-p article (cdr withdrawals) articles
                                   verdicts)))
    nil))

(defun fn-ctl-visible-filter (xs withdrawals articles verdicts)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (fn-ctl-withdrawn-by-p (car xs) withdrawals articles verdicts)
          (fn-ctl-visible-filter (cdr xs) withdrawals articles verdicts)
        (cons (car xs)
              (fn-ctl-visible-filter (cdr xs) withdrawals articles verdicts)))
    nil))

(defun fn-ctl-visible-articles (articles withdrawals verdicts)
  (declare (xargs :guard t))
  (fn-ctl-visible-filter articles withdrawals articles verdicts))

; The withdrawal status of MSGID in ARTICLES: nil (not withdrawn), or the
; effect :author / :authority of the first record that withdraws it.
(defun fn-ctl-withdrawal-status (msgid withdrawals articles verdicts)
  (declare (xargs :guard t))
  (let ((article (fn-find-article msgid articles)))
    (if (and (consp article)
             (fn-ctl-withdrawn-by-p article withdrawals articles verdicts))
        :withdrawn
      nil)))

; -----------------------------------------------------------------------------
; The records a journal holds.  Recovery-only: a pure function of the
; durable configuration journal CONFIGS (each record applies before every
; Store event whose txid is not below its own, `fn-cpr-config-firstp') and
; the ordered accepted withdrawing articles.  Each ENTRY is (TXID
; CAUSE-MSGID VERDICT TARGET), the article's Store txid, Message-ID, stored
; verdict and target (`fn-ctl-article-target').  A record is decided under the configuration in force at
; its cancel's txid, never under today's.

(defun fn-ctl-configs-through (txid configs)
  (declare (xargs :guard t))
  (if (and (consp configs)
           (<= (nfix (fn-cfg-record-txid (car configs))) (nfix txid)))
      (cons (car configs) (fn-ctl-configs-through txid (cdr configs)))
    nil))

(defun fn-ctl-apply-records (cfg records)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-ctl-apply-records (fn-cfg-apply-record cfg (car records))
                            (cdr records))
    cfg))

(defun fn-ctl-config-at (txid configs)
  (declare (xargs :guard t))
  (fn-ctl-apply-records (fn-cfg-initial)
                        (fn-ctl-configs-through txid configs)))

(defun fn-ctl-journal-withdrawals (entries configs)
  (declare (xargs :guard t))
  (if (consp entries)
      (let* ((e (car entries))
             (plan (fn-ctl-withdrawal-plan
                    (fn-ctl-at 1 e) (fn-ctl-at 2 e) (fn-ctl-at 3 e)
                    (fn-ctl-config-at (fn-ctl-at 0 e) configs)))
             (rest (fn-ctl-journal-withdrawals (cdr entries) configs)))
        (if (fn-ctl-withdrawalp plan) (cons plan rest) rest))
    nil))

; =============================================================================
; C2 theorems.

; KEYSTONE (C2).  Authorization requires the verdict this node verified.  A
; :carried verdict (D23: carriage is not authority), an unsigned article
; (no verdict), a legacy :verified blob that names no principal, and every
; other token decline.  Subject: `fn-ctl-authorize', called by
; `fn-ctl-cancel-authorize' below over the configuration the cancel commits
; under.
(defthm fn-ctl-authorize-requires-verified-verdict
  (implies (equal (car (fn-ctl-authorize verdict verb groups rows)) :execute)
           (and (equal (fn-stx-verdict-token verdict) :verified)
                (fn-ctl-principal-detailp (fn-stx-verdict-detail verdict))))
  :hints (("Goal" :in-theory (disable fn-ctl-principal-detailp
                                      fn-ctl-principal-hex))))

; The row a coverage fact rests on: the first grant row of PRINCIPAL for
; VERB whose namespace covers GROUP.
(defun fn-ctl-covering-row (principal verb rows group)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-b (car rows)) principal)
               (equal (fn-cfg-row-c (car rows)) verb)
               (fn-ctl-pattern-covers-p (fn-cfg-row-a (car rows)) group))
          (car rows)
        (fn-ctl-covering-row principal verb (cdr rows) group))
    nil))

(defthm fn-ctl-scope-covers-means-a-covering-row
  (implies (fn-ctl-some-pattern-covers-p (fn-ctl-grant-scope principal verb rows)
                                         group)
           (let ((row (fn-ctl-covering-row principal verb rows group)))
             (and (member-equal row rows)
                  (equal (fn-cfg-row-b row) principal)
                  (equal (fn-cfg-row-c row) verb)
                  (fn-ctl-pattern-covers-p (fn-cfg-row-a row) group))))
  :hints (("Goal" :in-theory (disable fn-ctl-pattern-covers-p))))

(defthm fn-ctl-covers-every-member
  (implies (and (fn-ctl-covers-every-p patterns groups)
                (member-equal group groups))
           (fn-ctl-some-pattern-covers-p patterns group))
  :hints (("Goal" :in-theory (disable fn-ctl-some-pattern-covers-p))))

; KEYSTONE (C2).  Authorization requires a grant covering the verb and
; EVERY group involved: for each group of GROUPS there is a row of ROWS
; granting the verified principal VERB over a namespace that covers it, and
; GROUPS is not empty.
(defthm fn-ctl-authorize-requires-a-covering-grant
  (implies (and (equal (car (fn-ctl-authorize verdict verb groups rows))
                       :execute)
                (member-equal group groups))
           (let* ((principal (fn-ctl-verified-principal verdict))
                  (row (fn-ctl-covering-row principal verb rows group)))
             (and (member-equal row rows)
                  (equal (fn-cfg-row-b row) principal)
                  (equal (fn-cfg-row-c row) verb)
                  (fn-ctl-pattern-covers-p (fn-cfg-row-a row) group))))
  :hints (("Goal" :in-theory (disable fn-ctl-pattern-covers-p
                                      fn-ctl-verified-principal
                                      fn-ctl-covering-row
                                      fn-ctl-some-pattern-covers-p
                                      fn-ctl-covers-every-p)
           :use ((:instance fn-ctl-scope-covers-means-a-covering-row
                            (principal (fn-ctl-verified-principal verdict)))
                 (:instance fn-ctl-covers-every-member
                            (patterns (fn-ctl-grant-scope
                                       (fn-ctl-verified-principal verdict)
                                       verb rows)))))))

(defthm fn-ctl-authorize-execute-is-nonempty
  (implies (equal (car (fn-ctl-authorize verdict verb groups rows)) :execute)
           (consp groups))
  :hints (("Goal" :in-theory (disable fn-ctl-verified-principal
                                      fn-ctl-covers-every-p))))

; Revocation, the future half: after `(:revoke-control NS P)' is applied
; the principal holds no grant over NS, whatever its verb.
(defthm fn-ctl-revoked-namespace-leaves-the-scope
  (not (member-equal ns (fn-ctl-grant-scope
                         principal verb
                         (fn-cfg-rows-without-pair rows ns principal))))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-without-pair))))

(defthm fn-ctl-grant-scope-of-apply-revoke
  (equal (fn-cfg-authorities
          (fn-cfg-apply-delta v gen stamp (fn-cfg-revoke-control ns principal)))
         (fn-cfg-rows-without-pair (fn-cfg-authorities v) ns principal))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta
                                     fn-cfg-revoke-control))))

; Revocation, the past half.  A configuration record appended after every
; recorded cancel's txid does not change which configuration any of them
; was decided under.
(defthm fn-ctl-configs-through-of-later-append
  (implies (or (not (consp more))
               (< (nfix txid) (nfix (fn-cfg-record-txid (car more)))))
           (equal (fn-ctl-configs-through txid (append configs more))
                  (fn-ctl-configs-through txid configs))))

(defun fn-ctl-entries-below-p (entries bound)
  (declare (xargs :guard t))
  (if (consp entries)
      (and (< (nfix (fn-ctl-at 0 (car entries))) (nfix bound))
           (fn-ctl-entries-below-p (cdr entries) bound))
    t))

; KEYSTONE (C2/C3).  REVOCATION NEVER REWRITES A PAST RECORD.  The records
; the journal holds for ENTRIES are unchanged by any configuration records
; MORE appended after them (a revoke, a new grant, anything), since each
; record is decided under the configuration in force at its own cancel's
; txid.  Subject: `fn-ctl-journal-withdrawals'.
(defthm fn-ctl-revoke-changes-decisions-not-records
  (implies (and (fn-ctl-entries-below-p entries
                                        (fn-cfg-record-txid (car more))))
           (equal (fn-ctl-journal-withdrawals entries (append configs more))
                  (fn-ctl-journal-withdrawals entries configs)))
  :hints (("Goal" :induct (fn-ctl-journal-withdrawals entries configs)
           :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                               fn-cfg-apply-record))))

; The configuration in force after every recorded configuration is the
; fold of all of them, and the fold is what replay computes whenever replay
; succeeds: so the live configuration (the replay `fn-owner-recover'
; installs, `fn-ocl-config-historyp') is the one a cancel committing now is
; recorded under.
(defun fn-ctl-configs-all-through-p (txid configs)
  (declare (xargs :guard t))
  (if (consp configs)
      (and (<= (nfix (fn-cfg-record-txid (car configs))) (nfix txid))
           (fn-ctl-configs-all-through-p txid (cdr configs)))
    t))

(defthm fn-ctl-configs-through-all
  (implies (and (fn-ctl-configs-all-through-p txid configs)
                (true-listp configs))
           (equal (fn-ctl-configs-through txid configs) configs)))

(defthm fn-ctl-replay-is-the-fold
  (implies (not (equal (fn-config-replay-loop cfg reserved ceiling records)
                       :fault))
           (equal (fn-config-replay-loop cfg reserved ceiling records)
                  (fn-ctl-apply-records cfg records)))
  :hints (("Goal" :induct (fn-config-replay-loop cfg reserved ceiling records)
           :in-theory (e/d (fn-config-replay-loop)
                           (fn-cfg-record-acceptablep fn-cfg-apply-record)))))

(defthm fn-ctl-config-at-after-every-record-is-the-replay
  (implies (and (fn-ctl-configs-all-through-p txid configs)
                (true-listp configs)
                (not (equal (fn-config-replay reserved ceiling configs)
                            :fault)))
           (equal (fn-ctl-config-at txid configs)
                  (fn-config-replay reserved ceiling configs)))
  :hints (("Goal" :in-theory (e/d (fn-config-replay)
                                  (fn-ctl-apply-records
                                   fn-config-replay-loop)))))

; =============================================================================
; C3 theorems.

; The recorded decision names the principal this node verified, the
; principal's cancel grants in the configuration it commits under, and that
; configuration's generation.
(defthm fn-ctl-cancel-plan-record-is-bound
  (implies (fn-ctl-withdrawalp (fn-ctl-cancel-plan cause verdict classified cfg))
           (let ((w (fn-ctl-cancel-plan cause verdict classified cfg)))
             (and (equal (fn-ctl-w-cause w) cause)
                  (equal (fn-ctl-w-target w) (fn-ctl-cancel-target classified))
                  (equal (fn-ctl-w-principal w)
                         (fn-ctl-verified-principal verdict))
                  (fn-ctl-verified-principal verdict)
                  (equal (fn-ctl-w-scope w)
                         (fn-ctl-grant-scope
                          (fn-ctl-verified-principal verdict) "cancel"
                          (fn-cfg-authorities (fn-cfg-value cfg))))
                  (equal (fn-ctl-w-generation w) (fn-cfg-generation cfg)))))
  :hints (("Goal" :in-theory (disable fn-ctl-verified-principal
                                      fn-ctl-cancel-target
                                      fn-ctl-grant-scope))))

; The same binding for the general plan (a cancel or a Supersedes field).
(defthm fn-ctl-withdrawal-plan-record-is-bound
  (implies (fn-ctl-withdrawalp (fn-ctl-withdrawal-plan cause verdict target cfg))
           (let ((w (fn-ctl-withdrawal-plan cause verdict target cfg)))
             (and (equal (fn-ctl-w-cause w) cause)
                  (equal (fn-ctl-w-target w) target)
                  (equal (fn-ctl-w-principal w)
                         (fn-ctl-verified-principal verdict))
                  (fn-ctl-verified-principal verdict)
                  (equal (fn-ctl-w-scope w)
                         (fn-ctl-grant-scope
                          (fn-ctl-verified-principal verdict) "cancel"
                          (fn-cfg-authorities (fn-cfg-value cfg))))
                  (equal (fn-ctl-w-generation w) (fn-cfg-generation cfg)))))
  :hints (("Goal" :in-theory (disable fn-ctl-verified-principal
                                      fn-ctl-grant-scope))))

; KEYSTONE (C3).  A WITHDRAWAL TAKES EFFECT ONLY FOR THE AUTHOR OR AN
; AUTHORITY COVERING EVERY GROUP THE TARGET IS SERVED IN.  T-GROUPS is the
; target's accepted group bindings (the article's groups in the archive,
; `fn-ctl-withdrawn-by-p'); the cancel's own Newsgroups never enter.
(defthm fn-ctl-cancel-executes-only-for-author-or-authority
  (implies (fn-ctl-effect-withdrawsp (fn-ctl-withdrawal-effect w t-groups t-verdict))
           (or (and (fn-ctl-named-principal t-verdict)
                    (equal (fn-ctl-named-principal t-verdict)
                           (fn-ctl-w-principal w)))
               (and (consp (fn-ctl-w-scope w))
                    (consp t-groups)
                    (fn-ctl-covers-every-p (fn-ctl-w-scope w) t-groups))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ctl-named-principal
                                      fn-ctl-covers-every-p))))

; A record whose cause is not in the view changes nothing in it: a
; connection pinned before the cancel committed keeps its archive.
(defthm fn-ctl-withdrawn-by-p-ignores-an-absent-cause
  (implies (not (fn-ctl-has-msgid-p (fn-ctl-w-cause w) articles))
           (equal (fn-ctl-withdrawn-by-p article (cons w ws) articles verdicts)
                  (fn-ctl-withdrawn-by-p article ws articles verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-effect))))

(defthm fn-ctl-visible-filter-ignores-an-absent-cause
  (implies (not (fn-ctl-has-msgid-p (fn-ctl-w-cause w) articles))
           (equal (fn-ctl-visible-filter xs (cons w ws) articles verdicts)
                  (fn-ctl-visible-filter xs ws articles verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

; KEYSTONE (C3, the pinned-reader clause).  Every record whose cause is
; outside a pinned article list leaves that list's visible articles as they
; were.
(defthm fn-ctl-pinned-view-keeps-its-archive
  (implies (not (fn-ctl-has-msgid-p (fn-ctl-w-cause w) articles))
           (equal (fn-ctl-visible-articles articles (cons w ws) verdicts)
                  (fn-ctl-visible-articles articles ws verdicts))))

(defthm fn-ctl-visible-filter-member
  (iff (member-equal a (fn-ctl-visible-filter xs ws articles verdicts))
       (and (member-equal a xs)
            (not (fn-ctl-withdrawn-by-p a ws articles verdicts))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

; The article list is read as a set of Message-IDs.
(defthm fn-ctl-has-msgid-p-of-swap
  (equal (fn-ctl-has-msgid-p m (list* x y rest))
         (fn-ctl-has-msgid-p m (list* y x rest))))

(defthm fn-ctl-withdrawn-by-p-of-swap
  (equal (fn-ctl-withdrawn-by-p a ws (list* x y rest) verdicts)
         (fn-ctl-withdrawn-by-p a ws (list* y x rest) verdicts))
  :hints (("Goal" :induct (fn-ctl-withdrawn-by-p a ws (list* x y rest) verdicts)
           :in-theory (disable fn-ctl-withdrawal-effect fn-ctl-has-msgid-p))))

; KEYSTONE (C3, the equivalence of D29).  visible(T then C) =
; visible(C then T): with equal records (the plan never reads the target, so
; equal grants give equal records) and equal target evidence, the archive
; that took T before C and the archive that took C before T serve the same
; articles.  The article lists differ in order; membership does not.
(defthm fn-ctl-visible-is-arrival-order-independent
  (iff (member-equal a (fn-ctl-visible-articles (list* tgt cancel rest) ws verdicts))
       (member-equal a (fn-ctl-visible-articles (list* cancel tgt rest) ws verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p fn-ctl-visible-filter)
           :use ((:instance fn-ctl-withdrawn-by-p-of-swap
                            (x tgt) (y cancel))))))

; KEYSTONE (C3, the early cancel).  A target whose withdrawing record's
; cause is in the same article list is never served by it: whichever
; arrived first, the first view holding both already excludes the target,
; and a view holding the target without the cancel is one pinned before the
; cancel committed (above).
(defthm fn-ctl-target-is-never-visible-beside-its-cancel
  (implies (and (member-equal w ws)
                (fn-ctl-withdrawalp w)
                (consp article)
                (equal (fn-ctl-w-target w) (fn-article-msgid article))
                (fn-ctl-has-msgid-p (fn-ctl-w-cause w) articles)
                (fn-ctl-effect-withdrawsp
                 (fn-ctl-withdrawal-effect
                  w (fn-article-groups article)
                  (fn-ctl-lookup-verdict (fn-article-msgid article) verdicts))))
           (not (member-equal article
                              (fn-ctl-visible-articles articles ws verdicts))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-effect
                                      fn-ctl-has-msgid-p
                                      fn-ctl-withdrawalp
                                      fn-ctl-effect-withdrawsp))))

; The visible articles are a sublist of the archive: a withdrawal adds
; nothing and reorders nothing.
(defthm fn-ctl-visible-filter-is-a-subset
  (implies (member-equal a (fn-ctl-visible-filter xs ws articles verdicts))
           (member-equal a xs)))
(defthm fn-cfg-namespace-patternp-is-a-label
  (implies (fn-cfg-namespace-patternp x) (fn-cfg-labelp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cfg-namespace-patternp))))
(defthm fn-cfg-principal-hexp-is-a-label
  (implies (fn-cfg-principal-hexp x) (fn-cfg-labelp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cfg-principal-hexp))))

; KEYSTONE (C2).  A grant is admissible exactly when its namespace is a
; pattern, its principal is 64 lowercase hex characters and its verb is
; grantable ("cancel" only: C4 is deferred by D29).  Subject:
; `fn-cfg-delta-reason', which `fn-ocfg-step' (:reconfigure) and replay
; (`fn-cfg-record-acceptablep') both call.
(defthm fn-cfg-grant-control-admissible-iff
  (iff (null (fn-cfg-delta-reason v gen stamp reserved ceiling
                                  (fn-cfg-grant-control ns principal verb)))
       (and (fn-cfg-namespace-patternp ns)
            (fn-cfg-principal-hexp principal)
            (member-equal verb *fn-cfg-control-verbs*)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-delta-reason fn-cfg-grant-control
                                   fn-cfg-deltap fn-cfg-grant-verb
                                   fn-cfg-rowp fn-cfg-row-listp fn-cfg-ag-car
                                   fn-record-uint32p)
                                  (fn-cfg-namespace-patternp
                                   fn-cfg-principal-hexp fn-cfg-labelp)))))
