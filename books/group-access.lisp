; fn: per-login group access (PRF-222, NNT-046; specs/nntp.md "Group
; access").
;
; A login's access rule is a row (LOGIN READ POST 3) of the configuration's
; accounts slot (books/config.lisp `fn-cfg-account-access', delta code 22):
; READ and POST are RFC 3977 section 4.2 wildmats over newsgroup names.  The
; owner projects the rows into the reader listing every connection pins
; (books/owner-agent.lisp `fn-oag-listing', the fourth element), so a rule
; reaches a connection exactly when the configuration it pins does.
;
; What a READ rule means is one construction, the RESTRICTED VIEW of the
; view the connection pinned: the store with every group outside READ
; absent.  `fn-gac-restrict-state' keeps the groups READ admits, their
; watermarks, and the articles with at least one such group, each article
; cut to its admitted groups and memberships; the Message-ID trie and the
; group buckets are the ones built from those articles
; (`fn-gac-restrict-index'), and the control pin's withdrawn list is cut the
; same way.  books/nntp-auth.lisp `fn-auth-delegate-pinned' serves a
; restricted session's command over that view with the reader machine
; unchanged, so every reply -- LIST in all its variants, GROUP, LISTGROUP,
; NEXT and LAST, ARTICLE by number or Message-ID, OVER, HDR, XPAT, NEWNEWS,
; the Xref field, `423/430 withdrawn' -- is the reply the reader gives over
; a store in which the excluded groups do not exist.  A group outside READ
; therefore answers GROUP exactly as an absent group does (411), and an
; article whose every group is outside READ answers 430: no existence
; oracle beyond the store itself.
;
; A POST rule closes each served group outside POST to the session's local
; posting (`fn-gac-post-config': the groups join the connection's closed
; list, books/group-status.lisp's gate), so the POST is refused with 441 and
; LIST ACTIVE shows those groups with status "n" to that session.
;
; Keystones (the theorem subjects are the functions
; books/nntp-auth.lisp `fn-auth-delegate-pinned' calls, which the served
; step books/served.lisp `fn-served-dispatch' and its carried twin
; books/served-carried.lisp `fn-scar-auth-delegate-pinned' call):
;   fn-gac-restrict-state-is-a-projection     the view is a store the reader
;                                              machine serves
;   fn-gac-restrict-index-corresponds          its index is the one built
;                                              from its articles
;   fn-gac-restrict-state-groups-are-readable  no excluded group is in it
;   fn-gac-restrict-articles-memberships-readable
;                                              no article of it names an
;                                              excluded group's number
;   fn-gac-restricted-article-is-held          an article is in the view
;                                              exactly when it has a
;                                              readable group
;   fn-gac-restrict-absent-group               NO ORACLE: the view of the
;                                              store with an excluded group
;                                              removed is the same view
;   fn-gac-deselected-consistent / -consistent-back
;                                              the reader session invariant
;                                              moves between the store and
;                                              the view
(in-package "ACL2")
(include-book "peer-inbound")
(include-book "nntp-invariants")
(include-book "group-bucket-index")
(include-book "control-served")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

(local (in-theory (enable fn-statep fn-articlep fn-pendingp)))

; -----------------------------------------------------------------------------
; The rule table the connection pins

; The fourth element of the reader listing (books/owner-agent.lisp
; `fn-oag-listing'): the access rows, (LOGIN READ POST 3) each.
(defun fn-gac-listing-table (listing)
  (declare (xargs :guard t))
  (if (and (consp listing) (consp (cdr listing)) (consp (cddr listing))
           (consp (cdddr listing)))
      (car (cdddr listing))
    nil))

(defun fn-gac-text-octets (x)
  (declare (xargs :guard t))
  (if (stringp x) (fn-nntp-string-octets x) nil))

; The rule row of LOGIN (octets; nil for a connection that has not
; authenticated, whose rule is keyed on ""): the first access row whose
; login spells LOGIN.
(defun fn-gac-rule (table login)
  (declare (xargs :guard t))
  (if (consp table)
      (let ((row (car table)))
        (if (and (consp row) (consp (cdr row)) (consp (cddr row))
                 (consp (cdddr row))
                 (equal (car (cdddr row)) 3)
                 (equal (fn-gac-text-octets (car row)) (true-list-fix login)))
            row
          (fn-gac-rule (cdr table) login)))
    nil))

; The READ (field 1) or POST (field 2) text of LOGIN's rule, or nil when the
; rule restricts nothing: no rule, or the pattern "*".
(defun fn-gac-pattern (table login field)
  (declare (xargs :guard t))
  (let* ((row (fn-gac-rule table login))
         (text (if (equal field 1) (cadr row) (caddr row))))
    (if (or (not (consp row)) (equal text "*"))
        nil
      (if (stringp text) text ""))))

; -----------------------------------------------------------------------------
; Readability

; GROUP is readable under TEXT when TEXT parses as a wildmat and matches
; GROUP.  A text that does not parse admits nothing (fail closed); the
; operator's verb admits only texts that parse (books/native-admin.lisp).
(defun fn-gac-text-readablep (text group)
  (declare (xargs :guard t))
  (let ((parsed (fn-wildmat-parse (fn-gac-text-octets text))))
    (and (fn-wildmat-result-okp parsed)
         (stringp group)
         (fn-nntp-group-matches-parsed-wildmatp
          (fn-wildmat-result-value parsed) group)
         t)))

; PKT-658 (PRF-228): a READ rule may also be (:hide TEXT Q ...), TEXT's rule
; with the moderation queues Q (group octets) absent: the queues a login
; that moderates none of their groups may not read (books/moderation.lisp
; `fn-mod-hidden-queues', composed by books/nntp-auth.lisp
; `fn-auth-access-text').
(defun fn-gac-readablep (text group)
  (declare (xargs :guard t))
  (if (and (consp text) (equal (car text) :hide) (consp (cdr text)))
      (and (fn-gac-text-readablep (cadr text) group)
           (not (member-equal (fn-gac-text-octets group)
                              (true-list-fix (cddr text))))
           t)
    (fn-gac-text-readablep text group)))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-gac-filter-groups-loop (text groups acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp groups)
      (if (fn-gac-readablep text (car groups))
          (fn-gac-filter-groups-loop text (cdr groups) (cons (car groups) acc))
        (fn-gac-filter-groups-loop text (cdr groups) acc))
    (revappend acc nil)))

(defun fn-gac-filter-groups (text groups)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp groups)
           (if (fn-gac-readablep text (car groups))
               (cons (car groups) (fn-gac-filter-groups text (cdr groups)))
             (fn-gac-filter-groups text (cdr groups)))
         nil)
       :exec (fn-gac-filter-groups-loop text groups nil)))

(local
 (defthm fn-gac-filter-groups-loop-is-revappend
   (equal (fn-gac-filter-groups-loop text groups acc)
          (revappend acc (fn-gac-filter-groups text groups)))
   :hints (("Goal" :induct (fn-gac-filter-groups-loop text groups acc)
                   :in-theory (union-theories '(fn-gac-filter-groups-loop fn-gac-filter-groups revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-gac-filter-groups-loop)

(verify-guards fn-gac-filter-groups
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-gac-filter-groups)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-gac-filter-groups-loop-is-revappend (acc nil))))))


; Memberships (GROUP . NUMBER) and watermarks (GROUP . NEXT) alike.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-gac-filter-pairs-loop (text pairs acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp pairs)
      (if (and (consp (car pairs)) (fn-gac-readablep text (car (car pairs))))
          (fn-gac-filter-pairs-loop text (cdr pairs) (cons (car pairs) acc))
        (fn-gac-filter-pairs-loop text (cdr pairs) acc))
    (revappend acc nil)))

(defun fn-gac-filter-pairs (text pairs)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp pairs)
           (if (and (consp (car pairs)) (fn-gac-readablep text (car (car pairs))))
               (cons (car pairs) (fn-gac-filter-pairs text (cdr pairs)))
             (fn-gac-filter-pairs text (cdr pairs)))
         nil)
       :exec (fn-gac-filter-pairs-loop text pairs nil)))

(local
 (defthm fn-gac-filter-pairs-loop-is-revappend
   (equal (fn-gac-filter-pairs-loop text pairs acc)
          (revappend acc (fn-gac-filter-pairs text pairs)))
   :hints (("Goal" :induct (fn-gac-filter-pairs-loop text pairs acc)
                   :in-theory (union-theories '(fn-gac-filter-pairs-loop fn-gac-filter-pairs revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-gac-filter-pairs-loop)

(verify-guards fn-gac-filter-pairs
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-gac-filter-pairs)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-gac-filter-pairs-loop-is-revappend (acc nil))))))


; -----------------------------------------------------------------------------
; The restricted view

(defun fn-gac-restrict-article (text a)
  (declare (xargs :guard t))
  (fn-make-article (fn-article-msgid a) (fn-article-payload a)
                   (fn-gac-filter-groups text (fn-article-groups a))
                   (fn-gac-filter-pairs text (fn-article-memberships a))
                   (fn-article-pin a) (fn-article-stamp a)))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-gac-restrict-articles-loop (text arts acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp arts)
      (if (consp (fn-gac-filter-groups text (fn-article-groups (car arts))))
          (fn-gac-restrict-articles-loop text
                                         (cdr arts)
                                         (cons (fn-gac-restrict-article text (car arts))
                                               acc))
        (fn-gac-restrict-articles-loop text (cdr arts) acc))
    (revappend acc nil)))

(defun fn-gac-restrict-articles (text arts)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp arts)
           (if (consp (fn-gac-filter-groups text (fn-article-groups (car arts))))
               (cons (fn-gac-restrict-article text (car arts))
                     (fn-gac-restrict-articles text (cdr arts)))
             (fn-gac-restrict-articles text (cdr arts)))
         nil)
       :exec (fn-gac-restrict-articles-loop text arts nil)))

(local
 (defthm fn-gac-restrict-articles-loop-is-revappend
   (equal (fn-gac-restrict-articles-loop text arts acc)
          (revappend acc (fn-gac-restrict-articles text arts)))
   :hints (("Goal" :induct (fn-gac-restrict-articles-loop text arts acc)
                   :in-theory (union-theories '(fn-gac-restrict-articles-loop fn-gac-restrict-articles revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-gac-restrict-articles-loop)

(verify-guards fn-gac-restrict-articles
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-gac-restrict-articles)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-gac-restrict-articles-loop-is-revappend (acc nil))))))


; The store with every group outside TEXT absent.  Nothing in flight is
; part of what a reader sees, so the view carries no pending write.
(defun fn-gac-restrict-state (text s)
  (declare (xargs :guard t))
  (fn-make-state (fn-gac-filter-groups text (fn-state-groups s))
                 (fn-gac-filter-pairs text (fn-state-nexts s))
                 (fn-gac-restrict-articles text (fn-state-articles s))
                 (fn-state-next-txid s)
                 nil nil))

; The index of the view: the trie and buckets built from its articles, and
; the control pin with its withdrawn list cut the same way (the withdrawal
; records stay: HDR :fn-control reads them only for an article the view
; holds).
(defun fn-gac-restrict-index (text index arts)
  (declare (xargs :guard t))
  (if (fn-gidx-pinp index)
      (let ((control (fn-gidx-pin-control index)))
        (fn-gidx-pin-with-control
         (fn-midx-build arts) (fn-gidx-build arts)
         (fn-ctl-pin (fn-gac-restrict-articles text (fn-ctl-pin-withdrawn control))
                     (fn-ctl-pin-ws control))))
    (fn-midx-build arts)))

; -----------------------------------------------------------------------------
; The session: a selection outside the view is dropped

(defun fn-gac-deselect (text ps)
  (declare (xargs :guard t))
  (let* ((pst (fn-peer-session-base ps))
         (ns (fn-post-session-base pst))
         (group (fn-nntp-session-group ns)))
    (if (or (null group) (fn-gac-readablep text group))
        ps
      (fn-peer-with-base
       ps (fn-post-make-session
           (fn-nntp-make-session (fn-nntp-session-openp ns) nil nil
                                 (fn-nntp-session-projected ns))
           (fn-post-session-awaiting pst))))))

; -----------------------------------------------------------------------------
; Posting: the groups outside POST join the closed list

; Executes by a loop (lane depth-debt, PRF-919): it walks the configured newsgroup list, operator
; data with no fixed cap (D27), and the recursion took one control-stack frame
; per element.  (mbe :logic <the recursion, unchanged> :exec <a loop>), equal
; by the lemma after it (books/rev-onto.lisp fn-ag-rev-onto).
(defun fn-gac-unpostable-octets-loop (text groups acc)
  (declare (xargs :guard t))
  (if (consp groups)
      (fn-gac-unpostable-octets-loop text (cdr groups)
       (if (not (fn-gac-readablep text (car groups))) (cons (fn-gac-text-octets (car groups)) acc) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-gac-unpostable-octets (text groups)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp groups)
           (if (fn-gac-readablep text (car groups))
               (fn-gac-unpostable-octets text (cdr groups))
             (cons (fn-gac-text-octets (car groups))
                   (fn-gac-unpostable-octets text (cdr groups))))
         nil)
       :exec (fn-gac-unpostable-octets-loop text groups nil)))

(defthm fn-gac-unpostable-octets-loop-is-rev-onto
  (equal (fn-gac-unpostable-octets-loop text groups acc)
         (fn-ag-rev-onto acc (fn-gac-unpostable-octets text groups)))
  :hints (("Goal" :induct (fn-gac-unpostable-octets-loop text groups acc)
                  :in-theory (union-theories
                              '(fn-gac-unpostable-octets-loop fn-gac-unpostable-octets fn-ag-rev-onto not car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-gac-unpostable-octets
  :hints (("Goal" :in-theory (union-theories
                              '(fn-gac-unpostable-octets fn-ag-rev-onto fn-gac-unpostable-octets-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

; A served group stays a group to the session when it may read it or post
; to it; a group it may do neither with is absent, so a POST naming it is
; refused as a POST naming any unknown group is (no existence oracle through
; posting either).  READ or POST nil restricts nothing.
(defun fn-gac-octets-group (o)
  (declare (xargs :guard t))
  (if (fn-octet-listp o) (fn-record-octets-string o) nil))

; Executes by a loop (lane depth-debt, PRF-919): it walks the configured newsgroup names, operator
; data with no fixed cap (D27), and the recursion took one control-stack frame
; per element.  (mbe :logic <the recursion, unchanged> :exec <a loop>), equal
; by the lemma after it (books/rev-onto.lisp fn-ag-rev-onto).
(defun fn-gac-servable-octets-loop (read post names acc)
  (declare (xargs :guard t))
  (if (consp names)
      (fn-gac-servable-octets-loop read post (cdr names)
       (if (or (null read) (null post)
           (fn-gac-readablep read (fn-gac-octets-group (car names)))
           (fn-gac-readablep post (fn-gac-octets-group (car names)))) (cons (car names) acc) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-gac-servable-octets (read post names)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp names)
           (if (or (null read) (null post)
                   (fn-gac-readablep read (fn-gac-octets-group (car names)))
                   (fn-gac-readablep post (fn-gac-octets-group (car names))))
               (cons (car names) (fn-gac-servable-octets read post (cdr names)))
             (fn-gac-servable-octets read post (cdr names)))
         nil)
       :exec (fn-gac-servable-octets-loop read post names nil)))

(defthm fn-gac-servable-octets-loop-is-rev-onto
  (equal (fn-gac-servable-octets-loop read post names acc)
         (fn-ag-rev-onto acc (fn-gac-servable-octets read post names)))
  :hints (("Goal" :induct (fn-gac-servable-octets-loop read post names acc)
                  :in-theory (union-theories
                              '(fn-gac-servable-octets-loop fn-gac-servable-octets fn-ag-rev-onto not car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-gac-servable-octets
  :hints (("Goal" :in-theory (union-theories
                              '(fn-gac-servable-octets fn-ag-rev-onto fn-gac-servable-octets-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

; A derived posting configuration carries its source's article bound and
; header limits as one post bound (books/injection.lisp `fn-inj-post-bound'):
; its octets and its limits read back unchanged.
(defthm fn-gac-bound-octets-of-post-bound
  (equal (fn-inj-bound-octets (cons octets limits)) octets)
  :hints (("Goal" :in-theory (enable fn-inj-bound-octets))))

(defthm fn-gac-bound-header-limits-of-post-bound
  (equal (fn-inj-bound-header-limits (cons octets limits)) limits)
  :hints (("Goal" :in-theory (enable fn-inj-bound-header-limits))))

(defun fn-gac-post-config (read post groups config)
  (declare (xargs :guard t))
  (fn-inj-make-config-full (fn-inj-config-allow config)
                           (fn-inj-config-agent config)
                           (fn-gac-servable-octets read post
                                                   (fn-inj-config-groups config))
                           ;; The article bound and the header limits
                           ;; (PRF-230) as the configuration carries them.
                           (fn-inj-post-bound (fn-inj-config-max-octets config)
                                              (fn-inj-config-header-limits config))
                           (fn-inj-config-listing config)
                           (append (true-list-fix (fn-inj-config-closed config))
                                   (and post (fn-gac-unpostable-octets post groups)))))

; -----------------------------------------------------------------------------
; The view is a store the reader machine serves

(in-theory (disable fn-gac-readablep fn-gac-text-readablep))

(defthm fn-gac-member-of-filter-groups
  (iff (member-equal g (fn-gac-filter-groups text groups))
       (and (member-equal g groups) (fn-gac-readablep text g))))

(defthm fn-gac-string-listp-of-filter-groups
  (implies (fn-string-listp groups)
           (fn-string-listp (fn-gac-filter-groups text groups))))

(defthm fn-gac-no-duplicatesp-of-filter-groups
  (implies (fn-no-duplicatesp groups)
           (fn-no-duplicatesp (fn-gac-filter-groups text groups))))

(defthm fn-gac-subsetp-of-filter-groups
  (implies (fn-subsetp xs ys)
           (fn-subsetp (fn-gac-filter-groups text xs)
                       (fn-gac-filter-groups text ys))))

(defthm fn-gac-safe-group-listp-of-filter-groups
  (implies (fn-nntp-safe-group-listp groups)
           (fn-nntp-safe-group-listp (fn-gac-filter-groups text groups)))
  :hints (("Goal" :in-theory (enable fn-nntp-safe-group-listp))))

(defthm fn-gac-nexts-for-p-of-filter
  (implies (fn-nexts-for-p groups nexts)
           (fn-nexts-for-p (fn-gac-filter-groups text groups)
                           (fn-gac-filter-pairs text nexts))))

(defthm fn-gac-membership-listp-of-filter
  (implies (fn-membership-listp groups memberships)
           (fn-membership-listp (fn-gac-filter-groups text groups)
                                (fn-gac-filter-pairs text memberships))))

(defthm fn-gac-nexts-boundedp-of-filter
  (implies (fn-nntp-nexts-boundedp nexts)
           (fn-nntp-nexts-boundedp (fn-gac-filter-pairs text nexts)))
  :hints (("Goal" :in-theory (enable fn-nntp-nexts-boundedp))))

(defthm fn-gac-readablep-implies-stringp
  (implies (fn-gac-readablep text g) (stringp g))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-gac-readablep fn-gac-text-readablep))))

(defthm fn-gac-next-number-of-filter
  (implies (fn-gac-readablep text group)
           (equal (fn-next-number group (fn-gac-filter-pairs text nexts))
                  (fn-next-number group nexts))))

(defthm fn-gac-len-of-restrict-articles
  (<= (len (fn-gac-restrict-articles text arts)) (len arts))
  :rule-classes :linear)

(defthm fn-gac-selection-validp-of-filter
  (implies (and (fn-selection-validp sel groups)
                (consp (fn-gac-filter-groups text sel)))
           (fn-selection-validp (fn-gac-filter-groups text sel)
                                (fn-gac-filter-groups text groups)))
  :hints (("Goal" :in-theory (enable fn-selection-validp))))

(defthm fn-gac-articlep-of-restrict-article
  (implies (and (fn-articlep groups a)
                (consp (fn-gac-filter-groups text (fn-article-groups a))))
           (fn-articlep (fn-gac-filter-groups text groups)
                        (fn-gac-restrict-article text a)))
  :hints (("Goal" :in-theory (disable fn-selection-validp fn-membership-listp
                                      fn-gac-filter-groups fn-gac-filter-pairs))))

(defthm fn-gac-msgid-of-restrict-article
  (equal (fn-article-msgid (fn-gac-restrict-article text a))
         (fn-article-msgid a)))

(defthm fn-gac-member-msgids-of-restrict-articles
  (implies (member-equal m (fn-article-msgids (fn-gac-restrict-articles text arts)))
           (member-equal m (fn-article-msgids arts))))

(defthm fn-gac-acceptedp-of-restrict-articles
  (implies (fn-acceptedp m (fn-gac-restrict-articles text arts))
           (fn-acceptedp m arts))
  :hints (("Goal" :in-theory (disable fn-gac-restrict-article))))

(defthm fn-gac-article-listp-of-restrict-articles
  (implies (fn-article-listp groups arts)
           (fn-article-listp (fn-gac-filter-groups text groups)
                             (fn-gac-restrict-articles text arts)))
  :hints (("Goal" :induct (fn-gac-restrict-articles text arts)
           :in-theory (disable fn-articlep fn-gac-restrict-article
                               fn-gac-filter-groups))))

(defthm fn-gac-pair-memberp-of-filter-pairs
  (implies (fn-pair-memberp p (fn-gac-filter-pairs text xs))
           (fn-pair-memberp p xs)))

(defthm fn-gac-pair-memberp-of-append
  (equal (fn-pair-memberp p (append a b))
         (or (fn-pair-memberp p a) (fn-pair-memberp p b))))

(defthm fn-gac-pair-memberp-of-all-memberships-restrict
  (implies (fn-pair-memberp p (fn-all-article-memberships
                               (fn-gac-restrict-articles text arts)))
           (fn-pair-memberp p (fn-all-article-memberships arts))))

(defthm fn-gac-conflictsp-of-filter-restrict
  (implies (fn-memberships-conflictsp (fn-gac-filter-pairs text m)
                                      (fn-gac-restrict-articles text arts))
           (fn-memberships-conflictsp m arts))
  :hints (("Goal" :induct (fn-gac-filter-pairs text m)
           :in-theory (disable fn-gac-restrict-articles))))

(defthm fn-gac-freshp-of-restrict-articles
  (implies (fn-articles-freshp arts)
           (fn-articles-freshp (fn-gac-restrict-articles text arts)))
  :hints (("Goal" :induct (fn-gac-restrict-articles text arts)
           :in-theory (disable fn-gac-filter-pairs fn-gac-filter-groups))))

(defthm fn-gac-below-nextsp-of-filter
  (implies (fn-memberships-below-nextsp m nexts)
           (fn-memberships-below-nextsp (fn-gac-filter-pairs text m)
                                        (fn-gac-filter-pairs text nexts))))

(defthm fn-gac-articles-below-nextsp-of-restrict
  (implies (fn-articles-below-nextsp arts nexts)
           (fn-articles-below-nextsp (fn-gac-restrict-articles text arts)
                                     (fn-gac-filter-pairs text nexts)))
  :hints (("Goal" :induct (fn-gac-restrict-articles text arts)
           :in-theory (disable fn-gac-filter-pairs fn-gac-filter-groups))))

(defthm fn-gac-restrict-state-is-a-state
  (implies (fn-statep s)
           (fn-statep (fn-gac-restrict-state text s)))
  :hints (("Goal" :in-theory (disable fn-gac-restrict-articles fn-gac-filter-groups
                                      fn-gac-filter-pairs fn-article-listp
                                      fn-articles-freshp fn-articles-below-nextsp
                                      fn-nexts-for-p))))

(defthm fn-gac-state-groups-of-restrict
  (equal (fn-state-groups (fn-gac-restrict-state text s))
         (fn-gac-filter-groups text (fn-state-groups s))))

(defthm fn-gac-state-nexts-of-restrict
  (equal (fn-state-nexts (fn-gac-restrict-state text s))
         (fn-gac-filter-pairs text (fn-state-nexts s))))

(defthm fn-gac-state-articles-of-restrict
  (equal (fn-state-articles (fn-gac-restrict-state text s))
         (fn-gac-restrict-articles text (fn-state-articles s))))

(in-theory (disable fn-gac-restrict-state))

(defthm fn-gac-restrict-state-is-a-projection
  (implies (fn-nntp-projectionp s)
           (fn-nntp-projectionp (fn-gac-restrict-state text s)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-projectionp)
                                  (fn-gac-restrict-articles fn-gac-filter-groups
                                   fn-gac-filter-pairs fn-statep)))))

(defthm fn-gac-membership-number-of-filter
  (implies (fn-gac-readablep text group)
           (equal (fn-nntp-membership-number group (fn-gac-filter-pairs text ms))
                  (fn-nntp-membership-number group ms)))
  :hints (("Goal" :in-theory (enable fn-nntp-membership-number))))

(defthm fn-gac-membership-number-of-dropped
  (implies (and (fn-membership-listp groups ms)
                (not (consp (fn-gac-filter-groups text groups)))
                (fn-gac-readablep text group))
           (equal (fn-nntp-membership-number group ms) 0))
  :hints (("Goal" :in-theory (enable fn-nntp-membership-number))))

(defthm fn-gac-article-number-of-restrict-article
  (implies (fn-gac-readablep text group)
           (equal (fn-nntp-article-number group (fn-gac-restrict-article text a))
                  (fn-nntp-article-number group a)))
  :hints (("Goal" :in-theory (enable fn-nntp-article-number fn-nntp-article-idp))))

(defthm fn-gac-article-number-of-dropped
  (implies (and (fn-articlep configured a)
                (not (consp (fn-gac-filter-groups text (fn-article-groups a))))
                (fn-gac-readablep text group))
           (equal (fn-nntp-article-number group a) 0))
  :hints (("Goal" :in-theory (e/d (fn-nntp-article-number)
                                  (fn-gac-filter-groups fn-membership-listp))
           :use ((:instance fn-gac-membership-number-of-dropped
                            (groups (fn-article-groups a))
                            (ms (fn-article-memberships a)))))))

(in-theory (disable fn-gac-restrict-article))

(defthm fn-gac-group-low-of-restrict
  (implies (and (fn-article-listp configured arts)
                (fn-gac-readablep text group))
           (equal (fn-nntp-group-low group (fn-gac-restrict-articles text arts))
                  (fn-nntp-group-low group arts)))
  :hints (("Goal" :induct (fn-gac-restrict-articles text arts)
           :in-theory (e/d (fn-nntp-group-low) (fn-articlep fn-gac-filter-groups)))))

(defthm fn-gac-statep-article-listp
  (implies (fn-statep s)
           (fn-article-listp (fn-state-groups s) (fn-state-articles s)))
  :rule-classes :forward-chaining)

(defthm fn-gac-group-nonemptyp-of-restrict
  (implies (and (fn-statep s) (fn-gac-readablep text group))
           (equal (fn-nntp-group-nonemptyp group (fn-gac-restrict-state text s))
                  (fn-nntp-group-nonemptyp group s)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-group-nonemptyp)
                                  (fn-gac-restrict-articles fn-statep))
           :use ((:instance fn-gac-group-low-of-restrict
                            (configured (fn-state-groups s))
                            (arts (fn-state-articles s)))))))

(defthm fn-gac-available-article-consp-of-restrict
  (implies (and (fn-article-listp configured arts)
                (fn-gac-readablep text group))
           (equal (consp (fn-nntp-available-article group n (fn-gac-restrict-articles text arts)))
                  (consp (fn-nntp-available-article group n arts))))
  :hints (("Goal" :induct (fn-gac-restrict-articles text arts)
           :in-theory (e/d (fn-nntp-available-article)
                           (fn-articlep fn-gac-filter-groups)))))

(defthm fn-gac-cursor-validp-of-restrict
  (implies (and (fn-statep s) (fn-gac-readablep text group))
           (equal (fn-nntp-cursor-validp group current (fn-gac-restrict-state text s))
                  (fn-nntp-cursor-validp group current s)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-cursor-validp)
                                  (fn-gac-restrict-articles fn-statep))
           :use ((:instance fn-gac-available-article-consp-of-restrict
                            (n current)
                            (configured (fn-state-groups s))
                            (arts (fn-state-articles s)))))))

(defthm fn-gac-consistent-into-view
  (implies (and (fn-nntp-session-consistentp ns s)
                (fn-nntp-session-projected ns)
                (or (null (fn-nntp-session-group ns))
                    (fn-gac-readablep text (fn-nntp-session-group ns))))
           (fn-nntp-session-consistentp ns (fn-gac-restrict-state text s)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-session-consistentp)
                                  (fn-nntp-projectionp fn-statep
                                   fn-nntp-group-nonemptyp fn-nntp-cursor-validp))
           :use ((:instance fn-gac-restrict-state-is-a-projection)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-nntp-session-consistentp fn-nntp-projectionp)
                                 (fn-statep fn-nntp-group-nonemptyp
                                  fn-nntp-cursor-validp))))))

(defthm fn-gac-consistent-from-view
  (implies (and (fn-nntp-session-consistentp ns (fn-gac-restrict-state text s))
                (fn-nntp-projectionp s))
           (fn-nntp-session-consistentp ns s))
  :hints (("Goal" :in-theory (e/d (fn-nntp-session-consistentp)
                                  (fn-nntp-projectionp fn-statep
                                   fn-nntp-group-nonemptyp fn-nntp-cursor-validp)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-nntp-session-consistentp fn-nntp-projectionp)
                                 (fn-statep fn-nntp-group-nonemptyp
                                  fn-nntp-cursor-validp))))))

(defthm fn-gac-restrict-index-corresponds
  (fn-gidx-pin-correspondencep
   (fn-gac-restrict-index text index (fn-gac-restrict-articles text (fn-state-articles s)))
   (fn-gac-restrict-state text s))
  :hints (("Goal" :in-theory (e/d (fn-gidx-pin-correspondencep fn-gac-restrict-index)
                                  (fn-gidx-pinp fn-midx-build fn-gidx-build
                                   fn-gac-restrict-articles)))))

(defthm fn-gac-post-sessionp-of-deselected
  (implies (fn-post-sessionp pst)
           (fn-post-sessionp
            (fn-post-make-session
             (fn-nntp-make-session (fn-nntp-session-openp (fn-post-session-base pst))
                                   nil nil
                                   (fn-nntp-session-projected (fn-post-session-base pst)))
             (fn-post-session-awaiting pst))))
  :hints (("Goal" :in-theory (enable fn-post-sessionp fn-nntp-sessionp))))

(defthm fn-gac-peer-sessionp-of-deselect
  (implies (fn-peer-sessionp ps)
           (fn-peer-sessionp (fn-gac-deselect text ps)))
  :hints (("Goal" :in-theory (e/d (fn-gac-deselect) (fn-peer-sessionp fn-post-sessionp
                                                     fn-peer-with-base)))))

(defthm fn-gac-deselected-consistent
  (implies (and (fn-peer-session-consistentp ps s)
                (fn-nntp-session-projected
                 (fn-post-session-base (fn-peer-session-base ps))))
           (fn-peer-session-consistentp (fn-gac-deselect text ps)
                                        (fn-gac-restrict-state text s)))
  :hints (("Goal" :in-theory (e/d (fn-gac-deselect fn-peer-session-consistentp
                                   fn-post-session-consistentp)
                                  (fn-nntp-session-consistentp fn-peer-sessionp
                                   fn-post-sessionp fn-peer-with-base
                                   fn-gac-restrict-state fn-nntp-projectionp))
           :use ((:instance fn-gac-consistent-into-view
                            (ns (fn-post-session-base (fn-peer-session-base ps))))))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-nntp-session-consistentp fn-post-sessionp
                                  fn-nntp-sessionp)
                                 (fn-peer-sessionp fn-peer-with-base
                                  fn-gac-restrict-state fn-nntp-projectionp))
                 :use ((:instance fn-gac-restrict-state-is-a-projection)
                       (:instance fn-gac-peer-sessionp-of-deselect)
                       (:instance fn-gac-consistent-into-view
                            (ns (fn-post-session-base (fn-peer-session-base ps)))))))))

(defthm fn-gac-consistent-back
  (implies (and (fn-peer-session-consistentp ps (fn-gac-restrict-state text s))
                (fn-nntp-projectionp s))
           (fn-peer-session-consistentp ps s))
  :hints (("Goal" :in-theory (e/d (fn-peer-session-consistentp
                                   fn-post-session-consistentp)
                                  (fn-nntp-session-consistentp fn-peer-sessionp
                                   fn-post-sessionp fn-gac-restrict-state
                                   fn-nntp-projectionp)))))

(defun fn-gac-all-readablep (text groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (and (fn-gac-readablep text (car groups))
           (fn-gac-all-readablep text (cdr groups)))
    t))

(defun fn-gac-pairs-readablep (text pairs)
  (declare (xargs :guard t))
  (if (consp pairs)
      (and (consp (car pairs))
           (fn-gac-readablep text (car (car pairs)))
           (fn-gac-pairs-readablep text (cdr pairs)))
    t))

(defun fn-gac-article-readablep (text a)
  (declare (xargs :guard t))
  (and (consp (fn-article-groups a))
       (fn-gac-all-readablep text (fn-article-groups a))
       (fn-gac-pairs-readablep text (fn-article-memberships a))))

(defun fn-gac-articles-readablep (text arts)
  (declare (xargs :guard t))
  (if (consp arts)
      (and (fn-gac-article-readablep text (car arts))
           (fn-gac-articles-readablep text (cdr arts)))
    t))

(defthm fn-gac-all-readablep-of-filter
  (fn-gac-all-readablep text (fn-gac-filter-groups text groups)))

(defthm fn-gac-pairs-readablep-of-filter
  (fn-gac-pairs-readablep text (fn-gac-filter-pairs text pairs)))

(defthm fn-gac-restrict-state-groups-are-readable
  (implies (member-equal g (fn-state-groups (fn-gac-restrict-state text s)))
           (and (fn-gac-readablep text g)
                (member-equal g (fn-state-groups s)))))

(defthm fn-gac-restrict-articles-memberships-readable
  (fn-gac-articles-readablep text (fn-gac-restrict-articles text arts))
  :hints (("Goal" :in-theory (enable fn-gac-restrict-article))))

(defthm fn-gac-restrict-state-articles-are-readable
  (fn-gac-articles-readablep text (fn-state-articles (fn-gac-restrict-state text s))))

(defthm fn-gac-restrict-index-withdrawn-are-readable
  (implies (fn-gidx-pinp index)
           (fn-gac-articles-readablep
            text (fn-ctl-pin-withdrawn
                  (fn-gidx-pin-control (fn-gac-restrict-index text index arts)))))
  :hints (("Goal" :in-theory (enable fn-gac-restrict-index))))

(defun fn-gac-some-readable-held (m text arts)
  (declare (xargs :guard t))
  (if (consp arts)
      (or (and (equal m (fn-article-msgid (car arts)))
               (consp (fn-gac-filter-groups text (fn-article-groups (car arts)))))
          (fn-gac-some-readable-held m text (cdr arts)))
    nil))

(defthm fn-gac-restricted-article-is-held
  (equal (fn-acceptedp m (fn-gac-restrict-articles text arts))
         (fn-gac-some-readable-held m text arts))
  :hints (("Goal" :in-theory (enable fn-gac-restrict-article))))

(defun fn-gac-coversp (text text2 groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (and (or (not (fn-gac-readablep text (car groups)))
               (fn-gac-readablep text2 (car groups)))
           (fn-gac-coversp text text2 (cdr groups)))
    t))

(defthm fn-gac-coversp-member
  (implies (and (fn-gac-coversp text text2 groups)
                (member-equal g groups)
                (fn-gac-readablep text g))
           (fn-gac-readablep text2 g)))

(defthm fn-gac-coversp-of-subset
  (implies (and (fn-gac-coversp text text2 groups)
                (fn-subsetp xs groups))
           (fn-gac-coversp text text2 xs)))

(defthm fn-gac-filter-groups-twice
  (implies (fn-gac-coversp text text2 gs)
           (equal (fn-gac-filter-groups text (fn-gac-filter-groups text2 gs))
                  (fn-gac-filter-groups text gs))))

(defthm fn-gac-filter-pairs-twice
  (implies (and (fn-membership-listp gs ps)
                (fn-gac-coversp text text2 gs))
           (equal (fn-gac-filter-pairs text (fn-gac-filter-pairs text2 ps))
                  (fn-gac-filter-pairs text ps))))

(defthm fn-gac-filter-nexts-twice
  (implies (and (fn-nexts-for-p gs ps)
                (fn-gac-coversp text text2 gs))
           (equal (fn-gac-filter-pairs text (fn-gac-filter-pairs text2 ps))
                  (fn-gac-filter-pairs text ps))))

(defthm fn-gac-filter-groups-empty-when-covered
  (implies (and (fn-gac-coversp text text2 gs)
                (not (consp (fn-gac-filter-groups text2 gs))))
           (not (consp (fn-gac-filter-groups text gs)))))

(defthm fn-gac-restrict-articles-twice
  (implies (and (fn-article-listp configured arts)
                (fn-gac-coversp text text2 configured))
           (equal (fn-gac-restrict-articles text (fn-gac-restrict-articles text2 arts))
                  (fn-gac-restrict-articles text arts)))
  :hints (("Goal" :induct (fn-gac-restrict-articles text2 arts)
           :in-theory (e/d (fn-gac-restrict-article fn-selection-validp)
                           (fn-gac-filter-groups fn-gac-filter-pairs
                            fn-gac-coversp-of-subset
                            fn-gac-filter-groups-empty-when-covered)))
          ("Subgoal *1/2" :use ((:instance fn-gac-coversp-of-subset
                                  (groups configured)
                                  (xs (fn-article-groups (car arts))))
                                (:instance fn-gac-filter-groups-empty-when-covered
                                  (gs (fn-article-groups (car arts))))))
          ("Subgoal *1/1" :use ((:instance fn-gac-coversp-of-subset
                                  (groups configured)
                                  (xs (fn-article-groups (car arts))))
                                (:instance fn-gac-filter-groups-empty-when-covered
                                  (gs (fn-article-groups (car arts))))))))

(defthm fn-gac-statep-nexts-for-p
  (implies (fn-statep s)
           (fn-nexts-for-p (fn-state-groups s) (fn-state-nexts s)))
  :rule-classes :forward-chaining)

(defthm fn-gac-restrict-absent-groups
  (implies (and (fn-statep s)
                (fn-gac-coversp text text2 (fn-state-groups s)))
           (equal (fn-gac-restrict-state text (fn-gac-restrict-state text2 s))
                  (fn-gac-restrict-state text s)))
  :hints (("Goal" :in-theory (e/d (fn-gac-restrict-state)
                                  (fn-gac-restrict-articles fn-gac-filter-groups
                                   fn-gac-filter-pairs fn-statep)))))

;; -----------------------------------------------------------------------------
;; PKT-643: the restricted view as one value.
;;
;; A restricted session's view is a function of its rule's read text and the
;; connection's pin (archive and control): the restricted store and its
;; index (the index reads only the control's withdrawn list and records).
;; books/group-access-cache.lisp prepares it once per pin and keeps it; the
;; served delegate (books/served-catalog-chain.lisp fn-scr-auth-delegate)
;; reads it instead of building it per command.  fn-gac-view-entry-is-per-
;; command equates it with the per-command restriction of a pinned index.

(defun fn-gac-view-entry (text archive control)
  (declare (xargs :guard t))
  (let ((rs (fn-gac-restrict-state text archive)))
    (cons rs (fn-gac-restrict-index text (fn-gidx-pin-with-control nil nil control)
                                    (fn-state-articles rs)))))

(defthm fn-gac-view-entry-reads-withdrawn-and-records
  (implies (and (equal (fn-ctl-pin-withdrawn c1) (fn-ctl-pin-withdrawn c2))
                (equal (fn-ctl-pin-ws c1) (fn-ctl-pin-ws c2)))
           (equal (equal (fn-gac-view-entry text archive c1)
                         (fn-gac-view-entry text archive c2))
                  t))
  :hints (("Goal" :in-theory (e/d (fn-gac-view-entry fn-gac-restrict-index)
                                  (fn-gac-restrict-state fn-midx-build fn-gidx-build
                                   fn-gac-restrict-articles)))))

; The per-command index of a pinned view is the entry's: fn-gac-restrict-index
; reads a pin's control and nothing else of it.
(defthm fn-gac-view-entry-is-per-command
  (implies (fn-gidx-pinp index)
           (equal (fn-gac-view-entry text archive (fn-gidx-pin-control index))
                  (cons (fn-gac-restrict-state text archive)
                        (fn-gac-restrict-index
                         text index
                         (fn-state-articles (fn-gac-restrict-state text archive))))))
  :hints (("Goal" :in-theory (e/d (fn-gac-view-entry fn-gac-restrict-index)
                                  (fn-gac-restrict-state fn-midx-build fn-gidx-build
                                   fn-gac-restrict-articles)))))

(in-theory (disable fn-gac-view-entry))
