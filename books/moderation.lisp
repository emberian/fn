; fn: moderated groups (P3; PRF-228, NNT-047; specs/nntp.md "Moderated
; groups").
;
; RFC 5537 section 3.5 item 7: "If the Newsgroups header contains one or
; more moderated groups and the proto-article does not contain an Approved
; header field, the injecting agent MUST either forward it to a moderator as
; specified in Section 3.5.1 or, if that is not possible, reject it.  This
; forwarding MUST be done after adding the Message-ID and Date headers if
; required, and before adding the Injection-Info and Injection-Date
; headers."  Section 3.5.1 forwards "to the moderator of the leftmost
; moderated group", method 1 being "the complete proto-article ...
; encapsulated ... with a Content-Type of application/news-transmission with
; the usage parameter set to "moderate"".  Section 7 (security): "Injecting
; agents SHOULD verify that messages approved for a moderated newsgroup are
; being injected by the moderator using authentication information from the
; underlying transport".
;
; fn has no mail path, so its forwarding is method 1 into the group's
; moderation QUEUE, a live group the operator names (books/config.lisp
; code 23): the node injects an envelope article into the queue whose body
; is the proto-article with its Message-ID and Date, and whose own
; Message-ID is the proto-article's with "fn-moderate." before its left
; part, so a resend of the same source is the same envelope (D25).  The
; envelope is an ordinary Store article: the queue needs no new persistence
; domain, 240 comes from its durable acceptance exactly as for any POST,
; and the moderator reads the queue over NNTP.  The moderator approves by
; posting the proto-article (the envelope's body) with an Approved header
; field from their own login: the original Message-ID was never stored, so
; the approved post is a fresh injection of it.
;
; The configuration reaches a connection as entries in its posting
; configuration's status list (books/owner-agent.lisp
; `fn-oag-moderation-entries'): (:moderated G Q MODS), G and Q octets and
; MODS the moderators' login octets.  A connection whose login is one of MODS
; sees that entry as (:approver G Q) (`fn-mod-session-entries', called by
; books/nntp-auth.lisp `fn-auth-moderation-config'); the owner never installs
; an :approver entry, so an unauthenticated or non-moderator connection
; cannot approve.
;
; The decision (`fn-mod-gate', called by books/nntp-post.lisp
; `fn-post-gated-decision', the served POST's decision) runs on an ordinary
; article the injection accepted and the read-only gate passed:
;   - no named group moderated: the injection's decision, unchanged;
;   - an Approved field, every named moderated group :approver: unchanged
;     (committed to the moderated groups);
;   - an Approved field otherwise: refused :approval-not-moderator (441);
;   - no Approved field: the envelope's injection into the leftmost
;     moderated group's queue, refused :moderation-unavailable when the
;     envelope is not injected or would land in a moderated or closed group.
; A control message (a cancel) is not a posting to the group and is not
; gated (RFC 5537 section 5.3: cancels need no Approved), as for the
; read-only gate.

(in-package "ACL2")
(include-book "injection")
(include-book "control-classify")
(include-book "nntp-responses")

; "approved", compared case-insensitively as every field name is.
(defconst *fn-mod-approved-name* '(97 112 112 114 111 118 101 100))

; -----------------------------------------------------------------------------
; Status-list entries

(defun fn-mod-entry-group (e)
  (declare (xargs :guard t))
  (fn-inj-car (fn-inj-cdr e)))

(defun fn-mod-entry-queue (e)
  (declare (xargs :guard t))
  (fn-inj-car (fn-inj-cdr (fn-inj-cdr e))))

(defun fn-mod-entry-moderators (e)
  (declare (xargs :guard t))
  (fn-inj-car (fn-inj-cdr (fn-inj-cdr (fn-inj-cdr e)))))

(defun fn-mod-entry-approverp (e)
  (declare (xargs :guard t))
  (and (consp e) (equal (car e) :approver)))

; The first moderated entry of group octets G, or nil.
(defun fn-mod-entry-of (g closed)
  (declare (xargs :guard t))
  (if (consp closed)
      (if (and (fn-nntp-moderated-entryp (car closed))
               (equal (fn-mod-entry-group (car closed)) g))
          (car closed)
        (fn-mod-entry-of g (cdr closed)))
    nil))

; The moderated entries of GROUPS, in Newsgroups order.
(defun fn-mod-named-entries (groups closed)
  (declare (xargs :guard t))
  (if (consp groups)
      (let ((e (fn-mod-entry-of (car groups) closed)))
        (if e
            (cons e (fn-mod-named-entries (cdr groups) closed))
          (fn-mod-named-entries (cdr groups) closed)))
    nil))

(defthm fn-mod-named-entries-of-no-groups
  (implies (not (consp groups))
           (equal (fn-mod-named-entries groups closed) nil)))

(defun fn-mod-all-approverp (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (and (fn-mod-entry-approverp (car entries))
           (fn-mod-all-approverp (cdr entries)))
    t))

; Whether some group of GROUPS is closed ("n") or moderated under CLOSED.
(defun fn-mod-some-gatedp (groups closed)
  (declare (xargs :guard t))
  (if (consp groups)
      (or (not (equal (fn-nntp-closed-status (car groups) closed) "y"))
          (fn-mod-some-gatedp (cdr groups) closed))
    nil))

; A connection's view of the entries: LOGIN's octets (nil when the
; connection has not authenticated) turn each :moderated entry naming LOGIN
; among its moderators into (:approver G Q); every other entry is kept.
(defun fn-mod-session-entries (closed login)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (enable fn-nntp-moderated-entryp)))))
  (if (consp closed)
      (let ((e (car closed)))
        (cons (if (and login
                       (fn-nntp-moderated-entryp e)
                       (equal (car e) :moderated)
                       (member-equal login (true-list-fix
                                            (fn-mod-entry-moderators e))))
                  (list :approver (fn-mod-entry-group e) (fn-mod-entry-queue e))
                e)
              (fn-mod-session-entries (cdr closed) login)))
    nil))

; No entry of CLOSED is an :approver entry: what the owner installs.
(defun fn-mod-no-approversp (closed)
  (declare (xargs :guard t))
  (if (consp closed)
      (and (not (fn-mod-entry-approverp (car closed)))
           (fn-mod-no-approversp (cdr closed)))
    t))

; -----------------------------------------------------------------------------
; What the gate reads of the proto-article

; nil when SOURCE is not an ordinary article the injection's proto-article
; check admits (the parse is bounded by the configuration's article bound, as
; the injection's is); else (APPROVEDP MSGID-SUPPLIEDP DATE-ABSENTP).
(defun fn-mod-facts (source config)
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
                  (list (not (fn-inj-absentp article *fn-mod-approved-name*))
                        (if (fn-inj-nth 1 check) t nil)
                        (fn-inj-absentp article *fn-inj-date-name*)))))))))))

(defun fn-mod-facts-approvedp (facts)
  (declare (xargs :guard t))
  (fn-inj-car facts))

; -----------------------------------------------------------------------------
; The envelope (RFC 5537 section 3.5.1, method 1)

(defconst *fn-mod-from* '(70 114 111 109 58 32 109 111 100 101 114 97 116 105
                          111 110 64))              ; "From: moderation@"
(defconst *fn-mod-subject*
  ; "Subject: held for moderation in "
  '(83 117 98 106 101 99 116 58 32 104 101 108 100 32 102 111 114 32 109 111
    100 101 114 97 116 105 111 110 32 105 110 32))
(defconst *fn-mod-newsgroups* '(78 101 119 115 103 114 111 117 112 115 58 32))
(defconst *fn-mod-content-type*
  ; "Content-Type: application/news-transmission; usage=moderate"
  '(67 111 110 116 101 110 116 45 84 121 112 101 58 32 97 112 112 108 105 99
    97 116 105 111 110 47 110 101 119 115 45 116 114 97 110 115 109 105 115 115
    105 111 110 59 32 117 115 97 103 101 61 109 111 100 101 114 97 116 101))
(defconst *fn-mod-id-prefix* '(102 110 45 109 111 100 101 114 97 116 101 46))
                                                    ; "fn-moderate."

; <fn-moderate.LEFT@RIGHT> for the proto-article's <LEFT@RIGHT>.
(defun fn-mod-envelope-msgid (msgid)
  (declare (xargs :guard t))
  (if (and (consp msgid) (equal (car msgid) 60))
      (cons 60 (fn-inj-append *fn-mod-id-prefix* (cdr msgid)))
    msgid))

; The proto-article as forwarded: its Message-ID and Date lines added when
; the poster supplied none (RFC 5537 section 3.5 item 7), then the source.
(defun fn-mod-forwarded-source (source facts msgid date)
  (declare (xargs :guard t))
  (fn-inj-append
   (if (fn-inj-car (fn-inj-cdr facts)) nil (fn-inj-message-id-line msgid))
   (fn-inj-append
    (if (fn-inj-car (fn-inj-cdr (fn-inj-cdr facts))) (fn-inj-date-line date) nil)
    source)))

(defun fn-mod-concat (pieces)
  (declare (xargs :guard t))
  (if (consp pieces)
      (fn-inj-append (car pieces) (fn-mod-concat (cdr pieces)))
    nil))

(defun fn-mod-envelope-source (agent group queue msgid forwarded)
  (declare (xargs :guard t))
  (fn-mod-concat
   (list *fn-mod-from* agent *fn-inj-crlf*
         *fn-mod-subject* group *fn-inj-crlf*
         *fn-mod-newsgroups* queue *fn-inj-crlf*
         (fn-inj-message-id-line (fn-mod-envelope-msgid msgid))
         *fn-mod-content-type* *fn-inj-crlf*
         *fn-inj-crlf*
         forwarded)))

; The forward: the envelope's injection into ENTRY's queue, or the refusal
; :moderation-unavailable when it is not injected or names a closed or
; moderated group.
(defun fn-mod-forward (source config observation decision facts entry)
  (declare (xargs :guard t))
  (if (not (and (fn-clock-observationp observation)
                (fn-clock-has-wall observation)))
      (fn-inj-refuse :moderation-unavailable)
    (let* ((msgid (fn-inj-decision-msgid decision))
           (date (fn-inj-date-octets
                  (fn-inj-instant-of (fn-clock-wall observation))))
           (envelope (fn-mod-envelope-source
                      (fn-inj-config-agent config)
                      (fn-mod-entry-group entry) (fn-mod-entry-queue entry)
                      msgid
                      (fn-mod-forwarded-source source facts msgid date)))
           (d (fn-inj-decide envelope config observation)))
      (if (and (fn-inj-injectedp d)
               (equal (fn-inj-decision-msgid d) (fn-mod-envelope-msgid msgid))
               (not (fn-mod-some-gatedp (fn-inj-decision-groups d)
                                        (fn-inj-config-closed config))))
          d
        (fn-inj-refuse :moderation-unavailable)))))

; -----------------------------------------------------------------------------
; The gate

; DECISION is the injection's accepted decision on SOURCE.
(defun fn-mod-gate (source config observation decision)
  (declare (xargs :guard t))
  (let* ((facts (fn-mod-facts source config))
         (entries (and facts
                       (fn-mod-named-entries (fn-inj-decision-groups decision)
                                             (fn-inj-config-closed config)))))
    (cond ((not (consp entries)) decision)
          ((fn-mod-facts-approvedp facts)
           (if (fn-mod-all-approverp entries)
               decision
             (fn-inj-refuse :approval-not-moderator)))
          (t (fn-mod-forward source config observation decision facts
                             (car entries))))))

; -----------------------------------------------------------------------------
; The gate's properties (the keystones over the served decision are in
; books/nntp-post.lisp, over `fn-post-gated-decision').

(defthm fn-mod-entry-group-of-an-entry
  (implies (fn-nntp-moderated-entryp e)
           (equal (fn-mod-entry-group e) (cadr e)))
  :hints (("Goal" :in-theory (enable fn-nntp-moderated-entryp fn-inj-car
                                     fn-inj-cdr))))

(local
 (defthm fn-mod-entry-of-is-moderated-member
   (implies (fn-mod-entry-of g closed)
            (fn-nntp-moderated-memberp g closed))
   :hints (("Goal" :in-theory (enable fn-nntp-moderated-memberp)))))

(defthm fn-mod-some-gatedp-when-named-entries
  (implies (consp (fn-mod-named-entries groups closed))
           (fn-mod-some-gatedp groups closed))
  :hints (("Goal" :in-theory (enable fn-nntp-closed-status))))

; A refusal of the injection names no group (as it carries no octets,
; books/injection-invariants.lisp `fn-inj-refusal-produces-no-octets').
(defthm fn-mod-injection-refusal-names-no-group
  (implies (not (fn-inj-injectedp (fn-inj-decide source config observation)))
           (equal (fn-inj-decision-groups
                   (fn-inj-decide source config observation))
                  nil))
  :hints (("Goal" :in-theory (e/d (fn-inj-decide fn-inj-refuse
                                   fn-inj-injectedp)
                                  (fn-article-parse fn-af-proto-article-check
                                   fn-article-result-okp
                                   fn-article-result-article
                                   fn-article-syntax-p fn-article-get-headers
                                   fn-clock-observationp fn-clock-has-wall
                                   fn-clock-wall fn-clock-monotonic)))))

; An unapproved ordinary article is never committed to a moderated group by
; the gate: what it returns, when injected, names no moderated group.
(defthm fn-mod-gate-unapproved-names-no-moderated-group
  (implies (and (fn-mod-facts source config)
                (not (fn-mod-facts-approvedp (fn-mod-facts source config)))
                (fn-inj-injectedp
                 (fn-mod-gate source config observation decision)))
           (not (fn-mod-named-entries
                 (fn-inj-decision-groups
                  (fn-mod-gate source config observation decision))
                 (fn-inj-config-closed config))))
  :hints (("Goal" :in-theory (e/d () (fn-mod-facts fn-inj-decide
                                      fn-mod-named-entries
                                      fn-mod-some-gatedp))
           :use ((:instance fn-mod-some-gatedp-when-named-entries
                            (groups (fn-inj-decision-groups
                                     (fn-mod-gate source config observation
                                                  decision)))
                            (closed (fn-inj-config-closed config)))))))

; What the gate submits is the injection's decision or the envelope, whose
; Message-ID is the proto-article's with the envelope prefix.
(defthm fn-mod-gate-is-the-decision-or-its-envelope
  (implies (fn-inj-injectedp (fn-mod-gate source config observation decision))
           (or (equal (fn-mod-gate source config observation decision)
                      decision)
               (equal (fn-inj-decision-msgid
                       (fn-mod-gate source config observation decision))
                      (fn-mod-envelope-msgid
                       (fn-inj-decision-msgid decision)))))
  :hints (("Goal" :in-theory (e/d () (fn-mod-facts fn-inj-decide
                                      fn-mod-named-entries fn-mod-some-gatedp
                                      fn-mod-envelope-msgid
                                      fn-mod-envelope-source))))
  :rule-classes nil)

; The envelope prefix is injective on identifiers that open with "<".
(defthm fn-mod-envelope-msgid-injective
  (implies (and (consp a) (equal (car a) 60) (consp b) (equal (car b) 60))
           (equal (equal (fn-mod-envelope-msgid a) (fn-mod-envelope-msgid b))
                  (equal a b)))
  :hints (("Goal" :in-theory (enable fn-inj-append))))

; An envelope identifier is never an identifier the injection generates:
; a generated one is "<" and then a decimal digit
; (`fn-inj-generated-message-id'), an envelope one "<fn-moderate.", and any
; other identifier is not changed and does not open with "<".  So a
; forwarded submission never takes the identity of a direct one.
(encapsulate
 ()
 (local (include-book "arithmetic/top" :dir :system))
 ; The floor/mod facts (books/injection-invariants.lisp takes them from ihs
 ; for the same renderer).
 (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

 (local
  (defthm fn-mod-a-decimal-digit
    (implies (natp n)
             (and (<= 0 (mod n 10)) (< (mod n 10) 10)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (disable mod)))))

 (local
  (defthm fn-mod-a-decimal-digit-is-an-integer
    (implies (natp n) (integerp (mod n 10)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (disable mod)))))

 (local
  (defthm fn-mod-digits-rev-members-are-digits
    (implies (member-equal x (fn-inj-digits-rev n w))
             (and (integerp x) (<= 48 x) (<= x 57)))
    :hints (("Goal" :in-theory (e/d (fn-inj-digits-rev) (mod floor))))))

 (local
  (defthm fn-mod-member-of-rev-append
    (iff (member-equal x (fn-inj-rev-append a b))
         (or (member-equal x a) (member-equal x b)))
    :hints (("Goal" :in-theory (enable fn-inj-rev-append)
             :induct (fn-inj-rev-append a b)))))

 (local
  (defthm fn-mod-digits-rev-of-a-width
    (implies (posp w) (consp (fn-inj-digits-rev n w)))
    :hints (("Goal" :in-theory (enable fn-inj-digits-rev)))))

 (local
  (defthm fn-mod-consp-of-rev-append
    (implies (consp a) (consp (fn-inj-rev-append a b)))
    :hints (("Goal" :in-theory (enable fn-inj-rev-append)))))

 (local
  (defthm fn-mod-car-of-rev-append-is-a-member
    (implies (consp a) (member-equal (car (fn-inj-rev-append a b)) a))
    :hints (("Goal" :in-theory (enable fn-inj-rev-append)
             :induct (fn-inj-rev-append a b)))))

 (local
  (defthm fn-mod-first-digit
    (and (consp (fn-inj-digits n 20))
         (integerp (car (fn-inj-digits n 20)))
         (<= 48 (car (fn-inj-digits n 20)))
         (<= (car (fn-inj-digits n 20)) 57))
    :hints (("Goal" :in-theory (enable fn-inj-digits)
             :use ((:instance fn-mod-digits-rev-members-are-digits
                              (x (car (fn-inj-rev-append
                                       (fn-inj-digits-rev n 20) nil)))
                              (w 20))
                   (:instance fn-mod-car-of-rev-append-is-a-member
                              (a (fn-inj-digits-rev n 20)) (b nil)))))
    :rule-classes nil))

 (local
  (defthm fn-mod-inj-append-of-a-cons
    (implies (consp a)
             (equal (fn-inj-append a b)
                    (cons (car a) (fn-inj-append (cdr a) b))))
    :hints (("Goal" :in-theory (enable fn-inj-append)))))

 (local
  (defthm fn-mod-inj-append-of-nil
    (equal (fn-inj-append nil b) b)
    :hints (("Goal" :in-theory (enable fn-inj-append)))))

 (local
  (defthm fn-mod-car-of-inj-append
    (implies (consp a)
             (equal (car (fn-inj-append a b)) (car a)))
    :hints (("Goal" :in-theory (enable fn-inj-append)))))

 (defthm fn-mod-generated-id-opens
    (and (consp (fn-inj-generated-message-id observation config))
         (equal (car (fn-inj-generated-message-id observation config)) 60)
         (consp (cdr (fn-inj-generated-message-id observation config)))
         (equal (cadr (fn-inj-generated-message-id observation config))
                (car (fn-inj-digits (fn-clock-wall observation) 20))))
    :hints (("Goal" :in-theory (e/d (fn-inj-generated-message-id)
                                    (fn-inj-digits))
             :use ((:instance fn-mod-first-digit
                              (n (fn-clock-wall observation))))))
    :rule-classes nil)

 (local
  (defthm fn-mod-envelope-msgid-opens
    (implies (and (consp m) (equal (car m) 60))
             (and (consp (fn-mod-envelope-msgid m))
                  (equal (car (fn-mod-envelope-msgid m)) 60)
                  (equal (cadr (fn-mod-envelope-msgid m)) 102)))
    :hints (("Goal" :in-theory (enable fn-mod-envelope-msgid fn-inj-append)))
    :rule-classes nil))

 (defthm fn-mod-envelope-msgid-is-not-a-generated-id
   (not (equal (fn-mod-envelope-msgid m)
               (fn-inj-generated-message-id observation config)))
   :hints (("Goal" :in-theory (disable fn-inj-generated-message-id
                                       fn-mod-envelope-msgid fn-inj-digits)
            :cases ((and (consp m) (equal (car m) 60)))
            :use ((:instance fn-mod-first-digit
                             (n (fn-clock-wall observation)))
                  (:instance fn-mod-generated-id-opens)
                  (:instance fn-mod-envelope-msgid-opens)))
           ("Subgoal 2" :in-theory (e/d (fn-mod-envelope-msgid)
                                        (fn-inj-generated-message-id
                                         fn-inj-digits))))))

; The session view: an entry of G becomes :approver exactly when the login
; is one of G's moderators (the owner installs no :approver entry).
(defthm fn-mod-entry-of-session-entries
  (equal (fn-mod-entry-of g (fn-mod-session-entries closed login))
         (let ((e (fn-mod-entry-of g closed)))
           (if (and e login (equal (car e) :moderated)
                    (member-equal login
                                  (true-list-fix (fn-mod-entry-moderators e))))
               (list :approver g (fn-mod-entry-queue e))
             e)))
  :hints (("Goal" :in-theory (enable fn-nntp-moderated-entryp fn-inj-car
                                     fn-inj-cdr))))

(local
 (defthm fn-mod-no-approver-member
   (implies (and (fn-mod-no-approversp closed) (member-equal e closed))
            (not (fn-mod-entry-approverp e)))))

(local
 (defthm fn-mod-entry-of-is-a-member
   (implies (fn-mod-entry-of g closed)
            (member-equal (fn-mod-entry-of g closed) closed))
   :hints (("Goal" :in-theory (disable fn-mod-entry-group-of-an-entry)))))

(local
 (defthm fn-mod-entry-of-without-approvers
   (implies (fn-mod-no-approversp closed)
            (not (fn-mod-entry-approverp (fn-mod-entry-of g closed))))
   :hints (("Goal" :in-theory (disable fn-mod-entry-of fn-mod-no-approversp
                                       fn-mod-entry-approverp)
            :cases ((fn-mod-entry-of g closed))
            :use ((:instance fn-mod-no-approver-member
                             (e (fn-mod-entry-of g closed)))
                  (:instance fn-mod-entry-of-is-a-member))))))

(defthm fn-mod-session-entries-approver-iff-moderator
  (implies (fn-mod-no-approversp closed)
           (iff (fn-mod-entry-approverp
                 (fn-mod-entry-of g (fn-mod-session-entries closed login)))
                (and login
                     (fn-mod-entry-of g closed)
                     (equal (car (fn-mod-entry-of g closed)) :moderated)
                     (member-equal login
                                   (true-list-fix
                                    (fn-mod-entry-moderators
                                     (fn-mod-entry-of g closed)))))))
  :hints (("Goal" :in-theory (disable fn-mod-entry-of fn-mod-session-entries
                                      fn-mod-no-approversp
                                      fn-mod-entry-of-without-approvers)
           :use ((:instance fn-mod-entry-of-without-approvers)))))

; And the view keeps every entry's group and its status: LIST ACTIVE lists
; the same "m" (and "n") on every connection.
; (G is a group name's octets, never an entry.)
(local
 (defthm fn-mod-session-entries-keep-closed-member
   (implies (not (fn-nntp-moderated-entryp g))
            (equal (fn-nntp-closed-memberp g (fn-mod-session-entries closed login))
                   (fn-nntp-closed-memberp g closed)))
   :hints (("Goal" :induct (fn-mod-session-entries closed login)
            :in-theory (enable fn-nntp-closed-memberp fn-nntp-moderated-entryp
                               fn-inj-car fn-inj-cdr)))))

(local
 (defthm fn-mod-session-entries-keep-moderated-member
   (equal (fn-nntp-moderated-memberp g (fn-mod-session-entries closed login))
          (fn-nntp-moderated-memberp g closed))
   :hints (("Goal" :induct (fn-mod-session-entries closed login)
            :in-theory (enable fn-nntp-moderated-memberp fn-nntp-moderated-entryp
                               fn-inj-car fn-inj-cdr)))))

(defthm fn-mod-session-entries-keep-the-status
  (implies (not (fn-nntp-moderated-entryp g))
           (equal (fn-nntp-closed-status g (fn-mod-session-entries closed login))
                  (fn-nntp-closed-status g closed)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-closed-status)
                                  (fn-mod-session-entries)))))

(deftheory fn-mod-vocabulary
  '((:d fn-mod-entry-group) (:d fn-mod-entry-queue) (:d fn-mod-entry-moderators)
    (:d fn-mod-entry-approverp) (:d fn-mod-entry-of) (:d fn-mod-named-entries)
    (:d fn-mod-all-approverp) (:d fn-mod-some-gatedp)
    (:d fn-mod-session-entries) (:d fn-mod-no-approversp) (:d fn-mod-facts)
    (:d fn-mod-facts-approvedp) (:d fn-mod-envelope-msgid)
    (:d fn-mod-forwarded-source) (:d fn-mod-concat) (:d fn-mod-envelope-source)
    (:d fn-mod-forward) (:d fn-mod-gate)))
(in-theory (disable fn-mod-vocabulary))
