; fn: D25 over the functions the host calls.  The duplicate-versus-conflict
; verdict of fn-pb-existing-action (books/poster-bytes.lisp; host callers at
; host/owner-host.lisp fn-owner-existing-action and fn-owner-prepare) is the
; word fn-own-outcome renders (host/owner-host.lisp fn-owner-outcome), and a
; resend of one proto-article injected at a later second has the same
; poster's bytes, so it is answered "already stored here".
(in-package "ACL2")
(include-book "poster-bytes")
(include-book "owner")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The projection, line by line

(local
 (defthm fn-pb-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-pb-inj-append-is-append
   (equal (fn-inj-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-pb-rest-of-append-lf-free
   (implies (not (member-equal 10 a))
            (equal (fn-pb-rest (append a y)) (fn-pb-rest y)))))

(local
 (defthm fn-pb-line-of-append-lf-free
   (implies (not (member-equal 10 a))
            (equal (fn-pb-line (append a y)) (append a (fn-pb-line y))))))

; An injected field line is dropped with its continuation lines.
(defthm fn-pb-project-skips-an-injected-line
  (implies (and (consp x)
                (not (fn-article-wspp (car x)))
                (fn-pb-line-injectedp x)
                (not (equal (fn-pb-line x) '(13 10))))
           (equal (fn-pb-project x drop) (fn-pb-project (fn-pb-rest x) t)))
  :hints (("Goal" :expand ((fn-pb-project x drop)))))

; Every other field line is kept verbatim.
(defthm fn-pb-project-keeps-a-field-line
  (implies (and (consp x)
                (not (fn-article-wspp (car x)))
                (not (fn-pb-line-injectedp x))
                (not (equal (fn-pb-line x) '(13 10))))
           (equal (fn-pb-project x drop)
                  (append (fn-pb-line x) (fn-pb-project (fn-pb-rest x) nil))))
  :hints (("Goal" :expand ((fn-pb-project x drop)))))

(defthm fn-pb-project-drop-is-irrelevant-off-a-continuation
  (implies (not (fn-article-wspp (car x)))
           (equal (fn-pb-project x t) (fn-pb-project x nil)))
  :hints (("Goal" :expand ((fn-pb-project x t) (fn-pb-project x nil)))))

(local (in-theory (disable fn-pb-project fn-pb-line-injectedp)))

; -----------------------------------------------------------------------------
; The node's injection prefix is invisible to the projection.  fn-inj-prefix
; (books/injection.lisp) is what fn-inj-decide prepends to the poster's
; source: Path, Injection-Date and Injection-Info, then a generated
; Message-ID line when none was supplied and a generated Date line when none
; was supplied.  With no generated Date, the projection of the injected
; article is the projection of the source after an injected field -- for
; every date, so the clock second never reaches the key.  (fn-inj-append is
; append; the statements below use append.)

(defthm fn-pb-project-of-an-injection-prefix
  (implies (and (not (member-equal 10 date))
                (not (member-equal 10 agent)))
           (equal (fn-pb-project
                   (append (fn-inj-prefix date msgid agent gid nil) source)
                   drop)
                  (fn-pb-project (append (if gid (fn-inj-message-id-line msgid) nil)
                                         source)
                                 t)))
  :hints (("Goal" :in-theory (enable fn-inj-prefix fn-inj-path-line
                                     fn-inj-injection-date-line
                                     fn-inj-injection-info-line
                                     fn-pb-line-injectedp))))

; With a supplied Message-ID and a source that opens on a field line, the
; poster's bytes of the injected article are the poster's bytes of the
; source itself.
(defthm fn-pb-poster-bytes-of-an-injection-are-the-sources
  (implies (and (not (member-equal 10 date))
                (not (member-equal 10 agent))
                (not (fn-article-wspp (car source))))
           (equal (fn-pb-poster-bytes
                   (append (fn-inj-prefix date msgid agent nil nil) source))
                  (fn-pb-poster-bytes source)))
  :hints (("Goal" :use ((:instance fn-pb-project-of-an-injection-prefix
                                   (gid nil) (drop nil))))))

; The rendered date and a configured agent contain no line feed.
(local
 (defthm fn-pb-component-octets-are-not-lf
   (and (not (equal (fn-inj-hi2 n) 10))
        (not (equal (fn-inj-lo2 n) 10))
        (not (equal (fn-inj-y-th n) 10))
        (not (equal (fn-inj-y-hu n) 10))
        (not (equal (fn-inj-y-te n) 10))
        (not (equal (fn-inj-y-un n) 10))
        (not (equal (fn-inj-month-c1 n) 10))
        (not (equal (fn-inj-month-c2 n) 10))
        (not (equal (fn-inj-month-c3 n) 10))
        (not (equal (fn-inj-dow-c1 n) 10))
        (not (equal (fn-inj-dow-c2 n) 10))
        (not (equal (fn-inj-dow-c3 n) 10)))
   :hints (("Goal" :in-theory (enable fn-inj-hi2 fn-inj-lo2 fn-inj-y-th
                                      fn-inj-y-hu fn-inj-y-te fn-inj-y-un
                                      fn-inj-r1 fn-inj-r2
                                      fn-inj-month-c1 fn-inj-month-c2
                                      fn-inj-month-c3 fn-inj-dow-c1
                                      fn-inj-dow-c2 fn-inj-dow-c3)))))

(defthm fn-pb-date-octets-have-no-lf
  (not (member-equal 10 (fn-inj-date-octets inst)))
  :hints (("Goal" :in-theory (e/d (fn-inj-date-octets)
                                  (fn-inj-hi2 fn-inj-lo2 fn-inj-y-th
                                   fn-inj-y-hu fn-inj-y-te fn-inj-y-un
                                   fn-inj-month-c1 fn-inj-month-c2
                                   fn-inj-month-c3 fn-inj-dow-c1
                                   fn-inj-dow-c2 fn-inj-dow-c3)))))

(defthm fn-pb-dot-atom-text-has-no-lf
  (implies (fn-af-dot-atom-text-aux bytes want)
           (not (member-equal 10 bytes)))
  :hints (("Goal" :in-theory (enable fn-af-dot-atom-text-aux fn-af-atextp))))

; Every injected article is the prefix fn-inj-prefix builds, over this
; clock's rendered date, the decision's Message-ID and the configured agent,
; followed by the source unchanged.
(defthm fn-pb-injected-octets-are-prefix-and-source
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (and (fn-inj-configp config)
                (equal (fn-inj-decision-octets (fn-inj-decide source config obs))
                       (append
                        (fn-inj-prefix
                         (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall obs)))
                         (fn-inj-decision-msgid (fn-inj-decide source config obs))
                         (fn-inj-config-agent config)
                         (not (fn-inj-nth 1 (fn-af-proto-article-check
                                             (fn-article-result-article
                                              (fn-article-parse source)))))
                         (fn-inj-absentp (fn-article-result-article
                                          (fn-article-parse source))
                                         *fn-inj-date-name*))
                        source))))
  :hints (("Goal" :in-theory (e/d (fn-inj-decide fn-inj-injectedp fn-inj-refuse)
                                  (fn-pb-poster-bytes fn-article-parse
                                   fn-af-proto-article-check fn-inj-configp
                                   fn-article-result-okp fn-article-result-article
                                   fn-article-syntax-p fn-inj-mandatory-reason
                                   fn-inj-groups-admissiblep fn-inj-absentp
                                   fn-inj-prefix fn-inj-date-octets
                                   fn-inj-instant-of fn-inj-generated-message-id
                                   fn-clock-observationp fn-clock-has-wall
                                   fn-clock-wall fn-clock-monotonic floor))))
  :rule-classes nil)

; KEYSTONE (injection invariance).  One proto-article injected under two
; clock readings, with one Message-ID and a Date the poster supplied, has one
; poster's bytes: Injection-Date is the only octets the clock writes, and
; the projection drops it.  Without a supplied Date the injection writes a
; Date line from the clock, which is the poster's field, and the key differs
; (the teeth in tests/acl2/poster-bytes-tests.lisp).
(defthm fn-pb-a-resent-injection-has-the-same-poster-bytes
  (implies (and (fn-inj-injectedp (fn-inj-decide source config a))
                (fn-inj-injectedp (fn-inj-decide source config b))
                (equal (fn-inj-decision-msgid (fn-inj-decide source config a))
                       (fn-inj-decision-msgid (fn-inj-decide source config b)))
                (not (fn-inj-absentp (fn-article-result-article
                                      (fn-article-parse source))
                                     *fn-inj-date-name*)))
           (equal (fn-pb-poster-bytes
                   (fn-inj-decision-octets (fn-inj-decide source config a)))
                  (fn-pb-poster-bytes
                   (fn-inj-decision-octets (fn-inj-decide source config b)))))
  :hints (("Goal" :use ((:instance fn-pb-injected-octets-are-prefix-and-source
                                   (obs a))
                        (:instance fn-pb-injected-octets-are-prefix-and-source
                                   (obs b)))
                  :in-theory (e/d (fn-inj-configp fn-af-dot-atom-textp)
                                  (fn-inj-decide fn-inj-injectedp fn-inj-absentp
                                   fn-inj-prefix fn-inj-date-octets
                                   fn-inj-instant-of fn-af-proto-article-check
                                   fn-article-parse fn-article-result-article))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The decision.  The two case equations restate fn-pb-existing-action; they
; are named -by-definition and are not the keystones.

(defthm fn-pb-existing-action-is-duplicate-iff-same-poster-bytes-by-definition
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (equal (equal (fn-pb-existing-action msgid payload groups s) :duplicate)
           (and (if held t nil)
                (equal (fn-pb-poster-bytes payload)
                       (fn-pb-poster-bytes (fn-article-payload held)))
                (equal groups (fn-article-groups held)))))
  :rule-classes nil)

(defthm fn-pb-existing-action-is-conflict-iff-poster-bytes-differ-by-definition
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (equal (equal (fn-pb-existing-action msgid payload groups s) :conflict)
           (and (if held t nil)
                (or (not (equal (fn-pb-poster-bytes payload)
                                (fn-pb-poster-bytes (fn-article-payload held))))
                    (not (equal groups (fn-article-groups held)))))))
  :rule-classes nil)

; The poster's-bytes decision refines the byte-identity one it replaced
; (fn-sn-existing-action): it answers for exactly the same held Message-IDs,
; and every byte-identical resend is still a duplicate.  Only a conflict can
; become a duplicate, and only when the injected fields are all that differ.
(defthm fn-pb-existing-action-refines-the-byte-identity-decision
  (and (iff (fn-pb-existing-action msgid payload groups s)
            (fn-sn-existing-action msgid payload groups s))
       (implies (equal (fn-sn-existing-action msgid payload groups s) :duplicate)
                (equal (fn-pb-existing-action msgid payload groups s) :duplicate)))
  :hints (("Goal" :in-theory (enable fn-sn-existing-action)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The served reply.  host/native/owner.lisp fnn-owner-attempt returns the
; verdict of fn-owner-existing-action (fn-pb-existing-action) as its word,
; and host/owner-host.lisp fn-owner-outcome hands that word to fn-own-outcome.

(defun fn-pb-served-reply (o id word)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (fn-served-result-effects
     (fn-served-post-outcome
      (fn-served-make-conn-group-indexed
       (fn-own-conn-wire conn) (fn-own-conn-session conn)
       (fn-own-conn-archive conn) (fn-own-conn-config conn)
       (fn-own-conn-observation conn) (fn-own-clock o)
       (fn-own-conn-verdicts conn) (fn-own-conn-index conn)
       (fn-own-conn-group-index conn))
      word))))


; KEYSTONE (duplicate).  Over the function the host calls, a submission whose
; poster's bytes and groups are the held article's is answered with the
; duplicate line, `441 posting failed; this article is already stored here'
; (fn-post-store-refusal-line), while no completion has been consumed.
(defthm fn-pb-same-poster-bytes-is-answered-already-stored
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (implies (and (fn-own-find-conn id (fn-own-conns o))
                  (fn-own-inflight o)
                  (equal (fn-own-sub-id (fn-own-inflight o)) id)
                  (not (fn-own-completion-consumedp o))
                  held
                  (equal (fn-pb-poster-bytes payload)
                         (fn-pb-poster-bytes (fn-article-payload held)))
                  (equal groups (fn-article-groups held)))
             (equal (car (fn-own-outcome
                          o id (fn-pb-existing-action msgid payload groups s)))
                    (fn-pb-served-reply o id :duplicate))))
  :hints (("Goal" :in-theory (e/d (fn-own-outcome fn-own-outcome-completion
                                   fn-own-outcome-rendering fn-own-refusal-wordp
                                   fn-post-store-refusalp fn-pb-existing-action)
                                  (fn-served-post-outcome fn-own-advance
                                   fn-own-feed-durable fn-own-find-conn
                                   fn-served-make-conn-group-indexed
                                   fn-pb-poster-bytes fn-find-article))))
  :rule-classes nil)

; KEYSTONE (conflict).  Different poster's bytes, or different groups, under
; a held Message-ID are answered `441 posting failed; a different article
; with this Message-ID is stored here'.
(defthm fn-pb-different-poster-bytes-is-answered-conflict
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (implies (and (fn-own-find-conn id (fn-own-conns o))
                  (fn-own-inflight o)
                  (equal (fn-own-sub-id (fn-own-inflight o)) id)
                  (not (fn-own-completion-consumedp o))
                  held
                  (or (not (equal (fn-pb-poster-bytes payload)
                                  (fn-pb-poster-bytes (fn-article-payload held))))
                      (not (equal groups (fn-article-groups held)))))
             (equal (car (fn-own-outcome
                          o id (fn-pb-existing-action msgid payload groups s)))
                    (fn-pb-served-reply o id :conflict))))
  :hints (("Goal" :in-theory (e/d (fn-own-outcome fn-own-outcome-completion
                                   fn-own-outcome-rendering fn-own-refusal-wordp
                                   fn-post-store-refusalp fn-pb-existing-action)
                                  (fn-served-post-outcome fn-own-advance
                                   fn-own-feed-durable fn-own-find-conn
                                   fn-served-make-conn-group-indexed
                                   fn-pb-poster-bytes fn-find-article))))
  :rule-classes nil)

; KEYSTONE (K1 closed).  The held article is one proto-article injected at
; clock A; the poster resends the same source, injected at clock B, under
; the same Message-ID and groups.  The reply is the duplicate line at every
; pair of clock readings.
(defthm fn-pb-a-resend-at-a-later-second-is-answered-already-stored
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (implies (and (fn-own-find-conn id (fn-own-conns o))
                  (fn-own-inflight o)
                  (equal (fn-own-sub-id (fn-own-inflight o)) id)
                  (not (fn-own-completion-consumedp o))
                  held
                  (equal (fn-article-payload held)
                         (fn-inj-decision-octets (fn-inj-decide source config a)))
                  (fn-inj-injectedp (fn-inj-decide source config a))
                  (fn-inj-injectedp (fn-inj-decide source config b))
                  (equal (fn-inj-decision-msgid (fn-inj-decide source config a))
                         (fn-inj-decision-msgid (fn-inj-decide source config b)))
                  (not (fn-inj-absentp (fn-article-result-article
                                        (fn-article-parse source))
                                       *fn-inj-date-name*))
                  (equal groups (fn-article-groups held)))
             (equal (car (fn-own-outcome
                          o id
                          (fn-pb-existing-action
                           msgid
                           (fn-inj-decision-octets (fn-inj-decide source config b))
                           groups s)))
                    (fn-pb-served-reply o id :duplicate))))
  :hints (("Goal" :use ((:instance fn-pb-same-poster-bytes-is-answered-already-stored
                                   (payload (fn-inj-decision-octets
                                             (fn-inj-decide source config b))))
                        fn-pb-a-resent-injection-has-the-same-poster-bytes)
                  :in-theory (disable fn-own-outcome fn-pb-existing-action
                                      fn-pb-poster-bytes fn-inj-decide
                                      fn-inj-injectedp fn-inj-absentp
                                      fn-find-article fn-pb-served-reply)))
  :rule-classes nil)
