; fn: D25 over the functions the host calls.  The duplicate-versus-conflict
; verdict of fn-pb-existing-action (books/poster-bytes.lisp; host callers at
; host/owner-host.lisp fn-owner-existing-action and fn-owner-prepare) is the
; word fn-own-outcome renders (host/owner-host.lisp fn-owner-outcome).  One
; source injected at any two clock readings is one article; two different
; sources under one Message-ID are two, whatever differs between them.
(in-package "ACL2")
(include-book "poster-bytes")
(include-book "injection-invariants")
(include-book "owner")

(local
 (defthm fn-pb-inj-append-is-append
   (equal (fn-inj-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-pb-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; -----------------------------------------------------------------------------
; The submission's agent is the one its Path line names.

(local
 (defthm fn-pb-line-of-append-lf-free
   (implies (not (member-equal 10 a))
            (equal (fn-pb-line (append a y)) (append a (fn-pb-line y))))))

(local
 (defthm fn-pb-strip-of-append-left
   (implies (true-listp a)
            (equal (fn-inj-strip a (append a b)) b))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-pb-take-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-inj-take n (append a b)) a))
   :hints (("Goal" :in-theory (enable fn-inj-take)))))

(defthm fn-pb-path-agent-of-a-path-line
  (implies (and (true-listp agent) (consp agent)
                (not (member-equal 10 agent)))
           (equal (fn-pb-path-agent (append (fn-inj-path-line agent) rest))
                  agent))
  :hints (("Goal" :in-theory (enable fn-inj-path-line fn-inj-strip))))

(local (in-theory (disable fn-pb-path-agent)))

(defthm fn-pb-dot-atom-text-has-no-lf
  (implies (fn-af-dot-atom-text-aux bytes want)
           (not (member-equal 10 bytes)))
  :hints (("Goal" :in-theory (enable fn-af-dot-atom-text-aux fn-af-atextp))))

(local
 (defthm fn-pb-a-configured-agent-is-a-line-free-list
   (implies (fn-inj-configp config)
            (and (true-listp (fn-inj-config-agent config))
                 (consp (fn-inj-config-agent config))
                 (not (member-equal 10 (fn-inj-config-agent config)))))
   :hints (("Goal" :in-theory (enable fn-inj-configp fn-af-dot-atom-textp)))))

(local
 (defthm fn-pb-an-injection-configures
   (implies (fn-inj-injectedp (fn-inj-decide source config obs))
            (fn-inj-configp config))
   :hints (("Goal" :in-theory (e/d (fn-inj-decide fn-inj-injectedp fn-inj-refuse)
                                   (fn-inj-configp fn-inj-mandatory-reason
                                    fn-inj-groups-admissiblep fn-inj-absentp
                                    fn-inj-prefix fn-inj-date-octets
                                    fn-inj-instant-of fn-inj-generated-message-id
                                    fn-inj-append floor fn-article-parse
                                    fn-af-proto-article-check fn-article-result-okp
                                    fn-article-result-article fn-article-syntax-p
                                    fn-clock-observationp fn-clock-has-wall
                                    fn-clock-wall))))))

; Every injection block opens with the agent's Path line.
(local
 (defthm fn-pb-path-agent-of-a-prefix
   (implies (and (true-listp agent) (consp agent)
                 (not (member-equal 10 agent)))
            (equal (fn-pb-path-agent
                    (fn-inj-append (fn-inj-prefix date msgid agent gid gdate) source))
                   agent))
   :hints (("Goal" :in-theory (e/d (fn-inj-prefix)
                                   (fn-inj-path-line fn-inj-injection-date-line
                                    fn-inj-injection-info-line
                                    fn-inj-message-id-line fn-inj-date-line))))))

; An injected article's Path line names the configured agent.
(defthm fn-pb-path-agent-of-an-injection
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (equal (fn-pb-path-agent
                   (fn-inj-decision-octets (fn-inj-decide source config obs)))
                  (fn-inj-config-agent config)))
  :hints (("Goal" :use ((:instance fn-inj-injected-octets-are-the-block-and-the-source)
                        fn-pb-an-injection-configures
                        fn-pb-a-configured-agent-is-a-line-free-list
                        (:instance fn-pb-path-agent-of-a-prefix
                                   (date (fn-inj-date-octets
                                          (fn-inj-instant-of (fn-clock-wall obs))))
                                   (msgid (fn-inj-decision-msgid
                                           (fn-inj-decide source config obs)))
                                   (agent (fn-inj-config-agent config))
                                   (gid (not (fn-inj-nth 1 (fn-af-proto-article-check
                                                            (fn-article-result-article
                                                             (fn-article-parse source))))))
                                   (gdate (fn-inj-absentp (fn-article-result-article
                                                           (fn-article-parse source))
                                                          *fn-inj-date-name*))))
                  :in-theory (theory 'minimal-theory))))

; -----------------------------------------------------------------------------
; The comparison over two injections.

(local (in-theory (disable fn-inj-decide fn-inj-injectedp fn-inj-source-of)))

; KEYSTONE (retry).  One source injected by one configuration at any two
; clock readings, under one Message-ID, is one article: Date present or
; absent, Message-ID supplied, and whatever the two readings are.
(defthm fn-pb-one-source-at-two-clocks-is-one-article
  (implies (and (fn-inj-injectedp (fn-inj-decide source config a))
                (fn-inj-injectedp (fn-inj-decide source config b))
                (equal (fn-inj-decision-msgid (fn-inj-decide source config a))
                       msgid)
                (equal (fn-inj-decision-msgid (fn-inj-decide source config b))
                       msgid))
           (fn-pb-same-articlep
            msgid
            (fn-inj-decision-octets (fn-inj-decide source config b))
            (fn-inj-decision-octets (fn-inj-decide source config a))))
  :hints (("Goal" :use ((:instance fn-inj-source-of-inverts-the-injection
                                   (observation a))
                        (:instance fn-inj-source-of-inverts-the-injection
                                   (observation b))
                        (:instance fn-pb-path-agent-of-an-injection (obs b))))))

; KEYSTONE (conflict).  Two different sources injected by one configuration
; under one Message-ID are two articles: one changed authored byte, a
; changed or removed authored Date, a changed signature.
(defthm fn-pb-two-sources-are-two-articles
  (implies (and (fn-inj-injectedp (fn-inj-decide source1 config a))
                (fn-inj-injectedp (fn-inj-decide source2 config b))
                (equal (fn-inj-decision-msgid (fn-inj-decide source1 config a))
                       msgid)
                (equal (fn-inj-decision-msgid (fn-inj-decide source2 config b))
                       msgid)
                (not (equal source1 source2)))
           (not (fn-pb-same-articlep
                 msgid
                 (fn-inj-decision-octets (fn-inj-decide source2 config b))
                 (fn-inj-decision-octets (fn-inj-decide source1 config a)))))
  :hints (("Goal" :use ((:instance fn-inj-source-of-inverts-the-injection
                                   (source source1) (observation a))
                        (:instance fn-inj-source-of-inverts-the-injection
                                   (source source2) (observation b))
                        (:instance fn-pb-path-agent-of-an-injection
                                   (source source2) (obs b))))))

; Recipe v1 (before 2026-09-24): Path, Injection-Date, Injection-Info, then
; the generated Message-ID and Date lines, then the source.
(defun fn-pb-v1-injection (date msgid agent gid gdate source)
  (declare (xargs :guard t))
  (fn-inj-append
   (fn-inj-path-line agent)
   (fn-inj-append
    (fn-inj-injection-date-line date)
    (fn-inj-append
     (fn-inj-injection-info-line agent)
     (fn-inj-append (if gid (fn-inj-message-id-line msgid) nil)
                    (fn-inj-append (if gdate (fn-inj-date-line date) nil)
                                   source))))))

; A v1 record is read under v1.  Where v1 is unambiguous -- a supplied
; Message-ID and Date, and a source that opens with neither this Message-ID's
; line nor a Date line of the injection's date -- a resend of that source,
; which v2 injects with no Injection-Date, is the same article.
(defthm fn-pb-a-v1-record-is-read-under-v1
  (implies (and (fn-inj-injectedp (fn-inj-decide source config b))
                (equal (fn-inj-decision-msgid (fn-inj-decide source config b))
                       msgid)
                (true-listp date) (equal (len date) 31)
                (equal (fn-inj-strip (fn-inj-message-id-line msgid) source) :no)
                (equal (fn-inj-strip (fn-inj-date-line date) source) :no))
           (fn-pb-same-articlep
            msgid
            (fn-inj-decision-octets (fn-inj-decide source config b))
            (fn-pb-v1-injection date msgid (fn-inj-config-agent config)
                                nil nil source)))
  :hints (("Goal" :use ((:instance fn-inj-source-of-inverts-the-injection
                                   (observation b))
                        (:instance fn-pb-path-agent-of-an-injection (obs b))
                        (:instance fn-inj-the-atom-no-is-never-injected
                                   (config config) (observation b))
                        (:instance fn-inj-source-of-a-v1-record
                                   (agent (fn-inj-config-agent config)))))))

; A v1 record whose source position opens with a Date line of the injection's
; date is ambiguous (the poster's Date or the injector's), and is compared
; exactly: its subject is its octets.
(defthm fn-pb-an-ambiguous-v1-record-is-compared-exactly
  (implies (and (true-listp date) (equal (len date) 31)
                (not (equal source :no)))
           (equal (fn-pb-subject (fn-pb-v1-injection date msgid agent nil t source)
                                 agent msgid)
                  (cons :octets (fn-pb-v1-injection date msgid agent nil t source))))
  :hints (("Goal" :use ((:instance fn-inj-source-of-an-ambiguous-v1-record)))))

; -----------------------------------------------------------------------------
; The decision.  The two case equations restate fn-pb-existing-action; they
; are named -by-definition and are not the keystones.

(defthm fn-pb-existing-action-is-duplicate-iff-same-article-by-definition
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (equal (equal (fn-pb-existing-action msgid payload groups s) :duplicate)
           (and (if held t nil)
                (fn-pb-same-articlep (fn-record-string-octets msgid) payload
                                     (fn-article-payload held))
                (equal groups (fn-article-groups held)))))
  :rule-classes nil)

; The source decision refines the byte-identity one it replaced
; (fn-sn-existing-action): it answers for exactly the same held Message-IDs,
; and every byte-identical resend is still a duplicate.
(defthm fn-pb-existing-action-refines-the-byte-identity-decision
  (and (iff (fn-pb-existing-action msgid payload groups s)
            (fn-sn-existing-action msgid payload groups s))
       (implies (equal (fn-sn-existing-action msgid payload groups s) :duplicate)
                (equal (fn-pb-existing-action msgid payload groups s) :duplicate)))
  :hints (("Goal" :in-theory (enable fn-sn-existing-action)))
  :rule-classes nil)

; A second post under a Message-ID the Store does not hold is not answered
; from the Store at all: the host prepares it as a new article.  This is the
; definition (the lookup is by Message-ID), stated so the new-article row of
; the matrix has a named subject.
(defthm fn-pb-an-unheld-message-id-is-a-new-article-by-definition
  (implies (not (fn-find-article
                 msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
           (equal (fn-pb-existing-action msgid payload groups s) nil))
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

; The duplicate line, `441 posting failed; this article is already stored
; here' (fn-post-store-refusal-line), for the same article and groups, while
; no completion has been consumed.
(defthm fn-pb-same-article-is-answered-already-stored
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (implies (and (fn-own-find-conn id (fn-own-conns o))
                  (fn-own-inflight o)
                  (equal (fn-own-sub-id (fn-own-inflight o)) id)
                  (not (fn-own-completion-consumedp o))
                  held
                  (fn-pb-same-articlep (fn-record-string-octets msgid) payload
                                       (fn-article-payload held))
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
                                   fn-pb-same-articlep fn-find-article))))
  :rule-classes nil)

; The conflict line, `441 posting failed; a different article with this
; Message-ID is stored here', for another article or other groups.
(defthm fn-pb-different-article-is-answered-conflict
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (implies (and (fn-own-find-conn id (fn-own-conns o))
                  (fn-own-inflight o)
                  (equal (fn-own-sub-id (fn-own-inflight o)) id)
                  (not (fn-own-completion-consumedp o))
                  held
                  (or (not (fn-pb-same-articlep (fn-record-string-octets msgid)
                                                payload (fn-article-payload held)))
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
                                   fn-pb-same-articlep fn-find-article))))
  :rule-classes nil)

; KEYSTONE (K1 closed, served).  The held article is one source injected at
; clock A; the poster resends that source, injected at clock B, under the
; same Message-ID and groups.  The reply is the duplicate line at every pair
; of readings, with the Date present or absent.
(defthm fn-pb-a-resend-at-any-clock-is-answered-already-stored
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (fn-inj-decide source config a))
        (db (fn-inj-decide source config b)))
    (implies (and (fn-own-find-conn id (fn-own-conns o))
                  (fn-own-inflight o)
                  (equal (fn-own-sub-id (fn-own-inflight o)) id)
                  (not (fn-own-completion-consumedp o))
                  held
                  (equal (fn-article-payload held) (fn-inj-decision-octets da))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (equal groups (fn-article-groups held)))
             (equal (car (fn-own-outcome
                          o id
                          (fn-pb-existing-action
                           msgid (fn-inj-decision-octets db) groups s)))
                    (fn-pb-served-reply o id :duplicate))))
  :hints (("Goal" :use ((:instance fn-pb-same-article-is-answered-already-stored
                                   (payload (fn-inj-decision-octets
                                             (fn-inj-decide source config b))))
                        (:instance fn-pb-one-source-at-two-clocks-is-one-article
                                   (msgid (fn-record-string-octets msgid))))
                  :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

; KEYSTONE (conflict, served).  A different source under the held Message-ID
; -- one changed authored byte, an authored Date changed or removed -- is
; answered with the conflict line, at every pair of clock readings.
(defthm fn-pb-a-changed-source-is-answered-conflict
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (fn-inj-decide source1 config a))
        (db (fn-inj-decide source2 config b)))
    (implies (and (fn-own-find-conn id (fn-own-conns o))
                  (fn-own-inflight o)
                  (equal (fn-own-sub-id (fn-own-inflight o)) id)
                  (not (fn-own-completion-consumedp o))
                  held
                  (equal (fn-article-payload held) (fn-inj-decision-octets da))
                  (fn-inj-injectedp da)
                  (fn-inj-injectedp db)
                  (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                  (not (equal source1 source2)))
             (equal (car (fn-own-outcome
                          o id
                          (fn-pb-existing-action
                           msgid (fn-inj-decision-octets db) groups s)))
                    (fn-pb-served-reply o id :conflict))))
  :hints (("Goal" :use ((:instance fn-pb-different-article-is-answered-conflict
                                   (payload (fn-inj-decision-octets
                                             (fn-inj-decide source2 config b))))
                        (:instance fn-pb-two-sources-are-two-articles
                                   (msgid (fn-record-string-octets msgid))))
                  :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

; KEYSTONE (no second obligation).  Whatever fn-pb-existing-action answers
; -- duplicate, conflict, or nothing held -- the outcome leaves the owner's
; Store as it was (the held article, its local number and its obligation are
; the ones already there), writes no outcome record and moves no feed: none
; of its words is the durable completion.
(defthm fn-pb-an-existing-action-writes-nothing
  (let ((next (cdr (fn-own-outcome
                    o id (fn-pb-existing-action msgid payload groups s)))))
    (and (equal (fn-own-store next) (fn-own-store o))
         (equal (fn-own-feeds next) (fn-own-feeds o))
         (null (fn-own-outcome-records
                o id (fn-pb-existing-action msgid payload groups s)))))
  :hints (("Goal" :in-theory (e/d (fn-own-outcome fn-own-outcome-completion
                                   fn-own-outcome-records fn-own-refusal-wordp
                                   fn-pb-existing-action)
                                  (fn-served-post-outcome fn-own-advance
                                   fn-own-feed-durable fn-own-find-conn
                                   fn-served-make-conn-group-indexed
                                   fn-pb-same-articlep fn-find-article))))
  :rule-classes nil)
