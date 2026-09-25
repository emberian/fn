; Witnesses and teeth for books/poster-bytes-invariants.lisp (D25): the
; duplicate-versus-conflict verdict keys on the poster's source, recovered by
; the injection inverse (books/injection.lisp fn-inj-source-of).
;
; The subjects are the functions the host calls: fn-pb-existing-action
; (host/owner-host.lisp fn-owner-existing-action and fn-owner-prepare,
; host/store-node-host.lisp) and fn-own-outcome (fn-owner-outcome).  The
; witnesses are proto-articles injected by the real fn-inj-decide at two
; clock readings 37 s apart, the held one committed through the real Store.
; The review's matrix (planning/review-2026-09-24-gpt6-direction.md, D25):
; Date present and absent, one changed authored byte, a changed or removed
; authored Date, another injecting identity, a recipe v1 record, and a
; second identical post under a new Message-ID.
(in-package "ACL2")
(include-book "../../books/poster-bytes-invariants")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun pbt-text (s) (fn-record-string-octets s))

(defconst *pbt-agent* (pbt-text "hbox.ember.software"))
(defconst *pbt-config*
  (fn-inj-make-config t *pbt-agent* (list (pbt-text "fn.letters")) 32768))
(defconst *pbt-other-config*
  (fn-inj-make-config t (pbt-text "fnB.hbox.test") (list (pbt-text "fn.letters")) 32768))
; Wall readings are milliseconds since 2000-01-01T00:00:00Z; B is 37 s after A.
(defconst *pbt-a* (fn-clock-observation 5000000 843004800000 0 t))
(defconst *pbt-b* (fn-clock-observation 5037000 843004837000 0 t))
(defconst *pbt-no-wall* (fn-clock-observation 5037000 nil 0 t))

(defun pbt-source-with (date msgid body)
  (append (pbt-text "From: poster@example.invalid") '(13 10)
          (pbt-text "Subject: hello") '(13 10)
          (pbt-text "Newsgroups: fn.letters") '(13 10)
          (if date (append (pbt-text "Date: ") date '(13 10)) nil)
          (if msgid (append (pbt-text "Message-ID: ") (pbt-text msgid) '(13 10)) nil)
          '(13 10)
          (pbt-text body) '(13 10)))
(defun pbt-source (date-p msgid-p body)
  (pbt-source-with (if date-p (pbt-text "Thu, 24 Sep 2026 20:00:00 +0000") nil)
                   (if msgid-p "<d25@example.invalid>" nil)
                   body))

(defconst *pbt-source* (pbt-source t t "Hello, news."))
(defconst *pbt-other-source* (pbt-source t t "Hello, news!"))
(defconst *pbt-dateless* (pbt-source nil t "Hello, news."))
(defconst *pbt-idless* (pbt-source t nil "Hello, news."))
(defconst *pbt-redated*
  (pbt-source-with (pbt-text "Thu, 24 Sep 2026 20:00:01 +0000") "<d25@example.invalid>"
                   "Hello, news."))
; The Date fn generates at A, written by the poster: the same octets as the
; generated line, but the poster's.
(defconst *pbt-dated-at-a*
  (pbt-source-with (fn-inj-date-octets (fn-inj-instant-of 843004800000))
                   "<d25@example.invalid>" "Hello, news."))
(defconst *pbt-new-id* (pbt-source-with (pbt-text "Thu, 24 Sep 2026 20:00:00 +0000")
                                        "<d25-second@example.invalid>" "Hello, news."))

(defun pbt-octets (source obs)
  (fn-inj-decision-octets (fn-inj-decide source *pbt-config* obs)))

(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-source* *pbt-config* *pbt-a*)))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-dateless* *pbt-config* *pbt-b*)))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-dated-at-a* *pbt-config* *pbt-b*)))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-new-id* *pbt-config* *pbt-b*)))


(defconst *pbt-msgid-octets* (pbt-text "<d25@example.invalid>"))

; RFC 5537 section 3.5 item 11: Date and Message-ID supplied, so no
; Injection-Date, and the two injections are byte-identical; without the
; Date, the Injection-Date and the generated Date move with the clock.
(assert-event (equal (pbt-octets *pbt-source* *pbt-a*) (pbt-octets *pbt-source* *pbt-b*)))
(assert-event (not (equal (pbt-octets *pbt-dateless* *pbt-a*)
                          (pbt-octets *pbt-dateless* *pbt-b*))))

; The subject of a comparison: the source, both clocks.
(assert-event (equal (fn-pb-subject (pbt-octets *pbt-dateless* *pbt-a*) *pbt-agent*
                                    *pbt-msgid-octets*)
                     (cons :source *pbt-dateless*)))
(assert-event (equal (fn-pb-subject (pbt-octets *pbt-dateless* *pbt-b*) *pbt-agent*
                                    *pbt-msgid-octets*)
                     (cons :source *pbt-dateless*)))
(assert-event (equal (fn-pb-path-agent (pbt-octets *pbt-dateless* *pbt-b*) *pbt-msgid-octets*)
                     *pbt-agent*))

; Keystone fn-pb-one-source-at-two-clocks-is-one-article, both Date cases.
(assert-event (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-dateless* *pbt-b*)
                                   (pbt-octets *pbt-dateless* *pbt-a*)))
(assert-event (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-source* *pbt-b*)
                                   (pbt-octets *pbt-source* *pbt-a*)))
; Teeth: a refused decision on either side; a generated Message-ID, which
; is a different Message-ID at B.
(assert-event (not (fn-inj-injectedp (fn-inj-decide *pbt-dateless* *pbt-config* *pbt-no-wall*))))
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets*
                                        (pbt-octets *pbt-dateless* *pbt-no-wall*)
                                        (pbt-octets *pbt-dateless* *pbt-a*))))
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets*
                                        (pbt-octets *pbt-dateless* *pbt-b*)
                                        (pbt-octets *pbt-dateless* *pbt-no-wall*))))
(defconst *pbt-idless-msgid-a*
  (fn-inj-decision-msgid (fn-inj-decide *pbt-idless* *pbt-config* *pbt-a*)))
(assert-event (not (equal *pbt-idless-msgid-a*
                          (fn-inj-decision-msgid (fn-inj-decide *pbt-idless* *pbt-config* *pbt-b*)))))
(assert-event (not (fn-pb-same-articlep *pbt-idless-msgid-a*
                                        (pbt-octets *pbt-idless* *pbt-b*)
                                        (pbt-octets *pbt-idless* *pbt-a*))))
(must-fail
 (defthm pbt-one-article-without-msgid-agreement
   (implies (and (fn-inj-injectedp (fn-inj-decide source config a))
                 (fn-inj-injectedp (fn-inj-decide source config b))
                 (equal (fn-inj-decision-msgid (fn-inj-decide source config a)) msgid))
            (fn-pb-same-articlep
             msgid
             (fn-inj-decision-octets (fn-inj-decide source config b))
             (fn-inj-decision-octets (fn-inj-decide source config a))))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-pb-same-articlep)))))

; Keystone fn-pb-two-sources-are-two-articles: one changed authored byte,
; a changed authored Date, the authored Date removed, and the poster's Date
; equal to the one fn would generate -- each a different source.
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-other-source* *pbt-b*)
                                        (pbt-octets *pbt-source* *pbt-a*))))
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-redated* *pbt-b*)
                                        (pbt-octets *pbt-source* *pbt-a*))))
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-dateless* *pbt-b*)
                                        (pbt-octets *pbt-source* *pbt-a*))))
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-dated-at-a* *pbt-b*)
                                        (pbt-octets *pbt-dateless* *pbt-a*))))
; The last pair shares a Date line octet for octet: the held article's
; generated Date is the resend's authored one.
(assert-event (fn-inj-infixp (fn-inj-date-line (fn-inj-date-octets (fn-inj-instant-of 843004800000)))
                             (pbt-octets *pbt-dateless* *pbt-a*)))
(assert-event (fn-inj-infixp (fn-inj-date-line (fn-inj-date-octets (fn-inj-instant-of 843004800000)))
                             *pbt-dated-at-a*))
; Tooth for the one distinguishing hypothesis: equal sources are one article.
(must-fail
 (defthm pbt-two-articles-without-distinct-sources
   (implies (and (fn-inj-injectedp (fn-inj-decide source1 config a))
                 (fn-inj-injectedp (fn-inj-decide source2 config b))
                 (equal (fn-inj-decision-msgid (fn-inj-decide source1 config a)) msgid)
                 (equal (fn-inj-decision-msgid (fn-inj-decide source2 config b)) msgid))
            (not (fn-pb-same-articlep
                  msgid
                  (fn-inj-decision-octets (fn-inj-decide source2 config b))
                  (fn-inj-decision-octets (fn-inj-decide source1 config a)))))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-pb-same-articlep)))))

; Another injecting identity: never widened, the octets are compared.
(defconst *pbt-other-agent-held*
  (fn-inj-decision-octets (fn-inj-decide *pbt-source* *pbt-other-config* *pbt-a*)))
(assert-event (equal (fn-pb-subject *pbt-other-agent-held* *pbt-agent* *pbt-msgid-octets*)
                     (cons :octets *pbt-other-agent-held*)))
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-source* *pbt-b*)
                                        *pbt-other-agent-held*)))

; Recipe v1 records.  Keystone fn-pb-a-v1-record-is-read-under-v1: the v1
; injection of the dated source is its resend.  fn-pb-an-ambiguous-v1-record-
; is-compared-exactly: the v1 injection of the Date-less source (a Date line
; of the injection's date where the source begins) is compared as octets,
; so its resend is a conflict -- one of that line's readings is the poster's.
(defconst *pbt-date-a* (fn-inj-date-octets (fn-inj-instant-of 843004800000)))
(defconst *pbt-v1-dated*
  (fn-pb-v1-injection *pbt-date-a* *pbt-msgid-octets* *pbt-agent* nil nil *pbt-source*))
(defconst *pbt-v1-dateless*
  (fn-pb-v1-injection *pbt-date-a* *pbt-msgid-octets* *pbt-agent* nil t *pbt-dateless*))
(assert-event (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-source* *pbt-b*)
                                   *pbt-v1-dated*))
(assert-event (equal (fn-pb-subject *pbt-v1-dateless* *pbt-agent* *pbt-msgid-octets*)
                     (cons :octets *pbt-v1-dateless*)))
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-dateless* *pbt-b*)
                                        *pbt-v1-dateless*)))
; Teeth for the v1 theorem's two source hypotheses: a source opening with
; the injection's Date line, or with this Message-ID's line, is not read.
(defconst *pbt-opens-with-id*
  (append (pbt-text "Message-ID: <d25@example.invalid>") '(13 10)
          (pbt-source t nil "Hello, news.")))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-opens-with-id* *pbt-config* *pbt-b*)))
(assert-event (not (fn-pb-same-articlep
                    *pbt-msgid-octets* (pbt-octets *pbt-opens-with-id* *pbt-b*)
                    (fn-pb-v1-injection *pbt-date-a* *pbt-msgid-octets* *pbt-agent*
                                        nil nil *pbt-opens-with-id*))))
(defconst *pbt-opens-with-date-a*
  (append (pbt-text "Date: ") *pbt-date-a* '(13 10) *pbt-dateless*))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-opens-with-date-a* *pbt-config* *pbt-b*)))
(assert-event (not (fn-pb-same-articlep
                    *pbt-msgid-octets* (pbt-octets *pbt-opens-with-date-a* *pbt-b*)
                    (fn-pb-v1-injection *pbt-date-a* *pbt-msgid-octets* *pbt-agent*
                                        nil nil *pbt-opens-with-date-a*))))

; -----------------------------------------------------------------------------
; The Store, holding the first injection under its Message-ID.

(defconst *pbt-groups* '("fn.letters"))
(defconst *pbt-msgid* "<d25@example.invalid>")
(defconst *pbt-record*
  (fn-record-make 0 0 0 *pbt-msgid* (pbt-octets *pbt-dateless* *pbt-a*) *pbt-groups*
                  "pbt-pin" "pbt-subject" "pbt-release" 2 841000000))
(defconst *pbt-reserved*
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io
              (fn-sn-initial *pbt-groups* 10) :start-frontier nil)
              :frontier-file :ok) :frontier-replace :ok)
              :frontier-directory :ok))
(defconst *pbt-store*
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-prepare *pbt-reserved* *pbt-record*)
                                 :record-file :ok)
                       :record-link :ok)
             :record-directory :ok)))

(assert-event (fn-sn-statep *pbt-store*))
(assert-event (equal (fn-article-payload
                      (fn-find-article *pbt-msgid*
                                       (fn-state-articles
                                        (fn-node-acceptance (fn-sn-node *pbt-store*)))))
                     (pbt-octets *pbt-dateless* *pbt-a*)))


; The held article is the Date-less source injected at A (the v0 matrix's
; shape).  K1 on the byte-identity decision it replaces, and D25 on the new.
(defconst *pbt-resend* (pbt-octets *pbt-dateless* *pbt-b*))
(defconst *pbt-other* (pbt-octets *pbt-other-source* *pbt-b*))
(assert-event (equal (fn-sn-existing-action *pbt-msgid* *pbt-resend* *pbt-groups* *pbt-store*)
                     :conflict))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* *pbt-resend* *pbt-groups* *pbt-store*)
                     :duplicate))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* (pbt-octets *pbt-dateless* *pbt-a*)
                                            *pbt-groups* *pbt-store*)
                     :duplicate))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* *pbt-other* *pbt-groups* *pbt-store*)
                     :conflict))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* (pbt-octets *pbt-dated-at-a* *pbt-b*)
                                            *pbt-groups* *pbt-store*)
                     :conflict))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* *pbt-resend* '("fn.other") *pbt-store*)
                     :conflict))
; A second identical post under a new Message-ID is not answered from the
; Store: the host prepares a new article.
(assert-event (null (fn-pb-existing-action "<d25-second@example.invalid>"
                                           (pbt-octets *pbt-new-id* *pbt-b*)
                                           *pbt-groups* *pbt-store*)))
(must-fail (assert-event (null (fn-pb-existing-action *pbt-msgid* *pbt-resend*
                                                      *pbt-groups* *pbt-store*))))

; -----------------------------------------------------------------------------
; The served reply: an owner whose in-flight submission is connection 0's,
; with completion mark 0 over an empty ledger (nothing consumed), and the
; same owner over a one-record ledger (consumed).

(defconst *pbt-conn*
  (fn-own-conn-make 0 0 0 nil (fn-auth-open-session nil nil nil nil nil nil) nil
                    *pbt-config* *pbt-b*))
(defun pbt-owner (id ledger)
  (fn-own-make nil nil (list *pbt-conn*) 1 4 nil ledger *pbt-b* nil
               *pbt-config* nil
               (fn-own-sub-make id 0 0 (fn-inj-decide *pbt-dateless* *pbt-config* *pbt-b*))
               nil))
(defconst *pbt-owner* (pbt-owner 0 nil))
(defconst *pbt-consumed* (pbt-owner 0 '(committed)))

(defmacro pbt-line (text)
  `(list (fn-nntp-reply-effect (fn-nntp-crlf (fn-nntp-string-octets ,text)))))
(defconst *pbt-duplicate-line*
  (pbt-line "441 posting failed; this article is already stored here"))
(defconst *pbt-conflict-line*
  (pbt-line "441 posting failed; a different article with this Message-ID is stored here"))

(defun pbt-reply (o id payload groups)
  (car (fn-own-outcome o id (fn-pb-existing-action *pbt-msgid* payload groups
                                                   *pbt-store*))))

(assert-event (equal (fn-pb-served-reply *pbt-owner* 0 :duplicate) *pbt-duplicate-line*))
(assert-event (equal (fn-pb-served-reply *pbt-owner* 0 :conflict) *pbt-conflict-line*))
; Keystones fn-pb-a-resend-at-any-clock-is-answered-already-stored and
; fn-pb-a-changed-source-is-answered-conflict on the real owner and Store.
(assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-resend* *pbt-groups*)
                     *pbt-duplicate-line*))
(assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-other* *pbt-groups*)
                     *pbt-conflict-line*))
(assert-event (equal (pbt-reply *pbt-owner* 0 (pbt-octets *pbt-dated-at-a* *pbt-b*) *pbt-groups*)
                     *pbt-conflict-line*))

; Teeth for the duplicate theorems: each hypothesis deleted, with the
; evaluated value that refutes the conclusion.
; No connection with that id: no reply at all.
(must-fail (assert-event (equal (pbt-reply *pbt-owner* 7 *pbt-resend* *pbt-groups*)
                                *pbt-duplicate-line*)))
; Nothing in flight.
(must-fail
 (assert-event
  (equal (car (fn-own-outcome
               (fn-own-make nil nil (list *pbt-conn*) 1 4 nil nil *pbt-b* nil
                            *pbt-config* nil nil nil)
               0 (fn-pb-existing-action *pbt-msgid* *pbt-resend* *pbt-groups*
                                        *pbt-store*)))
         *pbt-duplicate-line*)))
; The in-flight submission is another connection's.
(must-fail (assert-event (equal (car (fn-own-outcome
                                      (pbt-owner 3 nil) 0
                                      (fn-pb-existing-action
                                       *pbt-msgid* *pbt-resend* *pbt-groups* *pbt-store*)))
                                *pbt-duplicate-line*)))
; A completion consumed after the take: the reply is the uncertain line.
(must-fail (assert-event (equal (pbt-reply *pbt-consumed* 0 *pbt-resend* *pbt-groups*)
                                *pbt-duplicate-line*)))
; No held article under that Message-ID.
(must-fail
 (assert-event
  (equal (car (fn-own-outcome *pbt-owner* 0
                              (fn-pb-existing-action "<missing@example.invalid>"
                                                     *pbt-resend* *pbt-groups*
                                                     *pbt-store*)))
         *pbt-duplicate-line*)))
; Another source (the resend's injection held by the other theorem): conflict.
(must-fail (assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-other* *pbt-groups*)
                                *pbt-duplicate-line*)))
; Different groups: the conflict line.
(must-fail (assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-resend* '("fn.other"))
                                *pbt-duplicate-line*)))
; Teeth for the conflict theorems: with the difference deleted the reply is
; the duplicate line; with the consumed completion, the uncertain line.
(must-fail (assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-resend* *pbt-groups*)
                                *pbt-conflict-line*)))
(must-fail (assert-event (equal (pbt-reply *pbt-consumed* 0 *pbt-other* *pbt-groups*)
                                *pbt-conflict-line*)))

; Keystone fn-pb-an-existing-action-writes-nothing: the duplicate outcome
; leaves the Store and the feeds, and writes no record.  Its separating
; witness is the one word fn-pb-existing-action never answers: a durable
; completion, consumed, re-pins and moves the feed.
(assert-event (let ((next (cdr (fn-own-outcome *pbt-owner* 0 :duplicate))))
                (and (equal (fn-own-store next) (fn-own-store *pbt-owner*))
                     (null (fn-own-outcome-records *pbt-owner* 0 :duplicate)))))
(assert-event (equal (fn-own-outcome-completion *pbt-consumed* :durable) :durable))
(assert-event (not (member-equal :durable '(:duplicate :conflict nil))))

; The refinement: a byte-identical resend stays a duplicate, and every
; Message-ID the byte decision answers the source decision answers.
(assert-event (equal (fn-sn-existing-action *pbt-msgid* (pbt-octets *pbt-dateless* *pbt-a*)
                                            *pbt-groups* *pbt-store*)
                     :duplicate))

; -----------------------------------------------------------------------------
; D32: a supplied Path is part of the poster's source.  tin sends
; `Path: not-for-mail' first; the held article is that source, Date-less,
; injected at A (recipe v3: the block without a Path line, then the source
; with "hbox.ember.software!" inserted in its Path).
(defun pbt-with-path (path source)
  (append (pbt-text "Path: ") (pbt-text path) '(13 10) source))
(defconst *pbt-tin* (pbt-with-path "not-for-mail" *pbt-dateless*))
(defconst *pbt-tin-other-path* (pbt-with-path "example.org!hbox" *pbt-dateless*))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-tin* *pbt-config* *pbt-a*)))
(assert-event (fn-inj-supplies-pathp *pbt-tin*))
; The Date is generated, so the two clocks inject different octets.
(assert-event (not (equal (pbt-octets *pbt-tin* *pbt-a*) (pbt-octets *pbt-tin* *pbt-b*))))
; The agent is read from the block (fn-pb-path-agent-of-an-injection, v3 arm).
(assert-event (equal (fn-pb-path-agent (pbt-octets *pbt-tin* *pbt-b*) *pbt-msgid-octets*)
                     *pbt-agent*))
(assert-event (equal (fn-pb-subject (pbt-octets *pbt-tin* *pbt-b*) *pbt-agent*
                                    *pbt-msgid-octets*)
                     (cons :source *pbt-tin*)))
; Keystones fn-pb-one-source-at-two-clocks-is-one-article and
; fn-pb-two-sources-are-two-articles over v3 records.
(assert-event (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-tin* *pbt-b*)
                                   (pbt-octets *pbt-tin* *pbt-a*)))
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets*
                                        (pbt-octets *pbt-tin-other-path* *pbt-b*)
                                        (pbt-octets *pbt-tin* *pbt-a*))))
; A Path added to an otherwise identical source is a different source.
(assert-event (not (fn-pb-same-articlep *pbt-msgid-octets* (pbt-octets *pbt-tin* *pbt-b*)
                                        (pbt-octets *pbt-dateless* *pbt-a*))))

; Through the real Store: the tin article held, then resent.
(defconst *pbt-tin-record*
  (fn-record-make 0 0 0 *pbt-msgid* (pbt-octets *pbt-tin* *pbt-a*) *pbt-groups*
                  "pbt-pin" "pbt-subject" "pbt-release" 2 841000000))
(defconst *pbt-tin-store*
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-prepare *pbt-reserved* *pbt-tin-record*)
                                 :record-file :ok)
                       :record-link :ok)
             :record-directory :ok)))
(assert-event (fn-sn-statep *pbt-tin-store*))
; The byte decision it replaces calls the resend a conflict; D25 over the
; recovered source calls it a duplicate.  A changed supplied Path is the
; conflict line.
(assert-event (equal (fn-sn-existing-action *pbt-msgid* (pbt-octets *pbt-tin* *pbt-b*)
                                            *pbt-groups* *pbt-tin-store*)
                     :conflict))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* (pbt-octets *pbt-tin* *pbt-b*)
                                            *pbt-groups* *pbt-tin-store*)
                     :duplicate))
(assert-event (equal (fn-pb-existing-action *pbt-msgid*
                                            (pbt-octets *pbt-tin-other-path* *pbt-b*)
                                            *pbt-groups* *pbt-tin-store*)
                     :conflict))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* (pbt-octets *pbt-dateless* *pbt-b*)
                                            *pbt-groups* *pbt-tin-store*)
                     :conflict))
