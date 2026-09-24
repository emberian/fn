; Witnesses and teeth for books/poster-bytes-invariants.lisp (D25): the
; duplicate-versus-conflict verdict keys on the poster's bytes.
;
; The subjects are the functions the host calls: fn-pb-existing-action
; (host/owner-host.lisp fn-owner-existing-action and fn-owner-prepare,
; host/store-node-host.lisp) and fn-own-outcome (fn-owner-outcome).  The
; witness is one proto-article injected by the real fn-inj-decide at two
; clock seconds, committed through the real Store at the first; its two
; injected articles differ only in their Injection-Date line.  A second
; witness sends no Date, so the two injections also differ in the Date the
; node generated.
(in-package "ACL2")
(include-book "../../books/poster-bytes-invariants")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun pbt-text (s) (fn-record-string-octets s))

(defconst *pbt-agent* (pbt-text "hbox.ember.software"))
(defconst *pbt-config*
  (fn-inj-make-config t *pbt-agent* (list (pbt-text "fn.letters")) 32768))
; Wall readings are milliseconds since 2000-01-01T00:00:00Z; B is 37 s after A.
(defconst *pbt-a* (fn-clock-observation 5000000 843004800000 0 t))
(defconst *pbt-b* (fn-clock-observation 5037000 843004837000 0 t))
(defconst *pbt-no-wall* (fn-clock-observation 5037000 nil 0 t))

(defun pbt-source (date-p msgid-p body)
  (append (pbt-text "From: poster@example.invalid") '(13 10)
          (pbt-text "Subject: hello") '(13 10)
          (pbt-text "Newsgroups: fn.letters") '(13 10)
          (if date-p
              (append (pbt-text "Date: Thu, 24 Sep 2026 20:00:00 +0000") '(13 10))
            nil)
          (if msgid-p
              (append (pbt-text "Message-ID: <d25@example.invalid>") '(13 10))
            nil)
          '(13 10)
          (pbt-text body) '(13 10)))

(defconst *pbt-source* (pbt-source t t "Hello, news."))
(defconst *pbt-other-source* (pbt-source t t "Hello, other news."))
(defconst *pbt-dateless* (pbt-source nil t "Hello, news."))
(defconst *pbt-idless* (pbt-source t nil "Hello, news."))

(defun pbt-octets (source obs)
  (fn-inj-decision-octets (fn-inj-decide source *pbt-config* obs)))

(defconst *pbt-first* (pbt-octets *pbt-source* *pbt-a*))
(defconst *pbt-resend* (pbt-octets *pbt-source* *pbt-b*))
(defconst *pbt-other* (pbt-octets *pbt-other-source* *pbt-b*))

(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-source* *pbt-config* *pbt-a*)))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-source* *pbt-config* *pbt-b*)))

; Only Injection-Date differs: the two injected articles are unequal, have
; one length, and agree once their Injection-Date lines are replaced by one
; fixed line (the Path line precedes it, Injection-Info follows it).
(defun pbt-swap-injection-date (x)
  (let* ((path (fn-pb-line x))
         (rest (fn-pb-rest x)))
    (append path (pbt-text "Injection-Date: X") '(13 10) (fn-pb-rest rest))))
(assert-event (not (equal *pbt-first* *pbt-resend*)))
(assert-event (equal (len *pbt-first*) (len *pbt-resend*)))
(assert-event (equal (pbt-swap-injection-date *pbt-first*)
                     (pbt-swap-injection-date *pbt-resend*)))
(assert-event (fn-pb-line-injectedp (fn-pb-rest *pbt-first*)))

; The projection: equal across the two seconds, and equal to the source.
(assert-event (equal (fn-pb-poster-bytes *pbt-first*)
                     (fn-pb-poster-bytes *pbt-resend*)))
(assert-event (equal (fn-pb-poster-bytes *pbt-resend*) *pbt-source*))
(assert-event (not (equal (fn-pb-poster-bytes *pbt-other*)
                          (fn-pb-poster-bytes *pbt-first*))))

; -----------------------------------------------------------------------------
; The Store, holding the first injection under its Message-ID.

(defconst *pbt-groups* '("fn.letters"))
(defconst *pbt-msgid* "<d25@example.invalid>")
(defconst *pbt-record*
  (fn-record-make 0 0 0 *pbt-msgid* *pbt-first* *pbt-groups*
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
                     *pbt-first*))

; K1 on the byte-identity decision it replaces, and D25 on the new one.
(assert-event (equal (fn-sn-existing-action *pbt-msgid* *pbt-resend* *pbt-groups* *pbt-store*)
                     :conflict))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* *pbt-resend* *pbt-groups* *pbt-store*)
                     :duplicate))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* *pbt-first* *pbt-groups* *pbt-store*)
                     :duplicate))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* *pbt-other* *pbt-groups* *pbt-store*)
                     :conflict))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* *pbt-resend* '("fn.other") *pbt-store*)
                     :conflict))
(assert-event (null (fn-pb-existing-action "<missing@example.invalid>" *pbt-resend*
                                           *pbt-groups* *pbt-store*)))

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
               (fn-own-sub-make id 0 0 (fn-inj-decide *pbt-source* *pbt-config* *pbt-b*))
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
(assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-resend* *pbt-groups*)
                     *pbt-duplicate-line*))
(assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-other* *pbt-groups*)
                     *pbt-conflict-line*))

; The v0 matrix's case: no Date from the poster, the held article injected
; at A, the resend at B.  The byte decision said conflict; this one says
; already stored.
(defconst *pbt-dateless-store*
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io
     (fn-sn-prepare *pbt-reserved*
                    (fn-record-make 0 0 0 *pbt-msgid* (pbt-octets *pbt-dateless* *pbt-a*)
                                    *pbt-groups* "pbt-pin" "pbt-subject"
                                    "pbt-release" 2 841000000))
     :record-file :ok) :record-link :ok) :record-directory :ok)))
(assert-event (equal (fn-sn-existing-action *pbt-msgid* (pbt-octets *pbt-dateless* *pbt-b*)
                                            *pbt-groups* *pbt-dateless-store*)
                     :conflict))
(assert-event (equal (car (fn-own-outcome
                           *pbt-owner* 0
                           (fn-pb-existing-action *pbt-msgid*
                                                  (pbt-octets *pbt-dateless* *pbt-b*)
                                                  *pbt-groups* *pbt-dateless-store*)))
                     *pbt-duplicate-line*))

; Teeth for fn-pb-same-poster-bytes-is-answered-already-stored and
; fn-pb-a-resend-at-a-later-second-is-answered-already-stored: each
; hypothesis deleted, with the evaluated value that refutes the conclusion.
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
; Different poster's bytes: the conflict line.
(must-fail (assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-other* *pbt-groups*)
                                *pbt-duplicate-line*)))
; Different groups: the conflict line.
(must-fail (assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-resend* '("fn.other"))
                                *pbt-duplicate-line*)))

; Teeth for fn-pb-different-poster-bytes-is-answered-conflict: with the
; bytes-or-groups difference deleted the reply is the duplicate line, and
; with the consumed-completion hypothesis deleted it is the uncertain line.
(must-fail (assert-event (equal (pbt-reply *pbt-owner* 0 *pbt-resend* *pbt-groups*)
                                *pbt-conflict-line*)))
(must-fail (assert-event (equal (pbt-reply *pbt-consumed* 0 *pbt-other* *pbt-groups*)
                                *pbt-conflict-line*)))

; Teeth for fn-pb-a-resent-injection-has-the-same-poster-bytes.
; No Date from the poster: the node generates one from the clock, and the
; projection drops it with the Injection-Date (the v0 matrix posts this way).
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-dateless* *pbt-config* *pbt-a*)))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-dateless* *pbt-config* *pbt-b*)))
(assert-event (not (equal (pbt-octets *pbt-dateless* *pbt-a*)
                          (pbt-octets *pbt-dateless* *pbt-b*))))
(assert-event (equal (fn-pb-poster-bytes (pbt-octets *pbt-dateless* *pbt-a*))
                     (fn-pb-poster-bytes (pbt-octets *pbt-dateless* *pbt-b*))))
(assert-event (equal (fn-pb-poster-bytes (pbt-octets *pbt-dateless* *pbt-b*))
                     *pbt-dateless*))
; A source that opens with a Date equal, octet for octet, to the injection's
; rendering of clock A: at A it reads as the generated Date and is dropped,
; at B it is the poster's and kept, so the key moves.  This is the case
; fn-pb-opens-with-a-date excludes.
(defconst *pbt-opens-with-date*
  (append (pbt-text "Date:") '(32)
          (fn-inj-date-octets (fn-inj-instant-of 843004800000)) '(13 10)
          *pbt-dateless*))
(assert-event (fn-pb-opens-with-a-date *pbt-opens-with-date*))
(assert-event (not (fn-pb-opens-with-a-date *pbt-source*)))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-opens-with-date* *pbt-config* *pbt-a*)))
(assert-event (fn-inj-injectedp (fn-inj-decide *pbt-opens-with-date* *pbt-config* *pbt-b*)))
(must-fail (assert-event (equal (fn-pb-poster-bytes (pbt-octets *pbt-opens-with-date* *pbt-a*))
                                (fn-pb-poster-bytes (pbt-octets *pbt-opens-with-date* *pbt-b*)))))
; A generated Message-ID differs by clock; so do the two keys.
(assert-event (not (equal (fn-inj-decision-msgid (fn-inj-decide *pbt-idless* *pbt-config* *pbt-a*))
                          (fn-inj-decision-msgid (fn-inj-decide *pbt-idless* *pbt-config* *pbt-b*)))))
(must-fail (assert-event (equal (fn-pb-poster-bytes (pbt-octets *pbt-idless* *pbt-a*))
                                (fn-pb-poster-bytes (pbt-octets *pbt-idless* *pbt-b*)))))
; A refused second decision (no wall clock) has no octets.
(assert-event (not (fn-inj-injectedp (fn-inj-decide *pbt-source* *pbt-config* *pbt-no-wall*))))
(must-fail (assert-event (equal (fn-pb-poster-bytes (pbt-octets *pbt-source* *pbt-a*))
                                (fn-pb-poster-bytes (pbt-octets *pbt-source* *pbt-no-wall*)))))
(must-fail (assert-event (equal (fn-pb-poster-bytes (pbt-octets *pbt-source* *pbt-no-wall*))
                                (fn-pb-poster-bytes (pbt-octets *pbt-source* *pbt-b*)))))

; Teeth for fn-pb-poster-bytes-of-an-injection-are-the-sources: a source
; that opens on a continuation line is folded into Injection-Info and
; dropped with it; one that opens with the injection's own Date loses it.
(must-fail
 (assert-event
  (equal (fn-pb-poster-bytes
          (append (fn-inj-prefix (fn-inj-date-octets (fn-inj-instant-of 843004800000))
                                 nil *pbt-agent* nil nil)
                  (cons 32 *pbt-source*)))
         (fn-pb-poster-bytes (cons 32 *pbt-source*)))))
(must-fail
 (assert-event
  (equal (fn-pb-poster-bytes
          (append (fn-inj-prefix (fn-inj-date-octets (fn-inj-instant-of 843004800000))
                                 nil *pbt-agent* nil nil)
                  *pbt-opens-with-date*))
         (fn-pb-poster-bytes *pbt-opens-with-date*))))
; A date carrying a line feed splits the Injection-Date line.
(must-fail
 (assert-event
  (equal (fn-pb-poster-bytes
          (append (fn-inj-prefix (pbt-text "x") nil *pbt-agent* nil nil) *pbt-source*))
         (fn-pb-poster-bytes
          (append (fn-inj-prefix (list 10 13 10 88 58 32) nil *pbt-agent* nil nil)
                  *pbt-source*)))))

; The refinement: a byte-identical resend stays a duplicate, and every
; Message-ID the byte decision answers the poster's-bytes decision answers.
(assert-event (equal (fn-sn-existing-action *pbt-msgid* *pbt-first* *pbt-groups* *pbt-store*)
                     :duplicate))
