; Witnesses and teeth for books/owner-log.lisp, the native owner's service
; log lines.
;
; The subjects are the three renderers host/owner-host.lisp calls:
; fn-olog-served-post-line from fn-owner-outcome, fn-olog-control-post-line
; from fn-owner-control-outcome, fn-olog-connection-line from fn-owner-open
; and fn-owner-open-peer.  host/native/owner.lisp fnn-owner-log writes the
; octets they return and one LF.
;
; The keystones have no hypotheses, so each `must-fail' below names the
; weaker statement a host-word log would satisfy, with the evaluated value
; that refutes it beside it.

(in-package "ACL2")
(include-book "../../books/owner-log")
(include-book "std/testing/must-fail" :dir :system)

(defun olt-text (s) (fn-record-string-octets s))

; One real injected decision and one exact control decision.
(defconst *olt-agent* (olt-text "hbox.ember.software"))
(defconst *olt-config*
  (fn-inj-make-config t *olt-agent* (list (olt-text "fn.letters")) 32768))
; Wall readings are milliseconds since the DTN epoch, 2000-01-01T00:00:00Z.
(defconst *olt-observation* (fn-clock-observation 5000000 843004800000 0 t))
(defconst *olt-source*
  (append (olt-text "From: poster@example.invalid") '(13 10)
          (olt-text "Subject: hello") '(13 10)
          (olt-text "Newsgroups: fn.letters") '(13 10)
          (olt-text "Message-ID: <log@example.invalid>") '(13 10 13 10)
          (olt-text "Hello, news.") '(13 10)))
(defconst *olt-decision* (fn-inj-decide *olt-source* *olt-config* *olt-observation*))
(assert-event (fn-inj-injectedp *olt-decision*))

; A connection 0 pinned to that configuration, and an owner whose in-flight
; submission is connection 0's with completion mark 0 over a one-record
; ledger -- the shape fn-own-outcome-completion calls consumed after the take.
(defconst *olt-conn*
  (fn-own-conn-make 0 0 0 nil nil nil *olt-config* *olt-observation*))
(defun olt-owner (id ledger decision)
  (fn-own-make nil nil (list *olt-conn*) 1 4 nil ledger *olt-observation* nil
               *olt-config* nil (fn-own-sub-make id 0 0 decision) nil))
(defconst *olt-served* (olt-owner 0 '(committed) *olt-decision*))
(defconst *olt-served-unconsumed* (olt-owner 0 nil *olt-decision*))

; -----------------------------------------------------------------------------
; The served line

(defconst *olt-accepted-line* (fn-olog-served-post-line *olt-served* 0 :durable))
(assert-event
 (equal *olt-accepted-line*
        (olt-text "accepted post path=served connection=0 message-id=<log@example.invalid> agent=hbox.ember.software time=2026-09-18T00:00:00Z")))
(assert-event (equal (fn-olog-line-word *olt-accepted-line*) (olt-text "accepted")))

; A host :durable with no completion consumed after the take is uncertain,
; exactly as the reply is (no 240); refused and the host's duplicate are the
; refusal the client was sent.
(assert-event
 (equal (fn-olog-line-word (fn-olog-served-post-line *olt-served-unconsumed* 0 :durable))
        (olt-text "uncertain")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-served-post-line *olt-served-unconsumed* 0 :refused))
        (olt-text "refused")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-served-post-line *olt-served-unconsumed* 0 :duplicate))
        (olt-text "refused")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-served-post-line *olt-served-unconsumed* 0 :conflict))
        (olt-text "refused")))
; After a consumed completion no refusal word is a refusal: the reply is the
; uncertain line (fn-own-consumed-completion-is-240-or-uncertain), and so is
; the log (campaign W2, 2026-09-24).
(assert-event
 (equal (fn-olog-line-word (fn-olog-served-post-line *olt-served* 0 :refused))
        (olt-text "uncertain")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-served-post-line *olt-served* 0 :duplicate))
        (olt-text "uncertain")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-served-post-line *olt-served* 0 :garbage))
        (olt-text "uncertain")))

; The weaker statement a log that echoed the host's word would satisfy is
; false: the unconsumed owner above is its counterexample.
(assert-event
 (not (equal (equal (fn-olog-line-word
                     (fn-olog-served-post-line *olt-served-unconsumed* 0 :durable))
                    (olt-text "accepted"))
             (equal :durable :durable))))
(must-fail
 (defthm olt-served-line-echoes-the-host-word
   (equal (equal (fn-olog-line-word
                  (fn-olog-served-post-line *olt-served-unconsumed* 0 :durable))
                 (fn-olog-text "accepted"))
          (equal :durable :durable))
   :hints (("Goal" :in-theory (e/d (fn-olog-class-word fn-olog-text)
                                   (fn-own-outcome-completion fn-olog-field
                                    fn-olog-decimal fn-olog-time))))))

; -----------------------------------------------------------------------------
; The control line

(defconst *olt-control-decision*
  (fn-own-control-decision *olt-config* (olt-text "<ctl@example.invalid>")
                           (list (olt-text "fn.letters")) *olt-source*))
(defconst *olt-control* (olt-owner :control '(committed) *olt-control-decision*))
(defconst *olt-control-unconsumed* (olt-owner :control nil *olt-control-decision*))
(defconst *olt-control-line* (fn-olog-control-post-line *olt-control* :durable))
(assert-event
 (equal *olt-control-line*
        (olt-text "accepted post path=control message-id=<ctl@example.invalid> time=2026-09-18T00:00:00Z")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-control-post-line *olt-control-unconsumed* :duplicate))
        (olt-text "duplicate")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-control-post-line *olt-control-unconsumed* :refused))
        (olt-text "refused")))
(assert-event
 (equal (fn-own-control-outcome-result *olt-control-unconsumed* :duplicate) :duplicate))
; A duplicate reported after a consumed completion is not a duplicate.
(assert-event
 (equal (fn-own-control-outcome-result *olt-control* :duplicate) :uncertain))
; The control reply's word and the line's are the same word, not the host's:
; the host's :duplicate stays distinct for the control client, while the
; served line above reports it as the refusal the NNTP client was sent.
(must-fail
 (defthm olt-control-line-is-the-served-class
   (equal (fn-olog-line-word (fn-olog-control-post-line *olt-control-unconsumed* :duplicate))
          (fn-olog-class-word (fn-olog-served-class *olt-control-unconsumed* :duplicate)))
   :hints (("Goal" :in-theory (e/d (fn-olog-class-word fn-olog-text)
                                   (fn-own-control-outcome-result fn-olog-field
                                    fn-olog-decimal fn-olog-time))))))
(assert-event
 (not (equal (fn-olog-line-word (fn-olog-control-post-line *olt-control-unconsumed* :duplicate))
             (fn-olog-class-word (fn-olog-served-class *olt-control-unconsumed* :duplicate)))))

; -----------------------------------------------------------------------------
; The connection lines

(assert-event
 (equal (fn-olog-connection-line *olt-served* 2 nil)
        (olt-text "accepted reader connection=2 time=2026-09-18T00:00:00Z")))
(assert-event
 (equal (fn-olog-connection-line *olt-served* 3 (olt-text "innA"))
        (olt-text "accepted peer connection=3 peer=innA time=2026-09-18T00:00:00Z")))
(assert-event
 (equal (fn-olog-connection-line (olt-owner 0 nil *olt-decision*) 0 nil)
        (olt-text "accepted reader connection=0 time=2026-09-18T00:00:00Z")))

; -----------------------------------------------------------------------------
; One line whatever a client sent: a Message-ID or peer name carrying CR LF
; renders them as `?', and the line stays one line.

(defconst *olt-hostile* (append (olt-text "<a") '(13 10) (olt-text "b@x>")))
(defconst *olt-hostile-line*
  (fn-olog-connection-line *olt-served* 4 *olt-hostile*))
(assert-event (fn-olog-no-breakp *olt-hostile-line*))
(assert-event
 (equal *olt-hostile-line*
        (olt-text "accepted peer connection=4 peer=<a??b@x> time=2026-09-18T00:00:00Z")))
(assert-event (not (fn-olog-no-breakp *olt-hostile*)))
; A field is bounded: 300 octets of value keep 256.
(assert-event
 (equal (len (fn-olog-visible (make-list 300 :initial-element 65))) 256))
; Unsanitized, the same field would have broken the line.
(assert-event
 (not (fn-olog-no-breakp (append (olt-text "peer=") *olt-hostile*))))

; -----------------------------------------------------------------------------
; Peer transfer lines (hybrid-feed-storm, 2026-09-24).  Subjects:
; fn-olog-transit-line, installed by host/owner-host.lisp
; fn-owner-transit-log-line and written by host/native/owner.lisp
; fnn-owner-drain-one; fn-olog-feed-reply-line, installed by
; fn-owner-feed-octets and written by host/native/feed-service.lisp
; fnn-feed-reply-step.

(defconst *olt-transit-msgid* (olt-text "<relay@example.invalid>"))
(defconst *olt-transit-decision*
  (fn-peer-make-submission "other" :takethis *olt-transit-msgid* *olt-source*))
(assert-event (fn-peer-submissionp *olt-transit-decision*))
(defconst *olt-transit* (olt-owner 0 '(committed) *olt-transit-decision*))
(defconst *olt-transit-unconsumed* (olt-owner 0 nil *olt-transit-decision*))

; The failure-8 line: the receiver's ingress refused a signed carrier for want
; of its own enrollment, and the peer was sent 439.  The ingress refused
; before the Store, so no completion was consumed: the owner is the
; unconsumed one.  Over a consumed completion fn-own-outcome-completion reads
; a refusal word as uncertain and the line says `uncertain ... code=436',
; which is what this witness evaluated to over *olt-transit*.
(defconst *olt-refused-transit-line*
  (fn-olog-transit-line *olt-transit-unconsumed* 7 :want nil :refused
                        :local-enrollment))
(assert-event
 (equal (fn-olog-line-word
         (fn-olog-transit-line *olt-transit* 7 :want nil :refused
                               :local-enrollment))
        (olt-text "uncertain")))
(assert-event
 (equal *olt-refused-transit-line*
        (olt-text "refused transit connection=7 message-id=<relay@example.invalid> code=439 decision=want reason=none detail=local-enrollment time=2026-09-18T00:00:00Z")))
(assert-event
 (equal (fn-olog-line-word
         (fn-olog-transit-line *olt-transit* 7 :want nil :durable nil))
        (olt-text "accepted")))
; Uncertain stays uncertain (436 and a close), not a deferral, not refused.
(assert-event
 (equal (fn-olog-line-word
         (fn-olog-transit-line *olt-transit* 7 :want nil :uncertain nil))
        (olt-text "uncertain")))
; A durable host word with nothing consumed after the take is uncertain too.
(assert-event
 (equal (fn-olog-line-word
         (fn-olog-transit-line *olt-transit-unconsumed* 7 :want nil :durable nil))
        (olt-text "uncertain")))
; Decisions that never reached the Store: a deferral and a history refusal.
(assert-event
 (equal (fn-olog-line-word
         (fn-olog-transit-line *olt-transit* 7 :defer :busy :refused nil))
        (olt-text "deferred")))
(assert-event
 (equal (fn-olog-transit-line *olt-transit* 7 :reject :loop :refused nil)
        (olt-text "refused transit connection=7 message-id=<relay@example.invalid> code=439 decision=reject reason=loop detail=none time=2026-09-18T00:00:00Z")))
(assert-event (fn-olog-no-breakp *olt-refused-transit-line*))

; Teeth for the receiver keystone.  Its clause "not uncertain" is not
; redundant with the code: an uncertain completion is sent 436, never a
; rejection -- so the weaker claim "refused iff the host word is :refused"
; is what fails, witnessed by a :defer decision whose host word is
; :refused but whose line says deferred.
(assert-event
 (not (equal (fn-olog-line-word
              (fn-olog-transit-line *olt-transit* 7 :defer :busy :refused nil))
             (olt-text "refused"))))
(must-fail
 (defthm olt-transit-line-echoes-the-host-word
   (equal (equal (fn-olog-line-word
                  (fn-olog-transit-line o id kind reason word detail))
                 (fn-olog-text "refused"))
          (equal word :refused))
   :hints (("Goal" :in-theory (e/d (fn-olog-transit-class-word
                                    fn-olog-code-class-word fn-olog-text)
                                   (fn-olog-transit-code fn-olog-transit-completion
                                    fn-olog-field fn-olog-decimal fn-olog-time
                                    fn-olog-symbol-text))))))
; And without the completion clause: code 436 from an uncertain completion
; is not a rejection, so dropping the code test would call it refused.
(must-fail
 (defthm olt-transit-line-refused-unless-accepted
   (equal (equal (fn-olog-line-word
                  (fn-olog-transit-line o id kind reason word detail))
                 (fn-olog-text "refused"))
          (not (equal (fn-olog-transit-completion o kind word) :durable)))
   :hints (("Goal" :in-theory (e/d (fn-olog-transit-class-word
                                    fn-olog-code-class-word fn-olog-text)
                                   (fn-olog-transit-code fn-olog-transit-completion
                                    fn-olog-field fn-olog-decimal fn-olog-time
                                    fn-olog-symbol-text))))))

; The sender's lines.  A send-it prompt has no line; every outcome has one.
; The feed's Message-ID is the octets fn-feed-namep admits (the first
; developer image of this line printed `message-id=` empty when it was
; read as a string).
(assert-event (fn-feed-namep *olt-transit-msgid*))
(defconst *olt-feed-439*
  (fn-olog-feed-reply-line *olt-served* "other"
                           (fn-feed-response 439 *olt-transit-msgid*)))
(assert-event
 (equal *olt-feed-439*
        (olt-text "refused feed peer=other message-id=<relay@example.invalid> code=439 time=2026-09-18T00:00:00Z")))
(assert-event
 (null (fn-olog-feed-reply-line *olt-served* "other"
                                (fn-feed-response 238 *olt-transit-msgid*))))
(assert-event
 (equal (fn-olog-line-word
         (fn-olog-feed-reply-line *olt-served* "other"
                                  (fn-feed-response 431 *olt-transit-msgid*)))
        (olt-text "deferred")))
(assert-event
 (equal (fn-olog-line-word
         (fn-olog-feed-reply-line *olt-served* "other"
                                  (fn-feed-response 438 *olt-transit-msgid*)))
        (olt-text "duplicate")))
(assert-event
 (equal (fn-olog-line-word
         (fn-olog-feed-reply-line *olt-served* "other"
                                  (fn-feed-response 239 *olt-transit-msgid*)))
        (olt-text "accepted")))
; Teeth: the send-it clause is load-bearing (a 238 has no class line).
(must-fail
 (defthm olt-feed-line-always-classed
   (equal (fn-olog-line-word (fn-olog-feed-reply-line o peer response))
          (fn-olog-code-class-word (fn-feed-response-code response)))
   :hints (("Goal" :in-theory (e/d (fn-olog-code-class-word fn-olog-text)
                                   (fn-olog-field fn-olog-decimal fn-olog-time))))))

; The store's swallowed staging cleanup (host/native/io.lisp fnn-publish,
; fnn-log-staging-cleanup).  The witness is the line the probe's
; `record-stage-unlinked' EIO row reads: the unlink returned, the injected
; EIO came before the staging barrier, and the condition's report is
; SBCL's text for fnn-os-error.
(defconst *olt-stage-name*
  (olt-text "/w/store/staging/.stage-4242-0123456789ab"))
(defconst *olt-cleanup-line*
  (fn-olog-staging-cleanup-line :directory-barrier *olt-stage-name* 2 5
                                (olt-text "[Errno 5] Input/output error")))
(assert-event
 (equal *olt-cleanup-line*
        (olt-text "failed staging cleanup step=directory-barrier sequence=2 name=/w/store/staging/.stage-4242-0123456789ab errno=5 error=[Errno?5]?Input/output?error")))
; A condition with no errno reads `none', never errno=0.
(assert-event
 (equal (fn-olog-staging-cleanup-line :unlink *olt-stage-name* 3 nil
                                      (olt-text "fault"))
        (olt-text "failed staging cleanup step=unlink sequence=3 name=/w/store/staging/.stage-4242-0123456789ab errno=none error=fault")))
; The error text is the host's and may hold a line break; the line does not.
(defconst *olt-broken-text*
  (append (olt-text "[Errno 5]") '(13 10) (olt-text "accepted post")))
(assert-event
 (fn-olog-no-breakp
  (fn-olog-staging-cleanup-line :unlink *olt-stage-name* 3 5 *olt-broken-text*)))
; Teeth: the visible filter is what makes the line one line.  The field
; built from the raw text, as a host `format' would build it, has a break.
(assert-event (not (fn-olog-no-breakp *olt-broken-text*)))
(must-fail
 (defthm olt-cleanup-raw-error-field-is-one-line
   (fn-olog-no-breakp (append (fn-olog-text "error=") text))))
