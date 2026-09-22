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
 (equal (fn-olog-line-word (fn-olog-served-post-line *olt-served* 0 :refused))
        (olt-text "refused")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-served-post-line *olt-served* 0 :duplicate))
        (olt-text "refused")))
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
(defconst *olt-control-line* (fn-olog-control-post-line *olt-control* :durable))
(assert-event
 (equal *olt-control-line*
        (olt-text "accepted post path=control message-id=<ctl@example.invalid> time=2026-09-18T00:00:00Z")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-control-post-line *olt-control* :duplicate))
        (olt-text "duplicate")))
(assert-event
 (equal (fn-olog-line-word (fn-olog-control-post-line *olt-control* :refused))
        (olt-text "refused")))
(assert-event
 (equal (fn-own-control-outcome-result *olt-control* :duplicate) :duplicate))
; The control reply's word and the line's are the same word, not the host's:
; the host's :duplicate stays distinct for the control client, while the
; served line above reports it as the refusal the NNTP client was sent.
(must-fail
 (defthm olt-control-line-is-the-served-class
   (equal (fn-olog-line-word (fn-olog-control-post-line *olt-control* :duplicate))
          (fn-olog-class-word (fn-olog-served-class *olt-control* :duplicate)))
   :hints (("Goal" :in-theory (e/d (fn-olog-class-word fn-olog-text)
                                   (fn-own-control-outcome-result fn-olog-field
                                    fn-olog-decimal fn-olog-time))))))
(assert-event
 (not (equal (fn-olog-line-word (fn-olog-control-post-line *olt-control* :duplicate))
             (fn-olog-class-word (fn-olog-served-class *olt-control* :duplicate)))))

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
