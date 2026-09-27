; Teeth for the owner's connection form (PRF-207, books/owner.lisp):
; fn-own-feed-connect-in-ihave-form-offers-ihave,
; fn-own-feed-connect-in-ihave-form-sends-the-bare-article and
; fn-own-feed-connect-in-stream-form-offers-check.  Every witness runs the
; :feed-conn arm of `fn-own-step' (what the host's `fn-owner-feed-connect'
; runs) and then the feed machine the host's tick and reply entries run.
(in-package "ACL2")
(include-book "../../books/owner")
(include-book "std/testing/must-fail" :dir :system)

(defun off-o (s) (fn-record-string-octets s))
(defun off-line (s) (append (fn-record-string-octets s) '(13 10)))

; nodeB streams (outbound streaming t); nodeE does not (nil).
(defconst *off-b*
  (fn-cfg-peer-make "nodeB" "b.fn.test" '(:nntp "127.0.0.1" 1120)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.2")))
(defconst *off-e*
  (fn-cfg-peer-make "nodeE" "e.fn.test" '(:nntp "127.0.0.1" 1123)
                    '("fn.*" 32768 16) '("fn.*" nil 256 1000)
                    '(:source-address "127.0.0.5")))
(defconst *off-cfg*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-policy "path-identity" "a.fn.test")
                                         (fn-cfg-set-peer-delta *off-b*)
                                         (fn-cfg-set-peer-delta *off-e*)))
                           *fn-cfg-default-stamp*))))
(assert-event (fn-cfgp *off-cfg*))
(defconst *off-article*
  (append (off-line "Path: a.fn.test!not-for-mail")
          (off-line "From: writer@a.fn.test")
          (off-line "Newsgroups: fn.test")
          (off-line "Subject: one")
          (off-line "Message-ID: <1@a.fn.test>")
          (off-line "Date: Sat, 20 Sep 2026 12:00:00 -0000")
          '(13 10)
          (off-line "one body")))
(defconst *off-msgid* (off-o "<1@a.fn.test>"))
(defconst *off-tbl*
  (fn-own-feed-accept (fn-own-feed-reconfigure nil (fn-cfg-peers (fn-cfg-value *off-cfg*)))
                      nil *off-msgid* *off-article* 7))
(assert-event (fn-own-feed-tablep *off-tbl*))
(assert-event (equal (len (fn-feed-queue (fn-own-feed-find "nodeB" *off-tbl*))) 1))
(assert-event (equal (len (fn-feed-queue (fn-own-feed-find "nodeE" *off-tbl*))) 1))
; An owner whose only relevant slot is the feed table.
(defconst *off-o* (fn-own-make nil nil nil 0 0 nil nil nil nil nil nil nil *off-tbl* nil nil))

(defun off-feed (o peer)
  (fn-own-feed-entry-feed (fn-own-feed-entry-of peer (fn-own-feeds o))))
(defun off-offer (o peer msgid)
  (mv-let (f effects) (fn-feed-offer (off-feed o peer) msgid)
    (declare (ignore f))
    effects))
(defun off-send (o peer msgid article)
  (mv-let (f effects) (fn-feed-offer (off-feed o peer) msgid)
    (declare (ignore effects))
    (mv-let (g sent) (fn-feed-send f msgid article)
      (declare (ignore g))
      sent)))
(defun off-send-unoffered (o peer msgid article)
  (mv-let (g sent) (fn-feed-send (off-feed o peer) msgid article)
    (declare (ignore g))
    sent))
(defun off-connect (o peer conn form)
  (fn-own-feed-connect o peer conn form))

; The arm the host runs (`fn-owner-feed-connect' steps the owner with
; (:feed-conn peer conn form)) is the function the theorems are about.
(defthm off-feed-conn-arm-is-feed-connect
  (equal (fn-own-step o (list :feed-conn peer conn form))
         (fn-own-feed-connect o peer conn form))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-step) (fn-own-feed-connect)))))

; KEYSTONE fn-own-feed-connect-in-ihave-form-offers-ihave: a streaming peer
; connected in the :ihave form is offered IHAVE; the antecedent (an offer
; was made) and the conclusion hold.
(defconst *off-b-ih* (off-connect *off-o* "nodeB" 3 :ihave))
(assert-event (off-offer *off-b-ih* "nodeB" *off-msgid*))
(assert-event (equal (off-offer *off-b-ih* "nodeB" *off-msgid*)
                     (list (list :command 3 (fn-feed-ihave-line *off-msgid*)))))
(assert-event (equal (fn-feed-ihave-line *off-msgid*) (off-line "IHAVE <1@a.fn.test>")))
; Non-degenerate: the same peer on a streaming connection is offered CHECK.
(defconst *off-b-st* (off-connect *off-o* "nodeB" 3 nil))
(assert-event (equal (off-offer *off-b-st* "nodeB" *off-msgid*)
                     (list (list :command 3 (fn-feed-check-line *off-msgid*)))))
; The bit is per connect: a streaming connect after an IHAVE one streams.
(assert-event (equal (off-offer (off-connect *off-b-ih* "nodeB" 4 nil) "nodeB" *off-msgid*)
                     (list (list :command 4 (fn-feed-check-line *off-msgid*)))))
; Tooth for the one hypothesis (an offer was made): a Message-ID that is not
; queued makes no offer, and nil is not the IHAVE command.
(assert-event (and (null (off-offer *off-b-ih* "nodeB" (off-o "<none@a.fn.test>")))
                   (not (equal (off-offer *off-b-ih* "nodeB" (off-o "<none@a.fn.test>"))
                               (list (list :command 3 (fn-feed-ihave-line (off-o "<none@a.fn.test>"))))))))
(must-fail
 (defthm off-ihave-form-without-an-offer
   (let* ((f (fn-own-feed-entry-feed
              (fn-own-feed-entry-of peer (fn-own-feeds (fn-own-feed-connect o peer conn :ihave)))))
          (effects (mv-nth 1 (fn-feed-offer f msgid))))
     (equal effects (list (list :command conn (fn-feed-ihave-line msgid)))))
   :hints (("Goal" :in-theory (disable fn-own-feed-connect fn-feed-offer)))))

; KEYSTONE fn-own-feed-connect-in-ihave-form-sends-the-bare-article: after
; the 335 the article goes alone, not after a TAKETHIS line.
(assert-event (off-send *off-b-ih* "nodeB" *off-msgid* *off-article*))
(assert-event (equal (off-send *off-b-ih* "nodeB" *off-msgid* *off-article*)
                     (list (list :command 3 *off-article*))))
(assert-event (equal (off-send *off-b-st* "nodeB" *off-msgid* *off-article*)
                     (list (list :command 3 (append (fn-feed-takethis-line *off-msgid*)
                                                   *off-article*)))))
; Tooth: nothing offered, nothing sent.
(assert-event (null (off-send-unoffered *off-b-ih* "nodeB" *off-msgid* *off-article*)))
(must-fail
 (defthm off-bare-article-without-a-send
   (let* ((f (fn-own-feed-entry-feed
              (fn-own-feed-entry-of peer (fn-own-feeds (fn-own-feed-connect o peer conn :ihave)))))
          (effects (mv-nth 1 (fn-feed-send f msgid article))))
     (equal effects (list (list :command conn article))))
   :hints (("Goal" :in-theory (disable fn-own-feed-connect fn-feed-send)))))

; KEYSTONE fn-own-feed-connect-in-stream-form-offers-check: its hypotheses
; are the offer and the record's streaming bit.  Positive: nodeB above.
(assert-event (fn-cfg-peer-streamingp (fn-own-feed-entry-record
                                       (fn-own-feed-entry-of "nodeB" (fn-own-feeds *off-o*)))))
; Tooth for the streaming bit: nodeE's record does not stream, so even the
; streaming form offers IHAVE; the offer is made and the conclusion fails.
(defconst *off-e-st* (off-connect *off-o* "nodeE" 5 nil))
(assert-event (and (off-offer *off-e-st* "nodeE" *off-msgid*)
                   (not (fn-cfg-peer-streamingp
                         (fn-own-feed-entry-record
                          (fn-own-feed-entry-of "nodeE" (fn-own-feeds *off-o*)))))
                   (equal (off-offer *off-e-st* "nodeE" *off-msgid*)
                          (list (list :command 5 (fn-feed-ihave-line *off-msgid*))))
                   (not (equal (off-offer *off-e-st* "nodeE" *off-msgid*)
                               (list (list :command 5 (fn-feed-check-line *off-msgid*)))))))
(must-fail
 (defthm off-stream-form-without-a-streaming-record
   (let* ((f (fn-own-feed-entry-feed
              (fn-own-feed-entry-of peer (fn-own-feeds (fn-own-feed-connect o peer conn nil)))))
          (effects (mv-nth 1 (fn-feed-offer f msgid))))
     (implies effects
              (equal effects (list (list :command conn (fn-feed-check-line msgid))))))
   :hints (("Goal" :in-theory (disable fn-own-feed-connect fn-feed-offer)))))
; Tooth for the offer hypothesis: no offer, nil is not the CHECK command.
(assert-event (null (off-offer *off-b-st* "nodeB" (off-o "<none@a.fn.test>"))))
(must-fail
 (defthm off-stream-form-without-an-offer
   (let* ((e (fn-own-feed-entry-of peer (fn-own-feeds o)))
          (f (fn-own-feed-entry-feed
              (fn-own-feed-entry-of peer (fn-own-feeds (fn-own-feed-connect o peer conn nil)))))
          (effects (mv-nth 1 (fn-feed-offer f msgid))))
     (implies (fn-cfg-peer-streamingp (fn-own-feed-entry-record e))
              (equal effects (list (list :command conn (fn-feed-check-line msgid))))))
   :hints (("Goal" :in-theory (disable fn-own-feed-connect fn-feed-offer)))))
