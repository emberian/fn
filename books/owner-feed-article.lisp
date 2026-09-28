; fn: the outbound feed's article bytes over the payload arena, and the
; publication that never authorizes an empty command (lane feed-fault,
; 2026-09-27).
;
; The records flip (c5808cd72, records-flip; D33, PKT-635) made the retained
; article's payload position a HANDLE into the arena.  The feed's reply
; entry (host/owner-host.lisp `fn-owner-feed-octets') kept handing
; `fn-apr-feed-article' -- the row's payload position, now a natural -- to
; the feed port as the article, so after a 335 (IHAVE) or 238 (CHECK) the
; command `fn-feed-send' rendered was that natural, the renderer refused it
; (the publication's STATUS named the reason), and the host, which read only
; the empty command, stopped the owner: "feed connection/reply authorized an
; empty command" (tests.test_native_peering, 12 of 14 red on dev).
;
; Two functions, both called by the host:
;
;   fn-ofa-feed-article   the article's bytes: the row's handle read through
;                         the arena (books/store-intern.lisp fn-handle-bytes),
;                         never the handle itself.  KEYSTONE
;                         fn-ofa-feed-article-is-the-feed-article-over-alpha:
;                         at rest it is the payload the octet-list model's
;                         feed article has (store-intern's ALPHA of the
;                         acceptance articles), the bytes the pre-flip feed
;                         sent.
;   fn-ofa-publication    the reply/tick publication with its command word
;                         (:send, :offer) kept ONLY when the command has
;                         octets; otherwise the word is :unsendable, the
;                         step's records stay (the core already moved; the
;                         host flushes them and drops the connection, which
;                         fn-feed-lost requeues), and the log line names
;                         ACL2's reason.  KEYSTONE
;                         fn-ofa-publication-command-words-have-octets.
;
; The arena is only READ here (flip-L6-2's rule: an ACL2 entry the host calls
; with the arena reads it; the host seals and interns).
(in-package "ACL2")
(include-book "acceptance-payload-ref")
(include-book "store-intern")
(include-book "owner-results")

; -----------------------------------------------------------------------------
; The bytes.

(defun fn-ofa-feed-article (o msgid fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (fn-handle-bytes (fn-apr-feed-article o msgid fn-hist) fn-arena))

(local
 (defthm fn-ofa-find-article-of-articles-wire-of
   (implies (stringp msgid)
            (equal (fn-find-article msgid (fn-articles-wire-of articles fn-arena))
                   (let ((a (fn-find-article msgid articles)))
                     (and a
                          (fn-make-article (fn-article-msgid a)
                                           (fn-handle-bytes (fn-article-payload a) fn-arena)
                                           (fn-article-groups a) (fn-article-memberships a)
                                           (fn-article-pin a) (fn-article-stamp a))))))
   :hints (("Goal" :in-theory (e/d (fn-find-article fn-articles-wire-of)
                                   (fn-handle-bytes))))))

(local
 (defthm fn-ofa-article-payload-of-atom
   (implies (not (consp a)) (equal (fn-article-payload a) nil))
   :hints (("Goal" :in-theory (enable fn-article-payload)))))

(local
 (defthm fn-ofa-handle-bytes-of-nil
   (equal (fn-handle-bytes nil fn-arena) nil)
   :hints (("Goal" :in-theory (enable fn-handle-bytes)))))

; The octet-list model's feed article: `fn-own-feed-article' (books/owner.lisp)
; over ALPHA of the acceptance articles, the bytes it read before the flip.
(fn-payload-kind fn-ofa-wire-feed-article :wire "over fn-articles-wire-of: the octet model's articles")
(defun-nx fn-ofa-wire-feed-article (o msgid fn-arena)
  (let ((a (fn-find-article
            (fn-record-octets-string msgid)
            (fn-articles-wire-of
             (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o))))
             fn-arena))))
    (if (consp a) (fn-article-payload a) nil)))

; KEYSTONE.  Subject: fn-ofa-feed-article, which host/owner-host.lisp
; `fn-owner-feed-octets' passes to the feed port as the article of a 335/238
; (host/native/feed-service.lisp fnn-feed-reply-step).  At rest (the Store's
; relation; books/acceptance-payload-ref.lisp) it is the octet-list model's
; article bytes over the live arena.
(defthm fn-ofa-feed-article-is-the-feed-article-over-alpha
  (implies (and (fn-apr-store-at-restp (fn-own-store o))
                (fn-hist-of-storep fn-hist (fn-own-store o)))
           (equal (fn-ofa-feed-article o msgid fn-arena fn-hist)
                  (fn-ofa-wire-feed-article o msgid fn-arena)))
  :hints (("Goal" :use ((:instance fn-apr-feed-article-is-own-feed-article))
           :in-theory (e/d (fn-own-feed-article)
                           (fn-apr-feed-article-is-own-feed-article
                            fn-apr-feed-article fn-handle-bytes
                            fn-apr-store-at-restp)))))

;  KEYSTONE (PKT-EG-2b).  The book owner's feed step (books/owner.lisp
; fn-own-feed-reply, which fn-own-step runs on a :feed-octets event) hands
; the feed the bytes at fn-own-feed-article's handle; at rest those are the
; bytes the host entry sends (fn-ofa-feed-article, host/owner-host.lisp
; fn-owner-feed-octets).  Before the fix the model handed the handle itself.
(defthm fn-ofa-feed-article-is-the-owner-step-article
  (implies (and (fn-apr-store-at-restp (fn-own-store o))
                (fn-hist-of-storep fn-hist (fn-own-store o)))
           (equal (fn-ofa-feed-article o msgid fn-arena fn-hist)
                  (fn-handle-bytes (fn-own-feed-article o msgid) fn-arena)))
  :hints (("Goal" :use ((:instance fn-apr-feed-article-is-own-feed-article))
           :in-theory '(fn-ofa-feed-article))))

; The bytes are the payload sealed at the handle: never the handle, and an
; octet list whenever the arena is one (fn-arena-p).
(defthm fn-ofa-feed-article-is-an-octet-list
  (implies (fn-arena-p fn-arena)
           (fn-cbor-octet-listp (fn-ofa-feed-article o msgid fn-arena fn-hist)))
  :hints (("Goal" :in-theory (e/d (fn-arena-p-is-payload-listp fn-arena-count-is-len
                                   fn-arena-payload-is-nth)
                                  (fn-apr-feed-article)))))

; -----------------------------------------------------------------------------
; The publication.

(defconst *fn-ofa-command-words* '(:send :offer))

(local
 (defthm fn-ofa-frame-item-is-nth
   (implies (natp n)
            (equal (fn-frame-item n xs) (nth n xs)))
   :hints (("Goal" :in-theory (enable fn-frame-item nth)))))

(defun fn-ofa-reason (status)
  (declare (xargs :guard t))
  (if (and (symbolp status) (not (equal status :ok)))
      status
    :no-article))

(defun fn-ofa-unsendable-line (peer reason)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "feed peer=")
          (if (stringp peer) (fn-record-string-octets peer) nil)
          (fn-record-string-octets " unsendable reason=")
          (fn-record-string-octets (symbol-name (fn-ofa-reason reason)))
          (fn-record-string-octets
           " (the offered article has no bytes to send; the connection closes and the offer is requeued)")))

(local
 (defthm fn-ofa-string-octets-aux-is-octets
   (implies (character-listp chars)
            (fn-cbor-octet-listp (fn-record-string-octets-aux chars)))
   :hints (("Goal" :in-theory (enable fn-record-string-octets-aux fn-cbor-octet-listp)))))

(local
 (defthm fn-ofa-string-octets-is-octets
   (fn-cbor-octet-listp (fn-record-string-octets x))
   :hints (("Goal" :in-theory (enable fn-record-string-octets)))))

(defthm fn-ofa-unsendable-line-is-octets
  (fn-cbor-octet-listp (fn-ofa-unsendable-line peer reason))
  :hints (("Goal" :in-theory (e/d (fn-cbor-octet-listp-append)
                                  (fn-record-string-octets fn-ofa-reason)))))

(defun fn-ofa-publication (pub)
  (declare (xargs :guard t))
  (if (and (member-equal (fn-ores-feedpub-word pub) *fn-ofa-command-words*)
           (not (consp (fn-ores-feedpub-command pub))))
      (list :feed-publication :unsendable
            (fn-ores-feedpub-peer pub) (fn-ores-feedpub-plan pub)
            (fn-ores-feedpub-token pub) nil (fn-ores-feedpub-status pub)
            (fn-ofa-unsendable-line (fn-ores-feedpub-peer pub)
                                    (fn-ores-feedpub-status pub)))
    pub))

; KEYSTONE.  Subject: fn-ofa-publication, which host/owner-host.lisp
; `fn-owner-feed-octets' and `fn-owner-feed-tick' return to the host
; (host/native/feed-service.lisp fnn-feed-reply-step, fnn-feed-tick): a
; command word reaches the host only with a command that has octets, so the
; host's "authorized an empty command" stop is unreachable; a publication
; that fails it is :unsendable, keeps its sealed record plan (what the core
; already did is published) and its line names the renderer's reason.
(defthm fn-ofa-publication-command-words-have-octets
  (let ((out (fn-ofa-publication pub)))
    (and (implies (member-equal (fn-ores-feedpub-word out) *fn-ofa-command-words*)
                  (consp (fn-ores-feedpub-command out)))
         (equal (fn-ores-feedpub-plan out) (fn-ores-feedpub-plan pub))
         (implies (not (equal out pub))
                  (and (equal (fn-ores-feedpub-word out) :unsendable)
                       (member-equal (fn-ores-feedpub-word pub) *fn-ofa-command-words*)
                       (not (consp (fn-ores-feedpub-command pub)))))))
  :hints (("Goal" :in-theory (disable fn-ofa-unsendable-line))))

; A well-formed publication stays well-formed (the host's recognizer,
; host/native/owner.lisp fnn-owner-result).
(defthm fn-ofa-publication-is-well-formed
  (implies (fn-ores-feed-publication-p pub)
           (fn-ores-feed-publication-p (fn-ofa-publication pub)))
  :hints (("Goal" :in-theory (e/d (fn-ores-feed-publication-p)
                                  (fn-ofa-unsendable-line)))))
