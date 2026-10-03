; fn: the outbound feed link's redial backoff and its drop line (defect M3).
;
; The feed machine's own backoff (`fn-feed-lost', books/peer-feed.lisp)
; gates OFFERS and is durable: it is folded back from the FNFD journal.  The
; question here is a different one: after a link to a peer fails, how long the
; host waits before it dials that peer again.  Before this book the host
; waited the peer record's constant base (`fn-owner-feed-backoff-ms', 1000 ms
; from `peer add'), so a link that failed the same way every time (defect
; M3: a TLS read that met only a NewSessionTicket) was redialled every
; second or two for as long as an article stayed queued, with no line.
;
; The streak is the number of consecutive link failures since the link last
; became ready.  It is per process and not durable: after a restart the first
; failure waits the base again, which is the right answer for a process that
; has not yet seen the peer fail.  The host carries the value this book
; returns and hands it back; it never computes it (AGENTS.md: ACL2 owns
; bounds and decisions).
;
; Host callers (host/native/feed-service.lisp): fnn-feed-drop-link calls
; `fn-flb-lost' with the peer record's base and the link's streak, waits the
; delay it answers and keeps the streak it answers; it logs `fn-flb-drop-line'
; for every drop.  fnn-feed-consume calls `fn-flb-ready' when the reply
; machine reports :ready.

(in-package "ACL2")
(include-book "peer-feed-invariants")
(include-book "records-shape")
(include-book "nntp-syntax")
(include-book "peer-pull-session")

; A local policy, not an RFC requirement: five minutes between redials at
; most.  The feed machine's one-hour ceiling (*fn-feed-max-backoff*) is for
; offers already made; a link that is down is retried sooner.
(defconst *fn-flb-max-delay* 300000)

(defun fn-flb-delay (base streak)
  (declare (xargs :guard t))
  (let ((d (fn-feed-backoff-delay base (nfix streak))))
    (if (<= *fn-flb-max-delay* d) *fn-flb-max-delay* d)))

; One link failure: (DELAY NEXT-STREAK).  DELAY is how long the host waits
; before the next dial; the streak advances while the delay can still grow,
; so the carried number stays at most one past the doubling that reaches the
; ceiling (log2 of the ceiling over the base) and never grows without bound.
(defun fn-flb-lost (base streak)
  (declare (xargs :guard t))
  (let* ((n (nfix streak))
         (delay (fn-flb-delay base n)))
    (list delay
          (if (and (< 0 delay) (< delay *fn-flb-max-delay*)) (+ 1 n) n))))

; The link became ready (the peer greeted, TLS and AUTHINFO completed, MODE
; answered): the next failure starts from the base again.
(defun fn-flb-ready (streak)
  (declare (xargs :guard t) (ignore streak))
  0)

(defun fn-flb-lost-delay (base streak)
  (declare (xargs :guard t))
  (car (fn-flb-lost base streak)))

(defun fn-flb-lost-streak (base streak)
  (declare (xargs :guard t))
  (cadr (fn-flb-lost base streak)))

; Why a link was dropped, as the host observed it: the dial (TCP or the TLS
; handshake) failed, the peer closed it, a read or a write failed -- the
; words the pull round and the feed's failure lines already use
; (books/peer-pull-session.lisp fn-peer-lost-word) -- or the peer answered
; what ends the connection (the reply machine logged its line), or the offer
; could not be rendered.
(defconst *fn-flb-causes* '(:dial :tls :eof :read :send :peer :unsendable :credential))

(defun fn-flb-cause-word (cause)
  (declare (xargs :guard t))
  (cond ((equal cause :credential) "credential-refused")
        ((equal cause :peer) "lost-peer")
        ((equal cause :unsendable) "lost-unsendable")
        (t (fn-peer-lost-word cause))))

; `feed peer=P link=dropped reason=WORD retry-ms=N': one line per drop.
(defun fn-flb-drop-line (peer cause delay)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "feed peer=")
          (if (fn-feed-namep peer) peer nil)
          (fn-record-string-octets " link=dropped reason=")
          (fn-record-string-octets (fn-flb-cause-word cause))
          (fn-record-string-octets " retry-ms=")
          (fn-nntp-decimal-field (nfix delay))))

; -----------------------------------------------------------------------------
; Properties

(defthm fn-flb-delay-is-bounded
  (and (natp (fn-flb-delay base streak))
       (<= (fn-flb-delay base streak) *fn-flb-max-delay*))
  :rule-classes ((:rewrite :corollary (natp (fn-flb-delay base streak)))
                 (:linear :corollary (<= (fn-flb-delay base streak)
                                         *fn-flb-max-delay*))))

(defthm fn-flb-lost-delay-unfolds
  (equal (fn-flb-lost-delay base streak)
         (fn-flb-delay base streak)))

(defthm fn-flb-lost-streak-is-a-nat
  (natp (fn-flb-lost-streak base streak))
  :rule-classes (:rewrite :type-prescription))

; The first failure after the link was ready waits the base (clamped).
(defthm fn-flb-first-loss-after-ready-waits-the-base
  (equal (fn-flb-lost-delay base (fn-flb-ready streak))
         (min (nfix base) *fn-flb-max-delay*))
  :hints (("Goal" :expand ((fn-feed-backoff-delay base 0)))))

(local
 (defthm fn-flb-backoff-delay-step
   (implies (natp n)
            (equal (fn-feed-backoff-delay base (+ 1 n))
                   (if (<= *fn-feed-max-backoff*
                           (* 2 (fn-feed-backoff-delay base n)))
                       *fn-feed-max-backoff*
                     (* 2 (fn-feed-backoff-delay base n)))))
   :hints (("Goal" :expand ((fn-feed-backoff-delay base (+ 1 n)))))))

; KEYSTONE: a link failure advances the backoff.  Two consecutive failures
; (the second from the streak the first answered): the second delay is never
; smaller, and while the first is positive and below the ceiling the second
; is strictly larger.
(defthm fn-flb-lost-advances-the-backoff
  (let* ((d1 (fn-flb-lost-delay base streak))
         (d2 (fn-flb-lost-delay base (fn-flb-lost-streak base streak))))
    (and (<= d1 d2)
         (implies (and (< 0 d1) (< d1 *fn-flb-max-delay*))
                  (< d1 d2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-feed-backoff-delay))))

; The growth is a doubling while it stays under the ceiling.
(defthm fn-flb-lost-doubles-below-the-ceiling
  (let* ((d1 (fn-flb-lost-delay base streak))
         (d2 (fn-flb-lost-delay base (fn-flb-lost-streak base streak))))
    (implies (<= (* 2 d1) *fn-flb-max-delay*)
             (equal d2 (* 2 d1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-feed-backoff-delay))))

(in-theory (disable fn-flb-delay fn-flb-lost fn-flb-ready fn-flb-lost-delay
                    fn-flb-lost-streak fn-flb-drop-line))
