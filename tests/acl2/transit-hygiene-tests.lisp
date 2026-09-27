; Teeth for books/relay-checks.lisp (PRF-236), books/refused-offers.lisp and
; books/peer-refused-offers.lisp (PRF-235).  Every witness is a computation
; through the function the host calls: `fn-peer-decide-transfer' (host/owner-
; host.lisp fn-owner-transit-decide), `fn-peer-command' (the served offer,
; through fn-pgc-peer-command) and `fn-own-transit-refused' (books/owner.lisp
; fn-own-transit-outcome).
(in-package "ACL2")
(include-book "../../books/peer-refused-offers")
(include-book "../../books/peer-transit-forms")
(include-book "std/testing/must-fail" :dir :system)

(defun th-o (s) (fn-nntp-string-octets s))
(defun th-lines (strings)
  (if (consp strings) (cons (th-o (car strings)) (th-lines (cdr strings))) nil))

; -----------------------------------------------------------------------------
; The date reader (RFC 5322 section 3.3 and the section 4.3 obsolete forms)

(defconst *th-now* 1790473820)   ; 2026-09-27T01:50:20Z
(assert-event (equal (fn-rck-date-instant (th-o "Sun, 27 Sep 2026 01:50:20 +0000")) *th-now*))
; No day-of-week, no seconds, a comment, folding white space, lower case.
(assert-event (equal (fn-rck-date-instant (th-o "27 sep 2026 01:50 +0000 (UTC)")) (- *th-now* 20)))
(assert-event (equal (fn-rck-date-instant (th-o "Sun,  27 Sep 2026 03:50:20 +0200")) *th-now*))
(assert-event (equal (fn-rck-date-instant (th-o "Sat, 26 Sep 2026 20:50:20 -0500")) *th-now*))
(assert-event (equal (fn-rck-date-instant (th-o "Sat, 26 Sep 2026 20:50:20 EST")) *th-now*))
(assert-event (equal (fn-rck-date-instant (th-o "27 Sep 2026 01:50:20 GMT")) *th-now*))
; Two-digit years (section 4.3): 99 is 1999, 49 is 2049.
(assert-event (equal (fn-rck-date-instant (th-o "31 Dec 99 23:59 +0000")) 946684740))
(assert-event (equal (fn-rck-date-instant (th-o "1 Jan 49 00:00:00 +0000")) 2493072000))
; What this node's injector writes (books/injection.lisp fn-inj-date-octets).
(assert-event (equal (fn-rck-date-instant (th-o "Sat, 19 Sep 2026 12:00:00 +0000")) 1789819200))
; Not date-times.
(assert-event (null (fn-rck-date-instant (th-o "yesterday"))))
(assert-event (null (fn-rck-date-instant (th-o "27 Sep 2026 25:00:00 +0000"))))
(assert-event (null (fn-rck-date-instant (th-o "27 Sept 2026 01:50:20 +0000"))))
(assert-event (null (fn-rck-date-instant (th-o "27 Sep 2026 01:50:20 +0000 (unclosed"))))
(assert-event (null (fn-rck-date-instant (th-o "27 Sep 2026 01:50:20 +0000 trailing"))))
(assert-event (null (fn-rck-date-instant nil)))

; -----------------------------------------------------------------------------
; The Path grammar (RFC 5536 section 3.1.5)

(assert-event (fn-rck-path-wellformedp (th-o "inn.hbox.test!not-for-mail")))
(assert-event (fn-rck-path-wellformedp (th-o "fnA.hbox.test!!inn.hbox.test!.POSTED.127.0.0.1!not-for-mail")))
(assert-event (fn-rck-path-wellformedp (th-o "a! b!x")))
(assert-event (fn-rck-path-wellformedp (th-o "not-for-mail")))
(assert-event (not (fn-rck-path-wellformedp (th-o ""))))
(assert-event (not (fn-rck-path-wellformedp (th-o "a b!x"))))
(assert-event (not (fn-rck-path-wellformedp (th-o "inn.hbox.test!"))))
(assert-event (not (fn-rck-path-wellformedp (th-o "!inn.hbox.test!x"))))
(assert-event (fn-rck-path-wellformedp (th-o "inn.hbox.test!origin!fnA.hbox.test")))
(assert-event (not (fn-rck-path-wellformedp (th-o "inn.hbox.test!not for mail"))))

; -----------------------------------------------------------------------------
; Configuration, node, articles

(defconst *th-peer*
  (fn-cfg-peer-make "innA" "inn.hbox.test" '(:nntp "127.0.0.1" 1119)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.1")))
(defconst *th-peer-b*
  (fn-cfg-peer-make "innB" "innb.hbox.test" '(:nntp "127.0.0.2" 1119)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.2")))
(defun th-cfg (limits)
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-policy "path-identity" "fnA.hbox.test")
                                         (fn-cfg-set-peer-delta *th-peer*)
                                         (fn-cfg-set-peer-delta *th-peer-b*))
                                   limits)
                           *fn-cfg-default-stamp*))))
(defconst *th-cfg* (th-cfg nil))
(defconst *th-cfg-skew* (th-cfg (list (fn-cfg-set-limit "relay-date-skew" 3600)
                                      (fn-cfg-set-limit "refused-offer-capacity" 2)
                                      (fn-cfg-set-limit "relay-require-path" 1))))
(assert-event (fn-cfgp *th-cfg*))
(assert-event (fn-cfgp *th-cfg-skew*))
(assert-event (equal (fn-rck-skew *th-cfg*) 86400))
(assert-event (equal (fn-rck-skew *th-cfg-skew*) 3600))
(assert-event (equal (fn-rck-refused-capacity *th-cfg*) 4096))
(assert-event (equal (fn-rck-refused-capacity *th-cfg-skew*) 2))
; The operator's words: a skew above the RFC's 24 hours is refused.
(assert-event (fn-rck-limit-valuep "relay-date-skew" 86400))
(assert-event (not (fn-rck-limit-valuep "relay-date-skew" 86401)))
(assert-event (fn-rck-limit-valuep "refused-offer-capacity" 100000))
(assert-event (not (fn-rck-limit-valuep "relay-require-path" 2)))
(assert-event (fn-rck-require-pathp *th-cfg-skew*))
(assert-event (not (fn-rck-require-pathp *th-cfg*)))

(defconst *th-node* (fn-node-initial-state '("fn.letters" "fn.test") 1048576))
; The wall reading is DTN milliseconds (since 2000-01-01, books/clock.lisp).
(defconst *th-clock* (fn-clock-observation 1000000 (* 1000 (- *th-now* 946684800)) 500 t))
(assert-event (equal (fn-peer-clock-unix-seconds *th-clock*) *th-now*))

(defun th-article (id path date)
  ; PATH and DATE nil omit the field.
  (fn-post-body-octets
   (th-lines (append (if path (list (string-append "Path: " path)) nil)
                     (list "From: poster@example.invalid"
                           "Newsgroups: fn.letters" "Subject: hygiene")
                     (if date (list (string-append "Date: " date)) nil)
                     (list (string-append "Message-ID: " id) "" "Hello.")))))
(defconst *th-good-date* "Sun, 27 Sep 2026 01:00:00 +0000")
(defconst *th-good* (th-article "<g@example.invalid>" "inn.hbox.test!not-for-mail" *th-good-date*))
(defconst *th-nopath* (th-article "<np@example.invalid>" nil *th-good-date*))
(defconst *th-badpath* (th-article "<bp@example.invalid>" "inn hbox!x" *th-good-date*))
(defconst *th-baddate* (th-article "<bd@example.invalid>" "inn.hbox.test!x" "someday"))
; 25 hours ahead: past the RFC's 24 hours.  2 hours ahead: past a 1-hour skew.
(defconst *th-future* (th-article "<f@example.invalid>" "inn.hbox.test!x" "Mon, 28 Sep 2026 02:50:20 +0000"))
(defconst *th-soon* (th-article "<s@example.invalid>" "inn.hbox.test!x" "Sun, 27 Sep 2026 03:50:20 +0000"))

(defun th-decide (cfg peer id octets clock)
  (fn-peer-decide-transfer *th-node* cfg peer (th-o id) octets clock "ob" "s"))

; -----------------------------------------------------------------------------
; PRF-236: the relay refusals by name

(assert-event (equal (th-decide *th-cfg* "innA" "<g@example.invalid>" *th-good* *th-clock*)
                     (fn-peer-decision :want nil)))
; A missing Path is refused only when the operator requires Path.
(assert-event (equal (th-decide *th-cfg* "innA" "<np@example.invalid>" *th-nopath* *th-clock*)
                     (fn-peer-decision :want nil)))
(assert-event (equal (th-decide *th-cfg-skew* "innA" "<np@example.invalid>" *th-nopath* *th-clock*)
                     (fn-peer-decision :refuse :no-path)))
(assert-event (equal (th-decide *th-cfg* "innA" "<bp@example.invalid>" *th-badpath* *th-clock*)
                     (fn-peer-decision :refuse :path-syntax)))
(assert-event (equal (th-decide *th-cfg* "innA" "<bd@example.invalid>" *th-baddate* *th-clock*)
                     (fn-peer-decision :refuse :date-syntax)))
(assert-event (equal (th-decide *th-cfg* "innA" "<f@example.invalid>" *th-future* *th-clock*)
                     (fn-peer-decision :refuse :date-future)))
; Two hours ahead is inside the RFC's 24 hours, outside the operator's hour.
(assert-event (equal (th-decide *th-cfg* "innA" "<s@example.invalid>" *th-soon* *th-clock*)
                     (fn-peer-decision :want nil)))
(assert-event (equal (th-decide *th-cfg-skew* "innA" "<s@example.invalid>" *th-soon* *th-clock*)
                     (fn-peer-decision :refuse :date-future)))
; Without a clock reading the future check does not decide (the transfer
; then defers :no-clock, fn-peer-transfer; the last argument is the arena
; handle the transit entry fn-peer-transfer-interned hands it, records-flip).
(assert-event (equal (th-decide *th-cfg* "innA" "<f@example.invalid>" *th-future* nil)
                     (fn-peer-decision :want nil)))
(assert-event (equal (cadr (mv-list 2 (fn-peer-transfer *th-node* *th-cfg* "innA" (th-o "<f@example.invalid>")
                                                         *th-future* nil 1 "ob" "s" 0)))
                     (fn-peer-decision :defer :no-clock)))
; The reply text names the reason (RFC 3977 section 6.3.2: 437 with text).
(assert-event (equal (fn-peer-reason-text :no-path) "no Path"))
(assert-event (equal (fn-peer-reason-text :date-future) "dated in the future"))

; -----------------------------------------------------------------------------
; PRF-235: the octets' refusal, the memory, the offer

(assert-event (equal (fn-peer-intrinsic-refusal (th-o "<bp@example.invalid>") *th-badpath*) :path-syntax))
(assert-event (equal (fn-peer-intrinsic-refusal (th-o "<g@example.invalid>") *th-good*) nil))
; A missing Path is the operator's to refuse, so never remembered.
(assert-event (equal (fn-peer-intrinsic-refusal (th-o "<np@example.invalid>") *th-nopath*) nil))
; A future date is NOT an intrinsic refusal: tomorrow it is acceptable.
(assert-event (equal (fn-peer-intrinsic-refusal (th-o "<f@example.invalid>") *th-future*) nil))

; KEYSTONE fn-peer-decide-transfer-refuses-what-the-octets-refuse: the full
; antecedent and conclusion, from two peers, with and without a clock.
(defun th-k1-antecedent (cfg peer id octets)
  (let ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
    (and record (fn-cfg-peer-inbound record) (fn-af-message-idp (th-o id))
         (<= (len octets) (fn-cfg-peer-inbound-max-octets record))
         (fn-peer-intrinsic-refusal (th-o id) octets) t)))
(defun th-k1-conclusion (cfg peer id octets clock)
  (equal (th-decide cfg peer id octets clock)
         (fn-peer-decision :refuse (fn-peer-intrinsic-refusal (th-o id) octets))))
(assert-event (th-k1-antecedent *th-cfg* "innA" "<bp@example.invalid>" *th-badpath*))
(assert-event (th-k1-conclusion *th-cfg* "innA" "<bp@example.invalid>" *th-badpath* *th-clock*))
(assert-event (th-k1-conclusion *th-cfg* "innB" "<bp@example.invalid>" *th-badpath* nil))
; Hypothesis removal: not a peer (ghost) -- the rest hold, the conclusion fails.
(assert-event (and (not (fn-cfg-peer-find "ghost" (fn-cfg-peers (fn-cfg-value *th-cfg*))))
                   (fn-peer-intrinsic-refusal (th-o "<bp@example.invalid>") *th-badpath*)
                   (not (th-k1-conclusion *th-cfg* "ghost" "<bp@example.invalid>" *th-badpath* nil))))
(must-fail
 (defthm th-k1-without-a-record
   (implies (and (fn-af-message-idp msgid) (fn-peer-intrinsic-refusal msgid octets))
            (equal (fn-peer-decide-transfer node cfg peer msgid octets clock id subject)
                   (fn-peer-decision :refuse (fn-peer-intrinsic-refusal msgid octets))))))
; Hypothesis removal: the offered Message-ID is not one.
(assert-event (and (fn-peer-intrinsic-refusal (th-o "bp@example.invalid") *th-badpath*)
                   (not (fn-af-message-idp (th-o "bp@example.invalid")))
                   (equal (th-decide *th-cfg* "innA" "bp@example.invalid" *th-badpath* nil)
                          (fn-peer-decision :refuse :message-id-syntax))))
; Hypothesis removal: the octets exceed the peer's size (a peer whose bound is 64).
(defconst *th-peer-small*
  (fn-cfg-peer-make "innS" "inns.hbox.test" '(:nntp "127.0.0.3" 1119)
                    '("fn.*" 64 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.3")))
(defconst *th-cfg-small*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-peer-delta *th-peer-small*)))
                           *fn-cfg-default-stamp*))))
(assert-event (and (fn-cfg-peer-find "innS" (fn-cfg-peers (fn-cfg-value *th-cfg-small*)))
                   (< 64 (len *th-badpath*))
                   (equal (th-decide *th-cfg-small* "innS" "<bp@example.invalid>" *th-badpath* nil)
                          (fn-peer-decision :refuse :oversize))))
; Hypothesis removal: the octets refuse nothing (the good article is wanted).
(assert-event (and (null (fn-peer-intrinsic-refusal (th-o "<g@example.invalid>") *th-good*))
                   (not (th-k1-conclusion *th-cfg* "innA" "<g@example.invalid>" *th-good* *th-clock*))))

; The memory: bounded, oldest-first, first reason kept.
(defconst *th-m1* (fn-rof-record nil 2 "<a@x>" :path-syntax))
(defconst *th-m2* (fn-rof-record *th-m1* 2 "<b@x>" :path-syntax))
(defconst *th-m3* (fn-rof-record *th-m2* 2 "<c@x>" :no-date))
(assert-event (equal *th-m2* '(("<b@x>" . :path-syntax) ("<a@x>" . :path-syntax))))
(assert-event (equal *th-m3* '(("<c@x>" . :no-date) ("<b@x>" . :path-syntax))))
(assert-event (null (fn-rof-lookup "<a@x>" *th-m3*)))
(assert-event (equal (fn-rof-record *th-m3* 2 "<b@x>" :no-date) *th-m3*))
; Capacity 0 (the operator turned the memory off): a new entry empties it.
(assert-event (equal (fn-rof-record *th-m3* 0 "<d@x>" :no-date) nil))
(assert-event (null (fn-rof-record nil 0 "<d@x>" :no-date)))
(must-fail
 (defthm th-eviction-without-capacity-equality
   (implies (and (true-listp mem) (posp cap) reason (not (fn-rof-lookup msgid mem)))
            (equal (fn-rof-record mem cap msgid reason)
                   (cons (cons msgid reason) (butlast mem 1))))))

; The owner's record over the refusal from peer innA, then the offers of the
; same Message-ID from innA and innB answer 435 / 438 without a transfer.
(defconst *th-mem* (fn-peer-refused-record nil *th-cfg* (th-o "<bp@example.invalid>") *th-badpath*))
(assert-event (equal *th-mem* '(("<bp@example.invalid>" . :path-syntax))))
(defconst *th-ps-a* (fn-peer-with-refused
                     (fn-peer-open-session (fn-node-acceptance *th-node*) "innA" *th-node* *th-cfg*)
                     *th-mem*))
(defconst *th-ps-b* (fn-peer-with-refused
                     (fn-peer-open-session (fn-node-acceptance *th-node*) "innB" *th-node* *th-cfg*)
                     *th-mem*))
(assert-event (fn-peer-sessionp *th-ps-b*))
(defun th-code (ps k id)
  (fn-peer-wire-code (fn-post-result-effects (fn-peer-command ps (th-o k) (list (th-o id))))))
(assert-event (equal (th-code *th-ps-a* "CHECK" "<bp@example.invalid>") 438))
(assert-event (equal (th-code *th-ps-b* "CHECK" "<bp@example.invalid>") 438))
(assert-event (equal (th-code *th-ps-b* "IHAVE" "<bp@example.invalid>") 435))
(assert-event (equal (fn-post-result-effects
                      (fn-peer-command *th-ps-b* (th-o "IHAVE") (list (th-o "<bp@example.invalid>"))))
                     (fn-peer-single *th-ps-b* "435 not wanted; malformed Path")))
; Another Message-ID is still wanted, and a session with no memory wants it.
(assert-event (equal (th-code *th-ps-b* "CHECK" "<g@example.invalid>") 238))
(assert-event (equal (th-code (fn-peer-with-refused *th-ps-b* nil) "CHECK" "<bp@example.invalid>") 238))
; A memory entry whose reason is not one the octets decide says nothing.
(assert-event (equal (th-code (fn-peer-with-refused *th-ps-b* '(("<bp@example.invalid>" . :capacity)))
                              "CHECK" "<bp@example.invalid>")
                     238))

; KEYSTONE fn-prof-offer-answer-is-the-reparse over one run of transfers:
; the offer's refusal, the witness transfer and the re-parse's decision.
(defconst *th-transfers* (list (cons (th-o "<g@example.invalid>") *th-good*)
                               (cons (th-o "<bp@example.invalid>") *th-badpath*)))
(defconst *th-run* (fn-prof-run nil *th-cfg* *th-transfers*))
(assert-event (equal *th-run* *th-mem*))
(defconst *th-w* (fn-prof-witness "<bp@example.invalid>" :path-syntax *th-transfers*))
(assert-event (equal *th-w* (cons (th-o "<bp@example.invalid>") *th-badpath*)))
(assert-event (equal (fn-peer-decide-offer *th-node* *th-cfg* "innB" *th-ps-b*
                                           (th-o "<bp@example.invalid>") nil 0)
                     (fn-peer-decision :refuse :path-syntax)))
(assert-event (equal (fn-peer-decide-transfer *th-node* *th-cfg* "innB" (car *th-w*) (cdr *th-w*)
                                              *th-clock* "ob" "s")
                     (fn-peer-decision :refuse :path-syntax)))
; Hypothesis removal (history): without it the claim is false, because a
; held Message-ID is answered duplicate before the memory is read.
(must-fail
 (defthm th-offer-without-history
   (implies (and (fn-af-message-idp msgid)
                 (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))
                 (fn-cfg-peer-inbound (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
                 (fn-peer-remembered-reason msgid session))
            (equal (fn-peer-decide-offer node cfg peer session msgid clock inflight)
                   (fn-peer-decision :refuse (fn-peer-remembered-reason msgid session))))))

; The owner's recording step: only an intrinsic refusal is recorded, and the
; recorded reason is the octets', never the word the host relayed.
(assert-event (equal (fn-peer-refused-record nil *th-cfg* (th-o "<g@example.invalid>") *th-good*) nil))
(assert-event (equal (fn-peer-refused-record nil *th-cfg-skew* (th-o "<bp@example.invalid>") *th-badpath*)
                     '(("<bp@example.invalid>" . :path-syntax))))
