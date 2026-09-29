; Teeth for lane wire-bounds (fuzz-nntp F1 and F2, 2026-09-27):
;   books/served.lisp         fn-served-step-stops-at-quit (F1)
;   books/transit-bound.lisp  fn-tb-served-run-retains-at-most-the-body-limit,
;                             fn-tb-open-peer-body-limit-is-the-profile-bound (F2)
; Each keystone: a reachable positive witness asserting its antecedent and
; conclusion, and one hypothesis-removal witness per hypothesis (the
; retained hypotheses hold, the omitted one fails, the conclusion fails).

(in-package "ACL2")
(include-book "../../books/transit-bound")
(include-book "../../books/codec-attach")
(include-book "arena-lift")

(defun wb-o (s) (declare (xargs :guard (stringp s))) (fn-nntp-string-octets s))

; -----------------------------------------------------------------------------
; A reader connection, as books/served.lisp's own tests open one: one article
; in fn.letters, posting allowed, the RFC 3977 510-octet line, and a small
; body limit (64) so the article bound is reached in a few octets.

(defconst *wb-groups* '("fn.letters"))
(defconst *wb-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 114 101 97 100 101 114 64
    101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 13 10
    72 101 108 108 111 13 10))
(defconst *wb-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *wb-groups*) 1
                      "<reader@example.invalid>" 0 *wb-groups* 841000000)
   0 1 :durable))
(defconst *wb-config*
  (fn-inj-make-config t (wb-o "fn.example.invalid")
                      (list (wb-o "fn.letters")) 64))
(defconst *wb-observation* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *wb-conn*
  (fn-served-result-conn
   (fn-served-open *wb-archive* 510 64 *wb-config* *wb-observation*
                   *wb-observation* (fn-auth-open-config))))
(defconst *wb-arena* (list *wb-payload*))
(bpr-lift fn-served-step 2)
(bpr-lift fn-served-run 2)
(assert-event (fn-served-connp *wb-conn*))
(assert-event (not (fn-served-quitp *wb-conn*)))

; -----------------------------------------------------------------------------
; F1.  fn-served-step-stops-at-quit: hypothesis (fn-served-quitp (result-conn
; (fn-served-step conn left))).
;
; Positive: LEFT is QUIT, RIGHT is CAPABILITIES, which books/nntp-auth.lisp
; answers itself (before this lane it answered it after the 205).

(defconst *wb-quit* (wb-o (coerce (list #\Q #\U #\I #\T #\Return #\Newline) 'string)))
(defconst *wb-caps* (append (wb-o "CAPABILITIES") '(13 10)))
(defconst *wb-authinfo* (append (wb-o "AUTHINFO USER fuzz") '(13 10)))
(defconst *wb-date* (append (wb-o "DATE") '(13 10)))
(defconst *wb-205* (append (wb-o "205 closing connection") '(13 10)))

(defconst *wb-left* (in-arena-fn-served-step *wb-arena* *wb-conn* *wb-quit*))
(defconst *wb-whole*
  (in-arena-fn-served-step *wb-arena* *wb-conn* (append *wb-quit* *wb-caps*)))
; the antecedent
(assert-event (fn-served-quitp (fn-served-result-conn *wb-left*)))
; the conclusion, both conjuncts, and it is not degenerate: QUIT's 205 and
; its close are there, and nothing else
(assert-event (equal (fn-served-result-effects *wb-whole*)
                     (fn-served-result-effects *wb-left*)))
(assert-event (equal (fn-served-result-conn *wb-whole*)
                     (fn-served-result-conn *wb-left*)))
(assert-event (equal (fn-served-reply-octets (fn-served-result-effects *wb-whole*))
                     *wb-205*))
(assert-event (fn-served-closingp (fn-served-result-effects *wb-whole*)))
; The fuzz reproducers' shapes (tests/fixtures/fuzz-nntp/diff-quit-then-*):
; AUTHINFO in the same read, and CAPABILITIES in the next read -- the cut the
; host made visible.  Every cut serves the 205 and nothing else.
(assert-event (equal (fn-served-reply-octets
                      (fn-served-result-effects
                       (in-arena-fn-served-step *wb-arena* *wb-conn*
                                                (append *wb-quit* *wb-authinfo*))))
                     *wb-205*))
(assert-event (equal (fn-served-reply-octets
                      (fn-served-result-effects
                       (in-arena-fn-served-run *wb-arena* *wb-conn*
                                               (list *wb-quit* *wb-caps*))))
                     *wb-205*))
(assert-event (equal (fn-served-reply-octets
                      (fn-served-result-effects
                       (in-arena-fn-served-run *wb-arena* *wb-conn*
                                               (list (take 3 *wb-quit*)
                                                     (append (nthcdr 3 *wb-quit*)
                                                             (take 5 *wb-caps*))
                                                     (nthcdr 5 *wb-caps*)))))
                     *wb-205*))
; fn-served-step-of-quit-connection-is-a-no-op on the connection QUIT left.
(assert-event (equal (in-arena-fn-served-step *wb-arena*
                                              (fn-served-result-conn *wb-left*)
                                              *wb-authinfo*)
                     (fn-served-make-result (fn-served-result-conn *wb-left*) nil)))

; Hypothesis removed: LEFT is DATE, the session is still open, and the
; command after it is answered, so the whole read is not the prefix's.
(defconst *wb-left-open* (in-arena-fn-served-step *wb-arena* *wb-conn* *wb-date*))
(assert-event (not (fn-served-quitp (fn-served-result-conn *wb-left-open*))))
(assert-event
 (not (equal (fn-served-result-effects
              (in-arena-fn-served-step *wb-arena* *wb-conn* (append *wb-date* *wb-caps*)))
             (fn-served-result-effects *wb-left-open*))))

; -----------------------------------------------------------------------------
; F2.  fn-tb-served-run-retains-at-most-the-body-limit: hypothesis
; (fn-wire-statep (fn-served-conn-wire conn)).
;
; Positive: POST, then an article streamed in reads.  Forty octets retained
; (non-degenerate: the article is in flight, within the limit 64); and past
; the limit the wire closes, the reply names the size, nothing is retained.

(defconst *wb-post* (append (wb-o "POST") '(13 10)))
(defconst *wb-head* (append (wb-o "Newsgroups: fn.letters") '(13 10)
                            (wb-o "Subject: s") '(13 10)))
(defconst *wb-in-flight*
  (in-arena-fn-served-run *wb-arena* *wb-conn* (list *wb-post* *wb-head*)))
(defconst *wb-w1* (fn-served-conn-wire (fn-served-result-conn *wb-in-flight*)))
(assert-event (fn-wire-statep (fn-served-conn-wire *wb-conn*)))
(assert-event (equal (fn-wire-state-mode *wb-w1*) :article))
(assert-event (< 0 (fn-wire-state-body-size *wb-w1*)))
(assert-event (<= (fn-wire-state-body-size *wb-w1*)
                  (fn-wire-state-body-limit (fn-served-conn-wire *wb-conn*))))
(assert-event (<= (fn-wire-held-octets *wb-w1*)
                  (+ (fn-wire-state-body-limit (fn-served-conn-wire *wb-conn*))
                     (fn-tb-wire-ceiling (fn-served-conn-wire *wb-conn*)))))

(defconst *wb-body-line* (append (wb-o "body line") '(13 10)))
(defconst *wb-endless*
  (in-arena-fn-served-run *wb-arena* *wb-conn*
                          (list *wb-post* *wb-head* '(13 10)
                                *wb-body-line* *wb-body-line* *wb-body-line*
                                *wb-body-line* *wb-body-line* *wb-body-line*
                                *wb-body-line* *wb-body-line*)))
(defconst *wb-w2* (fn-served-conn-wire (fn-served-result-conn *wb-endless*)))
(assert-event (equal (fn-wire-state-mode *wb-w2*) :closed))
(assert-event (equal (fn-wire-state-body-size *wb-w2*) 0))
(assert-event (equal (fn-served-reply-octets (fn-served-result-effects *wb-endless*))
                     (append (wb-o "340 send article to be posted") '(13 10)
                             (wb-o "441 posting failed; the article exceeds the configured size")
                             '(13 10))))
(assert-event (fn-served-closingp (fn-served-result-effects *wb-endless*)))

; Hypothesis removed: a wire that is not a wire state -- an article record
; holding a 100-octet line under a limit of 10 -- keeps it through a run, so
; the conclusion fails.  (A corrupted-state witness: no open builds it.)
(defconst *wb-bad-wire*
  (fn-wire-make-state :article nil 0
                      (fn-bch-of (append (make-list 100 :initial-element 65) '(13 10)))
                      nil 102 510 10))
(defconst *wb-bad-conn* (fn-served-conn-with-wire *wb-conn* *wb-bad-wire*))
(assert-event (not (fn-wire-statep (fn-served-conn-wire *wb-bad-conn*))))
(assert-event
 (not (<= (fn-wire-state-body-size
           (fn-served-conn-wire
            (fn-served-result-conn (in-arena-fn-served-run *wb-arena* *wb-bad-conn* nil))))
          (fn-wire-state-body-limit (fn-served-conn-wire *wb-bad-conn*)))))

;; -----------------------------------------------------------------------------
;; B6b (lane chunked-body-2, PRF-929).
;; fn-tb-served-run-holds-at-most-the-body-limit-mid-article: hypothesis
;; (fn-wire-statep (fn-served-conn-wire conn)), and mid-article.
;;
;; Positive: the article in flight above holds its forty octets, within the
;; limit and one.
(assert-event (<= (fn-wire-held-octets *wb-w1*)
                  (+ 1 (fn-wire-state-body-limit *wb-w1*))))
;; A LINE past the body limit: one body line of 100 octets and no LF.  Before
;; the lane the wire held the body limit AND the line (up to the article line
;; limit) until the LF; now it closes :body-overlimit at the octet that dooms
;; the line, so nothing past the limit and one is ever held.
(defconst *wb-long-line*
  (in-arena-fn-served-run *wb-arena* *wb-conn*
                          (list *wb-post* *wb-head* '(13 10)
                                (make-list 100 :initial-element 120))))
(defconst *wb-w3* (fn-served-conn-wire (fn-served-result-conn *wb-long-line*)))
(assert-event (equal (fn-wire-state-mode *wb-w3*) :closed))
(assert-event (fn-served-closingp (fn-served-result-effects *wb-long-line*)))
;; The same line under a body limit it fits stays held, mid-article.
(defconst *wb-short-line*
  (in-arena-fn-served-run *wb-arena* *wb-conn*
                          (list *wb-post* *wb-head* '(13 10)
                                (make-list 10 :initial-element 120))))
(defconst *wb-w4* (fn-served-conn-wire (fn-served-result-conn *wb-short-line*)))
(assert-event (equal (fn-wire-state-mode *wb-w4*) :article))
(assert-event (<= (fn-wire-held-octets *wb-w4*) (+ 1 (fn-wire-state-body-limit *wb-w4*))))
;; books/wire.lisp KEYSTONE fn-wire-statep-article-holds-at-most-the-body-limit
;; (hypotheses: fn-wire-statep, article mode): the wire above is one, holding
;; 48 octets under the limit 64; the corrupted record below is not a wire
;; state and holds 102 under 10.
(assert-event (and (fn-wire-statep *wb-w4*) (equal (fn-wire-state-mode *wb-w4*) :article)
                   (<= (fn-wire-held-octets *wb-w4*) (+ 1 (fn-wire-state-body-limit *wb-w4*)))))
(assert-event (and (not (fn-wire-statep *wb-bad-wire*))
                   (equal (fn-wire-state-mode *wb-bad-wire*) :article)
                   (not (<= (fn-wire-held-octets *wb-bad-wire*)
                            (+ 1 (fn-wire-state-body-limit *wb-bad-wire*))))))
;; Command mode (the other hypothesis removed): a wire state holding a
;; command line of 100 octets under a body limit of 10 -- the line limit
;; bounds it, not the body limit.
(defconst *wb-cmd-wire* (fn-wire-make-state :command (make-list 100 :initial-element 65) 100
                                            nil nil 0 510 10))
(assert-event (and (fn-wire-statep *wb-cmd-wire*)
                   (not (equal (fn-wire-state-mode *wb-cmd-wire*) :article))
                   (not (<= (fn-wire-held-octets *wb-cmd-wire*)
                            (+ 1 (fn-wire-state-body-limit *wb-cmd-wire*))))))
;; Hypothesis removed (a corrupted-state witness: no open builds it): the
;; record above, mid-article with 102 octets under a limit of 10, is not a
;; wire state, and a run keeps them: the conclusion fails.
(defconst *wb-bad-w* (fn-served-conn-wire
                      (fn-served-result-conn (in-arena-fn-served-run *wb-arena* *wb-bad-conn* nil))))
(assert-event (equal (fn-wire-state-mode *wb-bad-w*) :article))
(assert-event (not (<= (fn-wire-held-octets *wb-bad-w*)
                       (+ 1 (fn-wire-state-body-limit *wb-bad-w*)))))

; -----------------------------------------------------------------------------
; F2.  fn-tb-open-peer-body-limit-is-the-profile-bound: hypotheses
; (fn-bs-profile-admittedp profile), (equal o2 (mv-nth 1 (fn-osb-install o
; profile))), (< (len (fn-own-conns o2)) (nfix (fn-own-max-conns o2))).
;
; The peer record is what `peer add' writes (books/native-admin-peer.lisp):
; inbound-max-octets = *fn-record-max-payload*, 4 GiB.  Before this lane that
; was the connection's body limit.

(defconst *wb-peer-record*
  (fn-cfg-peer-make "p" "peer.example" '(:nntp "127.0.0.1" 1119)
                    (list "fn.*" *fn-record-max-payload* 16) nil
                    '(:source-address "127.0.0.1")))
(assert-event (fn-cfg-peerp *wb-peer-record*))
(defconst *wb-peer-cfg*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-policy "path-identity" "wb.example")
                                         (fn-cfg-set-peer-delta *wb-peer-record*)))
                           *fn-cfg-default-stamp*))))
(assert-event (fn-cfgp *wb-peer-cfg*))
(assert-event (equal (fn-cfg-peer-find "p" (fn-cfg-peers (fn-cfg-value *wb-peer-cfg*)))
                     *wb-peer-record*))

; An owner with nothing open and room for two connections; its posting
; configuration still carries the codec ceiling recovery installs.
(defconst *wb-owner*
  (fn-own-make nil nil nil 0 2 nil nil nil nil
               (fn-inj-make-config t (wb-o "fn.example.invalid")
                                   (list (wb-o "fn.letters"))
                                   *fn-record-max-payload*)
               nil nil nil nil nil))
(defconst *wb-profile* *fn-bs-profile-defaults*)
; (mv-nth 1 (fn-osb-install o profile)), the theorem's O2
(defun wb-install (o profile)
  (mv-let (verdict o2) (fn-osb-install o profile)
    (declare (ignore verdict))
    o2))
(defconst *wb-o2* (wb-install *wb-owner* *wb-profile*))
(defun wb-peer-limit (o2)
  (fn-wire-state-body-limit
   (fn-own-conn-wire
    (car (fn-own-conns (cdr (fn-own-open-peer o2 "p" *wb-peer-cfg* nil)))))))
; the antecedent
(assert-event (fn-bs-profile-admittedp *wb-profile*))
(assert-event (< (len (fn-own-conns *wb-o2*)) (nfix (fn-own-max-conns *wb-o2*))))
; the conclusion, non-degenerate: the limit is exactly A, and A is far below
; the record's 4 GiB, which is what the connection used to open with
(assert-event (<= (wb-peer-limit *wb-o2*) (fn-bs-profile-max-article-octets *wb-profile*)))
(assert-event (equal (wb-peer-limit *wb-o2*) (fn-bs-profile-max-article-octets *wb-profile*)))
(assert-event (< (fn-bs-profile-max-article-octets *wb-profile*)
                 (fn-cfg-peer-inbound-max-octets *wb-peer-record*)))
; a record that asks for less keeps its own, smaller limit
(assert-event (equal (fn-own-peer-body-limit
                      *wb-o2*
                      (fn-cfg-peer-make "q" "q.example" '(:nntp "127.0.0.1" 1119)
                                        (list "fn.*" 1000 16) nil
                                        '(:source-address "127.0.0.2")))
                     1000))

; Hypothesis removed: an admitted profile.  NIL is not one; the install
; refuses, the owner keeps the codec ceiling, and the connection's limit is
; far above that profile's (absent) bound.
(assert-event (not (fn-bs-profile-admittedp nil)))
(assert-event (< (len (fn-own-conns (wb-install *wb-owner* nil)))
                 (nfix (fn-own-max-conns (wb-install *wb-owner* nil)))))
(assert-event (not (<= (wb-peer-limit (wb-install *wb-owner* nil))
                       (fn-bs-profile-max-article-octets nil))))

; Hypothesis removed: O2 is the installed owner.  The owner as recovery left
; it (codec ceiling) opens the connection at 4 GiB.
(assert-event (not (equal *wb-owner* *wb-o2*)))
(assert-event (< (len (fn-own-conns *wb-owner*)) (nfix (fn-own-max-conns *wb-owner*))))
(assert-event (not (<= (wb-peer-limit *wb-owner*)
                       (fn-bs-profile-max-article-octets *wb-profile*))))

; Hypothesis removed: room for the connection.  A full owner refuses the
; open, and the first connection it holds -- here one opened before, with
; the 4 GiB limit -- is not bounded by the profile.
(defconst *wb-full*
  (fn-own-make nil nil
               (list (list 7 0 0 (fn-wire-initial-state 510 *fn-record-max-payload*)))
               8 1 nil nil nil nil (fn-own-config *wb-o2*) nil nil nil nil nil))
; O2 is an installed owner (the install of itself), under the admitted profile
(assert-event (equal *wb-full* (wb-install *wb-full* *wb-profile*)))
(assert-event (not (< (len (fn-own-conns *wb-full*)) (nfix (fn-own-max-conns *wb-full*)))))
(assert-event (not (<= (wb-peer-limit *wb-full*)
                       (fn-bs-profile-max-article-octets *wb-profile*))))
