; Teeth for PKT-175 / PRF-168: HDR :fn-enrollment over fn-own-read, on the
; reachable T10a trace owner-verdict-tests.lisp steps through fn-own-step:
; an enrolled principal's verified post (reader B, conn 2: active), a
; durable rotation (reader C, conn 3: retired) and a durable revocation
; (reader D, conn 4: revoked), each reader opened after the completion.
(in-package "ACL2")
(include-book "owner-verdict-tests")
(include-book "../../books/owner-enrollment-read")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-oert-line (text)
  (append (fn-nntp-string-octets text) '(13 10)))
(defconst *oer-hdr* (fn-oert-line "HDR :fn-enrollment <carried@example.invalid>"))
(defconst *oer-prefix* (butlast *oer-hdr* 1))
(defconst *oer-lf* (car (last *oer-hdr*)))

(defun fn-oert-reply (item)
  (append (fn-nntp-string-octets "225 headers follow")
          '(13 10 48 32) (fn-nntp-string-octets item) '(13 10 46 13 10)))
(defun fn-oert-hex (octets)
  (coerce (fn-nntp-octets-chars (fn-stx-hex-octets octets)) 'string))

; The owner holds at most four connections: reader C (conn 3) closes, so a
; reader opened after the revocation is conn 4.
(defconst *oer-base* (fn-own-close *ov-reader-c* 3))
(assert-event (< (len (fn-own-conns *oer-base*)) (nfix (fn-own-max-conns *oer-base*))))
; The revocation: the principal's tombstone, the next keyring generation,
; completed durably after the rotation (the rotation trace's pattern).
(make-event
 `(defconst *oer-revocation*
    ',(fn-hl-revoke-event 3 3 3 3 *sit-principal*
                          (fn-sn-keyring-snapshots (fn-own-store *oer-base*)))))
(assert-event (fn-stxk-p *oer-revocation*))
(assert-event (equal (fn-sn-identity-next (fn-own-store *oer-base*)) 3))
(assert-event
 (equal (fn-stxk-context-kind
         (fn-replay-identity-step
          (fn-sn-identity-context (fn-own-store *oer-base*))
          *oer-revocation*))
        :ok))
(defconst *oer-revocation-events*
  (list '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare-identity *oer-revocation*))
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        '(:complete)))
(make-event `(defconst *oer-revoked*
               ',(fn-own-run (fn-own-step *oer-base* '(:begin 1))
                             *oer-revocation-events*)))
(defconst *oer-reader-d* (cdr (fn-own-open *oer-revoked* nil)))

; ---------------------------------------------------------------------------
; The three reachable states, over the host-called fn-own-read.
(defconst *oer-hex* (fn-oert-hex *sit-principal*))
(assert-event
 (equal (fn-served-reply-octets (car (fn-own-read *ov-reader-b* 2 *oer-hdr*)))
        (fn-oert-reply (concatenate 'string "active " *oer-hex* " keyring 1"))))
(assert-event
 (equal (fn-served-reply-octets (car (fn-own-read *ov-reader-c* 3 *oer-hdr*)))
        (fn-oert-reply (concatenate 'string "retired " *oer-hex* " keyring 2"))))
(assert-event
 (equal (fn-served-reply-octets (car (fn-own-read *oer-reader-d* 4 *oer-hdr*)))
        (fn-oert-reply (concatenate 'string "revoked " *oer-hex* " keyring 3"))))
; The historical verdict is the same line on all three readers.
(assert-event
 (equal (fn-served-reply-octets (car (fn-own-read *oer-reader-d* 4 *ov-hdr*)))
        (fn-served-reply-octets (car *ov-read-b*))))
; Pinning: reader B, opened before the rotation and the revocation, still
; sees the enrollment its view was committed with.
(assert-event
 (equal (fn-served-reply-octets (car (fn-own-read *oer-reader-d* 2 *oer-hdr*)))
        (fn-oert-reply (concatenate 'string "active " *oer-hex* " keyring 1"))))
; Reader A, pinned before the publication, has no such article: 430.
(assert-event
 (equal (fn-served-reply-octets (car (fn-own-read *oer-reader-d* 0 *oer-hdr*)))
        (fn-oert-line "430 no article with that message-id")))

; fn-own-reader-opened-after-completion-pins-the-finished-keyring, witnessed:
; the revocation's completing owner, a reader opened after (:complete).
(make-event
 `(defconst *oer-completing*
    ',(fn-own-run (fn-own-step *oer-base* '(:begin 1))
                  (butlast *oer-revocation-events* 1))))
(assert-event (fn-sn-completion-enabledp (fn-own-store *oer-completing*)))
(make-event
 `(defconst *oer-after*
    ',(cdr (fn-own-open (fn-own-step *oer-completing* '(:complete)) nil))))
(assert-event
 (equal (fn-enr-pin-keyring
         (fn-own-conn-control
          (fn-own-find-conn (fn-own-next-id *oer-completing*)
                            (fn-own-conns *oer-after*))))
        (fn-sn-keyring-snapshots (fn-sn-finish (fn-own-store *oer-completing*)))))
(assert-event (equal (fn-stxk-profile
                      (car (fn-sn-keyring-snapshots
                            (fn-sn-finish (fn-own-store *oer-completing*)))))
                     *fn-hl-revoked-profile*))
; Teeth: reader B (conn 2), opened before the rotation and the revocation,
; did not pin the finished keyring.
(assert-event (fn-own-find-conn 2 (fn-own-conns *oer-after*)))
(must-fail
 (thm (equal (fn-enr-pin-keyring
              (fn-own-conn-control
               (fn-own-find-conn 2 (fn-own-conns *oer-after*))))
             (fn-sn-keyring-snapshots
              (fn-sn-finish (fn-own-store *oer-completing*))))))

; ---------------------------------------------------------------------------
; PRF-168 keystone fn-own-read-hdr-fn-enrollment-is-the-pinned-enrollment:
; the hypothesis vector in the theorem's order (the fn-octl-reader-hyps
; conjunction is literal 7) and its right-hand side.
(defun fn-oert-hyps (o id prefix byte)
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (w0 (fn-own-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (events (fn-wire-result-events (fn-wire-feed-byte w1 byte)))
         (line (cadr (car events)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (as (fn-own-conn-live-session o conn))
         (tokens (fn-nntp-tokenize line)))
    (list (and conn t)
          (fn-wire-statep w0)
          (not (equal (fn-wire-state-mode w0) :closed))
          (not (fn-wire-result-events (fn-wire-feed-proper w0 prefix)))
          (equal events (list (list :command line)))
          (not (equal (fn-wire-state-mode w2) :closed))
          (and (fn-octl-reader-hyps as tokens line) t)
          (consp (cddr tokens))
          (null (cdddr tokens))
          (fn-nntp-keywordp (car tokens) "HDR")
          (fn-nntp-keywordp (cadr tokens) ":FN-ENROLLMENT")
          (fn-nntp-message-id-tokenp (caddr tokens))
          (fn-octet-listp (caddr tokens))
          (and (fn-own-conn-group-index conn) t)
          (consp (fn-midx-lookup (fn-nntp-token-string (caddr tokens))
                                 (fn-own-conn-index conn))))))

(defun fn-oert-rhs (o id prefix byte)
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (w0 (fn-own-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (line (cadr (car (fn-wire-result-events (fn-wire-feed-byte w1 byte)))))
         (ns (fn-post-session-base
              (fn-peer-session-base
               (fn-auth-session-base (fn-own-conn-live-session o conn)))))
         (tokens (fn-nntp-tokenize line))
         (msgid (fn-nntp-token-string (caddr tokens))))
    (fn-nntp-result-effects
     (fn-nntp-multi ns (fn-nntp-hdr-initial nil)
                    (list (fn-nntp-hdr-line
                           (fn-nntp-decimal-field 0)
                           (fn-enr-item
                            (fn-stx-reader-lookup msgid (fn-own-conn-verdicts conn))
                            (fn-own-conn-control conn))))))))

(defun fn-oert-all (n) (if (zp n) nil (cons t (fn-oert-all (1- n)))))
(defun fn-oert-only-false (i n) (update-nth i nil (fn-oert-all n)))

; Reachable witnesses: every premise holds on readers B, C and D, the reply
; is the right-hand side, and the three items differ.
(assert-event (equal (fn-oert-hyps *ov-reader-b* 2 *oer-prefix* *oer-lf*) (fn-oert-all 15)))
(assert-event (equal (fn-oert-hyps *ov-reader-c* 3 *oer-prefix* *oer-lf*) (fn-oert-all 15)))
(assert-event (equal (fn-oert-hyps *oer-reader-d* 4 *oer-prefix* *oer-lf*) (fn-oert-all 15)))
(assert-event (equal (car (fn-own-read *ov-reader-b* 2 *oer-hdr*))
                     (fn-oert-rhs *ov-reader-b* 2 *oer-prefix* *oer-lf*)))
(assert-event (equal (car (fn-own-read *ov-reader-c* 3 *oer-hdr*))
                     (fn-oert-rhs *ov-reader-c* 3 *oer-prefix* *oer-lf*)))
(assert-event (equal (car (fn-own-read *oer-reader-d* 4 *oer-hdr*))
                     (fn-oert-rhs *oer-reader-d* 4 *oer-prefix* *oer-lf*)))

; Without the article in the pinned trie (premise 15): a Message-ID reader D's
; view does not serve answers 430.  (Reader A, pinned before the publication,
; also answers 430 above, but it has no buckets either: premises 14 and 15.)
(defconst *oer-nosuch* (fn-oert-line "HDR :fn-enrollment <nosuch@example.invalid>"))
(defconst *oer-nosuch-prefix* (butlast *oer-nosuch* 1))
(assert-event (equal (fn-oert-hyps *oer-reader-d* 4 *oer-nosuch-prefix* *oer-lf*)
                     (fn-oert-only-false 14 15)))
(assert-event (equal (fn-served-reply-octets (car (fn-own-read *oer-reader-d* 4 *oer-nosuch*)))
                     (fn-oert-line "430 no article with that message-id")))
(must-fail
 (thm (equal (car (fn-own-read *oer-reader-d* 4 *oer-nosuch*))
             (fn-oert-rhs *oer-reader-d* 4 *oer-nosuch-prefix* *oer-lf*))))

; Without the framing premise (5): the read stops before its LF.
(defconst *oer-cut* (butlast *oer-prefix* 1))
(defconst *oer-cr* (car (last *oer-prefix*)))
(assert-event (equal (take 4 (fn-oert-hyps *oer-reader-d* 4 *oer-cut* *oer-cr*))
                     (fn-oert-all 4)))
(assert-event (not (nth 4 (fn-oert-hyps *oer-reader-d* 4 *oer-cut* *oer-cr*))))
(must-fail
 (thm (equal (car (fn-own-read *oer-reader-d* 4 (append *oer-cut* (list *oer-cr*))))
             (fn-oert-rhs *oer-reader-d* 4 *oer-cut* *oer-cr*))))

; Without :FN-ENROLLMENT (premise 11): HDR :fn-verified on the same article
; answers the historical verdict, not the enrollment.
(defconst *oer-verified-prefix* (butlast *ov-hdr* 1))
(assert-event (equal (fn-oert-hyps *oer-reader-d* 4 *oer-verified-prefix* *oer-lf*)
                     (fn-oert-only-false 10 15)))
(must-fail
 (thm (equal (car (fn-own-read *oer-reader-d* 4 *ov-hdr*))
             (fn-oert-rhs *oer-reader-d* 4 *oer-verified-prefix* *oer-lf*))))

; Without HDR (premise 10): OVER on the same Message-ID-shaped argument list.
(defconst *oer-xhdr* (fn-oert-line "XHDR :fn-enrollment <carried@example.invalid>"))
(defconst *oer-xhdr-prefix* (butlast *oer-xhdr* 1))
(assert-event (equal (fn-oert-hyps *oer-reader-d* 4 *oer-xhdr-prefix* *oer-lf*)
                     (fn-oert-only-false 9 15)))
(must-fail
 (thm (equal (car (fn-own-read *oer-reader-d* 4 *oer-xhdr*))
             (fn-oert-rhs *oer-reader-d* 4 *oer-xhdr-prefix* *oer-lf*))))

; Without the Message-ID token (premise 12): a range argument answers 501.
; No trie key is a non-Message-ID token, so premise 15 fails with it: this
; witness removes 12 and 15 together (no reachable state removes 12 alone).
(defconst *oer-range* (fn-oert-line "HDR :fn-enrollment 1-"))
(defconst *oer-range-prefix* (butlast *oer-range* 1))
(assert-event (equal (fn-oert-hyps *oer-reader-d* 4 *oer-range-prefix* *oer-lf*)
                     (update-nth 14 nil (fn-oert-only-false 11 15))))
(assert-event (equal (fn-served-reply-octets (car (fn-own-read *oer-reader-d* 4 *oer-range*)))
                     (fn-oert-line "501 syntax error")))
(must-fail
 (thm (equal (car (fn-own-read *oer-reader-d* 4 *oer-range*))
             (fn-oert-rhs *oer-reader-d* 4 *oer-range-prefix* *oer-lf*))))

; Without the one-argument shape (premise 9): a trailing argument.
(defconst *oer-extra* (fn-oert-line "HDR :fn-enrollment <carried@example.invalid> x"))
(defconst *oer-extra-prefix* (butlast *oer-extra* 1))
(assert-event (equal (fn-oert-hyps *oer-reader-d* 4 *oer-extra-prefix* *oer-lf*)
                     (fn-oert-only-false 8 15)))
(must-fail
 (thm (equal (car (fn-own-read *oer-reader-d* 4 *oer-extra*))
             (fn-oert-rhs *oer-reader-d* 4 *oer-extra-prefix* *oer-lf*))))

; Without an argument (premise 8): `HDR :fn-enrollment' alone answers 501.
(defconst *oer-bare* (fn-oert-line "HDR :fn-enrollment"))
(defconst *oer-bare-prefix* (butlast *oer-bare* 1))
(assert-event (equal (nth 7 (fn-oert-hyps *oer-reader-d* 4 *oer-bare-prefix* *oer-lf*)) nil))
(must-fail
 (thm (equal (car (fn-own-read *oer-reader-d* 4 *oer-bare*))
             (fn-oert-rhs *oer-reader-d* 4 *oer-bare-prefix* *oer-lf*))))

; Without a connection (premise 1): an unknown id reads nothing.
(assert-event (null (car (fn-own-read *oer-reader-d* 99 *oer-hdr*))))
(must-fail
 (thm (equal (car (fn-own-read *oer-reader-d* 99 (append *oer-prefix* (list *oer-lf*))))
             (fn-oert-rhs *oer-reader-d* 99 *oer-prefix* *oer-lf*))))
