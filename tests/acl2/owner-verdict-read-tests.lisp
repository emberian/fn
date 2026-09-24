; Teeth for P8 / PRF-026: the kind-4 finish keystone
; (books/hybrid-lifecycle-store-invariants) and the served HDR :fn-verified
; keystone (books/owner-verdict-read), on the reachable T10a trace that
; owner-verdict-tests.lisp already steps through fn-own-step.
(in-package "ACL2")
(include-book "owner-verdict-tests")
(include-book "../../books/owner-verdict-read")
(include-book "../../books/hybrid-lifecycle-store-invariants")
(include-book "std/testing/must-fail" :dir :system)

; The Store one step before the owner's (:complete): the kind-4 composite is
; the pending completion record.
(make-event
 `(defconst *ovr-completing*
    ',(fn-own-store (fn-own-run *ov-begun* (butlast *ov-post-events* 1)))))
(make-event
 `(defconst *ovr-linked*
    ',(fn-own-store (fn-own-run *ov-begun* (butlast *ov-post-events* 2)))))

; ---------------------------------------------------------------------------
; Keystone 1: fn-sn-finish-of-a-kind-4-acceptance-records-its-verdict.
(make-event
 `(defconst *ovr-kind4*
    ',(fn-hls-kind4-verdict-event (fn-sn-completion-record *ovr-completing*))))
(defun fn-ovrt-finish-rhs (v)
  (fn-stx-make-verdict (fn-stxe-token v) (fn-stxe-detail v)
                       (fn-stxe-keyring-generation v)))

; Reachable witness: both premises hold, the lookup was empty before, and the
; finished Store answers the kind-4 event's verdict for its Message-ID.
(assert-event (fn-sn-completion-enabledp *ovr-completing*))
(assert-event (fn-stxa-p (fn-sn-completion-record *ovr-completing*)))
(assert-event (equal (fn-stxe-msgid *ovr-kind4*)
                     "<carried@example.invalid>"))
(assert-event (null (fn-sn-verdict-lookup *ovr-completing*
                                          (fn-stxe-msgid *ovr-kind4*))))
(assert-event (equal (fn-stxe-token *ovr-kind4*) :verified))
(assert-event (equal (fn-sn-verdict-lookup (fn-sn-finish *ovr-completing*)
                                           (fn-stxe-msgid *ovr-kind4*))
                     (fn-ovrt-finish-rhs *ovr-kind4*)))

; Without fn-sn-completion-enabledp: the same kind-4 completion record, with
; the identity sequence one ahead (the model's own advance), so the identity
; step faults, the gate is closed and finish is a no-op.
(make-event
 `(defconst *ovr-off-sequence* ',(fn-sn-advance-identity-next *ovr-completing*)))
(assert-event (fn-stxa-p (fn-sn-completion-record *ovr-off-sequence*)))
(assert-event (not (fn-sn-completion-enabledp *ovr-off-sequence*)))
(assert-event (not (equal (fn-sn-verdict-lookup
                           (fn-sn-finish *ovr-off-sequence*)
                           (fn-stxe-msgid *ovr-kind4*))
                          (fn-ovrt-finish-rhs *ovr-kind4*))))
(must-fail
 (thm (equal (fn-sn-verdict-lookup
              (fn-sn-finish *ovr-off-sequence*)
              (fn-stxe-msgid (fn-hls-kind4-verdict-event
                              (fn-sn-completion-record *ovr-off-sequence*))))
             (fn-ovrt-finish-rhs
              (fn-hls-kind4-verdict-event
               (fn-sn-completion-record *ovr-off-sequence*))))))

; Without fn-stxa-p: a reachable enabled kind-3 keyring completion (the
; rotation trace of owner-verdict-tests).  It records no verdict.
(make-event
 `(defconst *ovr-rotating*
    ',(fn-own-store (fn-own-run (fn-own-step *ov-reader-b* '(:begin 1))
                                (butlast *ov-rotation-events* 1)))))
(assert-event (fn-sn-completion-enabledp *ovr-rotating*))
(assert-event (not (fn-stxa-p (fn-sn-completion-record *ovr-rotating*))))
(assert-event (fn-stxk-p (fn-sn-completion-record *ovr-rotating*)))
(assert-event (equal (fn-sn-verdicts (fn-sn-finish *ovr-rotating*))
                     (fn-sn-verdicts *ovr-rotating*)))
(must-fail
 (thm (equal (fn-sn-verdict-lookup
              (fn-sn-finish *ovr-rotating*)
              (fn-stxe-msgid (fn-hls-kind4-verdict-event
                              (fn-sn-completion-record *ovr-rotating*))))
             (fn-ovrt-finish-rhs
              (fn-hls-kind4-verdict-event
               (fn-sn-completion-record *ovr-rotating*))))))

; Sibling: every other Message-ID keeps its lookup.
(assert-event
 (equal (fn-sn-verdict-lookup (fn-sn-finish *ovr-completing*)
                              "<other@example.invalid>")
        (fn-sn-verdict-lookup *ovr-completing*
                              "<other@example.invalid>")))

; ---------------------------------------------------------------------------
; Keystone 2: fn-own-reader-opened-after-completion-pins-the-finished-verdicts.
; Witness: the owner of owner-verdict-tests at :completing, a reader opened
; after (:complete).  Teeth: reader A (connection 0) was opened before the
; completion and its pin is not the finished verdict list.
(make-event
 `(defconst *ovr-owner-completing*
    ',(fn-own-run *ov-begun* (butlast *ov-post-events* 1))))
(assert-event (fn-sn-completion-enabledp (fn-own-store *ovr-owner-completing*)))
(assert-event (< (len (fn-own-conns *ovr-owner-completing*))
                 (nfix (fn-own-max-conns *ovr-owner-completing*))))
(make-event
 `(defconst *ovr-reader-after*
    ',(cdr (fn-own-open (fn-own-step *ovr-owner-completing* '(:complete)) nil))))
(assert-event
 (equal (fn-own-conn-verdicts
         (fn-own-find-conn (fn-own-next-id *ovr-owner-completing*)
                           (fn-own-conns *ovr-reader-after*)))
        (fn-sn-verdicts (fn-sn-finish (fn-own-store *ovr-owner-completing*)))))
(assert-event (consp (fn-sn-verdicts (fn-sn-finish
                                      (fn-own-store *ovr-owner-completing*)))))
(assert-event (not (equal (fn-own-conn-verdicts
                           (fn-own-find-conn 0 (fn-own-conns *ovr-reader-after*)))
                          (fn-sn-verdicts (fn-sn-finish
                                           (fn-own-store *ovr-owner-completing*))))))
(must-fail
 (thm (equal (fn-own-conn-verdicts
              (fn-own-find-conn 0 (fn-own-conns *ovr-reader-after*)))
             (fn-sn-verdicts (fn-sn-finish
                              (fn-own-store *ovr-owner-completing*))))))

; ---------------------------------------------------------------------------
; Keystone 3: fn-own-read-hdr-fn-verified-is-the-pinned-verdict.
; The hypothesis vector, in the theorem's order, and its right-hand side.
(defun fn-ovrt-hyps (o id prefix byte)
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (w0 (fn-own-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (events (fn-wire-result-events (fn-wire-feed-byte w1 byte)))
         (line (cadr (car events)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (as (fn-own-conn-live-session o conn))
         (ps (fn-auth-session-base as))
         (pst (fn-peer-session-base ps))
         (ns (fn-post-session-base pst))
         (tokens (fn-nntp-tokenize line)))
    (list (and conn t)
          (fn-wire-statep w0)
          (not (equal (fn-wire-state-mode w0) :closed))
          (not (fn-wire-result-events (fn-wire-feed-proper w0 prefix)))
          (equal events (list (list :command line)))
          (not (equal (fn-wire-state-mode w2) :closed))
          (fn-auth-sessionp as)
          (not (fn-auth-session-handshakingp as))
          (not (fn-auth-gatedp as (car tokens)))
          (fn-peer-sessionp ps)
          (null (fn-peer-session-peer ps))
          (fn-post-sessionp pst)
          (not (fn-post-session-awaiting pst))
          (fn-nntp-sessionp ns)
          (equal (fn-nntp-session-openp ns) t)
          (and (fn-nntp-session-projected ns) t)
          (fn-nntp-command-inputp line)
          (fn-nntp-command-arguments-at-mostp tokens)
          (consp (cddr tokens))
          (null (cdddr tokens))
          (fn-nntp-keyword-tokenp (car tokens))
          (fn-nntp-keywordp (car tokens) "HDR")
          (fn-nntp-keywordp (cadr tokens) ":FN-VERIFIED")
          (fn-nntp-message-id-tokenp (caddr tokens))
          (not (fn-nntp-range-okp (fn-nntp-parse-range (caddr tokens))))
          (consp (fn-find-article (fn-nntp-token-string (caddr tokens))
                                  (fn-state-articles
                                   (fn-own-conn-archive conn)))))))

(defun fn-ovrt-rhs (o id prefix byte)
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (w0 (fn-own-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (line (cadr (car (fn-wire-result-events (fn-wire-feed-byte w1 byte)))))
         (ns (fn-post-session-base
              (fn-peer-session-base
               (fn-auth-session-base (fn-own-conn-live-session o conn)))))
         (tokens (fn-nntp-tokenize line))
         (article (fn-find-article (fn-nntp-token-string (caddr tokens))
                                   (fn-state-articles
                                    (fn-own-conn-archive conn)))))
    (fn-nntp-result-effects
     (fn-nntp-multi ns (fn-nntp-hdr-initial nil)
                    (list (fn-nntp-hdr-line
                           (fn-nntp-decimal-field 0)
                           (fn-stx-reader-item
                            (fn-stx-reader-lookup
                             (fn-article-msgid article)
                             (fn-own-conn-verdicts conn)))))))))

(defun fn-ovrt-all-but (n)
  (if (zp n) nil (cons t (fn-ovrt-all-but (1- n)))))
(defun fn-ovrt-only-false (i n)
  (update-nth i nil (fn-ovrt-all-but n)))

(defconst *ovr-prefix* (butlast *ov-hdr* 1))
(defconst *ovr-lf* (car (last *ov-hdr*)))

; Reachable witness: reader B (connection 2), opened after the kind-4
; publication, one socket read of the HDR line.  Every premise holds and the
; reply is the verified item, which is not the "absent no-record" item.
(assert-event (equal (fn-ovrt-hyps *ov-reader-b* 2 *ovr-prefix* *ovr-lf*)
                     (fn-ovrt-all-but 26)))
(assert-event (equal (car (fn-own-read *ov-reader-b* 2
                                       (append *ovr-prefix* (list *ovr-lf*))))
                     (fn-ovrt-rhs *ov-reader-b* 2 *ovr-prefix* *ovr-lf*)))
(assert-event (equal (fn-served-reply-octets
                      (fn-ovrt-rhs *ov-reader-b* 2 *ovr-prefix* *ovr-lf*))
                     (fn-served-reply-octets (car *ov-read-b*))))
(assert-event (not (equal (fn-stx-reader-item
                           (fn-stx-reader-lookup
                            (fn-stxe-msgid *ovr-kind4*)
                            (fn-own-conn-verdicts
                             (fn-own-find-conn 2 (fn-own-conns *ov-reader-b*)))))
                          (fn-stx-reader-item nil))))

; Without the article in the pinned archive (premise 26): reader A pinned
; before the publication answers 430, not a verdict line.
(assert-event (equal (fn-ovrt-hyps *ov-reader-b* 0 *ovr-prefix* *ovr-lf*)
                     (fn-ovrt-only-false 25 26)))
(assert-event (not (equal (car (fn-own-read *ov-reader-b* 0 *ov-hdr*))
                          (fn-ovrt-rhs *ov-reader-b* 0 *ovr-prefix* *ovr-lf*))))
(must-fail
 (thm (equal (car (fn-own-read *ov-reader-b* 0 (append *ovr-prefix* (list *ovr-lf*))))
             (fn-ovrt-rhs *ov-reader-b* 0 *ovr-prefix* *ovr-lf*))))

; Without the framing premise (5): the read stops before its LF, so its last
; octet frames nothing and no reply is written.
(defconst *ovr-cut* (butlast *ovr-prefix* 1))
(defconst *ovr-cr* (car (last *ovr-prefix*)))
(assert-event (equal (take 4 (fn-ovrt-hyps *ov-reader-b* 2 *ovr-cut* *ovr-cr*))
                     (fn-ovrt-all-but 4)))
(assert-event (not (nth 4 (fn-ovrt-hyps *ov-reader-b* 2 *ovr-cut* *ovr-cr*))))
(assert-event (null (car (fn-own-read *ov-reader-b* 2 *ovr-prefix*))))
(assert-event (not (equal (car (fn-own-read *ov-reader-b* 2 *ovr-prefix*))
                          (fn-ovrt-rhs *ov-reader-b* 2 *ovr-cut* *ovr-cr*))))
(must-fail
 (thm (equal (car (fn-own-read *ov-reader-b* 2
                               (append *ovr-cut* (list *ovr-cr*))))
             (fn-ovrt-rhs *ov-reader-b* 2 *ovr-cut* *ovr-cr*))))

; Without the :fn-verified item (premise 23): HDR Subject for the same
; Message-ID answers the article's Subject, not the verdict.
(defconst *ovr-subject*
  (append (fn-nntp-string-octets "HDR Subject <carried@example.invalid>")
          '(13 10)))
(defconst *ovr-subject-prefix* (butlast *ovr-subject* 1))
(assert-event (equal (fn-ovrt-hyps *ov-reader-b* 2 *ovr-subject-prefix* *ovr-lf*)
                     (fn-ovrt-only-false 22 26)))
(assert-event (not (equal (car (fn-own-read *ov-reader-b* 2 *ovr-subject*))
                          (fn-ovrt-rhs *ov-reader-b* 2 *ovr-subject-prefix*
                                       *ovr-lf*))))
(must-fail
 (thm (equal (car (fn-own-read *ov-reader-b* 2
                               (append *ovr-subject-prefix* (list *ovr-lf*))))
             (fn-ovrt-rhs *ov-reader-b* 2 *ovr-subject-prefix* *ovr-lf*))))
