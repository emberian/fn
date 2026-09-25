; fn: the peer arm of the served step with no node recognizer in its guard.
;
; fn-pix-peer-step-pinned (books/peer-offer-indexed.lisp) tests
; fn-peer-sessionp on every event, and so fn-node-statep of the session's
; node, O(N^2) in the archive.  It cannot drop the test and stay
; guard-verified: its transit arms call fn-peer-command, whose guard is
; fn-peer-sessionp, and fn-peer-decide-offer, whose guard is (fn-node-statep
; node); fn-peer-step, the transfer arm, tests fn-peer-sessionp again
; (planning/evidence/served-path-cost-2026-09-24.md, finding 1).
;
; What those guards are for is one call: fn-retain-admissiblep, whose guard
; is fn-retain-statep of the node's retention.  Every other function the peer
; arms call is guard t.  This book is the peer arm with that call replaced by
; fn-pgc-retain-admissiblep, which is the reference's executable body with
; guard t, so the arm's guard is fn-pgc-peer-sessionp: the peer session
; recognizer with its node conjunct removed.  The node is a logical premise
; only.  Each copy is proved EQUAL to its reference under (fn-node-statep
; node) of the session's node, and the peer arm under fn-peer-sessionp,
; which the carried step (fn-scar-peer-step-pinned, books/served-carried.lisp)
; supplies from the owner's node premise by one pointer comparison.

(in-package "ACL2")
(include-book "peer-offer-indexed")

; -----------------------------------------------------------------------------
; The retention test, guard t

(defun fn-pgc-obligation-ids (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (fn-retain-obligation-id (car xs))
            (fn-pgc-obligation-ids (cdr xs)))
    nil))

(defun fn-pgc-release-ids (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (fn-retain-release-id (car xs))
            (fn-pgc-release-ids (cdr xs)))
    nil))

(local (defthm fn-pgc-obligation-ids-is-retain-obligation-ids
  (equal (fn-pgc-obligation-ids xs) (fn-retain-obligation-ids xs))
  :hints (("Goal" :in-theory (enable fn-pgc-obligation-ids
                                     fn-retain-obligation-ids)))))

(local (defthm fn-pgc-release-ids-is-retain-release-ids
  (equal (fn-pgc-release-ids xs) (fn-retain-release-ids xs))
  :hints (("Goal" :in-theory (enable fn-pgc-release-ids
                                     fn-retain-release-ids)))))

; fn-retain-admissiblep's :exec body, whose only guard need is the two
; numbers it adds and compares; those are tested here, and are true under
; fn-retain-statep, which the reference's :logic body conjoins.
(defun fn-pgc-retain-admissiblep (s id subject kind evidence charge)
  (declare (xargs :guard t))
  (and (stringp id)
       (stringp subject)
       (fn-retain-kindp kind)
       (fn-provp evidence)
       (posp charge)
       (not (or (member-equal id (fn-pgc-obligation-ids (fn-retain-pins s)))
                (member-equal id (fn-pgc-release-ids (fn-retain-releases s)))))
       (natp (fn-retain-reserved s))
       (natp (fn-retain-capacity s))
       (<= (+ (fn-retain-reserved s) charge)
           (fn-retain-capacity s))))

(defthm fn-pgc-retain-admissiblep-is-retain-admissiblep
  (implies (fn-retain-statep s)
           (equal (fn-pgc-retain-admissiblep s id subject kind evidence charge)
                  (fn-retain-admissiblep s id subject kind evidence charge)))
  :hints (("Goal" :in-theory (e/d (fn-pgc-retain-admissiblep
                                   fn-retain-admissiblep fn-retain-known-idp
                                   fn-retain-statep)
                                  (fn-retain-obligation-ids
                                   fn-retain-release-ids
                                   fn-retain-obligation-listp
                                   fn-retain-release-listp
                                   fn-retain-no-duplicatesp
                                   fn-retain-sum fn-retain-kindp fn-provp)))))

; -----------------------------------------------------------------------------
; The offer decision

(defun fn-pgc-decide-offer (node cfg peer session msgid clock inflight trie arts)
  (declare (xargs :guard t)
           (ignorable session clock))
  (let ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
    (cond ((not record) (fn-peer-decision :refuse :not-a-peer))
          ((null (fn-cfg-peer-inbound record))
           (fn-peer-decision :refuse :no-inbound))
          ((not (fn-af-message-idp msgid))
           (fn-peer-decision :refuse :message-id-syntax))
          ((fn-pix-history-hasp (fn-record-octets-string msgid) node trie arts)
           (fn-peer-decision :have :history))
          ((fn-peer-stagedp (fn-record-octets-string msgid) node)
           (fn-peer-decision :defer :staged))
          ((equal (fn-state-fenced (fn-node-acceptance node)) t)
           (fn-peer-decision :defer :fenced))
          ((<= (fn-cfg-peer-inbound-max-inflight record) (nfix inflight))
           (fn-peer-decision :defer :inflight-limit))
          ((not (fn-pgc-retain-admissiblep (fn-node-retention node)
                                           (fn-peer-probe-obligation-id msgid)
                                           (fn-peer-probe-subject) :archive
                                           (fn-peer-evidence peer cfg)
                                           (fn-charge-for-payload 0)))
           (fn-peer-decision :defer :capacity))
          (t (fn-peer-decision :want nil)))))

(local (defthm fn-pgc-node-statep-retention
  (implies (fn-node-statep node)
           (fn-retain-statep (fn-node-retention node)))
  :hints (("Goal" :in-theory (enable fn-node-statep)))))

(defthm fn-pgc-decide-offer-is-pix-decide-offer
  (implies (fn-node-statep node)
           (equal (fn-pgc-decide-offer node cfg peer session msgid clock
                                       inflight trie arts)
                  (fn-pix-decide-offer node cfg peer session msgid clock
                                       inflight trie arts)))
  :hints (("Goal" :in-theory (e/d (fn-pgc-decide-offer fn-pix-decide-offer)
                                  (fn-pgc-retain-admissiblep
                                   fn-retain-admissiblep
                                   fn-pix-history-hasp fn-node-statep
                                   fn-retain-statep
                                   fn-peer-stagedp fn-cfg-peer-find
                                   fn-af-message-idp fn-record-octets-string)))))

; -----------------------------------------------------------------------------
; The transit commands

; The peer session recognizer with its node conjunct removed: what the peer
; arm's guard obligations use.
(defun fn-pgc-peer-sessionp (x)
  (declare (xargs :guard t))
  (and (fn-peer-session-shapep x)
       (fn-post-sessionp (fn-peer-session-base x))
       (stringp (fn-peer-session-peer x))
       (fn-cfgp (fn-peer-session-cfg x))
       (fn-peer-transferp (fn-peer-session-transfer x))
       (natp (fn-peer-session-inflight x))))

(defthm fn-pgc-peer-sessionp-of-peer-sessionp
  (implies (and (fn-peer-sessionp x) (fn-peer-session-peer x))
           (fn-pgc-peer-sessionp x))
  :hints (("Goal" :in-theory (enable fn-peer-sessionp fn-pgc-peer-sessionp))))

(defun fn-pgc-peer-command (ps keyword args trie arts)
  (declare (xargs :guard (fn-pgc-peer-sessionp ps) :verify-guards nil))
  (let ((node (fn-peer-session-node ps))
        (cfg (fn-peer-session-cfg ps))
        (peer (fn-peer-session-peer ps))
        (inflight (fn-peer-session-inflight ps)))
    (cond
     ((fn-nntp-keywordp keyword "IHAVE")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps "501 syntax error") nil)
        (let ((d (fn-pgc-decide-offer node cfg peer ps (car args) nil inflight
                                      trie arts)))
          (if (equal (fn-peer-decision-kind d) :want)
              (fn-post-make-result
               (fn-peer-with-transfer ps (list :ihave (car args)) inflight)
               (append (fn-peer-single ps (fn-peer-ihave-offer-line d))
                       (list (fn-nntp-begin-article-effect)))
               nil)
            (fn-post-make-result ps (fn-peer-single ps (fn-peer-ihave-offer-line d))
                                 nil)))))
     ((fn-nntp-keywordp keyword "CHECK")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps "501 syntax error") nil)
        (let ((d (fn-pgc-decide-offer node cfg peer ps (car args) nil inflight
                                      trie arts)))
          (fn-post-make-result
           (if (equal (fn-peer-decision-kind d) :want)
               (fn-peer-with-transfer ps nil (+ 1 (nfix inflight)))
             ps)
           (fn-peer-echo-reply (fn-peer-check-code d) (car args))
           nil))))
     ((fn-nntp-keywordp keyword "TAKETHIS")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps "501 syntax error") nil)
        (fn-post-make-result
         (fn-peer-with-transfer ps (list :takethis (car args))
                                (nfix (- (nfix inflight) 1)))
         (list (fn-nntp-begin-article-effect))
         nil)))
     ((and (fn-nntp-keywordp keyword "MODE")
           (consp args) (null (cdr args))
           (fn-nntp-keywordp (car args) "STREAM"))
      (fn-post-make-result ps (fn-peer-single ps "203 streaming permitted") nil))
     ((and (fn-nntp-keywordp keyword "CAPABILITIES")
           (or (null args)
               (and (consp args) (null (cdr args))
                    (fn-nntp-keyword-tokenp (car args)))))
      (fn-post-make-result
       ps
       (fn-nntp-result-effects
        (fn-nntp-multi (fn-peer-reader-session ps)
                       "101 capability list follows"
                       (fn-peer-capability-lines
                        (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))
                        nil)))
       nil))
     (t nil))))

(defthm fn-pgc-peer-command-is-peer-command
  (implies (and (fn-node-statep (fn-peer-session-node ps))
                (fn-midx-correspondencep trie arts))
           (equal (fn-pgc-peer-command ps keyword args trie arts)
                  (fn-peer-command ps keyword args)))
  :hints (("Goal" :in-theory (e/d (fn-pgc-peer-command fn-peer-command)
                                  (fn-pgc-decide-offer fn-peer-decide-offer
                                   fn-pix-decide-offer
                                   fn-node-statep fn-midx-correspondencep
                                   fn-nntp-keywordp fn-peer-msgid-argp
                                   fn-peer-single fn-peer-echo-reply
                                   fn-peer-ihave-offer-line fn-peer-check-code
                                   fn-peer-with-transfer fn-peer-capability-lines)))))

(local (defthm fn-pgc-msgid-argp-forward
  (implies (fn-peer-msgid-argp args)
           (and (consp args) (null (cdr args))
                (fn-nntp-printable-tokenp (car args))
                (fn-af-message-idp (car args))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-peer-msgid-argp)))))

(local (defthm fn-pgc-peer-single-true-listp
  (true-listp (fn-peer-single ps text))
  :hints (("Goal" :in-theory (enable fn-peer-single fn-nntp-result-effects
                                     fn-nntp-single fn-nntp-make-result)))))

(verify-guards fn-pgc-peer-command
  :hints (("Goal" :in-theory (disable fn-pgc-decide-offer fn-peer-command
                                      fn-peer-single fn-peer-msgid-argp))))

; -----------------------------------------------------------------------------
; The transfer arm: fn-peer-step's branch for a session awaiting the transit
; article, without fn-peer-step's own session test.

(local (defthm fn-pgc-transferp-forward
  (implies (and (fn-peer-transferp x) x)
           (and (consp x) (consp (cdr x))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-transferp))
                                  ((:d fn-nntp-printable-tokenp)
                                   (:d fn-af-message-idp)))))))

(defun fn-pgc-transfer-step (ps wire-event)
  (declare (xargs :guard (and (fn-pgc-peer-sessionp ps)
                              (fn-peer-session-transfer ps))))
  (let ((transfer (fn-peer-session-transfer ps)))
    (if (and (consp wire-event)
             (equal (car wire-event) :article)
             (consp (cdr wire-event))
             (null (cdr (cdr wire-event))))
        (fn-post-make-result
         (fn-peer-with-transfer ps nil (fn-peer-session-inflight ps))
         nil
         (fn-peer-make-submission (fn-peer-session-peer ps)
                                  (car transfer) (car (cdr transfer))
                                  (fn-post-body-octets (car (cdr wire-event)))))
      (fn-post-make-result
       (fn-peer-with-transfer ps nil (fn-peer-session-inflight ps))
       (append (fn-peer-single
                ps (if (equal (car transfer) :ihave)
                       "436 transfer failed; the article was not received"
                     "436 the article was not received; closing"))
               (list (fn-nntp-close-effect)))
       nil))))

(defthm fn-pgc-transfer-step-is-peer-step
  (implies (and (fn-peer-sessionp ps)
                (fn-peer-session-peer ps)
                (equal (fn-nntp-session-openp (fn-peer-reader-session ps)) t)
                (fn-peer-session-transfer ps))
           (equal (fn-peer-step ps archive config observation injection
                                wire-event)
                  (fn-pgc-transfer-step ps wire-event)))
  :hints (("Goal" :in-theory (e/d (fn-pgc-transfer-step fn-peer-step)
                                  (fn-peer-sessionp fn-peer-command
                                   fn-peer-delegate fn-peer-with-transfer
                                   fn-peer-single fn-peer-make-submission
                                   fn-post-body-octets)))))

; -----------------------------------------------------------------------------
; The peer arm: fn-pix-peer-step-pinned past its first two branches, for a
; peer session, with no session recognizer evaluated.  What the peer commands
; do not answer goes to the reader delegate whose Message-ID retrieval walks
; the trie by index (fn-pix-peer-delegate-pinned, equal to
; fn-peer-delegate-pinned with no hypothesis: books/peer-offer-indexed.lisp).

(defun fn-pgc-peer-arm
    (ps trie arts archive index verdicts config observation injection wire-event)
  (declare (xargs :guard (fn-pgc-peer-sessionp ps)))
  (cond
   ((not (equal (fn-nntp-session-openp (fn-peer-reader-session ps)) t))
    (fn-pix-peer-delegate-pinned ps archive index verdicts config observation
                                 injection wire-event))
   ((fn-peer-session-transfer ps) (fn-pgc-transfer-step ps wire-event))
   ((and (consp wire-event)
         (equal (car wire-event) :command)
         (consp (cdr wire-event))
         (null (cdr (cdr wire-event)))
         (fn-nntp-command-inputp (car (cdr wire-event))))
    (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
      (if (and (consp tokens)
               (fn-nntp-keyword-tokenp (car tokens))
               (fn-nntp-command-arguments-at-mostp tokens))
          (let ((r (fn-pgc-peer-command ps (car tokens) (cdr tokens) trie arts)))
            (if r r
              (fn-pix-peer-delegate-pinned ps archive index verdicts config
                                           observation injection wire-event)))
        (fn-pix-peer-delegate-pinned ps archive index verdicts config observation
                                     injection wire-event))))
   (t (fn-pix-peer-delegate-pinned ps archive index verdicts config observation
                                   injection wire-event))))

; KEYSTONE.  On a peer session, the arm is the reference step: the premise
; is fn-peer-sessionp (so fn-node-statep of the session's node) and the
; trie's correspondence; the arm itself evaluates neither.
(defthm fn-pgc-peer-arm-is-peer-step-pinned
  (implies (and (fn-peer-sessionp ps)
                (fn-peer-session-peer ps)
                (fn-midx-correspondencep trie arts))
           (equal (fn-pgc-peer-arm ps trie arts archive index verdicts config
                                   observation injection wire-event)
                  (fn-peer-step-pinned ps archive index verdicts config
                                       observation injection wire-event)))
  :hints (("Goal" :in-theory (e/d (fn-pgc-peer-arm fn-peer-step-pinned
                                   fn-peer-sessionp)
                                  (fn-pgc-peer-command fn-peer-command
                                   fn-pgc-transfer-step fn-peer-step
                                   fn-node-statep fn-cfgp fn-post-sessionp
                                   fn-peer-transferp fn-midx-correspondencep
                                   fn-peer-delegate-pinned fn-pix-peer-delegate-pinned
                                   fn-nntp-tokenize fn-nntp-command-inputp)))))

(in-theory (disable fn-pgc-obligation-ids fn-pgc-release-ids
                    fn-pgc-retain-admissiblep fn-pgc-decide-offer
                    fn-pgc-peer-sessionp fn-pgc-peer-command
                    fn-pgc-transfer-step fn-pgc-peer-arm))
