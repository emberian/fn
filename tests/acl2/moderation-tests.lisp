; Witnesses and teeth for P3, moderated groups (PRF-228, NNT-047):
; books/config.lisp (:set-group-moderation, code 23),
; books/config-invariants.lisp `fn-cfg-set-group-moderation-sets-the-moderation',
; books/native-admin.lisp (`group moderate'), books/owner-agent.lisp (the
; moderated entries in the posting configuration), books/moderation.lisp (the
; gate, the envelope, the session view), books/nntp-post.lisp (the three
; keystones over `fn-post-gated-decision' and the host-called
; `fn-nntp-post-step'), books/nntp-auth.lisp `fn-auth-moderation-config' and
; books/peer-inbound.lisp (the relay refusal).
(in-package "ACL2")
(include-book "../../books/nntp-auth")
(include-book "../../books/config-invariants")
(include-book "../../books/owner-agent")
(include-book "../../books/native-admin")
(include-book "../../books/account-list")
(include-book "std/testing/must-fail" :dir :system)

(defun mdt-o (s) (declare (xargs :guard (stringp s))) (fn-nntp-string-octets s))
(defconst *mdt-crlf* (coerce '(#\Return #\Newline) 'string))

; ---------------------------------------------------------------------------
; 1. The configuration: the delta, its code, its admission and its fold.

(defconst *mdt-stamp* (fn-clock-observation 0 0 0 nil))
(defconst *mdt-v1*
  (fn-cfg-apply (fn-cfg-empty-value) 1 *mdt-stamp*
                (list (fn-cfg-create-group "fn.test" *fn-cfg-default-policy-id*)
                      (fn-cfg-create-group "fn.mod" *fn-cfg-default-policy-id*)
                      (fn-cfg-create-group "fn.queue" *fn-cfg-default-policy-id*))))
(defconst *mdt-delta*
  (fn-cfg-set-group-moderation "fn.mod" "fn.queue" "" '("alice" "bob")))
(defconst *mdt-v2* (fn-cfg-apply-delta *mdt-v1* 2 *mdt-stamp* *mdt-delta*))
(assert-event (fn-cfg-valuep *mdt-v1*))
(assert-event (fn-cfg-valuep *mdt-v2*))
(assert-event (equal (fn-cfg-kind-code :set-group-moderation) 23))
(assert-event (equal (fn-cfg-code-kind 23) :set-group-moderation))
(assert-event (fn-cfg-deltap *mdt-delta*))
(assert-event (fn-cfg-deltap (fn-cfg-set-group-moderation "fn.mod" "" "" nil)))
; Admitted: a live group, a live other unmoderated queue, account logins.
(assert-event (null (fn-cfg-delta-reason *mdt-v1* 2 *mdt-stamp* 0 512 *mdt-delta*)))
; Refused by name.
(assert-event (equal (fn-cfg-delta-reason
                      *mdt-v1* 2 *mdt-stamp* 0 512
                      (fn-cfg-set-group-moderation "fn.absent" "fn.queue" "" '("alice")))
                     :no-such-group))
(assert-event (equal (fn-cfg-delta-reason
                      *mdt-v1* 2 *mdt-stamp* 0 512
                      (fn-cfg-set-group-moderation "fn.mod" "fn.absent" "" '("alice")))
                     :moderation-queue))
(assert-event (equal (fn-cfg-delta-reason
                      *mdt-v1* 2 *mdt-stamp* 0 512
                      (fn-cfg-set-group-moderation "fn.mod" "fn.mod" "" '("alice")))
                     :moderation-queue))
; A moderated queue, and a queue that is itself moderated, are refused.
(assert-event (equal (fn-cfg-delta-reason
                      *mdt-v2* 3 *mdt-stamp* 0 512
                      (fn-cfg-set-group-moderation "fn.test" "fn.mod" "" '("alice")))
                     :moderation-queue))
(assert-event (equal (fn-cfg-delta-reason
                      *mdt-v2* 3 *mdt-stamp* 0 512
                      (fn-cfg-set-group-moderation "fn.queue" "fn.test" "" '("alice")))
                     :moderation-queue))
(assert-event (equal (fn-cfg-delta-reason
                      *mdt-v1* 2 *mdt-stamp* 0 512
                      (fn-cfg-set-group-moderation "fn.mod" "fn.queue" "" '("a b")))
                     :moderator-login))
; The fold.
(assert-event (equal (fn-cfg-group-moderation *mdt-v2* 2 "fn.mod")
                     '("fn.queue" "" ("alice" "bob"))))
(assert-event (null (fn-cfg-group-moderation *mdt-v2* 2 "fn.test")))
(assert-event (null (fn-cfg-group-moderation *mdt-v1* 2 "fn.mod")))
(assert-event (equal (fn-cfg-group-names *mdt-v2* 2) (fn-cfg-group-names *mdt-v1* 2)))
; --off ends it.
(assert-event (null (fn-cfg-group-moderation
                     (fn-cfg-apply-delta *mdt-v2* 3 *mdt-stamp*
                                         (fn-cfg-set-group-moderation "fn.mod" "" "" nil))
                     3 "fn.mod")))
; A re-moderation replaces the moderators.
(assert-event (equal (fn-cfg-group-moderation
                      (fn-cfg-apply-delta
                       *mdt-v2* 3 *mdt-stamp*
                       (fn-cfg-set-group-moderation "fn.mod" "fn.queue" "mod@example.invalid"
                                                    '("carol")))
                      3 "fn.mod")
                     '("fn.queue" "mod@example.invalid" ("carol"))))
; The record round trip: replay reads the delta back.
(defconst *mdt-record* (fn-cfg-record-make 1 5 2 (list *mdt-delta*) *mdt-stamp*))
(assert-event (equal (fn-cfg-decode-exact (fn-cfg-encode *mdt-record*))
                     (fn-record-parse-ok *mdt-record* nil)))
; The rows are an account's role: `account list' names them.
(assert-event (equal (fn-acct-kinds-list-report *mdt-v2*)
                     (fn-record-string-octets
                      (concatenate 'string
                                   "moderation fn.mod fn.queue" (string #\Newline)
                                   "moderator alice fn.mod" (string #\Newline)
                                   "moderator bob fn.mod" (string #\Newline)))))

; KEYSTONE fn-cfg-set-group-moderation-sets-the-moderation: reachable witness,
; its hypothesis and both conclusions asserted.
(assert-event
 (let ((v *mdt-v1*) (gen 2) (other "fn.test"))
   (and (not (fn-cfg-set-group-moderation-reason
              v gen (fn-cfg-set-group-moderation "fn.mod" "fn.queue" "" '("alice" "bob"))))
        (equal (fn-cfg-group-moderation
                (fn-cfg-apply-delta v gen *mdt-stamp*
                                    (fn-cfg-set-group-moderation
                                     "fn.mod" "fn.queue" "" '("alice" "bob")))
                gen "fn.mod")
               (list "fn.queue" "" '("alice" "bob")))
        (not (equal other "fn.mod"))
        (equal (fn-cfg-group-moderation
                (fn-cfg-apply-delta v gen *mdt-stamp*
                                    (fn-cfg-set-group-moderation
                                     "fn.mod" "fn.queue" "" '("alice" "bob")))
                gen other)
               (fn-cfg-group-moderation v gen other)))))
; Without the hypothesis (an absent group, refused :no-such-group): the fold
; still writes the rows, and the moderation read is not the one staged.
(assert-event (fn-cfg-set-group-moderation-reason
               *mdt-v1* 2 (fn-cfg-set-group-moderation "fn.absent" "fn.queue" ""
                                                       '("alice"))))
(must-fail
 (assert-event (equal (fn-cfg-group-moderation
                       (fn-cfg-apply-delta *mdt-v1* 2 *mdt-stamp*
                                           (fn-cfg-set-group-moderation
                                            "fn.absent" "fn.queue" "" '("alice")))
                       2 "fn.absent")
                      (list "fn.queue" "" '("alice")))))

; ---------------------------------------------------------------------------
; 2. The operator verb: `group moderate' stages exactly the delta.

(defun mdt-argv (words)
  (if (consp words) (cons (mdt-o (car words)) (mdt-argv (cdr words))) nil))
(defun mdt-plan (words) (fn-native-admin-plan (mdt-argv words)))
(assert-event (equal (fn-native-admin-plan-deltas
                      (mdt-plan '("group" "moderate" "fn.mod" "--moderators" "alice,bob"
                                  "--queue" "fn.queue")))
                     (list *mdt-delta*)))
(assert-event (equal (fn-native-admin-plan-deltas
                      (mdt-plan '("group" "moderate" "fn.mod" "--queue" "fn.queue"
                                  "--moderators" "alice,bob"
                                  "--submission" "mod@example.invalid")))
                     (list (fn-cfg-set-group-moderation "fn.mod" "fn.queue"
                                                        "mod@example.invalid"
                                                        '("alice" "bob")))))
; The default queue is NAME.moderation.
(assert-event (equal (fn-native-admin-plan-deltas
                      (mdt-plan '("group" "moderate" "fn.mod" "--moderators" "alice")))
                     (list (fn-cfg-set-group-moderation "fn.mod" "fn.mod.moderation" ""
                                                        '("alice")))))
(assert-event (equal (fn-native-admin-plan-deltas
                      (mdt-plan '("group" "moderate" "fn.mod" "--off")))
                     (list (fn-cfg-set-group-moderation "fn.mod" "" "" nil))))
(assert-event (fn-cfg-delta-listp
               (fn-native-admin-plan-deltas
                (mdt-plan '("group" "moderate" "fn.mod" "--moderators" "alice,bob")))))
; Refused by name: no moderators, a repeated option, an empty login.
(assert-event (equal (fn-native-admin-result-status
                      (mdt-plan '("group" "moderate" "fn.mod" "--queue" "fn.queue")))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (mdt-plan '("group" "moderate" "fn.mod" "--moderators" "a"
                                  "--moderators" "b")))
                     :refused))
(assert-event (equal (fn-native-admin-result-reason
                      (mdt-plan '("group" "moderate" "fn.mod" "--moderators" "alice,")))
                     :moderator-login))

; ---------------------------------------------------------------------------
; 3. The posting configuration the owner installs, and LIST ACTIVE's "m".

(defconst *mdt-cfg-record* (fn-cfg-make 2 *mdt-v2*))
(defconst *mdt-post-config* (fn-oag-post-config *mdt-cfg-record* 32768))
(defconst *mdt-entry*
  (list :moderated (mdt-o "fn.mod") (mdt-o "fn.queue")
        (list (mdt-o "alice") (mdt-o "bob"))))
(assert-event (equal (fn-inj-config-closed *mdt-post-config*) (list *mdt-entry*)))
(assert-event (fn-mod-no-approversp (fn-inj-config-closed *mdt-post-config*)))

(defconst *mdt-agent* (mdt-o "fn.example.invalid"))
(defconst *mdt-groups* (list (mdt-o "fn.test") (mdt-o "fn.mod") (mdt-o "fn.queue")))
; The owner's view (no one approves), and alice's (she moderates fn.mod).
(defconst *mdt-cfg*
  (fn-inj-make-config-closed t *mdt-agent* *mdt-groups* 32768 (list *mdt-entry*)))
(defconst *mdt-alice-session*
  (fn-auth-make-session nil nil (mdt-o "alice") '(:principal) nil nil))
(defconst *mdt-carol-session*
  (fn-auth-make-session nil nil (mdt-o "carol") '(:principal) nil nil))
(defconst *mdt-alice-cfg* (fn-auth-moderation-config *mdt-alice-session* *mdt-cfg*))
(defconst *mdt-approver-entry*
  (list :approver (mdt-o "fn.mod") (mdt-o "fn.queue")))
(assert-event (equal (fn-inj-config-closed *mdt-alice-cfg*) (list *mdt-approver-entry*)))
; carol and an unauthenticated session approve nothing.
(assert-event (equal (fn-auth-moderation-config *mdt-carol-session* *mdt-cfg*) *mdt-cfg*))
(assert-event (equal (fn-auth-moderation-config
                      (fn-auth-make-session nil nil (mdt-o "alice") nil nil nil)
                      *mdt-cfg*)
                     *mdt-cfg*))

; KEYSTONE fn-mod-session-entries-approver-iff-moderator: its hypothesis, both
; directions reachable.
(assert-event (fn-mod-no-approversp (list *mdt-entry*)))
(assert-event (fn-mod-entry-approverp
               (fn-mod-entry-of (mdt-o "fn.mod")
                                (fn-mod-session-entries (list *mdt-entry*) (mdt-o "bob")))))
(assert-event (not (fn-mod-entry-approverp
                    (fn-mod-entry-of (mdt-o "fn.mod")
                                     (fn-mod-session-entries (list *mdt-entry*)
                                                             (mdt-o "carol"))))))
; Without the hypothesis (a list that already holds an :approver entry,
; which the owner never installs): carol "approves".
(assert-event (not (fn-mod-no-approversp (list *mdt-approver-entry*))))
(must-fail
 (assert-event (not (fn-mod-entry-approverp
                     (fn-mod-entry-of (mdt-o "fn.mod")
                                      (fn-mod-session-entries (list *mdt-approver-entry*)
                                                              (mdt-o "carol")))))))

; ---------------------------------------------------------------------------
; 4. The gate and the host-called step.

(defconst *mdt-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defun mdt-article (newsgroups extra)
  (declare (xargs :guard (and (stringp newsgroups) (stringp extra))))
  (mdt-o (concatenate 'string
                      "From: poster@example.invalid" *mdt-crlf*
                      "Subject: hello" *mdt-crlf*
                      "Newsgroups: " newsgroups *mdt-crlf*
                      "Message-ID: <m1@example.invalid>" *mdt-crlf*
                      extra
                      *mdt-crlf*
                      "Hello." *mdt-crlf*)))
(defconst *mdt-approved-line*
  (concatenate 'string "Approved: alice@example.invalid" *mdt-crlf*))
(defconst *mdt-held* (mdt-article "fn.mod" ""))
(defconst *mdt-approved* (mdt-article "fn.mod" *mdt-approved-line*))
(defconst *mdt-cross* (mdt-article "fn.test,fn.mod" ""))
(defconst *mdt-open* (mdt-article "fn.test" ""))
(defconst *mdt-cancel*
  (mdt-article "fn.mod" (concatenate 'string "Control: cancel <x@example.invalid>"
                                     *mdt-crlf*)))

(defun mdt-decide (source cfg) (fn-post-gated-decision source cfg *mdt-obs*))
(defun mdt-in-moderatedp (d cfg)
  (and (fn-inj-injectedp d)
       (fn-mod-named-entries (fn-inj-decision-groups d) (fn-inj-config-closed cfg))
       t))

; Held: the owner's view forwards the article into fn.queue, as an envelope
; whose Message-ID carries the prefix, whose body is the proto-article.
(defconst *mdt-envelope* (mdt-decide *mdt-held* *mdt-cfg*))
(assert-event (fn-inj-injectedp *mdt-envelope*))
(assert-event (equal (fn-inj-decision-groups *mdt-envelope*) (list (mdt-o "fn.queue"))))
(assert-event (equal (fn-inj-decision-msgid *mdt-envelope*)
                     (mdt-o "<fn-moderate.m1@example.invalid>")))
(defun mdt-suffixp (tail x)
  (declare (xargs :measure (acl2-count x)))
  (or (equal tail x) (and (consp x) (mdt-suffixp tail (cdr x)))))
(assert-event (mdt-suffixp *mdt-held* (fn-inj-decision-octets *mdt-envelope*)))
(assert-event (not (mdt-in-moderatedp *mdt-envelope* *mdt-cfg*)))
; A cross-post is held whole: the envelope, not a partial posting.
(assert-event (equal (fn-inj-decision-groups (mdt-decide *mdt-cross* *mdt-cfg*))
                     (list (mdt-o "fn.queue"))))
; A moderator's Approved: committed as the injection decides, into fn.mod.
(assert-event (equal (mdt-decide *mdt-approved* *mdt-alice-cfg*)
                     (fn-inj-decide *mdt-approved* *mdt-alice-cfg* *mdt-obs*)))
(assert-event (equal (fn-inj-decision-groups (mdt-decide *mdt-approved* *mdt-alice-cfg*))
                     (list (mdt-o "fn.mod"))))
; Anyone else's Approved: refused by name.
(assert-event (equal (mdt-decide *mdt-approved* *mdt-cfg*)
                     (fn-inj-refuse :approval-not-moderator)))
; An unmoderated group, and a cancel, are not gated.
(assert-event (equal (mdt-decide *mdt-open* *mdt-cfg*)
                     (fn-inj-decide *mdt-open* *mdt-cfg* *mdt-obs*)))
(assert-event (equal (mdt-decide *mdt-cancel* *mdt-cfg*)
                     (fn-inj-decide *mdt-cancel* *mdt-cfg* *mdt-obs*)))
; A queue that is no longer carried: refused by name, never posted.
(defconst *mdt-no-queue-cfg*
  (fn-inj-make-config-closed t *mdt-agent* (list (mdt-o "fn.test") (mdt-o "fn.mod"))
                             32768 (list *mdt-entry*)))
(assert-event (equal (mdt-decide *mdt-held* *mdt-no-queue-cfg*)
                     (fn-inj-refuse :moderation-unavailable)))

; KEYSTONE fn-post-unapproved-article-is-never-in-a-moderated-group: its two
; hypotheses asserted, the conclusion on the reachable witness.
(assert-event (and (fn-mod-facts *mdt-held* *mdt-cfg*)
                   (not (fn-mod-facts-approvedp (fn-mod-facts *mdt-held* *mdt-cfg*)))
                   (not (mdt-in-moderatedp (mdt-decide *mdt-held* *mdt-cfg*) *mdt-cfg*))))
; Without "not approved" (a moderator's approved article): it is in fn.mod.
(assert-event (fn-mod-facts-approvedp (fn-mod-facts *mdt-approved* *mdt-alice-cfg*)))
(must-fail
 (assert-event (not (mdt-in-moderatedp (mdt-decide *mdt-approved* *mdt-alice-cfg*)
                                       *mdt-alice-cfg*))))
; Without "ordinary" (a cancel, no facts): it names fn.mod.
(assert-event (null (fn-mod-facts *mdt-cancel* *mdt-cfg*)))
(must-fail
 (assert-event (not (mdt-in-moderatedp (mdt-decide *mdt-cancel* *mdt-cfg*) *mdt-cfg*))))

; KEYSTONE fn-post-moderator-approved-article-is-committed: its three
; hypotheses and its conclusion on the reachable witness.
(defun mdt-entries (source cfg)
  (fn-mod-named-entries (fn-inj-decision-groups (fn-inj-decide source cfg *mdt-obs*))
                        (fn-inj-config-closed cfg)))
(assert-event (and (not (fn-gst-post-gate *mdt-approved* *mdt-alice-cfg*))
                   (fn-mod-facts-approvedp (fn-mod-facts *mdt-approved* *mdt-alice-cfg*))
                   (fn-mod-all-approverp (mdt-entries *mdt-approved* *mdt-alice-cfg*))
                   (equal (mdt-decide *mdt-approved* *mdt-alice-cfg*)
                          (fn-inj-decide *mdt-approved* *mdt-alice-cfg* *mdt-obs*))))
; Without "the named moderated groups approve" (the owner's view): refused.
(assert-event (not (fn-mod-all-approverp (mdt-entries *mdt-approved* *mdt-cfg*))))
(must-fail
 (assert-event (equal (mdt-decide *mdt-approved* *mdt-cfg*)
                      (fn-inj-decide *mdt-approved* *mdt-cfg* *mdt-obs*))))
; Without "approved" (the held article on alice's connection): forwarded.
(assert-event (fn-mod-all-approverp (mdt-entries *mdt-held* *mdt-alice-cfg*)))
(must-fail
 (assert-event (equal (mdt-decide *mdt-held* *mdt-alice-cfg*)
                      (fn-inj-decide *mdt-held* *mdt-alice-cfg* *mdt-obs*))))
; Without "not read-only" (fn.mod also closed): the read-only refusal.
(defconst *mdt-closed-alice-cfg*
  (fn-inj-make-config-closed t *mdt-agent* *mdt-groups* 32768
                             (list (mdt-o "fn.mod") *mdt-approver-entry*)))
(assert-event (fn-gst-post-gate *mdt-approved* *mdt-closed-alice-cfg*))
(must-fail
 (assert-event (equal (mdt-decide *mdt-approved* *mdt-closed-alice-cfg*)
                      (fn-inj-decide *mdt-approved* *mdt-closed-alice-cfg*
                                     *mdt-obs*))))

; KEYSTONE fn-post-forged-approval-is-refused-by-name: its four hypotheses
; and its conclusion on the reachable witness.
(assert-event (and (not (fn-gst-post-gate *mdt-approved* *mdt-cfg*))
                   (fn-mod-facts-approvedp (fn-mod-facts *mdt-approved* *mdt-cfg*))
                   (consp (mdt-entries *mdt-approved* *mdt-cfg*))
                   (not (fn-mod-all-approverp (mdt-entries *mdt-approved* *mdt-cfg*)))
                   (equal (mdt-decide *mdt-approved* *mdt-cfg*)
                          (fn-inj-refuse :approval-not-moderator))))
; Without "some approver is missing" (alice): committed, not refused.
(must-fail
 (assert-event (equal (mdt-decide *mdt-approved* *mdt-alice-cfg*)
                      (fn-inj-refuse :approval-not-moderator))))
; Without "a moderated group is named" (fn.test only, with Approved).
(defconst *mdt-open-approved* (mdt-article "fn.test" *mdt-approved-line*))
(assert-event (not (consp (mdt-entries *mdt-open-approved* *mdt-cfg*))))
(must-fail
 (assert-event (equal (mdt-decide *mdt-open-approved* *mdt-cfg*)
                      (fn-inj-refuse :approval-not-moderator))))
; Without "approved": held, not refused.
(must-fail
 (assert-event (equal (mdt-decide *mdt-held* *mdt-cfg*)
                      (fn-inj-refuse :approval-not-moderator))))
; Without "not read-only": the read-only refusal.
(defconst *mdt-closed-cfg*
  (fn-inj-make-config-closed t *mdt-agent* *mdt-groups* 32768
                             (list (mdt-o "fn.mod") *mdt-entry*)))
(must-fail
 (assert-event (equal (mdt-decide *mdt-approved* *mdt-closed-cfg*)
                      (fn-inj-refuse :approval-not-moderator))))

; The served step answers them: 441 lines by name, 240 owed only for a
; submission.
(defconst *mdt-archive* (fn-initial-state '("fn.mod" "fn.queue" "fn.test")))
(defconst *mdt-s0* (fn-post-open-session *mdt-archive*))
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift fn-nntp-post-step 6)
(defconst *mdt-awaiting*
  (fn-post-result-session
   (in-arena-fn-nntp-post-step *sr-arena* *mdt-s0* *mdt-archive* *mdt-cfg* *mdt-obs* *mdt-obs* (list :command (mdt-o "POST")))))
(defun mdt-post (source cfg fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-nntp-post-step *mdt-awaiting* *mdt-archive* cfg *mdt-obs* *mdt-obs*
                     (list :article (list source)) fn-arena))
(bpr-lift mdt-post 2)
(defun mdt-reply (text)
  (list (fn-nntp-reply-effect (fn-nntp-crlf (fn-nntp-string-octets text)))))
(assert-event (equal (fn-post-result-submission (in-arena-mdt-post *sr-arena* *mdt-held* *mdt-cfg*))
                     (mdt-decide (fn-post-body-octets (list *mdt-held*)) *mdt-cfg*)))
(assert-event (equal (fn-inj-decision-groups
                      (fn-post-result-submission (in-arena-mdt-post *sr-arena* *mdt-held* *mdt-cfg*)))
                     (list (mdt-o "fn.queue"))))
(assert-event (equal (fn-post-result-effects (in-arena-mdt-post *sr-arena* *mdt-approved* *mdt-cfg*))
                     (mdt-reply "441 posting failed; Approved is accepted only from a moderator of each moderated group named (LIST ACTIVE status m)")))
(assert-event (null (fn-post-result-submission (in-arena-mdt-post *sr-arena* *mdt-approved* *mdt-cfg*))))
(assert-event (equal (fn-post-result-effects (in-arena-mdt-post *sr-arena* *mdt-held* *mdt-no-queue-cfg*))
                     (mdt-reply "441 posting failed; a moderated group is named and the article could not be forwarded to its moderation queue")))

; LIST ACTIVE: fn.mod is "m" on every connection's view.
(defun mdt-list (cfg words fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-post-result-effects
   (fn-nntp-post-step *mdt-s0* *mdt-archive* cfg *mdt-obs* *mdt-obs*
                      (list :command (mdt-o words)) fn-arena)))
(bpr-lift mdt-list 2)
(defun mdt-listing (lines)
  (fn-nntp-result-effects
   (fn-nntp-multi nil "215 list of active newsgroups follows" lines)))
(assert-event (equal (in-arena-mdt-list *sr-arena* *mdt-cfg* "LIST ACTIVE")
                     (mdt-listing (list (mdt-o "fn.mod 0 1 m")
                                        (mdt-o "fn.queue 0 1 y")
                                        (mdt-o "fn.test 0 1 y")))))
(assert-event (equal (in-arena-mdt-list *sr-arena* *mdt-alice-cfg* "LIST ACTIVE")
                     (in-arena-mdt-list *sr-arena* *mdt-cfg* "LIST ACTIVE")))

; ---------------------------------------------------------------------------
; 5. The envelope never takes a direct submission's identity.

(assert-event (not (equal (fn-mod-envelope-msgid (mdt-o "<a@b>"))
                          (fn-inj-generated-message-id *mdt-obs* *mdt-cfg*))))
(assert-event (equal (fn-mod-envelope-msgid (mdt-o "<a@b>"))
                     (mdt-o "<fn-moderate.a@b>")))

; ---------------------------------------------------------------------------
; 6. The relay: a transferred article in a moderated group without Approved.

(assert-event (fn-peer-moderated-namesp '("fn.test" "fn.mod") *mdt-v2* 2))
(assert-event (not (fn-peer-moderated-namesp '("fn.test" "fn.queue") *mdt-v2* 2)))
(assert-event (equal (fn-peer-reason-text :unapproved-moderated)
                     "no Approved header field for a moderated newsgroup"))
(assert-event (member-equal :unapproved-moderated *fn-peer-reasons*))

; ---------------------------------------------------------------------------
; 7. PKT-658: the queue is readable only by its group's moderators
; (books/nntp-auth.lisp fn-auth-view-hides-the-queue-from-a-non-moderator).

; An article's payload is its arena handle (books/acceptance.lisp): the
; envelope is handle 0 and the public article handle 1.  The checks below
; read views and never an article's bytes, so no arena holds them.
(defconst *mdt-env*
  (fn-make-article "<fn-moderate.h@example.invalid>" 0
                   '("fn.queue") (list (cons "fn.queue" 1)) t 841000000))
(defconst *mdt-pub*
  (fn-make-article "<p@example.invalid>" 1
                   '("fn.test") (list (cons "fn.test" 1)) t 841000000))
(defconst *mdt-state*
  (fn-make-state '("fn.test" "fn.mod" "fn.queue")
                 (list (cons "fn.test" 2) (cons "fn.mod" 1) (cons "fn.queue" 2))
                 (list *mdt-env* *mdt-pub*) 3 nil nil))
(defconst *mdt-acfg* (fn-auth-make-config t nil t nil))
(defconst *mdt-as-anon* (fn-auth-open-session *mdt-state* nil nil nil *mdt-acfg* nil))
(defun mdt-logged-in (name)
  (fn-auth-make-session (fn-auth-session-base *mdt-as-anon*) *mdt-acfg*
                        (mdt-o name) (make-list 32 :initial-element 7) nil nil))
(defconst *mdt-as-carol* (mdt-logged-in "carol"))
(defconst *mdt-as-alice* (mdt-logged-in "alice"))
(defun mdt-view-groups (as)
  (fn-state-groups (fn-auth-view-archive as *mdt-cfg* *mdt-state*)))
(defun mdt-view-arts (as)
  (fn-state-articles (fn-auth-view-archive as *mdt-cfg* *mdt-state*)))
; Reachable positive witness (carol, a login that moderates nothing): every
; hypothesis holds, and the view holds neither the queue nor its envelope,
; while it keeps fn.test and its article.
(assert-event (fn-mod-queue-hiddenp (fn-gac-text-octets "fn.queue")
                                    (fn-inj-config-closed *mdt-cfg*)
                                    (fn-auth-access-login *mdt-as-carol*)))
(assert-event (null (fn-auth-session-peer *mdt-as-carol*)))
(assert-event (fn-nntp-session-projected (fn-auth-reader-session *mdt-as-carol*)))
(assert-event (not (member-equal "fn.queue" (mdt-view-groups *mdt-as-carol*))))
(assert-event (not (fn-auth-arts-name-groupp "fn.queue" (mdt-view-arts *mdt-as-carol*))))
(assert-event (member-equal "fn.test" (mdt-view-groups *mdt-as-carol*)))
(assert-event (equal (mdt-view-arts *mdt-as-carol*) (list *mdt-pub*)))
; Before AUTHINFO the queue is hidden too.
(assert-event (not (member-equal "fn.queue" (mdt-view-groups *mdt-as-anon*))))
; Hypothesis removal (the hiddenp literal): alice moderates fn.mod, the other
; literals hold, and both conclusions fail: she reads the queue.
(assert-event (not (fn-mod-queue-hiddenp (fn-gac-text-octets "fn.queue")
                                         (fn-inj-config-closed *mdt-cfg*)
                                         (fn-auth-access-login *mdt-as-alice*))))
(assert-event (null (fn-auth-session-peer *mdt-as-alice*)))
(assert-event (fn-nntp-session-projected (fn-auth-reader-session *mdt-as-alice*)))
(assert-event (member-equal "fn.queue" (mdt-view-groups *mdt-as-alice*)))
(assert-event (fn-auth-arts-name-groupp "fn.queue" (mdt-view-arts *mdt-as-alice*)))
; With no moderated group, no one is restricted by the queue rule.
(assert-event (null (fn-auth-access-text *mdt-as-carol*
                                         (fn-inj-make-config-closed
                                          t *mdt-agent* *mdt-groups* 32768 nil)
                                         1)))
; The feed half (books/owner.lisp): the queue is a queue, fn.mod is not.
(assert-event (fn-mod-names-a-queuep (list (mdt-o "fn.queue")) (list *mdt-entry*)))
(assert-event (not (fn-mod-names-a-queuep (list (mdt-o "fn.mod") (mdt-o "fn.test"))
                                          (list *mdt-entry*))))
; Hypothesis removal (projection): carol's session with no projection
; (*mdt-carol-session*) keeps the other literals; its view is the archive,
; so the queue is there (the reader machine answers 503 to every archive
; command on such a session, books/nntp-auth.lisp fn-auth-access-read).
(assert-event (fn-mod-queue-hiddenp (fn-gac-text-octets "fn.queue")
                                    (fn-inj-config-closed *mdt-cfg*)
                                    (fn-auth-access-login *mdt-carol-session*)))
(assert-event (null (fn-auth-session-peer *mdt-carol-session*)))
(assert-event (not (fn-nntp-session-projected (fn-auth-reader-session *mdt-carol-session*))))
(assert-event (member-equal "fn.queue" (mdt-view-groups *mdt-carol-session*)))
