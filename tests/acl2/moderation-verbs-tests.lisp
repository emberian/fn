; Witnesses and teeth for the operator's moderation verbs and withdrawal
; (PKT-657, PKT-575; PRF-228, PRF-196): books/moderation-verbs.lisp (the
; owner's plan), books/config.lisp (:withdraw-article, code 26),
; books/config-invariants.lisp `fn-cfg-withdraw-article-authorizes-the-cause',
; books/control-authority.lisp (the :node arm and
; `fn-ctl-node-withdrawal-withdraws-exactly-its-target'),
; books/native-control-reason.lisp (FNCT kind 21), books/native-admin.lisp
; (`article withdraw-record') and books/native-operator.lisp (the verbs).
(in-package "ACL2")
(include-book "../../books/moderation-verbs")
(include-book "../../books/native-admin")
(include-book "../../books/native-operator")
(include-book "must-fail-checked")
(include-book "arena-lift")

(defun mvt-o (s) (declare (xargs :guard (stringp s))) (fn-record-string-octets s))
(defconst *mvt-crlf* (coerce '(#\Return #\Newline) 'string))

; ---------------------------------------------------------------------------
; 1. The owner's posting configuration: fn.mod moderated by alice and bob,
; queue fn.queue (the entry books/owner-agent.lisp installs).

(defconst *mvt-entry*
  (list :moderated (mvt-o "fn.mod") (mvt-o "fn.queue")
        (list (mvt-o "alice") (mvt-o "bob"))))
(defconst *mvt-agent* (mvt-o "fn.example.invalid"))
(defconst *mvt-cfg*
  (fn-inj-make-config-closed t *mvt-agent*
                             (list (mvt-o "fn.test") (mvt-o "fn.mod") (mvt-o "fn.queue")
                                   (mvt-o "control.cancel"))
                             32768 (list *mvt-entry*)))
(defconst *mvt-obs* (fn-clock-observation 1000000 843004800000 500 t))
; The Store's node: the operator created control.cancel (NNT-010's filing
; group for a cancel).
(defconst *mvt-node*
  (fn-node-make-state (fn-initial-state '("control.cancel" "fn.mod" "fn.queue" "fn.test"))
                      nil nil nil))
(defconst *mvt-held*
  (mvt-o (concatenate 'string
                      "From: poster@example.invalid" *mvt-crlf*
                      "Subject: hello" *mvt-crlf*
                      "Newsgroups: fn.mod" *mvt-crlf*
                      "Message-ID: <m1@example.invalid>" *mvt-crlf*
                      *mvt-crlf* "Hello." *mvt-crlf*)))
; The served POST forwards it: the envelope.
(defconst *mvt-envelope-decision* (fn-post-gated-decision *mvt-held* *mvt-cfg* *mvt-obs*))
(assert-event (fn-inj-injectedp *mvt-envelope-decision*))
(defconst *mvt-env-id* "<fn-moderate.m1@example.invalid>")
(assert-event (equal (fn-inj-decision-msgid *mvt-envelope-decision*) (mvt-o *mvt-env-id*)))
(defun mvt-art (id payload groups)
  (fn-make-article id payload groups (list (cons (car groups) 1)) t 841000000))
; A FLIPPED archive (records flip; lane matrix-reds): the stored envelope
; carries arena handle 0, and the arena holds its octets, as the owner's
; archive does.  Every approve below reads the envelope through the arena.
(defconst *mvt-env*
  (mvt-art *mvt-env-id* 0 '("fn.queue")))
(defconst *mvt-arena* (list (fn-inj-decision-octets *mvt-envelope-decision*)))
(defconst *mvt-raw* (list *mvt-env* (mvt-art "<other@example.invalid>" nil '("fn.test"))))

; The IDs: the post's names its envelope; an envelope's is itself.
(assert-event (equal (fn-mvb-envelope-id "<m1@example.invalid>") *mvt-env-id*))
(assert-event (equal (fn-mvb-envelope-id *mvt-env-id*) *mvt-env-id*))
(assert-event (equal (fn-mvb-cause *mvt-env-id*)
                     "<fn-withdraw.fn-moderate.m1@example.invalid>"))

; ---------------------------------------------------------------------------
; 2. Approve.

(defun mvt-approve-a (raw ws login id fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-mvb-approve raw ws nil *mvt-cfg* *mvt-obs* (mvt-o login) id fn-arena))
(bpr-lift mvt-approve-a 4)
(bpr-lift fn-mvb-held-article 1)
(defun mvt-approve-in (arena raw ws login id)
  (in-arena-mvt-approve-a arena raw ws login id))
(defun mvt-approve (raw ws login id)
  (mvt-approve-in *mvt-arena* raw ws login id))
(defconst *mvt-approved* (mvt-approve *mvt-raw* nil "alice" "<m1@example.invalid>"))
(defconst *mvt-approved-octets*
  (fn-mvb-approved-article (mvt-o "alice")
                           (in-arena-fn-mvb-held-article *mvt-arena* *mvt-env*)))
; The reachable positive witness: every literal of the keystone.
(assert-event (equal (car *mvt-approved*) :submit))
(assert-event (fn-mvb-moderates-some (mvt-o "alice") '("fn.queue") (list *mvt-entry*)))
(assert-event (equal (fn-cev-envelope-state *mvt-env* nil *mvt-raw* nil) "held"))
(assert-event (equal (cadddr *mvt-approved*) *mvt-approved-octets*))
(assert-event (equal (cadr *mvt-approved*) (mvt-o "<m1@example.invalid>")))
(assert-event (equal (caddr *mvt-approved*) (list (mvt-o "fn.mod"))))
(defconst *mvt-gated* (fn-post-gated-decision *mvt-approved-octets*
                                              (fn-mvb-login-config *mvt-cfg* (mvt-o "alice"))
                                              *mvt-obs*))
(assert-event (fn-inj-injectedp *mvt-gated*))
(assert-event (equal (fn-inj-decision-msgid *mvt-gated*) (cadr *mvt-approved*)))
(assert-event (equal (fn-inj-decision-groups *mvt-gated*) (caddr *mvt-approved*)))
(assert-event (fn-inj-injectedp (fn-own-operator-decision
                                 *mvt-cfg* *mvt-obs* :absent (cadr *mvt-approved*)
                                 (caddr *mvt-approved*) *mvt-approved-octets*)))
; The octets are the held proto-article with Approved: alice first.
(assert-event (equal (take 17 *mvt-approved-octets*) (mvt-o (concatenate 'string "Approved: alice" *mvt-crlf*))))
(assert-event (equal (nthcdr 17 *mvt-approved-octets*)
                     (fn-mvb-after-blank (fn-inj-decision-octets *mvt-envelope-decision*))))
; The login's view is the served one: fn-auth-moderation-config's for alice.
(assert-event (equal (fn-inj-config-closed (fn-mvb-login-config *mvt-cfg* (mvt-o "alice")))
                     (list (list :approver (mvt-o "fn.mod") (mvt-o "fn.queue")))))

; fn-mvb-held-article-is-the-model-body: the held body read through the
; arena is the body of the envelope's octet model, which is the envelope as
; the pre-flip archive stored it (octets in the payload position).
(assert-event (equal (in-arena-fn-mvb-held-article *mvt-arena* *mvt-env*)
                     (fn-mvb-after-blank (fn-inj-decision-octets *mvt-envelope-decision*))))
(assert-event (consp (in-arena-fn-mvb-held-article *mvt-arena* *mvt-env*)))
; The arena is what approve reads: with no octets under the envelope's
; handle (an empty arena) the held body is empty and approve refuses
; :envelope-malformed, the answer dev gave before this lane
; (tests.test_native_moderation); the submission conclusion fails.
(assert-event (equal (mvt-approve-in nil *mvt-raw* nil "alice" "<m1@example.invalid>")
                     '(:refused :envelope-malformed)))
(must-fail-checked
 (assert-event (equal (car (mvt-approve-in nil *mvt-raw* nil "alice" "<m1@example.invalid>"))
                      :submit)))
; A pre-flip archive (the envelope's octets in its payload position) is read
; as before: the non-handle payload passes through the arena read.
(assert-event
 (equal (mvt-approve-in nil (list (mvt-art *mvt-env-id*
                                           (fn-inj-decision-octets *mvt-envelope-decision*)
                                           '("fn.queue")))
                        nil "alice" "<m1@example.invalid>")
        *mvt-approved*))

; Hypothesis removal (the plan is not a submission): carol, by name; the
; conclusion's first literal fails.
(defconst *mvt-carol* (mvt-approve *mvt-raw* nil "carol" "<m1@example.invalid>"))
(assert-event (equal *mvt-carol* '(:refused :not-a-moderator)))
(must-fail-checked
 (assert-event (fn-mvb-moderates-some (mvt-o "carol") '("fn.queue") (list *mvt-entry*))))
; Already approved (the post's own Message-ID stored), already rejected (a
; node record withdraws the envelope), no such envelope.
(defconst *mvt-raw-approved* (cons (mvt-art "<m1@example.invalid>" nil '("fn.mod")) *mvt-raw*))
(assert-event (equal (mvt-approve *mvt-raw-approved* nil "alice" "<m1@example.invalid>")
                     '(:refused :already-approved)))
(must-fail-checked
 (assert-event (equal (fn-cev-envelope-state *mvt-env* nil *mvt-raw-approved* nil) "held")))
(defconst *mvt-node-record*
  (fn-ctl-withdrawal-make *mvt-env-id* "<fn-withdraw.fn-moderate.m1@example.invalid>"
                          :node nil 3))
(assert-event (equal (mvt-approve *mvt-raw* (list *mvt-node-record*) "alice"
                                  "<m1@example.invalid>")
                     '(:refused :already-rejected)))
(assert-event (equal (mvt-approve *mvt-raw* nil "alice" "<absent@example.invalid>")
                     '(:refused :no-such-held-article)))

; ---------------------------------------------------------------------------
; 3. Reject and the node's withdrawal.

(defconst *mvt-rows* nil)
(defconst *mvt-rejected*
  (fn-mvb-reject *mvt-raw* nil nil *mvt-cfg* *mvt-obs* *mvt-node* *mvt-rows* (mvt-o "alice")
                 "<m1@example.invalid>" "off-topic"))
(defconst *mvt-cause* "<fn-withdraw.fn-moderate.m1@example.invalid>")
(assert-event (equal (car *mvt-rejected*) :withdraw))
(assert-event (equal *mvt-rejected*
                     (fn-mvb-withdraw *mvt-raw* *mvt-cfg* *mvt-obs* *mvt-node* *mvt-rows* *mvt-env-id* "off-topic")))
(assert-event (equal (cadr *mvt-rejected*)
                     (fn-mvb-withdraw-argv *mvt-cause* *mvt-env-id* "off-topic")))
(assert-event (equal (caddr *mvt-rejected*) (mvt-o *mvt-cause*)))
(assert-event (equal (cadddr *mvt-rejected*) (list (mvt-o "control.cancel"))))
(assert-event (equal (fn-pa-filing-plan (car (cddddr *mvt-rejected*)) (cadddr *mvt-rejected*)
                                        (fn-state-groups (fn-node-acceptance *mvt-node*)))
                     (list :file (cadddr *mvt-rejected*))))
; Without control.cancel the commit could not file the cause: refused by
; name before any row.
(assert-event (equal (fn-mvb-reject *mvt-raw* nil nil *mvt-cfg* *mvt-obs* nil nil (mvt-o "alice")
                                    "<m1@example.invalid>" "off-topic")
                     '(:refused :control-not-filed)))
; carol is refused by name; a rejection with no reason names the default.
(assert-event (equal (fn-mvb-reject *mvt-raw* nil nil *mvt-cfg* *mvt-obs* *mvt-node* nil (mvt-o "carol")
                                    "<m1@example.invalid>" "")
                     '(:refused :not-a-moderator)))
(assert-event (equal (fn-mvb-reject-reason "") "rejected by the moderator"))

; The row's vector plans exactly the :withdraw-article delta (code 26).
(defconst *mvt-admin* (fn-native-admin-plan (cadr *mvt-rejected*)))
(assert-event (equal (fn-native-admin-result-status *mvt-admin*) :accepted))
(assert-event (equal (fn-native-admin-plan-deltas *mvt-admin*)
                     (list (fn-cfg-withdraw-article *mvt-cause* *mvt-env-id* "off-topic"))))
(assert-event (equal (fn-cfg-kind-code :withdraw-article) 26))
(assert-event (equal (fn-cfg-code-kind 26) :withdraw-article))

; The configuration keystone: admitted, the row authorizes CAUSE for the
; envelope; others unchanged.
(defconst *mvt-v0* (fn-cfg-empty-value))
(defconst *mvt-delta* (fn-cfg-withdraw-article *mvt-cause* *mvt-env-id* "off-topic"))
(assert-event (null (fn-cfg-withdraw-article-reason *mvt-v0* *mvt-delta*)))
(defconst *mvt-v1* (fn-cfg-apply-delta *mvt-v0* 1 nil *mvt-delta*))
(assert-event (equal (fn-cfg-withdrawal-target (fn-cfg-authorities *mvt-v1*) *mvt-cause*)
                     *mvt-env-id*))
(assert-event (null (fn-cfg-withdrawal-target (fn-cfg-authorities *mvt-v1*) "<x@y>")))
; Hypothesis removal: a second row for the same cause is refused by name,
; and applied anyway it would not make CAUSE name the new target.
(defconst *mvt-delta2* (fn-cfg-withdraw-article *mvt-cause* "<other@example.invalid>" "x"))
(assert-event (equal (fn-cfg-withdraw-article-reason *mvt-v1* *mvt-delta2*)
                     :withdrawal-duplicate))
(must-fail-checked
 (assert-event (equal (fn-cfg-withdrawal-target
                       (fn-cfg-authorities (fn-cfg-apply-delta *mvt-v1* 1 nil *mvt-delta2*))
                       *mvt-cause*)
                      "<other@example.invalid>")))
; Refused by name: not a Message-ID, a cause that is its target.
(assert-event (equal (fn-cfg-withdraw-article-reason
                      *mvt-v0* (fn-cfg-withdraw-article "c" *mvt-env-id* "r"))
                     :withdrawal-message-id))
(assert-event (equal (fn-cfg-withdraw-article-reason
                      *mvt-v0* (fn-cfg-withdraw-article *mvt-env-id* *mvt-env-id* "r"))
                     :withdrawal-message-id))

; The composed keystone: after the row, the configuration authorizes the
; cause for exactly the envelope.
(assert-event (fn-ctl-node-authorizesp *mvt-cause* *mvt-env-id* (fn-cfg-make 1 *mvt-v1*)))
(must-fail-checked
 (assert-event (fn-ctl-node-authorizesp *mvt-cause* *mvt-env-id* (fn-cfg-make 1 *mvt-v0*))))

; The cause article the node injects: a cancel of the envelope under the
; cause's Message-ID, into the envelope's group; the control machine reads
; its target from the injected octets.
(defconst *mvt-cancel-decision*
  (fn-own-operator-decision *mvt-cfg* *mvt-obs* :absent (caddr *mvt-rejected*)
                            (cadddr *mvt-rejected*) (car (cddddr *mvt-rejected*))))
(assert-event (fn-inj-injectedp *mvt-cancel-decision*))
(assert-event (equal (fn-ctl-target-octets (fn-inj-decision-octets *mvt-cancel-decision*))
                     *mvt-env-id*))

; The control keystone over the refresh's plan: the node's record withdraws
; exactly the envelope, once the cause is in the view.
(defconst *mvt-cfgrec* (fn-cfg-make 1 *mvt-v1*))
(defconst *mvt-plan* (fn-ctl-withdrawal-plan *mvt-cause* nil *mvt-env-id* nil *mvt-cfgrec*))
(assert-event (fn-ctl-withdrawalp *mvt-plan*))
(assert-event (equal (fn-ctl-w-principal *mvt-plan*) :node))
(defconst *mvt-with-cause*
  (append *mvt-raw* (list (mvt-art *mvt-cause* (fn-inj-decision-octets *mvt-cancel-decision*)
                                   '("control.cancel")))))
(assert-event (fn-ctl-withdrawn-by-p *mvt-env* (list *mvt-plan*) *mvt-with-cause* nil))
(assert-event (not (fn-ctl-withdrawn-by-p (cadr *mvt-raw*) (list *mvt-plan*)
                                          *mvt-with-cause* nil)))
; A view pinned before the cause keeps the envelope.
(assert-event (not (fn-ctl-withdrawn-by-p *mvt-env* (list *mvt-plan*) *mvt-raw* nil)))
(assert-event (equal (fn-ctl-visible-articles *mvt-with-cause* (list *mvt-plan*) nil)
                     (cdr *mvt-with-cause*)))
; Hypothesis removal: without the row the unsigned cause declines.
(must-fail-checked
 (assert-event (fn-ctl-withdrawalp
                (fn-ctl-withdrawal-plan *mvt-cause* nil *mvt-env-id* nil
                                        (fn-cfg-make 1 *mvt-v0*)))))
; The report reads it: rejected.
(assert-event (equal (fn-cev-envelope-state *mvt-env* (list *mvt-plan*) *mvt-with-cause* nil)
                     "rejected"))

; ---------------------------------------------------------------------------
; 4. The general withdrawal.

(assert-event (equal (fn-mvb-withdraw *mvt-raw* *mvt-cfg* *mvt-obs* *mvt-node* nil "<absent@example.invalid>" "x")
                     '(:refused :no-such-article)))
(must-fail-checked
 (assert-event (consp (fn-cev-find-article "<absent@example.invalid>" *mvt-raw*))))
(assert-event (equal (fn-mvb-withdraw *mvt-with-cause* *mvt-cfg* *mvt-obs* *mvt-node* nil *mvt-env-id* "x")
                     '(:refused :already-withdrawn)))
; A retry after the row alone: no vector, the article only.
(defconst *mvt-retry* (fn-mvb-withdraw *mvt-raw* *mvt-cfg* *mvt-obs* *mvt-node* (fn-cfg-authorities *mvt-v1*)
                                       *mvt-env-id* "off-topic"))
(assert-event (equal (car *mvt-retry*) :withdraw))
(assert-event (null (cadr *mvt-retry*)))
(assert-event (equal (fn-mvb-withdraw *mvt-raw* *mvt-cfg* *mvt-obs* *mvt-node* nil "<other@example.invalid>" "")
                     (list :withdraw
                           (fn-mvb-withdraw-argv "<fn-withdraw.other@example.invalid>"
                                                 "<other@example.invalid>" "")
                           (mvt-o "<fn-withdraw.other@example.invalid>")
                           (list (mvt-o "control.cancel"))
                           (fn-mvb-cancel-article *mvt-agent*
                                                  "<fn-withdraw.other@example.invalid>"
                                                  "<other@example.invalid>"
                                                  '("control.cancel") ""))))

; ---------------------------------------------------------------------------
; 5. The plan the host calls, and the wire.

(defun mvt-request ()
  (fn-native-control-moderation-encode :approve (mvt-o "alice")
                                       (mvt-o "<m1@example.invalid>") nil))
(assert-event (consp (mvt-request)))
(assert-event (equal (fn-native-control-moderation-decode (mvt-request))
                     (list :moderation :approve (mvt-o "alice")
                           (mvt-o "<m1@example.invalid>") nil)))
(assert-event (fn-native-control-reasoned-framep (mvt-request)))
(assert-event (equal (fn-native-control-moderation-encode :other nil nil nil) :bad))
(assert-event (equal (fn-native-control-moderation-decode
                      (fn-native-control-admin-encode (list (mvt-o "group"))))
                     :bad))

; The operator's grammar.
(defun mvt-parse (command words)
  (fn-native-operator-result-arguments (fn-nop-parse-moderate command words nil)))
(assert-event (equal (mvt-parse "moderation" '("approve" "<m1@x>" "--moderator" "alice"))
                     (list :moderate :approve (mvt-o "alice") (mvt-o "<m1@x>") nil)))
(assert-event (equal (mvt-parse "moderation" '("reject" "<m1@x>" "--moderator" "alice"
                                               "--reason" "spam"))
                     (list :moderate :reject (mvt-o "alice") (mvt-o "<m1@x>") (mvt-o "spam"))))
(assert-event (equal (mvt-parse "article" '("withdraw" "<m1@x>" "--reason" "takedown"))
                     (list :moderate :withdraw nil (mvt-o "<m1@x>") (mvt-o "takedown"))))
(assert-event (equal (fn-native-operator-result-status
                      (fn-nop-parse-moderate "moderation" '("approve" "m1" "--moderator" "alice") nil))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-nop-parse-moderate "article" '("withdraw" "<m1@x>") nil))
                     :usage))
