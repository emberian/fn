; Keystones for the forwarding-obligation release (wave 2, packet A).
;
; Subject: fn-bprl-release-decision and fn-bprl-undertake over the workflow
; state's node image, and fn-bprl-apply-journal-record, the wrapper that
; extends the host-called fn-bp-apply-journal-record
; (host/workflow-host.lisp:27, :40) with the two new records.
;
; Keystones (cite these, not the -by-definition lemmas):
;   fn-bprl-authorized-receipt-evidence-matches-required
;   fn-bprl-release-removes-the-forward-pin
;   fn-bprl-release-preserves-independent-pin
;   fn-bprl-release-preserves-archive-pin
;   fn-bprl-release-preserves-node-state
;   fn-bprl-release-preserves-binding-state
;   fn-bprl-undertake-preserves-node-state
;   fn-bprl-undertake-preserves-binding-state
;   fn-bprl-undertake-pins-the-forwarding-obligation
;   fn-bprl-no-receipt-no-release-no-peer-reliance
;   fn-bprl-apply-journal-record-agrees-with-host-on-bp-records
(in-package "ACL2")
(include-book "bp-release")
(include-book "bp-workflow-binding-core")
(include-book "retention-invariants")
; retention proof vocabulary is withdrawn at that book's export (core, 2026-09-19); open it here.
(local (in-theory (enable fn-retention-invariants-vocabulary)))
(local (in-theory (enable fn-retain-statep fn-retain-admissiblep fn-retain-admit fn-retain-release
                          fn-node-stagep fn-node-statep fn-statep)))

; -----------------------------------------------------------------------------
; Selector arithmetic

(defthm fn-bprl-nth-cons
  (implies (natp n)
           (equal (fn-bp-nth n (cons a b))
                  (if (equal n 0) a (fn-bp-nth (1- n) b))))
  :hints (("Goal" :in-theory (enable fn-bp-nth fn-ag-car fn-ag-cdr fn-ag-less))))

(defthm fn-bprl-nth-nil
  (implies (natp n) (equal (fn-bp-nth n nil) nil))
  :hints (("Goal" :in-theory (enable fn-bp-nth fn-ag-car fn-ag-cdr fn-ag-less))))

(defthm fn-bprl-node-with-retention-components
  (and (true-listp (fn-bprl-node-with-retention node r))
       (equal (len (fn-bprl-node-with-retention node r)) 4)
       (equal (fn-node-acceptance (fn-bprl-node-with-retention node r))
              (fn-node-acceptance node))
       (equal (fn-node-retention (fn-bprl-node-with-retention node r)) r)
       (equal (fn-node-stage (fn-bprl-node-with-retention node r))
              (fn-node-stage node))
       (equal (fn-node-bindings (fn-bprl-node-with-retention node r))
              (fn-node-bindings node)))
  :hints (("Goal" :in-theory (enable fn-bprl-node-with-retention
                                      fn-node-make-state fn-node-acceptance
                                      fn-node-retention fn-node-stage
                                      fn-node-bindings))))

; The rebuilt node has the node-state shape (core's record lemma
; fn-node-state-shapep-of-fn-node-make-state, opaque records 2026-09-19).
(defthm fn-bprl-node-with-retention-is-shaped
  (fn-node-state-shapep (fn-bprl-node-with-retention node r))
  :hints (("Goal" :in-theory (enable fn-bprl-node-with-retention))))

(defthm fn-bprl-with-node-components
  (and (true-listp (fn-bprl-with-node s node))
       (equal (len (fn-bprl-with-node s node)) 7)
       (equal (fn-bp-state-node (fn-bprl-with-node s node)) node)
       (equal (fn-bp-state-config (fn-bprl-with-node s node))
              (fn-bp-state-config s))
       (equal (fn-bp-state-works (fn-bprl-with-node s node))
              (fn-bp-state-works s))
       (equal (fn-bp-state-receipts (fn-bprl-with-node s node))
              (fn-bp-state-receipts s))
       (equal (fn-bp-state-pending (fn-bprl-with-node s node))
              (fn-bp-state-pending s))
       (equal (fn-bp-state-fenced (fn-bprl-with-node s node))
              (fn-bp-state-fenced s))
       (equal (fn-bp-state-used-txs (fn-bprl-with-node s node))
              (fn-bp-state-used-txs s)))
  :hints (("Goal" :in-theory (enable fn-bprl-with-node fn-bp-make-state
                                      fn-bp-state-node fn-bp-state-config
                                      fn-bp-state-works fn-bp-state-receipts
                                      fn-bp-state-pending fn-bp-state-fenced
                                      fn-bp-state-used-txs))))

; From here on the state accessors and the two constructors are opaque; the
; component lemmas above are the interface, so rules stated in accessor form
; match.
(in-theory (disable fn-bp-state-node fn-bp-state-config fn-bp-state-works
                    fn-bp-state-receipts fn-bp-state-pending fn-bp-state-fenced
                    fn-bp-state-used-txs fn-node-acceptance fn-node-retention
                    fn-node-stage fn-node-bindings fn-retain-pins
                    fn-retain-releases fn-bprl-with-node
                    fn-bprl-node-with-retention))

; -----------------------------------------------------------------------------
; Retention-level lemmas

(defthm fn-bprl-statep-no-duplicate-pins
  (implies (fn-retain-statep s)
           (fn-retain-no-duplicatesp
            (fn-retain-obligation-ids (fn-retain-pins s))))
  :hints (("Goal" :in-theory (enable fn-retain-statep))))

(defthm fn-bprl-find-id-of-remove-self
  (implies (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))
           (equal (fn-retain-find-id id (fn-retain-remove-id id pins)) nil))
  :hints (("Goal"
           :use ((:instance fn-retain-release-remove-id-members (other id))
                 (:instance fn-retain-find-id-absent
                            (pins (fn-retain-remove-id id pins))))
           :in-theory (disable fn-retain-release-remove-id-members
                               fn-retain-find-id-absent
                               fn-retain-remove-id fn-retain-find-id))))

(defthm fn-bprl-release-pins
  (implies (and (fn-retain-statep s)
                (fn-retain-matching-releasep
                 (fn-retain-find-id id (fn-retain-pins s))
                 id subject kind evidence))
           (equal (fn-retain-pins (fn-retain-release s id subject kind evidence))
                  (fn-retain-remove-id id (fn-retain-pins s))))
  :hints (("Goal" :in-theory (e/d (fn-retain-release fn-retain-make-state
                                                     fn-retain-pins)
                                  (fn-retain-statep fn-retain-find-id
                                                    fn-retain-remove-id
                                                    fn-retain-matching-releasep)))))

(defthm fn-bprl-admit-pins
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (equal (fn-retain-pins
                   (fn-retain-admit s id subject kind evidence charge))
                  (cons (fn-retain-make-obligation id subject kind evidence charge)
                        (fn-retain-pins s))))
  :hints (("Goal" :in-theory (e/d (fn-retain-admit fn-retain-make-state
                                                   fn-retain-pins)
                                  (fn-retain-admissiblep)))))

(defthm fn-bprl-admissible-id-not-pinned
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (not (member-equal id (fn-retain-obligation-ids (fn-retain-pins s)))))
  :hints (("Goal" :in-theory (enable fn-retain-admissiblep fn-retain-known-idp))))

; -----------------------------------------------------------------------------
; Node-level lemmas: bindings and archive pins survive a change to a pin that
; no binding names.

(defthm fn-bprl-subsetp-of-cons
  (implies (fn-subsetp xs ys)
           (fn-subsetp xs (cons a ys)))
  :hints (("Goal" :induct (fn-subsetp xs ys)
           :in-theory (enable fn-subsetp))))

(defthm fn-bprl-subsetp-of-remove
  (implies (and (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))
                (fn-subsetp xs (fn-retain-obligation-ids pins))
                (not (member-equal id xs)))
           (fn-subsetp xs (fn-retain-obligation-ids
                           (fn-retain-remove-id id pins))))
  :hints (("Goal" :induct (fn-subsetp xs (fn-retain-obligation-ids pins))
           :in-theory (e/d (fn-subsetp)
                           (fn-retain-remove-id fn-retain-obligation-ids)))))

(defthm fn-bprl-find-binding-id-is-member
  (implies (consp (fn-node-find-binding msgid bindings))
           (member-equal (fn-node-binding-id (fn-node-find-binding msgid bindings))
                         (fn-node-binding-ids bindings)))
  :hints (("Goal" :induct (fn-node-find-binding msgid bindings)
           :in-theory (enable fn-node-find-binding fn-node-binding-ids))))

(defthm fn-bprl-find-id-of-cons-other
  (implies (not (equal id (fn-retain-obligation-id ob)))
           (equal (fn-retain-find-id id (cons ob pins))
                  (fn-retain-find-id id pins)))
  :hints (("Goal" :in-theory (enable fn-retain-find-id))))

(defthm fn-bprl-archive-bindings-after-remove
  (implies (and (fn-node-articles-have-archive-bindingsp articles bindings pins)
                (not (member-equal id (fn-node-binding-ids bindings))))
           (fn-node-articles-have-archive-bindingsp
            articles bindings (fn-retain-remove-id id pins)))
  :hints (("Goal" :induct (fn-node-articles-have-archive-bindingsp
                           articles bindings pins)
           :in-theory (e/d (fn-node-articles-have-archive-bindingsp)
                           (fn-retain-remove-id fn-retain-find-id
                                                fn-retain-matching-releasep
                                                fn-node-find-binding
                                                fn-node-binding-id
                                                fn-article-msgid)))
          ("Subgoal *1/1"
           :use ((:instance fn-bprl-find-binding-id-is-member
                            (msgid (fn-article-msgid (car articles))))
                 (:instance fn-retain-release-remove-keeps-other-pin
                            (other (fn-node-binding-id
                                    (fn-node-find-binding
                                     (fn-article-msgid (car articles))
                                     bindings))))))))

(defthm fn-bprl-archive-bindings-after-cons-pin
  (implies (and (fn-node-articles-have-archive-bindingsp articles bindings pins)
                (not (member-equal id (fn-node-binding-ids bindings))))
           (fn-node-articles-have-archive-bindingsp
            articles bindings
            (cons (fn-retain-make-obligation id subject kind evidence charge)
                  pins)))
  :hints (("Goal" :induct (fn-node-articles-have-archive-bindingsp
                           articles bindings pins)
           :in-theory (e/d (fn-node-articles-have-archive-bindingsp
                            fn-retain-make-obligation fn-retain-obligation-id)
                           (fn-retain-find-id fn-retain-matching-releasep
                                              fn-node-find-binding
                                              fn-node-binding-id
                                              fn-article-msgid)))
          ("Subgoal *1/1"
           :use ((:instance fn-bprl-find-binding-id-is-member
                            (msgid (fn-article-msgid (car articles))))
                 (:instance fn-bprl-find-id-of-cons-other
                            (id (fn-node-binding-id
                                 (fn-node-find-binding
                                  (fn-article-msgid (car articles))
                                  bindings)))
                            (ob (fn-retain-make-obligation id subject kind
                                                           evidence charge)))))))

(defthm fn-bprl-node-statep-retention
  (implies (fn-node-statep node)
           (fn-retain-statep (fn-node-retention node)))
  :hints (("Goal" :in-theory (enable fn-node-statep))))

(defthm fn-bprl-node-statep-binding-ids-subset
  (implies (fn-node-statep node)
           (fn-subsetp (fn-node-binding-ids (fn-node-bindings node))
                       (fn-retain-obligation-ids
                        (fn-retain-pins (fn-node-retention node)))))
  :hints (("Goal" :in-theory (enable fn-node-statep))))

; The two node-level keystones: a release or an admission of a pin that no
; binding names, while no archive transaction is staged, keeps fn-node-statep.
(defthm fn-bprl-node-release-preserves-statep
  (implies (and (fn-node-statep node)
                (null (fn-node-stage node))
                (not (member-equal id (fn-node-binding-ids (fn-node-bindings node))))
                (fn-retain-matching-releasep
                 (fn-retain-find-id id (fn-retain-pins (fn-node-retention node)))
                 id subject kind evidence))
           (fn-node-statep
            (fn-bprl-node-with-retention
             node
             (fn-retain-release (fn-node-retention node) id subject kind evidence))))
  :hints (("Goal"
           :use ((:instance fn-retain-release-preserves-statep
                            (s (fn-node-retention node)))
                 (:instance fn-bprl-release-pins (s (fn-node-retention node)))
                 (:instance fn-bprl-statep-no-duplicate-pins
                            (s (fn-node-retention node)))
                 (:instance fn-bprl-subsetp-of-remove
                            (pins (fn-retain-pins (fn-node-retention node)))
                            (xs (fn-node-binding-ids (fn-node-bindings node))))
                 (:instance fn-bprl-archive-bindings-after-remove
                            (articles (fn-state-articles (fn-node-acceptance node)))
                            (bindings (fn-node-bindings node))
                            (pins (fn-retain-pins (fn-node-retention node)))))
           :in-theory (e/d (fn-node-statep)
                           (fn-retain-release fn-retain-statep fn-statep
                                              fn-node-stagep fn-node-binding-listp
                                              fn-node-articles-have-archive-bindingsp
                                              fn-subsetp fn-retain-remove-id
                                              fn-retain-find-id
                                              fn-retain-matching-releasep
                                              fn-retain-obligation-ids
                                              fn-node-binding-ids
                                              fn-retain-release-preserves-statep
                                              fn-bprl-release-pins
                                              fn-bprl-subsetp-of-remove
                                              fn-bprl-archive-bindings-after-remove)))))

(defthm fn-bprl-node-admit-preserves-statep
  (implies (and (fn-node-statep node)
                (null (fn-node-stage node))
                (fn-retain-admissiblep (fn-node-retention node)
                                       id subject kind evidence charge))
           (fn-node-statep
            (fn-bprl-node-with-retention
             node
             (fn-retain-admit (fn-node-retention node)
                              id subject kind evidence charge))))
  :hints (("Goal"
           :use ((:instance fn-retain-admit-preserves-statep
                            (s (fn-node-retention node)))
                 (:instance fn-bprl-admit-pins (s (fn-node-retention node)))
                 (:instance fn-bprl-admissible-id-not-pinned
                            (s (fn-node-retention node)))
                 (:instance fn-not-member-of-subset
                            (xs (fn-node-binding-ids (fn-node-bindings node)))
                            (ys (fn-retain-obligation-ids
                                 (fn-retain-pins (fn-node-retention node))))
                            (x id))
                 (:instance fn-bprl-subsetp-of-cons
                            (xs (fn-node-binding-ids (fn-node-bindings node)))
                            (ys (fn-retain-obligation-ids
                                 (fn-retain-pins (fn-node-retention node))))
                            (a id))
                 (:instance fn-bprl-archive-bindings-after-cons-pin
                            (articles (fn-state-articles (fn-node-acceptance node)))
                            (bindings (fn-node-bindings node))
                            (pins (fn-retain-pins (fn-node-retention node)))))
           :in-theory (e/d (fn-node-statep fn-retain-obligation-ids
                                           fn-retain-make-obligation
                                           fn-retain-obligation-id)
                           (fn-retain-admit fn-retain-admissiblep
                                            fn-retain-statep fn-statep
                                            fn-node-stagep fn-node-binding-listp
                                            fn-node-articles-have-archive-bindingsp
                                            fn-subsetp fn-retain-find-id
                                            fn-retain-matching-releasep
                                            fn-node-binding-ids
                                            fn-retain-admit-preserves-statep
                                            fn-bprl-admit-pins
                                            fn-bprl-admissible-id-not-pinned
                                            fn-not-member-of-subset
                                            fn-bprl-subsetp-of-cons
                                            fn-bprl-archive-bindings-after-cons-pin)))))

; -----------------------------------------------------------------------------
; Lifting through the workflow state

(defthm fn-bprl-with-node-preserves-statep
  (implies (and (fn-bp-statep s) (fn-node-statep node))
           (fn-bp-statep (fn-bprl-with-node s node)))
  :hints (("Goal"
           :use ((:instance fn-bp-statep-components)
                 (:instance fn-bp-statep-of-make-state
                            (config (fn-bp-state-config s))
                            (works (fn-bp-state-works s))
                            (receipts (fn-bp-state-receipts s))
                            (pending (fn-bp-state-pending s))
                            (fenced (fn-bp-state-fenced s))
                            (used-txs (fn-bp-state-used-txs s))))
           :in-theory (e/d (fn-bprl-with-node)
                           (fn-bp-statep fn-node-statep fn-bp-configp
                                         fn-bp-work-listp fn-bp-receipt-listp
                                         fn-bp-pendingp fn-bp-tx-key-listp
                                         fn-bp-statep-components
                                         fn-bp-statep-of-make-state)))))

(defthm fn-bprl-work-boundp-with-retention
  (equal (fn-bp-work-boundp (fn-bprl-node-with-retention node r) work)
         (fn-bp-work-boundp node work))
  :hints (("Goal" :in-theory (e/d (fn-bp-work-boundp) (fn-node-find-binding)))))

(defthm fn-bprl-works-boundp-with-retention
  (equal (fn-bp-works-boundp (fn-bprl-node-with-retention node r) works)
         (fn-bp-works-boundp node works))
  :hints (("Goal" :induct (fn-bp-works-boundp node works)
           :in-theory (e/d (fn-bp-works-boundp) (fn-bp-work-boundp)))))

(defthm fn-bprl-pending-boundp-with-retention
  (equal (fn-bp-pending-boundp (fn-bprl-node-with-retention node r) pending)
         (fn-bp-pending-boundp node pending))
  :hints (("Goal" :in-theory (e/d (fn-bp-pending-boundp) (fn-bp-work-boundp)))))

(defthm fn-bprl-with-node-preserves-binding-statep
  (implies (and (fn-bp-binding-statep s)
                (fn-node-statep (fn-bprl-node-with-retention
                                 (fn-bp-state-node s) r)))
           (fn-bp-binding-statep
            (fn-bprl-with-node s (fn-bprl-node-with-retention
                                  (fn-bp-state-node s) r))))
  :hints (("Goal"
           :use ((:instance fn-bprl-with-node-preserves-statep
                            (node (fn-bprl-node-with-retention
                                   (fn-bp-state-node s) r))))
           :in-theory (e/d (fn-bp-binding-statep)
                           (fn-bp-statep fn-node-statep fn-bp-works-boundp
                                         fn-bp-pending-boundp
                                         fn-bprl-with-node
                                         fn-bprl-node-with-retention
                                         fn-bprl-with-node-preserves-statep)))))

; -----------------------------------------------------------------------------
; Release keystones

(defthm fn-bprl-authorized-receipt-evidence-matches-required
  (implies (fn-bp-authorized-receiptp config work receipt)
           (equal (fn-bprl-evidence-string (fn-bprl-receipt-evidence receipt))
                  (fn-bprl-required-evidence config work)))
  :hints (("Goal" :in-theory (enable fn-bp-authorized-receiptp
                                      fn-bprl-evidence-string
                                      fn-bprl-receipt-evidence
                                      fn-bprl-required-evidence
                                      fn-bprl-make-evidence fn-bprl-make-term
                                      fn-bprl-evidence-work-id
                                      fn-bprl-evidence-subject
                                      fn-bprl-evidence-issuer
                                      fn-bprl-evidence-term
                                      fn-bprl-evidence-incarnation
                                      fn-bprl-term-policy-id
                                      fn-bprl-term-terms-id))))

(defthm fn-bprl-release-okp-implies-statep
  (implies (fn-bprl-release-okp s receipt work) (fn-bp-statep s))
  :hints (("Goal" :in-theory (enable fn-bprl-release-okp))))

(defthm fn-bprl-decision-state-formula
  (equal (fn-bprl-decision-state (fn-bprl-release-decision s receipt-id))
         (let* ((receipt (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s)))
                (work (fn-bp-find-work (fn-bp-receipt-work-id receipt)
                                       (fn-bp-state-works s))))
           (if (fn-bprl-release-okp s receipt work)
               (fn-bprl-with-node
                s (fn-bprl-node-with-retention
                   (fn-bp-state-node s)
                   (fn-retain-release (fn-node-retention (fn-bp-state-node s))
                                      (fn-bp-work-obligation-id work)
                                      (fn-bp-work-subject work) :forward
                                      (fn-bprl-evidence-string
                                       (fn-bprl-receipt-evidence receipt)))))
             s)))
  :hints (("Goal" :in-theory (e/d (fn-bprl-release-decision
                                   fn-bprl-decision-state)
                                  (fn-bprl-release-okp fn-bprl-with-node
                                                       fn-bprl-node-with-retention
                                                       fn-retain-release
                                                       fn-bprl-find-receipt
                                                       fn-bp-find-work
                                                       fn-bprl-receipt-evidence
                                                       fn-bprl-evidence-string)))))

(defthm fn-bprl-decision-okp-formula
  (equal (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
         (let* ((receipt (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s)))
                (work (fn-bp-find-work (fn-bp-receipt-work-id receipt)
                                       (fn-bp-state-works s))))
           (if (fn-bprl-release-okp s receipt work) t nil)))
  :hints (("Goal" :in-theory (e/d (fn-bprl-release-decision
                                   fn-bprl-decision-okp)
                                  (fn-bprl-release-okp fn-bprl-with-node
                                                       fn-bprl-node-with-retention
                                                       fn-retain-release
                                                       fn-bprl-find-receipt
                                                       fn-bp-find-work
                                                       fn-bprl-receipt-evidence
                                                       fn-bprl-evidence-string)))))

(defthm fn-bprl-decision-evidence-formula
  (equal (fn-bprl-decision-evidence (fn-bprl-release-decision s receipt-id))
         (let* ((receipt (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s)))
                (work (fn-bp-find-work (fn-bp-receipt-work-id receipt)
                                       (fn-bp-state-works s))))
           (if (fn-bprl-release-okp s receipt work)
               (fn-bprl-receipt-evidence receipt)
             nil)))
  :hints (("Goal" :in-theory (e/d (fn-bprl-release-decision
                                   fn-bprl-decision-evidence)
                                  (fn-bprl-release-okp fn-bprl-with-node
                                                       fn-bprl-node-with-retention
                                                       fn-retain-release
                                                       fn-bprl-find-receipt
                                                       fn-bp-find-work
                                                       fn-bprl-receipt-evidence
                                                       fn-bprl-evidence-string)))))

(in-theory (disable fn-bprl-release-decision fn-bprl-decision-state
                    fn-bprl-decision-okp fn-bprl-decision-evidence))

; The pin named by the work is gone and the ledger's release record carries the
; rendered typed evidence.
(defthm fn-bprl-release-removes-the-forward-pin
  (implies (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
           (let* ((receipt (fn-bprl-find-receipt receipt-id
                                                 (fn-bp-state-receipts s)))
                  (work (fn-bp-find-work (fn-bp-receipt-work-id receipt)
                                         (fn-bp-state-works s)))
                  (next (fn-bprl-decision-state
                         (fn-bprl-release-decision s receipt-id))))
             (and (equal (fn-retain-find-id (fn-bp-work-obligation-id work)
                                            (fn-bprl-pins next))
                         nil)
                  (equal (car (fn-retain-releases
                               (fn-node-retention (fn-bp-state-node next))))
                         (fn-retain-make-release
                          (fn-bp-work-obligation-id work)
                          (fn-bp-work-subject work) :forward
                          (fn-bprl-evidence-string
                           (fn-bprl-decision-evidence
                            (fn-bprl-release-decision s receipt-id))))))))
  :hints (("Goal"
           :use ((:instance fn-bprl-release-pins
                            (s (fn-node-retention (fn-bp-state-node s)))
                            (id (fn-bp-work-obligation-id
                                 (fn-bp-find-work
                                  (fn-bp-receipt-work-id
                                   (fn-bprl-find-receipt
                                    receipt-id (fn-bp-state-receipts s)))
                                  (fn-bp-state-works s))))
                            (subject (fn-bp-work-subject
                                      (fn-bp-find-work
                                       (fn-bp-receipt-work-id
                                        (fn-bprl-find-receipt
                                         receipt-id (fn-bp-state-receipts s)))
                                       (fn-bp-state-works s))))
                            (kind :forward)
                            (evidence (fn-bprl-evidence-string
                                       (fn-bprl-receipt-evidence
                                        (fn-bprl-find-receipt
                                         receipt-id (fn-bp-state-receipts s))))))
                 (:instance fn-bp-statep-components)
                 (:instance fn-bprl-node-statep-retention
                            (node (fn-bp-state-node s)))
                 (:instance fn-bprl-statep-no-duplicate-pins
                            (s (fn-node-retention (fn-bp-state-node s))))
                 (:instance fn-retain-exact-release-records-its-evidence
                            (s (fn-node-retention (fn-bp-state-node s)))
                            (id (fn-bp-work-obligation-id
                                 (fn-bp-find-work
                                  (fn-bp-receipt-work-id
                                   (fn-bprl-find-receipt
                                    receipt-id (fn-bp-state-receipts s)))
                                  (fn-bp-state-works s))))
                            (subject (fn-bp-work-subject
                                      (fn-bp-find-work
                                       (fn-bp-receipt-work-id
                                        (fn-bprl-find-receipt
                                         receipt-id (fn-bp-state-receipts s)))
                                       (fn-bp-state-works s))))
                            (kind :forward)
                            (evidence (fn-bprl-evidence-string
                                       (fn-bprl-receipt-evidence
                                        (fn-bprl-find-receipt
                                         receipt-id (fn-bp-state-receipts s)))))))
           :in-theory (e/d (fn-bprl-release-okp fn-bprl-work-pinnedp
                                                fn-bprl-work-pin fn-bprl-pins)
                           (fn-bp-statep fn-retain-release fn-retain-statep
                                         fn-retain-find-id fn-retain-remove-id
                                         fn-retain-matching-releasep
                                         fn-bp-authorized-receiptp
                                         fn-bprl-find-receipt fn-bp-find-work
                                         fn-bprl-receipt-evidence
                                         fn-bprl-evidence-string
                                         fn-bprl-required-evidence
                                         fn-node-binding-ids
                                         fn-bprl-release-pins
                                         fn-retain-exact-release-records-its-evidence
                                         fn-retain-make-release
                                         fn-node-statep fn-statep fn-node-stagep
                                         fn-bp-configp fn-bp-work-listp
                                         fn-bp-receipt-listp fn-bp-pendingp
                                         fn-bp-tx-key-listp fn-bp-workp
                                         fn-bp-receiptp fn-bp-attemptp
                                         fn-fencedp fn-retain-admissiblep
                                         fn-retain-admit)))))

; Lifted fn-retain-release-preserves-independent-pin: every other pin, in
; particular the article's archive pin, is untouched.
(defthm fn-bprl-release-preserves-independent-pin
  (implies (and (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
                (not (equal other
                            (fn-bp-work-obligation-id
                             (fn-bp-find-work
                              (fn-bp-receipt-work-id
                               (fn-bprl-find-receipt receipt-id
                                                     (fn-bp-state-receipts s)))
                              (fn-bp-state-works s))))))
           (equal (fn-retain-find-id
                   other
                   (fn-bprl-pins (fn-bprl-decision-state
                                  (fn-bprl-release-decision s receipt-id))))
                  (fn-retain-find-id other (fn-bprl-pins s))))
  :hints (("Goal"
           :in-theory (e/d (fn-bprl-pins)
                           (fn-bp-statep fn-retain-statep fn-retain-find-id
                                         fn-retain-remove-id fn-retain-release
                                         fn-bprl-release-okp
                                         fn-retain-matching-releasep
                                         fn-bprl-find-receipt fn-bp-find-work
                                         fn-bprl-receipt-evidence
                                         fn-bprl-evidence-string)))))

(defthm fn-bprl-release-preserves-archive-pin
  (implies (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
           (let ((work (fn-bp-find-work
                        (fn-bp-receipt-work-id
                         (fn-bprl-find-receipt receipt-id
                                               (fn-bp-state-receipts s)))
                        (fn-bp-state-works s))))
             (equal (fn-retain-find-id
                     (fn-bp-work-archive-id work)
                     (fn-bprl-pins (fn-bprl-decision-state
                                    (fn-bprl-release-decision s receipt-id))))
                    (fn-retain-find-id (fn-bp-work-archive-id work)
                                       (fn-bprl-pins s)))))
  :hints (("Goal"
           :use ((:instance fn-bprl-release-preserves-independent-pin
                            (other (fn-bp-work-archive-id
                                    (fn-bp-find-work
                                     (fn-bp-receipt-work-id
                                      (fn-bprl-find-receipt
                                       receipt-id (fn-bp-state-receipts s)))
                                     (fn-bp-state-works s))))))
           :in-theory (e/d (fn-bprl-release-okp)
                           (fn-bp-statep fn-retain-find-id fn-bprl-pins
                                         fn-bp-authorized-receiptp
                                         fn-bprl-work-pinnedp
                                         fn-bprl-find-receipt fn-bp-find-work
                                         fn-node-binding-ids
                                         fn-bprl-release-preserves-independent-pin)))))

(defthm fn-bprl-release-preserves-node-state
  (implies (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
           (fn-node-statep
            (fn-bp-state-node
             (fn-bprl-decision-state (fn-bprl-release-decision s receipt-id)))))
  :hints (("Goal"
           :use ((:instance fn-bprl-node-release-preserves-statep
                            (node (fn-bp-state-node s))
                            (id (fn-bp-work-obligation-id
                                 (fn-bp-find-work
                                  (fn-bp-receipt-work-id
                                   (fn-bprl-find-receipt
                                    receipt-id (fn-bp-state-receipts s)))
                                  (fn-bp-state-works s))))
                            (subject (fn-bp-work-subject
                                      (fn-bp-find-work
                                       (fn-bp-receipt-work-id
                                        (fn-bprl-find-receipt
                                         receipt-id (fn-bp-state-receipts s)))
                                       (fn-bp-state-works s))))
                            (kind :forward)
                            (evidence (fn-bprl-evidence-string
                                       (fn-bprl-receipt-evidence
                                        (fn-bprl-find-receipt
                                         receipt-id (fn-bp-state-receipts s))))))
                 (:instance fn-bprl-authorized-receipt-evidence-matches-required
                            (config (fn-bp-state-config s))
                            (work (fn-bp-find-work
                                   (fn-bp-receipt-work-id
                                    (fn-bprl-find-receipt
                                     receipt-id (fn-bp-state-receipts s)))
                                   (fn-bp-state-works s)))
                            (receipt (fn-bprl-find-receipt
                                      receipt-id (fn-bp-state-receipts s))))
                 (:instance fn-bp-statep-components))
           :in-theory (e/d (fn-bprl-release-okp fn-bprl-work-pinnedp
                                                fn-bprl-work-pin fn-bprl-pins)
                           (fn-bp-statep fn-node-statep fn-retain-release
                                         fn-retain-statep fn-retain-find-id
                                         fn-retain-matching-releasep
                                         fn-bp-authorized-receiptp
                                         fn-bprl-find-receipt fn-bp-find-work
                                         fn-bprl-receipt-evidence
                                         fn-bprl-evidence-string
                                         fn-bprl-required-evidence
                                         fn-node-binding-ids
                                         fn-bprl-node-with-retention
                                         fn-bprl-node-release-preserves-statep
                                         fn-bprl-authorized-receipt-evidence-matches-required
                                         fn-bp-statep-components
                                         fn-bp-configp fn-bp-work-listp
                                         fn-bp-receipt-listp fn-bp-pendingp
                                         fn-bp-tx-key-listp)))))

(defthm fn-bprl-release-preserves-state
  (implies (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
           (fn-bp-statep
            (fn-bprl-decision-state (fn-bprl-release-decision s receipt-id))))
  :hints (("Goal"
           :use ((:instance fn-bprl-release-preserves-node-state)
                 (:instance fn-bprl-with-node-preserves-statep
                            (node (fn-bprl-node-with-retention
                                   (fn-bp-state-node s)
                                   (fn-retain-release
                                    (fn-node-retention (fn-bp-state-node s))
                                    (fn-bp-work-obligation-id
                                     (fn-bp-find-work
                                      (fn-bp-receipt-work-id
                                       (fn-bprl-find-receipt
                                        receipt-id (fn-bp-state-receipts s)))
                                      (fn-bp-state-works s)))
                                    (fn-bp-work-subject
                                     (fn-bp-find-work
                                      (fn-bp-receipt-work-id
                                       (fn-bprl-find-receipt
                                        receipt-id (fn-bp-state-receipts s)))
                                      (fn-bp-state-works s)))
                                    :forward
                                    (fn-bprl-evidence-string
                                     (fn-bprl-receipt-evidence
                                      (fn-bprl-find-receipt
                                       receipt-id (fn-bp-state-receipts s)))))))))
           :in-theory (e/d ()
                           (fn-bp-statep fn-node-statep fn-retain-release
                                         fn-bprl-release-okp
                                         fn-bprl-find-receipt fn-bp-find-work
                                         fn-bprl-receipt-evidence
                                         fn-bprl-evidence-string
                                         fn-bprl-node-with-retention
                                         fn-bprl-with-node
                                         fn-bprl-release-preserves-node-state
                                         fn-bprl-with-node-preserves-statep)))))

(defthm fn-bprl-release-preserves-binding-state
  (implies (and (fn-bp-binding-statep s)
                (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id)))
           (fn-bp-binding-statep
            (fn-bprl-decision-state (fn-bprl-release-decision s receipt-id))))
  :hints (("Goal"
           :use ((:instance fn-bprl-release-preserves-node-state)
                 (:instance fn-bprl-with-node-preserves-binding-statep
                            (r (fn-retain-release
                                (fn-node-retention (fn-bp-state-node s))
                                (fn-bp-work-obligation-id
                                 (fn-bp-find-work
                                  (fn-bp-receipt-work-id
                                   (fn-bprl-find-receipt
                                    receipt-id (fn-bp-state-receipts s)))
                                  (fn-bp-state-works s)))
                                (fn-bp-work-subject
                                 (fn-bp-find-work
                                  (fn-bp-receipt-work-id
                                   (fn-bprl-find-receipt
                                    receipt-id (fn-bp-state-receipts s)))
                                  (fn-bp-state-works s)))
                                :forward
                                (fn-bprl-evidence-string
                                 (fn-bprl-receipt-evidence
                                  (fn-bprl-find-receipt
                                   receipt-id (fn-bp-state-receipts s))))))))
           :in-theory (e/d ()
                           (fn-bp-statep fn-bp-binding-statep fn-node-statep
                                         fn-retain-release fn-bprl-release-okp
                                         fn-bprl-find-receipt fn-bp-find-work
                                         fn-bprl-receipt-evidence
                                         fn-bprl-evidence-string
                                         fn-bprl-node-with-retention
                                         fn-bprl-with-node
                                         fn-bprl-release-preserves-node-state
                                         fn-bprl-with-node-preserves-binding-statep)))))

; -----------------------------------------------------------------------------
; Undertake keystones

(defthm fn-bprl-undertake-formula
  (equal (fn-bprl-undertake s work-id charge)
         (let ((work (fn-bp-find-work work-id (fn-bp-state-works s))))
           (if (fn-bprl-undertake-okp s work charge)
               (fn-bprl-with-node
                s (fn-bprl-node-with-retention
                   (fn-bp-state-node s)
                   (fn-retain-admit (fn-node-retention (fn-bp-state-node s))
                                    (fn-bp-work-obligation-id work)
                                    (fn-bp-work-subject work) :forward
                                    (fn-bprl-required-evidence
                                     (fn-bp-state-config s) work)
                                    charge)))
             s)))
  :hints (("Goal" :in-theory (e/d (fn-bprl-undertake)
                                  (fn-bprl-undertake-okp fn-bprl-with-node
                                                         fn-bprl-node-with-retention
                                                         fn-retain-admit
                                                         fn-bp-find-work
                                                         fn-bprl-required-evidence)))))

(in-theory (disable fn-bprl-undertake))

(defthm fn-bprl-undertake-preserves-node-state
  (implies (fn-bprl-undertake-okp s (fn-bp-find-work work-id (fn-bp-state-works s))
                                  charge)
           (fn-node-statep (fn-bp-state-node (fn-bprl-undertake s work-id charge))))
  :hints (("Goal"
           :use ((:instance fn-bprl-node-admit-preserves-statep
                            (node (fn-bp-state-node s))
                            (id (fn-bp-work-obligation-id
                                 (fn-bp-find-work work-id (fn-bp-state-works s))))
                            (subject (fn-bp-work-subject
                                      (fn-bp-find-work work-id (fn-bp-state-works s))))
                            (kind :forward)
                            (evidence (fn-bprl-required-evidence
                                       (fn-bp-state-config s)
                                       (fn-bp-find-work work-id (fn-bp-state-works s))))
                            (charge charge))
                 (:instance fn-bp-statep-components))
           :in-theory (e/d (fn-bprl-undertake-okp)
                           (fn-bp-statep fn-node-statep fn-retain-admit
                                         fn-retain-admissiblep fn-bp-find-work
                                         fn-bprl-required-evidence
                                         fn-bprl-node-with-retention
                                         fn-bprl-node-admit-preserves-statep
                                         fn-bp-statep-components
                                         fn-bp-configp fn-bp-work-listp
                                         fn-bp-receipt-listp fn-bp-pendingp
                                         fn-bp-tx-key-listp)))))

(defthm fn-bprl-undertake-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep (fn-bprl-undertake s work-id charge)))
  :hints (("Goal"
           :use ((:instance fn-bprl-undertake-preserves-node-state)
                 (:instance fn-bprl-with-node-preserves-statep
                            (node (fn-bprl-node-with-retention
                                   (fn-bp-state-node s)
                                   (fn-retain-admit
                                    (fn-node-retention (fn-bp-state-node s))
                                    (fn-bp-work-obligation-id
                                     (fn-bp-find-work work-id (fn-bp-state-works s)))
                                    (fn-bp-work-subject
                                     (fn-bp-find-work work-id (fn-bp-state-works s)))
                                    :forward
                                    (fn-bprl-required-evidence
                                     (fn-bp-state-config s)
                                     (fn-bp-find-work work-id (fn-bp-state-works s)))
                                    charge)))))
           :in-theory (e/d ()
                           (fn-bp-statep fn-node-statep fn-retain-admit
                                         fn-bprl-undertake-okp fn-bp-find-work
                                         fn-bprl-required-evidence
                                         fn-bprl-node-with-retention
                                         fn-bprl-with-node
                                         fn-bprl-undertake-preserves-node-state
                                         fn-bprl-with-node-preserves-statep)))))

(defthm fn-bprl-undertake-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep (fn-bprl-undertake s work-id charge)))
  :hints (("Goal"
           :use ((:instance fn-bprl-undertake-preserves-node-state)
                 (:instance fn-bprl-with-node-preserves-binding-statep
                            (r (fn-retain-admit
                                (fn-node-retention (fn-bp-state-node s))
                                (fn-bp-work-obligation-id
                                 (fn-bp-find-work work-id (fn-bp-state-works s)))
                                (fn-bp-work-subject
                                 (fn-bp-find-work work-id (fn-bp-state-works s)))
                                :forward
                                (fn-bprl-required-evidence
                                 (fn-bp-state-config s)
                                 (fn-bp-find-work work-id (fn-bp-state-works s)))
                                charge))))
           :in-theory (e/d ()
                           (fn-bp-statep fn-bp-binding-statep fn-node-statep
                                         fn-retain-admit fn-bprl-undertake-okp
                                         fn-bp-find-work fn-bprl-required-evidence
                                         fn-bprl-node-with-retention
                                         fn-bprl-with-node
                                         fn-bprl-undertake-preserves-node-state
                                         fn-bprl-with-node-preserves-binding-statep)))))

; After a successful undertaking the release decision's pin premise holds for
; that work: release is reachable from this state.
(defthm fn-bprl-undertake-pins-the-forwarding-obligation
  (implies (fn-bprl-undertake-okp s (fn-bp-find-work work-id (fn-bp-state-works s))
                                  charge)
           (fn-bprl-work-pinnedp (fn-bprl-undertake s work-id charge)
                                 (fn-bp-find-work work-id (fn-bp-state-works s))))
  :hints (("Goal"
           :use ((:instance fn-retain-admission-binds-subject-immutably
                            (s (fn-node-retention (fn-bp-state-node s)))
                            (id (fn-bp-work-obligation-id
                                 (fn-bp-find-work work-id (fn-bp-state-works s))))
                            (subject (fn-bp-work-subject
                                      (fn-bp-find-work work-id (fn-bp-state-works s))))
                            (kind :forward)
                            (evidence (fn-bprl-required-evidence
                                       (fn-bp-state-config s)
                                       (fn-bp-find-work work-id (fn-bp-state-works s))))
                            (charge charge)))
           :in-theory (e/d (fn-bprl-undertake-okp fn-bprl-work-pinnedp
                                                  fn-bprl-work-pin fn-bprl-pins
                                                  fn-retain-matching-releasep
                                                  fn-retain-make-obligation
                                                  fn-retain-obligation-id
                                                  fn-retain-obligation-subject
                                                  fn-retain-obligation-kind
                                                  fn-retain-obligation-evidence)
                           (fn-bp-statep fn-retain-admit fn-retain-admissiblep
                                         fn-retain-find-id fn-bp-find-work
                                         fn-bprl-required-evidence
                                         fn-retain-admission-binds-subject-immutably)))))

; -----------------------------------------------------------------------------
; A-PEER: no receipt, no release, and no peer undertaking to rely on.
; The second conjunct is A-PEER's constraint fn-assume-peer-needs-a-receipt.

(defthm fn-bprl-no-receipt-no-release-no-peer-reliance
  (implies (not (consp (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s))))
           (and (not (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id)))
                (equal (fn-bprl-decision-state (fn-bprl-release-decision s receipt-id))
                       s)
                (not (fn-assume-peer-retainsp
                      (fn-bprl-find-receipt receipt-id (fn-bp-state-receipts s))
                      failures))))
  :hints (("Goal" :in-theory (e/d (fn-bprl-release-okp)
                                  (fn-bp-statep fn-bprl-find-receipt
                                                fn-bp-find-work
                                                fn-bp-authorized-receiptp
                                                fn-bprl-work-pinnedp
                                                fn-node-binding-ids)))))

; A-POLICY: the decision yields the shapes fn-assume-policy-authorizedp
; consumes; its constraints fn-assume-policy-needs-terms and
; fn-assume-policy-needs-evidence cannot refuse them.  Binding the verdict
; itself to that signature is the D09 item.
(defthm fn-bprl-release-evidence-has-policy-shape
  (implies (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id))
           (let ((ev (fn-bprl-decision-evidence
                      (fn-bprl-release-decision s receipt-id))))
             (and (fn-bprl-evidencep ev)
                  (consp ev)
                  (consp (fn-bprl-evidence-term ev)))))
  :hints (("Goal" :in-theory (e/d (fn-bprl-release-okp fn-bp-authorized-receiptp
                                                       fn-bp-receiptp
                                                       fn-bprl-receipt-evidence
                                                       fn-bprl-evidencep
                                                       fn-bprl-termp
                                                       fn-bprl-make-evidence
                                                       fn-bprl-make-term)
                                  (fn-bp-statep fn-bprl-find-receipt
                                                fn-bp-find-work fn-bp-workp
                                                fn-bp-configp
                                                fn-bprl-work-pinnedp
                                                fn-node-binding-ids)))))

; -----------------------------------------------------------------------------
; Journal wrapper

(defthm fn-bprl-bp-record-is-not-release-or-undertake
  (implies (fn-bp-journal-recordp r)
           (and (not (fn-bprl-release-recordp r))
                (not (fn-bprl-undertake-recordp r))))
  :hints (("Goal" :in-theory (enable fn-bp-journal-recordp
                                      fn-bprl-release-recordp
                                      fn-bprl-undertake-recordp
                                      fn-bp-config-recordp
                                      fn-bp-journal-nth))))

(defthm fn-bprl-apply-journal-record-agrees-with-host-on-bp-records
  (implies (fn-bp-journal-recordp r)
           (equal (fn-bprl-apply-journal-record s r)
                  (fn-bp-apply-journal-record s r)))
  :hints (("Goal" :in-theory (e/d (fn-bprl-apply-journal-record)
                                  (fn-bp-journal-recordp
                                   fn-bprl-release-recordp
                                   fn-bprl-undertake-recordp
                                   fn-bp-apply-journal-record
                                   fn-bprl-release-decision
                                   fn-bprl-undertake)))))

; Replay reproduces the decision: an accepted :release record yields exactly
; the decision state, and its evidence fields are the computed evidence.
(defthm fn-bprl-release-record-replays-decision-by-definition
  (implies (and (fn-bprl-release-recordp r)
                (car (fn-bprl-apply-journal-record s r)))
           (and (equal (fn-bp-journal-nth 1 (fn-bprl-apply-journal-record s r))
                       (fn-bprl-decision-state
                        (fn-bprl-release-decision s (fn-bp-journal-nth 1 r))))
                (equal (fn-bprl-record-evidence r)
                       (fn-bprl-decision-evidence
                        (fn-bprl-release-decision s (fn-bp-journal-nth 1 r))))
                (fn-bprl-decision-okp
                 (fn-bprl-release-decision s (fn-bp-journal-nth 1 r)))))
  :hints (("Goal" :in-theory (e/d (fn-bprl-apply-journal-record fn-bp-journal-nth)
                                  (fn-bprl-release-recordp
                                   fn-bprl-undertake-recordp
                                   fn-bp-apply-journal-record
                                   fn-bprl-release-decision
                                   fn-bprl-record-evidence
                                   fn-bprl-undertake
                                   fn-bprl-decision-state-formula
                                   fn-bprl-decision-okp-formula
                                   fn-bprl-decision-evidence-formula)))))
