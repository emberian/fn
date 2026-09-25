; Teeth for books/peer-guard-carried.lisp and the carried peer step
; fn-scar-peer-step-pinned (books/served-carried.lisp): the peer arm with no
; node recognizer in its guard.
(in-package "ACL2")
(include-book "../../books/served-carried")
(include-book "std/testing/must-fail" :dir :system)
(include-book "peer-offer-indexed-tests")

; -----------------------------------------------------------------------------
; What the host runs: guard-verified copies, and no guard among them names
; fn-node-statep.  fn-scar-peer-step-pinned's first branch is the one node
; test left on a peer event, and with `live' the session's own node it is a
; pointer comparison.

(assert-event
 (and (eq (symbol-class 'fn-pgc-retain-admissiblep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pgc-decide-offer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pgc-peer-command (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pgc-transfer-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pgc-peer-arm (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scar-peer-step-pinned (w state)) :common-lisp-compliant)))

(defun pgc-guard-names-node-statep (fns wrld)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (or (member-eq 'fn-node-statep
                   (all-fnnames (guard (car fns) nil wrld)))
        (pgc-guard-names-node-statep (cdr fns) wrld))))
(assert-event
 (not (pgc-guard-names-node-statep
       '(fn-pgc-retain-admissiblep fn-pgc-decide-offer fn-pgc-peer-command
         fn-pgc-transfer-step fn-pgc-peer-arm fn-scar-peer-step-pinned)
       (w state))))
(assert-event
 (not (member-eq 'fn-node-statep
                 (all-fnnames (body 'fn-pgc-peer-sessionp nil (w state))))))

; -----------------------------------------------------------------------------
; Reachable witness: *pt-ps1* (peer-inbound-tests), the session over the
; node after one transit transfer and its durable completion; `live' is that
; node, the object the session holds, as fn-own-conn-live-session makes it.

(defun pgc-scar (ps live event trie arts)
  (fn-post-result-effects
   (fn-scar-peer-step-pinned ps live trie arts *pix-t-archive* nil nil
                             *pt-inj* *pt-obs* *pt-obs* event)))
(defun pgc-arm (ps event trie arts)
  (fn-post-result-effects
   (fn-pgc-peer-arm ps trie arts *pix-t-archive* nil nil
                    *pt-inj* *pt-obs* *pt-obs* event)))
(defun pgc-ref (ps event)
  (fn-post-result-effects
   (fn-peer-step-pinned ps *pix-t-archive* nil nil
                        *pt-inj* *pt-obs* *pt-obs* event)))

(assert-event (equal (fn-peer-session-node *pt-ps1*) *pt-node1*))

; Duplicate and absent, IHAVE and CHECK: the carried step answers 435/438
; and 335/238, each the reference's answer.
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "IHAVE <a1@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (list (pt-reply "435 duplicate"))))
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "CHECK <a1@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (list (pt-echo "438 " *pt-id1*))))
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "IHAVE <loop@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (list (pt-reply "335 send it; end with <CR-LF>.<CR-LF>")
                           (fn-nntp-begin-article-effect))))
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "CHECK <loop@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (list (pt-echo "238 " *pt-idloop*))))
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "IHAVE <a1@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (pgc-ref *pt-ps1* (pt-cmd "IHAVE <a1@example.invalid>"))))
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "CHECK <a1@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (pgc-ref *pt-ps1* (pt-cmd "CHECK <a1@example.invalid>"))))
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "IHAVE <loop@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (pgc-ref *pt-ps1* (pt-cmd "IHAVE <loop@example.invalid>"))))
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "CHECK <loop@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (pgc-ref *pt-ps1* (pt-cmd "CHECK <loop@example.invalid>"))))
; The other transit arms and a delegated command.
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "MODE STREAM") *pix-t-trie* *pix-t-arts*)
                     (pgc-ref *pt-ps1* (pt-cmd "MODE STREAM"))))
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "CAPABILITIES") *pix-t-trie* *pix-t-arts*)
                     (pgc-ref *pt-ps1* (pt-cmd "CAPABILITIES"))))
(assert-event (equal (pgc-scar *pt-ps1* *pt-node1* (pt-cmd "STAT <a1@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (pgc-ref *pt-ps1* (pt-cmd "STAT <a1@example.invalid>"))))

; The transfer arm: after IHAVE of an absent id the session awaits the
; article; the article event leaves as the reference's submission, with no
; effects, and a non-article event is the reference's 436 and close.
(defconst *pgc-t-awaiting*
  (fn-post-result-session
   (fn-scar-peer-step-pinned *pt-ps1* *pt-node1* *pix-t-trie* *pix-t-arts*
                             *pix-t-archive* nil nil *pt-inj* *pt-obs* *pt-obs*
                             (pt-cmd "IHAVE <loop@example.invalid>"))))
(assert-event (fn-peer-session-transfer *pgc-t-awaiting*))
(assert-event (fn-peer-sessionp *pgc-t-awaiting*))
(defun pgc-scar-full (ps event)
  (fn-scar-peer-step-pinned ps *pt-node1* *pix-t-trie* *pix-t-arts*
                            *pix-t-archive* nil nil *pt-inj* *pt-obs* *pt-obs*
                            event))
(defun pgc-ref-full (ps event)
  (fn-peer-step-pinned ps *pix-t-archive* nil nil *pt-inj* *pt-obs* *pt-obs*
                       event))
(assert-event (fn-post-result-submission
               (pgc-scar-full *pgc-t-awaiting* (list :article *pt-loop-lines*))))
(assert-event (equal (pgc-scar-full *pgc-t-awaiting* (list :article *pt-loop-lines*))
                     (pgc-ref-full *pgc-t-awaiting* (list :article *pt-loop-lines*))))
(assert-event (equal (pgc-scar-full *pgc-t-awaiting* (pt-cmd "QUIT"))
                     (pgc-ref-full *pgc-t-awaiting* (pt-cmd "QUIT"))))

; -----------------------------------------------------------------------------
; One failure per hypothesis.

; A session holding a node that is not a node state: *pix-t-orphan*
; (peer-offer-indexed-tests), whose binding names a Message-ID no article
; has.  The trie and list agree (both empty).
(defconst *pgc-t-orphan-ps* (fn-peer-with-node *pt-ps1* *pix-t-orphan*))
(defconst *pgc-t-empty-trie* (fn-midx-build nil))
(assert-event (not (fn-node-statep *pix-t-orphan*)))
(assert-event (not (fn-peer-sessionp *pgc-t-orphan-ps*)))
(assert-event (fn-midx-correspondencep *pgc-t-empty-trie* nil))
(assert-event (fn-pgc-peer-sessionp *pgc-t-orphan-ps*))

; fn-scar-peer-step-pinned-is-peer-step-pinned, hypothesis (fn-node-statep
; live): when `live' is the session's own non-node-state, the pointer
; comparison admits the session; the carried step takes the orphaned id
; (335) where the reference, whose recognizer refuses the session, answers
; nothing.
(assert-event (equal (pgc-scar *pgc-t-orphan-ps* *pix-t-orphan*
                               (pt-cmd "IHAVE <orphan@example.invalid>")
                               *pgc-t-empty-trie* nil)
                     (list (pt-reply "335 send it; end with <CR-LF>.<CR-LF>")
                           (fn-nntp-begin-article-effect))))
(assert-event (equal (pgc-ref *pgc-t-orphan-ps* (pt-cmd "IHAVE <orphan@example.invalid>"))
                     nil))
(must-fail
 (assert-event (equal (pgc-scar *pgc-t-orphan-ps* *pix-t-orphan*
                                (pt-cmd "IHAVE <orphan@example.invalid>")
                                *pgc-t-empty-trie* nil)
                      (pgc-ref *pgc-t-orphan-ps* (pt-cmd "IHAVE <orphan@example.invalid>")))))
; With a node-state `live' the same session is tested by fn-node-statep and
; refused, as the reference refuses it.
(assert-event (equal (pgc-scar *pgc-t-orphan-ps* *pt-node1*
                               (pt-cmd "IHAVE <orphan@example.invalid>")
                               *pgc-t-empty-trie* nil)
                     (pgc-ref *pgc-t-orphan-ps* (pt-cmd "IHAVE <orphan@example.invalid>"))))

; fn-pgc-peer-arm-is-peer-step-pinned, hypothesis fn-peer-sessionp: the
; same orphan session at the arm.
(must-fail
 (assert-event (equal (pgc-arm *pgc-t-orphan-ps* (pt-cmd "IHAVE <orphan@example.invalid>")
                               *pgc-t-empty-trie* nil)
                      (pgc-ref *pgc-t-orphan-ps* (pt-cmd "IHAVE <orphan@example.invalid>")))))
; Hypothesis (fn-peer-session-peer ps): a real reader session.  The arm
; decides the offer (a refusal, no peer record) where the reference
; delegates to the reader's step (502).
(assert-event (fn-peer-sessionp *pt-reader*))
(must-fail
 (assert-event (equal (pgc-arm *pt-reader* (pt-cmd "IHAVE <a1@example.invalid>")
                               *pix-t-trie* *pix-t-arts*)
                      (pgc-ref *pt-reader* (pt-cmd "IHAVE <a1@example.invalid>")))))
; Hypothesis (fn-midx-correspondencep trie arts): the empty trie keyed to
; the node's list takes the held id (335) where the reference refuses it.
(must-fail
 (assert-event (equal (pgc-arm *pt-ps1* (pt-cmd "IHAVE <a1@example.invalid>") nil *pix-t-arts*)
                      (pgc-ref *pt-ps1* (pt-cmd "IHAVE <a1@example.invalid>")))))

; fn-pgc-retain-admissiblep-is-retain-admissiblep, hypothesis
; fn-retain-statep: a ledger whose reserved count disagrees with its pins.
; The guard-t copy admits; the reference, whose logic conjoins the
; recognizer, refuses.
(defconst *pgc-t-bad-ledger* (fn-retain-make-state 10 3 nil nil))
(assert-event (not (fn-retain-statep *pgc-t-bad-ledger*)))
(assert-event (fn-pgc-retain-admissiblep *pgc-t-bad-ledger* "id" "subject" :archive
                                         (fn-peer-evidence "innA" *pt-cfg*) 1))
(must-fail
 (assert-event (equal (fn-pgc-retain-admissiblep *pgc-t-bad-ledger* "id" "subject" :archive
                                                 (fn-peer-evidence "innA" *pt-cfg*) 1)
                      (fn-retain-admissiblep *pgc-t-bad-ledger* "id" "subject" :archive
                                             (fn-peer-evidence "innA" *pt-cfg*) 1))))
; fn-pgc-decide-offer-is-pix-decide-offer, hypothesis (fn-node-statep node):
; the same ledger in an otherwise reachable node.  The copy wants the absent
; id; the reference defers it on capacity.
(defconst *pgc-t-bad-ledger-node*
  (fn-node-make-state (fn-node-acceptance *pt-node0*) *pgc-t-bad-ledger* nil nil))
(assert-event (not (fn-node-statep *pgc-t-bad-ledger-node*)))
(must-fail
 (assert-event (equal (fn-pgc-decide-offer *pgc-t-bad-ledger-node* *pt-cfg* "innA" nil
                                           *pt-idloop* nil 0 *pgc-t-empty-trie* nil)
                      (fn-pix-decide-offer *pgc-t-bad-ledger-node* *pt-cfg* "innA" nil
                                           *pt-idloop* nil 0 *pgc-t-empty-trie* nil))))

; -----------------------------------------------------------------------------
; A peer's retrieval by Message-ID (lane/rep-records-2): the peer commands do
; not answer STAT or ARTICLE, so the arm delegates to the reader step, now
; fn-pix-peer-delegate-pinned, which looks the Message-ID up in the pinned
; view trie by index.  With the view pinned (*pix-t-pin*,
; peer-offer-indexed-tests) the held article answers 223 and the absent one
; 430, each the reference step's answer.
(defun pgc-arm-pinned (event)
  (fn-post-result-effects
   (fn-pgc-peer-arm *pt-ps1* *pix-t-trie* *pix-t-arts* *pix-t-archive* *pix-t-pin* nil
                    *pt-inj* *pt-obs* *pt-obs* event)))
(defun pgc-ref-pinned (event)
  (fn-post-result-effects
   (fn-peer-step-pinned *pt-ps1* *pix-t-archive* *pix-t-pin* nil
                        *pt-inj* *pt-obs* *pt-obs* event)))
(assert-event (fn-peer-session-peer *pt-ps1*))
(assert-event (equal (pgc-arm-pinned (pt-cmd "STAT <a1@example.invalid>"))
                     (pgc-ref-pinned (pt-cmd "STAT <a1@example.invalid>"))))
(assert-event (equal (take 3 (cadr (car (pgc-arm-pinned (pt-cmd "STAT <a1@example.invalid>")))))
                     (pt-o "223")))
(assert-event (equal (pgc-arm-pinned (pt-cmd "STAT <loop@example.invalid>"))
                     (pgc-ref-pinned (pt-cmd "STAT <loop@example.invalid>"))))
(assert-event (equal (take 3 (cadr (car (pgc-arm-pinned (pt-cmd "STAT <loop@example.invalid>")))))
                     (pt-o "430")))
(assert-event (equal (pgc-arm-pinned (pt-cmd "ARTICLE <a1@example.invalid>"))
                     (pgc-ref-pinned (pt-cmd "ARTICLE <a1@example.invalid>"))))
