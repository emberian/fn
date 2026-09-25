; Teeth for books/peer-offer-indexed.lisp and books/owner-offer-indexed.lisp:
; the IHAVE/CHECK history test answered from the view trie.
(in-package "ACL2")
(include-book "../../books/owner-offer-indexed")
(include-book "std/testing/must-fail" :dir :system)
(include-book "peer-inbound-tests")
(include-book "owner-served-carried-tests")

; -----------------------------------------------------------------------------
; Reachable witness (peer-inbound-tests): the node after one transit transfer
; of <a1@example.invalid> and its durable completion, and the peer session
; that pins it.  The trie is the one the owner's refresh builds from that
; node's article list.

(defconst *pix-t-arts* (fn-state-articles (fn-node-acceptance *pt-node1*)))
(defconst *pix-t-trie* (fn-midx-build *pix-t-arts*))
(defconst *pix-t-archive* (fn-node-acceptance *pt-node1*))

(assert-event (fn-node-statep *pt-node1*))
(assert-event (fn-midx-correspondencep *pix-t-trie* *pix-t-arts*))
(assert-event (consp *pix-t-arts*))
(assert-event (fn-peer-sessionp *pt-ps1*))
(assert-event (equal (fn-peer-session-node *pt-ps1*) *pt-node1*))

; The fast path is the one taken: the session's node holds exactly the list
; the trie is keyed to, and the trie finds the held article.
(assert-event (equal (fn-state-articles (fn-node-acceptance
                                         (fn-peer-session-node *pt-ps1*)))
                     *pix-t-arts*))
(assert-event (fn-midx-lookup "<a1@example.invalid>" *pix-t-trie*))
(assert-event (not (fn-midx-lookup "<loop@example.invalid>" *pix-t-trie*)))

(defun pix-step (event trie arts)
  (fn-post-result-effects
   (fn-pix-peer-step-pinned *pt-ps1* trie arts *pix-t-archive* nil nil
                            *pt-inj* *pt-obs* *pt-obs* event)))
(defun pix-ref (event)
  (fn-post-result-effects
   (fn-peer-step-pinned *pt-ps1* *pix-t-archive* nil nil
                        *pt-inj* *pt-obs* *pt-obs* event)))

; An offer of the held Message-ID is refused: IHAVE 435, CHECK 438.
(assert-event (equal (pix-step (pt-cmd "IHAVE <a1@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (list (pt-reply "435 duplicate"))))
(assert-event (equal (pix-step (pt-cmd "CHECK <a1@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (list (pt-echo "438 " *pt-id1*))))
; An offer of an absent Message-ID is accepted: IHAVE 335, CHECK 238.
(assert-event (equal (pix-step (pt-cmd "IHAVE <loop@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (list (pt-reply "335 send it; end with <CR-LF>.<CR-LF>")
                           (fn-nntp-begin-article-effect))))
(assert-event (equal (pix-step (pt-cmd "CHECK <loop@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (list (pt-echo "238 " *pt-idloop*))))
; Each equals the reference step (fn-pix-peer-step-pinned-is-peer-step-pinned
; on the witness).
(assert-event (equal (pix-step (pt-cmd "IHAVE <a1@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (pix-ref (pt-cmd "IHAVE <a1@example.invalid>"))))
(assert-event (equal (pix-step (pt-cmd "CHECK <a1@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (pix-ref (pt-cmd "CHECK <a1@example.invalid>"))))
(assert-event (equal (pix-step (pt-cmd "IHAVE <loop@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (pix-ref (pt-cmd "IHAVE <loop@example.invalid>"))))
(assert-event (equal (pix-step (pt-cmd "CHECK <loop@example.invalid>") *pix-t-trie* *pix-t-arts*)
                     (pix-ref (pt-cmd "CHECK <loop@example.invalid>"))))

; The host's call runs compiled code: the copies are guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-pix-history-hasp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pix-decide-offer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pix-peer-command (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pix-peer-step-pinned (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The keystone fn-pix-history-hasp-is-peer-history-hasp on the witness, and
; one failure per hypothesis.

(assert-event (equal (fn-pix-history-hasp "<a1@example.invalid>" *pt-node1* *pix-t-trie* *pix-t-arts*)
                     (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*)))
(assert-event (equal (fn-pix-history-hasp "<a1@example.invalid>" *pt-node1* *pix-t-trie* *pix-t-arts*) t))
(assert-event (equal (fn-pix-history-hasp "<loop@example.invalid>" *pt-node1* *pix-t-trie* *pix-t-arts*) nil))

; Correspondence hypothesis: the empty trie keyed to the same list.  The
; fast path is taken (the list matches) and answers "absent" where the scan
; answers "held".
(assert-event (not (fn-midx-correspondencep nil *pix-t-arts*)))
(assert-event (null (fn-pix-history-hasp "<a1@example.invalid>" *pt-node1* nil *pix-t-arts*)))
(assert-event (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*))
(must-fail
 (assert-event (equal (fn-pix-history-hasp "<a1@example.invalid>" *pt-node1* nil *pix-t-arts*)
                      (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*))))
; At the step: the same session with the wrong trie takes the held article
; (335) where the reference refuses it (435).
(assert-event (equal (pix-step (pt-cmd "IHAVE <a1@example.invalid>") nil *pix-t-arts*)
                     (list (pt-reply "335 send it; end with <CR-LF>.<CR-LF>")
                           (fn-nntp-begin-article-effect))))
(must-fail
 (assert-event (equal (pix-step (pt-cmd "IHAVE <a1@example.invalid>") nil *pix-t-arts*)
                      (pix-ref (pt-cmd "IHAVE <a1@example.invalid>")))))

; Node hypothesis: a node whose binding names a Message-ID no article has
; (fn-node-statep's binding-subset conjunct fails).  Trie and list agree
; (both empty); the trie answers "absent" and the scan, through the binding,
; answers "held".
(defconst *pix-t-orphan*
  (fn-node-make-state (fn-node-acceptance *pt-node0*)
                      (fn-node-retention *pt-node0*)
                      nil
                      (list (fn-node-make-binding "<orphan@example.invalid>"
                                                  "subject" "ob-orphan"))))
(assert-event (not (fn-node-statep *pix-t-orphan*)))
(assert-event (fn-midx-correspondencep (fn-midx-build nil) nil))
(assert-event (equal (fn-state-articles (fn-node-acceptance *pix-t-orphan*)) nil))
(assert-event (fn-peer-history-hasp "<orphan@example.invalid>" *pix-t-orphan*))
(must-fail
 (assert-event (equal (fn-pix-history-hasp "<orphan@example.invalid>" *pix-t-orphan* nil nil)
                      (fn-peer-history-hasp "<orphan@example.invalid>" *pix-t-orphan*))))

; A list the trie is not keyed to: the fast path is not taken and the answer
; is the scan's, whatever the trie holds.
(assert-event (equal (fn-pix-history-hasp "<a1@example.invalid>" *pt-node1* nil '(:other))
                     (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*)))

; -----------------------------------------------------------------------------
; The owner premise fn-scar-view-indexedp: it holds on the reachable
; configured owner of owner-served-carried-tests, after its served read, and
; after an fn-ocfg-step event; a view whose trie is not the build of its
; articles violates it.

(assert-event (fn-scar-view-indexedp *scar-t-o*))
(assert-event (fn-scar-view-indexedp
               (fn-ocfg-owner (fn-own-tls-result-owner *scar-t-carried*))))
(assert-event (fn-scar-view-indexedp
               (fn-ocfg-owner (fn-ocfg-step *scar-t-oc* (list :close 1)))))
(assert-event (fn-scar-view-indexedp (fn-own-start (fn-own-store *scar-t-o*) 4)))
(defconst *pix-t-bad-view-owner*
  (fn-own-make (fn-own-store *scar-t-o*)
               (fn-own-view-make-group-indexed
                (fn-own-view-version (fn-own-view *scar-t-o*))
                (fn-own-view-frontier (fn-own-view *scar-t-o*))
                (fn-own-view-archive (fn-own-view *scar-t-o*))
                (fn-own-view-verdicts (fn-own-view *scar-t-o*))
                '((#\< (:fn-midx-value . :not-an-article)))
                (fn-own-view-group-index (fn-own-view *scar-t-o*)))
               (fn-own-conns *scar-t-o*) (fn-own-next-id *scar-t-o*)
               (fn-own-max-conns *scar-t-o*) (fn-own-pending *scar-t-o*)
               (fn-own-ledger *scar-t-o*) (fn-own-clock *scar-t-o*)
               (fn-own-facts *scar-t-o*) (fn-own-config *scar-t-o*)
               (fn-own-queue *scar-t-o*) (fn-own-inflight *scar-t-o*)
               (fn-own-feeds *scar-t-o*)))
(must-fail (assert-event (fn-scar-view-indexedp *pix-t-bad-view-owner*)))

; -----------------------------------------------------------------------------
; The Message-ID lookup by index (books/msgid-index-concrete.lisp) on the
; served path (lane/rep-records-2).  fn-pix-history-hasp above now looks up
; with fn-mxc-lookup; its answers on the witness are unchanged (the asserts
; above run against the rerouted definition).  The reader retrieval chain:
; the bottom twin answers STAT for the held Message-ID from the trie (223)
; and 430 for an absent one, equal to the reference; the top twin, the one
; books/served-carried.lisp calls, equals its reference on the witness
; session for the same commands.

(defconst *pix-t-session* (fn-post-session-base (fn-peer-session-base *pt-ps1*)))
(defconst *pix-t-stat-held*
  (fn-pix-msgid-retrieval-indexed *pix-t-session* *pix-t-archive* *pix-t-trie*
                                  :stat *pt-id1*))
(assert-event (equal *pix-t-stat-held*
                     (fn-nntp-msgid-retrieval-indexed *pix-t-session* *pix-t-archive*
                                                      *pix-t-trie* :stat *pt-id1*)))
(assert-event (equal (take 3 (cadr
                              (car (fn-nntp-result-effects *pix-t-stat-held*))))
                     (pt-o "223")))
(defconst *pix-t-stat-absent*
  (fn-pix-msgid-retrieval-indexed *pix-t-session* *pix-t-archive* *pix-t-trie*
                                  :stat (pt-o "<loop@example.invalid>")))
(assert-event (equal *pix-t-stat-absent*
                     (fn-nntp-msgid-retrieval-indexed *pix-t-session* *pix-t-archive*
                                                      *pix-t-trie* :stat
                                                      (pt-o "<loop@example.invalid>"))))
(assert-event (equal (take 3 (cadr
                              (car (fn-nntp-result-effects *pix-t-stat-absent*))))
                     (pt-o "430")))
; With the empty trie the held article is not found (430 where the scan
; finds it): the lookup is what answers.
(assert-event (equal (take 3 (cadr
                              (car (fn-nntp-result-effects
                                    (fn-pix-msgid-retrieval-indexed
                                     *pix-t-session* *pix-t-archive* nil :stat *pt-id1*)))))
                     (pt-o "430")))

(defconst *pix-t-pin* (fn-gidx-pin *pix-t-trie* (fn-gidx-build *pix-t-arts*)))
(defun pix-t-delegate (event)
  (equal (fn-pix-peer-delegate-pinned *pt-ps1* *pix-t-archive* *pix-t-pin* nil
                                      *pt-inj* *pt-obs* *pt-obs* event)
         (fn-peer-delegate-pinned *pt-ps1* *pix-t-archive* *pix-t-pin* nil
                                  *pt-inj* *pt-obs* *pt-obs* event)))
(assert-event (and (pix-t-delegate (pt-cmd "STAT <a1@example.invalid>"))
                   (pix-t-delegate (pt-cmd "STAT <loop@example.invalid>"))
                   (pix-t-delegate (pt-cmd "ARTICLE <a1@example.invalid>"))
                   (pix-t-delegate (pt-cmd "HEAD <a1@example.invalid>"))
                   (pix-t-delegate (pt-cmd "GROUP fn.test"))
                   (pix-t-delegate (pt-cmd "STAT"))))

(assert-event
 (and (eq (symbol-class 'fn-pix-msgid-retrieval-indexed (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pix-archive-command-pinned (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pix-command-pinned (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pix-step-pinned (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pix-post-step-pinned (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pix-peer-delegate-pinned (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scar-peer-step-pinned (w state)) :common-lisp-compliant)))

; The history test's non-empty test is by length (no character list): the
; empty Message-ID takes the scan, and both answer nil; the empty trie with
; the matching list answers nil for the held one (the lookup answers), where
; the scan answers t.
(assert-event (equal (fn-pix-history-hasp "" *pt-node1* *pix-t-trie* *pix-t-arts*)
                     (fn-peer-history-hasp "" *pt-node1*)))
(assert-event (null (fn-pix-history-hasp "" *pt-node1* *pix-t-trie* *pix-t-arts*)))
(assert-event (and (null (fn-pix-history-hasp "<a1@example.invalid>" *pt-node1* nil *pix-t-arts*))
                   (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*)))
