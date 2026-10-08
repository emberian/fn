; Teeth for books/peer-offer-indexed.lisp:
; the IHAVE/CHECK history test answered from the view's article list.
(in-package "ACL2")
(include-book "../../books/peer-offer-indexed")
(include-book "must-fail-checked")
(include-book "peer-inbound-tests")

; -----------------------------------------------------------------------------
; Reachable witness (peer-inbound-tests): the node after one transit transfer
; of <a1@example.invalid> and its durable completion, and the peer session
; that pins it.  The list is the one the owner's refresh stores from that
; node's acceptance.

(defconst *pix-t-arts* (fn-state-articles (fn-node-acceptance *pt-node1*)))
(defconst *pix-t-archive* (fn-node-acceptance *pt-node1*))
(defconst *pix-t-pin* (fn-gidx-pin (fn-gidx-build *pix-t-arts*)))

(assert-event (fn-node-statep *pt-node1*))
(assert-event (consp *pix-t-arts*))
(assert-event (fn-peer-sessionp *pt-ps1*))
(assert-event (equal (fn-peer-session-node *pt-ps1*) *pt-node1*))

; The fast path is the one taken: the session's node holds exactly the list
; asked of, and the list finds the held article.
(assert-event (equal (fn-state-articles (fn-node-acceptance
                                         (fn-peer-session-node *pt-ps1*)))
                     *pix-t-arts*))
(assert-event (fn-find-article "<a1@example.invalid>" *pix-t-arts*))
(assert-event (not (fn-find-article "<loop@example.invalid>" *pix-t-arts*)))

(defun pix-ref (event fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-post-result-effects
   (fn-peer-step-pinned *pt-ps1* *pix-t-archive* nil nil
                        *pt-inj* *pt-obs* *pt-obs* event fn-arena)))

; The reference peer step over the witness node (the indexed copy was
; deleted; fn-pgc-peer-arm is the served one, peer-guard-carried-tests).
; An offer of the held Message-ID is refused: IHAVE 435, CHECK 438.
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift pix-ref 1)
(assert-event (equal (in-arena-pix-ref *sr-arena* (pt-cmd "IHAVE <a1@example.invalid>"))
                     (list (pt-reply "435 duplicate"))))
(assert-event (equal (in-arena-pix-ref *sr-arena* (pt-cmd "CHECK <a1@example.invalid>"))
                     (list (pt-echo "438 " *pt-id1*))))
; An offer of an absent Message-ID is accepted: IHAVE 335, CHECK 238.
(assert-event (equal (in-arena-pix-ref *sr-arena* (pt-cmd "IHAVE <loop@example.invalid>"))
                     (list (pt-reply "335 send it; end with <CR-LF>.<CR-LF>")
                           (fn-nntp-begin-article-effect))))
(assert-event (equal (in-arena-pix-ref *sr-arena* (pt-cmd "CHECK <loop@example.invalid>"))
                     (list (pt-echo "238 " *pt-idloop*))))
; The host's call runs compiled code: the history test is guard-verified.
(assert-event
 (eq (symbol-class 'fn-pix-history-hasp (w state)) :common-lisp-compliant))

; -----------------------------------------------------------------------------
; The keystone fn-pix-history-hasp-is-peer-history-hasp on the witness, and
; one failure per hypothesis.  (Its correspondence hypothesis was deleted
; with the Message-ID trie: the fast path answers fn-find-article over the
; list, which is the scan's answer under the node invariant alone.)

(assert-event (equal (fn-pix-history-hasp "<a1@example.invalid>" *pt-node1* *pix-t-arts*)
                     (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*)))
(assert-event (equal (fn-pix-history-hasp "<a1@example.invalid>" *pt-node1* *pix-t-arts*) t))
(assert-event (equal (fn-pix-history-hasp "<loop@example.invalid>" *pt-node1* *pix-t-arts*) nil))
; At the step: peer-guard-carried-tests (fn-pgc-peer-arm, the served arm).

; Node hypothesis: a node whose binding names a Message-ID no article has
; (fn-node-statep's binding-subset conjunct fails).  The list asked of is
; empty; the list lookup answers "absent" and the scan, through the
; binding, answers "held".
(defconst *pix-t-orphan*
  (fn-node-make-state (fn-node-acceptance *pt-node0*)
                      (fn-node-retention *pt-node0*)
                      nil
                      (list (fn-node-make-binding "<orphan@example.invalid>"
                                                  "subject" "ob-orphan"))))
(assert-event (not (fn-node-statep *pix-t-orphan*)))
(assert-event (equal (fn-state-articles (fn-node-acceptance *pix-t-orphan*)) nil))
(assert-event (fn-peer-history-hasp "<orphan@example.invalid>" *pix-t-orphan*))
(must-fail-checked
 (assert-event (equal (fn-pix-history-hasp "<orphan@example.invalid>" *pix-t-orphan* nil)
                      (fn-peer-history-hasp "<orphan@example.invalid>" *pix-t-orphan*))))

; A list that is not the node's: the fast path is not taken and the answer
; is the scan's.
(assert-event (equal (fn-pix-history-hasp "<a1@example.invalid>" *pt-node1* '(:other))
                     (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*)))

; The history test's non-empty test is by length: the empty Message-ID takes
; the scan, and both answer nil.
(assert-event (equal (fn-pix-history-hasp "" *pt-node1* *pix-t-arts*)
                     (fn-peer-history-hasp "" *pt-node1*)))
(assert-event (null (fn-pix-history-hasp "" *pt-node1* *pix-t-arts*)))
