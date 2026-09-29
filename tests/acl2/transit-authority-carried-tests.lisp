; Teeth for books/transit-authority-carried.lisp (served-costs-6, Q5a-2):
; KEYSTONE fn-ptac-decide-of-refresh-is-pta-decide, the host's
; fn-owner-transit-decide call.  peer-inbound-tests' nodes: NODE0 (empty
; ledger) and NODE1 (A1 completed, its ledger pins "ob-a1"); the carry is the
; host's, fn-prc-refresh to the node's ledger; the profile's limits (6 6 200)
; admit the stored octets (transit-header-limits-tests).  No statement is
; carried and no group is governed, so a :want's verdict is :ungoverned.
(in-package "ACL2")
(include-book "../../books/transit-authority-carried")
(include-book "peer-inbound-tests")

(defconst *ptact-v* (fn-cfg-value *pt-cfg*))
(defconst *ptact-gen* (fn-cfg-generation *pt-cfg*))
(defconst *ptact-t0* (fn-prc-refresh nil (fn-node-retention *pt-node0*)))
(defun ptact-twin (node id carry)
  (mv-let (d a)
    (fn-ptac-decide nil nil *ptact-v* *ptact-gen* node *pt-cfg* "innA"
                    *pt-idloop* *pt-noloop* nil id "s" '(6 6 200) carry)
    (list d a)))
(defun ptact-ref (node id)
  (mv-let (d a)
    (fn-pta-decide nil nil *ptact-v* *ptact-gen* node *pt-cfg* "innA"
                   *pt-idloop* *pt-noloop* nil id "s" '(6 6 200))
    (list d a)))

; REACHABLE POSITIVE WITNESSES: the antecedent (fn-prc-carryp of the carry
; before the refresh) holds, and the pair equals fn-pta-decide's on both
; arms the carry decides: a fresh id is wanted (with its verdict), the
; pinned id is refused :capacity (no verdict).  The carry is refreshed from
; nil and, as the host keeps it, from NODE0's carry to NODE1's ledger.
(assert-event (and (fn-prc-carryp nil) (fn-prc-carryp *ptact-t0*)))
(assert-event (fn-rii-knownp "ob-a1" (fn-node-retention *pt-node1*)))
(assert-event
 (equal (ptact-twin *pt-node1* "ob-new"
                    (fn-prc-refresh *ptact-t0* (fn-node-retention *pt-node1*)))
        (list (fn-peer-decision :want nil) :ungoverned)))
(assert-event
 (equal (ptact-ref *pt-node1* "ob-new")
        (list (fn-peer-decision :want nil) :ungoverned)))
(assert-event
 (equal (ptact-twin *pt-node1* "ob-a1"
                    (fn-prc-refresh nil (fn-node-retention *pt-node1*)))
        (list (fn-peer-decision :refuse :capacity) :none)))
(assert-event
 (equal (ptact-ref *pt-node1* "ob-a1")
        (list (fn-peer-decision :refuse :capacity) :none)))

; HYPOTHESIS-REMOVAL WITNESS (fn-prc-carryp omitted): NODE0's ledger with a
; trie that also names "ob".  The omitted hypothesis fails, the refresh keeps
; the carry (same ledger), and the conclusion fails: the twin refuses
; :capacity with no verdict what fn-pta-decide wants.
(defconst *ptact-bad*
  (cons (fn-node-retention *pt-node0*) (fn-prc-add "ob" (cdr *ptact-t0*))))
(assert-event (not (fn-prc-carryp *ptact-bad*)))
(assert-event (equal (fn-prc-refresh *ptact-bad* (fn-node-retention *pt-node0*))
                     *ptact-bad*))
(assert-event
 (equal (ptact-ref *pt-node0* "ob")
        (list (fn-peer-decision :want nil) :ungoverned)))
(assert-event
 (with-guard-checking :none
  (equal (ptact-twin *pt-node0* "ob"
                     (fn-prc-refresh *ptact-bad* (fn-node-retention *pt-node0*)))
         (list (fn-peer-decision :refuse :capacity) :none))))
