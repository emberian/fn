; Witnesses and teeth for books/owner-feed-txid-reuse.lisp (lane log-2):
; a txid reused after a crash against the FNFD journal's intents.
(in-package "ACL2")
(include-book "../../books/owner-feed-txid-reuse")

; A dead intent (txid 5, article A, never stored) and, after the open, a new
; POST handed the same txid 5 (article B).
(defun oft-v (msgid tick) (declare (xargs :guard t))
  (fn-own-feed-intent-values "peer.example" (fn-record-string-octets msgid)
                             '(1 2 3) '(4 5) 1 5 tick))
(defun oft-a () (declare (xargs :guard t)) (oft-v "<a@x>" 1))
(defun oft-b () (declare (xargs :guard t)) (oft-v "<b@x>" 2))

; fn-own-feed-intent-reuse-is-a-fresh-intent, reachable: the open resolved
; the dead intent (the pending set is empty), then B's intent and commit.
(assert-event
 (let* ((i1 (fn-own-feed-intent-apply nil :feed-intent (oft-a)))
        (i2 (fn-own-feed-intent-apply i1 :feed-abort (oft-a))))
   (and (equal i1 (list (fn-own-feed-intent-key (oft-a))))
        (equal i2 nil)
        (not (fn-own-feed-intent-memberp (fn-own-feed-intent-key (oft-b)) i2))
        (equal (fn-frame-item 5 (oft-a)) (fn-frame-item 5 (oft-b)))
        (equal (fn-own-feed-intent-apply i2 :feed-intent (oft-b))
               (list (fn-own-feed-intent-key (oft-b))))
        (equal (fn-own-feed-intent-apply
                (fn-own-feed-intent-apply i2 :feed-intent (oft-b)) :feed-commit (oft-b))
               nil))))
; The same whole key again (the same article re-posted at the same txid and
; tick) after its abort is also a fresh intent.
(assert-event
 (let ((i2 (fn-own-feed-intent-apply
            (fn-own-feed-intent-apply nil :feed-intent (oft-a)) :feed-abort (oft-a))))
   (equal (fn-own-feed-intent-apply
           (fn-own-feed-intent-apply i2 :feed-intent (oft-a)) :feed-commit (oft-a))
          i2)))
; Tooth (no pending intent of the key): with A's intent still pending, a
; second A intent and one resolution resolve BOTH -- the pending set does
; not come back.  The open's reconciliation (to :done) is what excludes it.
(assert-event
 (let ((pending (list (fn-own-feed-intent-key (oft-a)))))
   (and (fn-own-feed-intent-memberp (fn-own-feed-intent-key (oft-a)) pending)
        (not (equal (fn-own-feed-intent-apply
                     (fn-own-feed-intent-apply pending :feed-intent (oft-a))
                     :feed-abort (oft-a))
                    pending)))))
; Tooth (a true list): an improper pending value is not restored.
(assert-event
 (and (not (true-listp 'x))
      (not (equal (fn-own-feed-intent-apply
                   (fn-own-feed-intent-apply 'x :feed-intent (oft-b)) :feed-abort (oft-b))
                  'x))))
; Tooth (a resolution kind): a second intent record is not a resolution.
(assert-event
 (not (equal (fn-own-feed-intent-apply
              (fn-own-feed-intent-apply nil :feed-intent (oft-b)) :feed-intent (oft-b))
             nil)))

; fn-own-feed-intent-reconcile-kind-reads-no-txid: the empty node holds no
; article, so A's dead intent is aborted, at txid 5 or any other.
(assert-event
 (and (equal (fn-own-feed-intent-reconcile-kind nil (oft-a)) :feed-abort)
      (equal (fn-own-feed-intent-reconcile-kind
              nil (fn-own-feed-intent-values "peer.example" (fn-record-string-octets "<a@x>")
                                             '(1 2 3) '(4 5) 9 77 3))
             :feed-abort)))

; fn-own-feed-intent-reconcile-kind-reads-no-txid, on a REACHED node that
; holds the article, its binding and the retention pin (audit packet G1-3,
; lane audit-fixes): owner-tests' reopened owner (*own-reopened*), where the
; reconciliation answers :feed-commit.  It answers :feed-commit at the
; journal's txid 9 and at any other generation, txid and tick; and the three
; slots it reads matter (mutation witnesses: a changed identity, evidence or
; Message-ID flips it to :feed-abort) -- so the equality is not the constant
; answer of the empty node.
(include-book "owner-tests")
(defun oft-reopened-node () (fn-sn-node (fn-own-store *own-reopened*)))
(defun oft-reopened-v (msgid identity evidence generation txid tick)
  (fn-own-feed-intent-values "out" msgid identity evidence generation txid tick))
(defun oft-m () (fn-frame-item 1 (own-reopened-intent-values)))
(defun oft-i () (fn-frame-item 2 (own-reopened-intent-values)))
(defun oft-e () (fn-frame-item 3 (own-reopened-intent-values)))
(assert-event
 (and (equal (fn-own-feed-intent-reconcile-kind
              (oft-reopened-node) (oft-reopened-v (oft-m) (oft-i) (oft-e) 1 9 0))
             :feed-commit)
      (equal (fn-own-feed-intent-reconcile-kind
              (oft-reopened-node) (oft-reopened-v (oft-m) (oft-i) (oft-e) 1 9 0))
             (fn-own-feed-intent-reconcile-kind
              (oft-reopened-node) (oft-reopened-v (oft-m) (oft-i) (oft-e) 3 5 7)))
      (equal (fn-own-feed-intent-reconcile-kind
              (oft-reopened-node) (oft-reopened-v (oft-m) (oft-i) (oft-e) 0 77 12))
             :feed-commit)))
; Mutation witnesses (each changes one READ slot; the answer flips).
(assert-event
 (and (equal (fn-own-feed-intent-reconcile-kind
              (oft-reopened-node)
              (oft-reopened-v (oft-m) (fn-record-string-octets "another-obligation") (oft-e) 1 9 0))
             :feed-abort)
      (equal (fn-own-feed-intent-reconcile-kind
              (oft-reopened-node)
              (oft-reopened-v (oft-m) (oft-i) (fn-record-string-octets "other-evidence") 1 9 0))
             :feed-abort)
      (equal (fn-own-feed-intent-reconcile-kind
              (oft-reopened-node)
              (oft-reopened-v (fn-record-string-octets "<absent@example>") (oft-i) (oft-e) 1 9 0))
             :feed-abort)))
