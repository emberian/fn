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
