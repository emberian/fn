; Teeth for books/held-message-id-answer (Q3d (i), PKT-239).  The Store is
; tests/acl2/visibility-join-tests': target T accepted, cancel C prepared
; and published (*vjt-completing*), then completed by fn-sn-finish
; (*vjt-two*); the entry is the one the host calls (vjt-entry, over the
; arena that interned the rows).
(in-package "ACL2")
(include-book "../../books/held-message-id-answer")
(include-book "visibility-join-tests")
(include-book "must-fail-checked")

; fn-hma-a-completion-keeps-the-held-answer
; REACHABLE positive: the whole antecedent ...
(assert-event (fn-sn-statep *vjt-completing*))
(assert-event (fn-acceptedp *vjt-t* (fn-vj-articles *vjt-completing*)))
; ... and the conclusion, for the same source (:duplicate on both sides) and
; a changed one (:conflict on both sides).
(assert-event (equal (vjt-entry *vjt-t* *vjt-t-payload* '("fn.test") *vjt-two*)
                     (vjt-entry *vjt-t* *vjt-t-payload* '("fn.test") *vjt-completing*)))
(assert-event (equal (vjt-entry *vjt-t* *vjt-t-payload* '("fn.test") *vjt-two*) :duplicate))
(assert-event (equal (vjt-entry *vjt-t* *vjt-changed* '("fn.test") *vjt-two*)
                     (vjt-entry *vjt-t* *vjt-changed* '("fn.test") *vjt-completing*)))
(assert-event (equal (vjt-entry *vjt-t* *vjt-changed* '("fn.test") *vjt-two*) :conflict))

; Hypothesis removal (REACHABLE): without "held".  C is not held before its
; completion (the keystone's only hypothesis fails); the answer moves
; from nil (a fresh prepare) to :duplicate.
(assert-event (not (fn-acceptedp *vjt-c* (fn-vj-articles *vjt-completing*))))
(assert-event (equal (vjt-entry *vjt-c* *vjt-c-payload* '("control.cancel") *vjt-completing*)
                     nil))
(assert-event (not (equal (vjt-entry *vjt-c* *vjt-c-payload* '("control.cancel") *vjt-two*)
                          nil)))
(must-fail-checked
 (defthm hmat-without-held
   (equal (fn-store-existing-action msgid payload groups (fn-sn-finish s) fn-arena)
          (fn-store-existing-action msgid payload groups s fn-arena))
   :hints (("Goal" :in-theory (disable fn-sn-finish fn-store-existing-action)))))

; MUTATION (the carried uniqueness is what the keystone rests on): a
; transition that put a second article under a held Message-ID ahead of the
; first -- here a copy of T's article under C's Message-ID prepended to
; *vjt-two*, which fn-statep forbids -- changes the answer for C's own
; source from :duplicate to :conflict.  fn-sn-finish never does this: its
; gate requires fn-sn-statep, and it preserves it.
(defun hmat-subst (new old x)
  (declare (xargs :guard t))
  (cond ((equal x old) new)
        ((consp x) (cons (hmat-subst new old (car x)) (hmat-subst new old (cdr x))))
        (t x)))
(defconst *hmat-dup*
  (let* ((node (fn-sn-node *vjt-two*))
         (acc (fn-node-acceptance node))
         (arts (fn-state-articles acc))
         (acc2 (fn-make-state (fn-state-groups acc) (fn-state-nexts acc)
                              (cons (hmat-subst *vjt-c* *vjt-t* (cadr arts)) arts)
                              (fn-state-next-txid acc)
                              (fn-state-pending acc)
                              (fn-state-fenced acc))))
    (update-nth 3 (update-nth (vjt-index-of acc node 0) acc2 node) *vjt-two*)))
(assert-event (equal (fn-article-msgids (fn-vj-articles *hmat-dup*))
                     (list *vjt-c* *vjt-c* *vjt-t*)))
(assert-event (not (fn-sn-statep *hmat-dup*)))
(assert-event (equal (vjt-entry *vjt-c* *vjt-c-payload* '("control.cancel") *vjt-two*)
                     :duplicate))
(assert-event (equal (vjt-entry *vjt-c* *vjt-c-payload* '("control.cancel") *hmat-dup*)
                     :conflict))
; And outside fn-sn-statep the completion is a stutter.
(make-event `(defconst *hmat-dup-finished*
               ',(with-guard-checking :none (fn-sn-finish *hmat-dup*))))
(assert-event (equal *hmat-dup-finished* *hmat-dup*))
