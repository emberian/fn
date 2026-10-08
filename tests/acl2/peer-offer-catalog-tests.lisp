; fn: teeth for books/peer-offer-catalog.lisp (lane s-viewidx, P2):
; fn-peer-history-hasp-is-the-catalog-column.
;
;  - the positive witness (peer-inbound-tests' node after one transit
;    transfer): the node invariant and the row relation asserted whole, then
;    the equation for the held id, for the held id after the catalog marks
;    its row withdrawn (raw membership: still known), and for an absent id;
;  - hypothesis removal, node invariant: a node whose binding names an id no
;    article has, over the empty catalog (the row relation holds, the
;    invariant fails): the scan answers known, the column unknown;
;  - hypothesis removal, row relation: the invariant node over the empty
;    catalog (the invariant holds, the relation fails): same split.

(in-package "ACL2")
(include-book "../../books/peer-offer-catalog")
(include-book "must-fail-checked")
(include-book "peer-inbound-tests")

(defconst *poc-art* (car (fn-state-articles (fn-node-acceptance *pt-node1*))))

; The catalog row for that article (obligation, subject and charge as the
; node's binding carries them; the numbers are the row relation's).
(defconst *poc-h*
  (fn-cat-assign (fn-held-make 0 0 0 "<a1@example.invalid>" 0 '("fn.letters")
                               "ob-a1" "subject-a1" "e" 1 843696000 nil nil nil nil)
                 nil))
(defconst *poc-c* (list *poc-h*))
(defconst *poc-cw* (list (fn-held-with-withdrawn *poc-h* (cons 1 1))))

(assert-event (and (equal (fn-scj-row-art *poc-h*) *poc-art*)
                   (null (fn-held-withdrawn *poc-h*))
                   (equal (fn-held-withdrawn (car *poc-cw*)) '(1 . 1))))

(defthm poc-w-history-is-the-column
  (and (fn-node-statep *pt-node1*)
       (fn-scj-acc-rowsp (fn-node-acceptance *pt-node1*) *poc-c*)
       (fn-scj-acc-rowsp (fn-node-acceptance *pt-node1*) *poc-cw*)
       ; held: both sides true, also with the row withdrawn
       (equal (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*) t)
       (equal (if (consp (fn-cat-msgid-seqs "<a1@example.invalid>" *poc-c*)) t nil) t)
       (equal (if (consp (fn-cat-msgid-seqs "<a1@example.invalid>" *poc-cw*)) t nil) t)
       ; absent: both sides nil
       (equal (fn-peer-history-hasp "<loop@example.invalid>" *pt-node1*) nil)
       (equal (if (consp (fn-cat-msgid-seqs "<loop@example.invalid>" *poc-c*)) t nil) nil))
  :rule-classes nil)

; Node invariant removed: the orphan-binding node (peer-offer-indexed-tests'
; witness) over the empty catalog.
(defconst *poc-orphan*
  (fn-node-make-state (fn-node-acceptance *pt-node0*)
                      (fn-node-retention *pt-node0*)
                      nil
                      (list (fn-node-make-binding "<orphan@example.invalid>"
                                                  "subject" "ob-orphan"))))
(defthm poc-w-without-node-statep
  (and (fn-scj-acc-rowsp (fn-node-acceptance *poc-orphan*) nil)
       (not (fn-node-statep *poc-orphan*))
       (equal (fn-peer-history-hasp "<orphan@example.invalid>" *poc-orphan*) t)
       (equal (if (consp (fn-cat-msgid-seqs "<orphan@example.invalid>" nil)) t nil) nil))
  :rule-classes nil)
(must-fail-checked
 (defthm poc-r-without-node-statep
   (equal (fn-peer-history-hasp "<orphan@example.invalid>" *poc-orphan*)
          (if (consp (fn-cat-msgid-seqs "<orphan@example.invalid>" nil)) t nil))
   :rule-classes nil))

; Row relation removed: the invariant node over the empty catalog.
(defthm poc-w-without-the-row-relation
  (and (fn-node-statep *pt-node1*)
       (not (fn-scj-acc-rowsp (fn-node-acceptance *pt-node1*) nil))
       (equal (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*) t)
       (equal (if (consp (fn-cat-msgid-seqs "<a1@example.invalid>" nil)) t nil) nil))
  :rule-classes nil)
(must-fail-checked
 (defthm poc-r-without-the-row-relation
   (equal (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*)
          (if (consp (fn-cat-msgid-seqs "<a1@example.invalid>" nil)) t nil))
   :rule-classes nil))
