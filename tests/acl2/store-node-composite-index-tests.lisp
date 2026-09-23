; Composite acceptance grows both the real Store and the carried statement
; index.  The statement bytes below come from the signed article witness;
; the hybrid observations exercise the Store codec and replay route, not the
; native cryptographic primitives.
(in-package "ACL2")
(include-book "store-node-index-tests")
(include-book "../../books/hybrid-store")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sni-hybrid-principal* (make-list 32 :initial-element 7))
(defconst *sni-hybrid-ed-key* (make-list 32 :initial-element 11))
(defconst *sni-hybrid-ml-key* (make-list 1952 :initial-element 13))
(defconst *sni-hybrid-keys*
  (list (cons :ed25519 *sni-hybrid-ed-key*)
        (cons :ml-dsa-65 *sni-hybrid-ml-key*)))
(defconst *sni-hybrid-signatures*
  (list (cons :ed25519 (make-list 64 :initial-element 17))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(make-event
 `(defconst *sni-hybrid-snapshot*
    ',(fn-hsig-keyring-snapshot *sni-hybrid-principal* *sni-hybrid-keys*)))
(make-event
 `(defconst *sni-hybrid-enrollment*
    ',(fn-hsig-keyring-event 0 0 0 1 *sni-hybrid-principal* *sni-hybrid-keys*)))

(defun fn-sni-commit-identity (s event)
  (fn-sn-finish
   (fn-sni-publish (fn-sn-prepare-identity (fn-sni-reserve s) event))))

(make-event
 `(defconst *sni-composite-enrolled*
    ',(fn-sni-commit-identity (fn-sn-initial *sni-groups* 32)
                               *sni-hybrid-enrollment*)))
(make-event
 `(defconst *sni-composite-keyed*
    ',(fn-sn-set-keyring *sni-composite-enrolled* *sni-keyring*)))
(assert-event (fn-sn-indexedp *sni-composite-keyed*))

(make-event
 `(defconst *sni-composite-record*
    ',(fn-record-make 1 1 1 "<sni@example>" *sni-octets* *sni-groups*
                      "sni-pin" "sni-content" "sni-release" 2 841000000)))
(make-event
 `(defconst *sni-composite-event*
    ',(fn-hsig-authorized-article-event
       1 1 1 1 *sni-hybrid-snapshot* "<sni@example>"
       (fn-record-string-octets "sni-content")
       (fn-record-encode-impl *sni-composite-record*)
       *sni-hybrid-principal* *sni-hybrid-keys* *sni-octets*
       *sni-hybrid-signatures* *sni-hybrid-ml-key*
       :verified :verified)))
(assert-event (fn-stxa-bindsp *sni-composite-event*))
(assert-event (equal (fn-stx-delta *sni-octets* *sni-keyring*)
                     (list *sni-stmt*)))

(make-event
 `(defconst *sni-composite-completing*
    ',(fn-sni-publish
       (fn-sn-prepare-identity (fn-sni-reserve *sni-composite-keyed*)
                               *sni-composite-event*))))
(assert-event (fn-sn-completion-enabledp *sni-composite-completing*))
(assert-event (fn-sn-indexedp *sni-composite-completing*))
(assert-event
 (equal (fn-sn-statement-lookup *sni-composite-completing*
                                (fn-stmt-id *sni-stmt*))
        nil))
(make-event
 `(defconst *sni-composite-finished*
    ',(fn-sn-finish *sni-composite-completing*)))
(assert-event (fn-sn-indexedp *sni-composite-finished*))
(assert-event (equal (len (fn-stx-store (fn-sn-node *sni-composite-finished*)))
                     1))
(assert-event
 (equal (fn-article-payload
         (car (fn-stx-store (fn-sn-node *sni-composite-finished*))))
        *sni-octets*))
(assert-event
 (equal (fn-stx-index-bindings (fn-sn-index *sni-composite-finished*))
        (fn-stx-index-bindings (fn-sn-index *sni-finished*))))
(assert-event
 (equal (len (fn-stx-index-bindings (fn-sn-index *sni-composite-finished*)))
        1))
(assert-event
 (equal (fn-sn-statement-lookup *sni-composite-finished*
                                (fn-stmt-id *sni-stmt*))
        *sni-stmt*))
(assert-event
 (equal (fn-sn-statement-lookup *sni-composite-finished*
                                (fn-stmt-id *sni-stmt*))
        (fn-lace-lookup (fn-stx-lace (fn-sn-node *sni-composite-finished*)
                                    (fn-sn-keyring *sni-composite-finished*))
                        (fn-stmt-id *sni-stmt*))))

; The indexedp premise matters: a completing state with a well-shaped index
; that already includes an unrelated second statement remains stale.
(make-event
 `(defconst *sni-composite-stale*
    ',(fn-sn-update-indexed
       *sni-composite-completing*
       (fn-sn-files *sni-composite-completing*)
       (fn-sn-node *sni-composite-completing*)
       (fn-sn-index *sni-forked*))))
(assert-event (fn-sn-statep *sni-composite-stale*))
(assert-event (not (fn-sn-indexedp *sni-composite-stale*)))
(assert-event (not (fn-sn-indexedp (fn-sn-finish *sni-composite-stale*))))
(must-fail
 (assert-event (fn-sn-indexedp (fn-sn-finish *sni-composite-stale*))))
