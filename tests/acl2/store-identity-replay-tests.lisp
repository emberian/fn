; Fresh-process replay of one ordered Store history containing enrolled trust,
; an atomic article+verdict, retention, and a later legacy article.
(in-package "ACL2")
(include-book "../../books/replay")
(include-book "../../books/codec-attach")
(include-book "../../books/hybrid-store")

(defconst *fn-sir-principal* (make-list 32 :initial-element 7))
(defconst *fn-sir-ed-key* (make-list 32 :initial-element 11))
(defconst *fn-sir-ml-key* (make-list 1952 :initial-element 13))
(defconst *fn-sir-keys*
  (list (cons :ed25519 *fn-sir-ed-key*)
        (cons :ml-dsa-65 *fn-sir-ml-key*)))
(defconst *fn-sir-signatures*
  (list (cons :ed25519 (make-list 64 :initial-element 17))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(make-event `(defconst *fn-sir-snapshot* ',(fn-hsig-keyring-event 0 0 0 0 *fn-sir-principal* *fn-sir-keys*)))
(defconst *fn-sir-record*
  (fn-record-make 1 1 1 "<signed@example.invalid>" '(65 13 10) '("g")
                  "archive-signed" "subject-signed" "post-signed" 3))
(make-event `(defconst *fn-sir-accept* ',(fn-hsig-authorized-article-event
   1 1 1 0 (fn-stxk-snapshot *fn-sir-snapshot*)
   "<signed@example.invalid>" (fn-record-string-octets "subject-signed")
   (fn-record-encode-impl *fn-sir-record*) *fn-sir-principal* *fn-sir-keys*
   '(65 13 10) *fn-sir-signatures* *fn-sir-ml-key* :verified :verified)))
(defconst *fn-sir-retention*
  (fn-store-retention-event-make :undertake 2 2 2
                                 "forward-signed" "subject-signed" "custody" 5))
(defconst *fn-sir-legacy*
  (fn-record-make 3 3 3 "<later@example.invalid>" '(66 13 10) '("g")
                  "archive-later" "subject-later" "post-later" 3))
(defconst *fn-sir-history*
  (list *fn-sir-snapshot* *fn-sir-accept* *fn-sir-retention* *fn-sir-legacy*))
(make-event `(defconst *fn-sir-identity* ',(fn-replay-identity *fn-sir-history*)))
(make-event `(defconst *fn-sir-open* ',(fn-replay '("g") 64 *fn-sir-history*)))

(assert-event (equal (fn-stxk-context-kind *fn-sir-identity*) :ok))
(assert-event (equal (fn-stxk-context-next *fn-sir-identity*) 4))
(assert-event (equal (len (fn-replay-verdict-pairs
                           (fn-stxk-context-verdicts *fn-sir-identity*))) 1))
(assert-event (equal (fn-replay-result-kind *fn-sir-open*) :ok))
(assert-event
 (equal (len (fn-state-articles
              (fn-node-acceptance (fn-replay-result-node *fn-sir-open*)))) 2))
(assert-event (equal (fn-replay '("g") 64 *fn-sir-history*) *fn-sir-open*))
(assert-event
 (equal (assoc-equal
         "<later@example.invalid>"
         (fn-replay-verdict-pairs
          (fn-stxk-context-verdicts *fn-sir-identity*)))
        nil))

; A validly shaped but differently enrolled snapshot cannot authorize the
; already signed composite under the same generation label.
(make-event `(defconst *fn-sir-wrong-snapshot* ',(fn-hsig-keyring-event
   0 0 0 0 *fn-sir-principal*
   (list (cons :ed25519 (make-list 32 :initial-element 23))
         (cons :ml-dsa-65 (make-list 1952 :initial-element 29))))))
(assert-event
 (equal (fn-stxk-context-kind
         (fn-replay-identity (list *fn-sir-wrong-snapshot* *fn-sir-accept*)))
        :fault))
