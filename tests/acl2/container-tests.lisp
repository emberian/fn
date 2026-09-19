; Witnesses and teeth for the object container (C2-05).
;
; The witness is a container carrying one tampered article, one valid article
; and one valid article that depends on the valid sibling, plus an unknown
; object.  The tampered article is refused with no receipt, both valid
; articles publish through fn-node-prepare/fn-node-complete, and the unknown
; object is carried.  Then one concrete case per hypothesis of every keystone
; in books/container-invariants.lisp in which the conclusion fails without it.

(in-package "ACL2")
(include-book "../../books/container-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defconst *ct-profile* (fn-ct-make-profile 4 64 4 2 16))
(assert-event (fn-ct-profilep *ct-profile*))
(defconst *ct-groups* '("fn.letters"))
(defconst *ct-node* (fn-node-initial-state *ct-groups* 64))
(assert-event (fn-node-statep *ct-node*))

; Host digests (SHA-256 is A-CRYPTO; ACL2 owns everything around it).
(defconst *ct-digest-a*
  '(1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1))
(defconst *ct-digest-b*
  '(2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2))
(defconst *ct-digest-t*
  '(3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3))
(defconst *ct-digest-c*
  '(4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4))
(defconst *ct-digest-d*
  '(5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5))
(defconst *ct-obligation-1*
  '(9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9))
(defconst *ct-obligation-2*
  '(8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8))
(defconst *ct-obligation-3*
  '(7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7 7))

(defconst *ct-id-a* (fn-id-subject *ct-digest-a*))
(defconst *ct-id-b* (fn-id-subject *ct-digest-b*))
(defconst *ct-id-c* (fn-id-subject *ct-digest-c*))
(defconst *ct-id-d* (fn-id-subject *ct-digest-d*))

; A: no dependencies.  B: depends on A.  T: declares A's identity over other
; octets, so the host digest of its octets is not A's.
(defconst *ct-a* (fn-ct-make-article "<a@example.invalid>" *ct-id-a* '(72 105) nil))
(defconst *ct-b* (fn-ct-make-article "<b@example.invalid>" *ct-id-b* '(66 121 101)
                                     (list *ct-id-a*)))
(defconst *ct-t* (fn-ct-make-article "<t@example.invalid>" *ct-id-a* '(72 105 33) nil))

(defconst *ct-unknown* (list 7 '(1 2 3)))
(defconst *ct-container*
  (fn-ct-make-container 1 (list *ct-t* *ct-a* *ct-b*) (list *ct-unknown*)))
(defconst *ct-digests* (list *ct-digest-t* *ct-digest-a* *ct-digest-b*))
(defconst *ct-obligations*
  (list *ct-obligation-1* *ct-obligation-2* *ct-obligation-3*))
(assert-event (fn-ct-containerp *ct-container* *ct-profile*))

; Validation, before any node is involved.
(assert-event (fn-ct-identity-okp *ct-a* *ct-digest-a*))
(assert-event (not (fn-ct-identity-okp *ct-t* *ct-digest-t*)))
(assert-event
 (fn-ct-article-validp *ct-a* *ct-digest-a* (fn-ct-articles *ct-container*)
                       *ct-digests* nil *ct-profile* 3))
(assert-event
 (fn-ct-article-validp *ct-b* *ct-digest-b* (fn-ct-articles *ct-container*)
                       *ct-digests* nil *ct-profile* 3))
(assert-event
 (not (fn-ct-article-validp *ct-t* *ct-digest-t* (fn-ct-articles *ct-container*)
                            *ct-digests* nil *ct-profile* 3)))
; B's dependency is provided by A, not by T, although T declares A's id.
(assert-event
 (equal (fn-ct-find-provider *ct-id-a* (fn-ct-articles *ct-container*) *ct-digests*)
        (cons *ct-a* *ct-digest-a*)))

; Publication of the whole container.
(defconst *ct-run*
  (fn-ct-publish-container *ct-node* *ct-container* *ct-digests* *ct-obligations*
                           '(:durable :durable :durable) nil *ct-profile*
                           1 *ct-groups* "release"))
(assert-event (equal (fn-frame-item 0 *ct-run*) :ok))
(defconst *ct-final* (fn-frame-item 1 *ct-run*))
(defconst *ct-outcomes* (fn-frame-item 2 *ct-run*))
(assert-event (fn-node-statep *ct-final*))
(assert-event (equal (len (fn-state-articles (fn-node-acceptance *ct-final*))) 2))
(assert-event (fn-acceptedp "<a@example.invalid>"
                            (fn-state-articles (fn-node-acceptance *ct-final*))))
(assert-event (fn-acceptedp "<b@example.invalid>"
                            (fn-state-articles (fn-node-acceptance *ct-final*))))
(assert-event (not (fn-acceptedp "<t@example.invalid>"
                                 (fn-state-articles (fn-node-acceptance *ct-final*)))))
(assert-event (equal (nth 0 *ct-outcomes*) (list "<t@example.invalid>" :invalid nil)))
(assert-event (equal (fn-frame-item 1 (nth 1 *ct-outcomes*)) :accepted))
(assert-event (fn-ct-receiptp (fn-frame-item 2 (nth 1 *ct-outcomes*))))
(assert-event (equal (fn-frame-item 1 (nth 2 *ct-outcomes*)) :accepted))
(assert-event
 (equal (fn-frame-item 2 (nth 2 *ct-outcomes*))
        (list :accepted "<b@example.invalid>" *ct-id-b*
              (fn-ct-obligation-string *ct-obligation-3*))))
(assert-event (equal (fn-frame-item 3 *ct-run*) nil))
; The unknown object was carried and changed nothing.
(assert-event
 (equal (fn-ct-publish-container
         *ct-node* (fn-ct-make-container 1 (list *ct-t* *ct-a* *ct-b*) nil)
         *ct-digests* *ct-obligations* '(:durable :durable :durable) nil
         *ct-profile* 1 *ct-groups* "release")
        *ct-run*))

; Refusals that never reach the node: version, missing dependency, cycles,
; sizes, a non-durable completion.
(assert-event
 (equal (fn-ct-publish-container
         *ct-node* (fn-ct-make-container 2 (list *ct-a*) nil) (list *ct-digest-a*)
         (list *ct-obligation-1*) '(:durable) nil *ct-profile* 1 *ct-groups*
         "release")
        '(:refused :container)))
(defconst *ct-m* (fn-ct-make-article "<m@example.invalid>" *ct-id-c* '(77)
                                     (list *ct-id-d*)))
(assert-event (not (fn-ct-article-validp *ct-m* *ct-digest-c* (list *ct-m*)
                                         (list *ct-digest-c*) nil *ct-profile* 1)))
(assert-event (fn-ct-article-validp *ct-m* *ct-digest-c* (list *ct-m*)
                                    (list *ct-digest-c*) (list *ct-id-d*)
                                    *ct-profile* 1))
(defconst *ct-c1* (fn-ct-make-article "<c1@example.invalid>" *ct-id-c* '(67)
                                      (list *ct-id-d*)))
(defconst *ct-c2* (fn-ct-make-article "<c2@example.invalid>" *ct-id-d* '(68)
                                      (list *ct-id-c*)))
(assert-event
 (not (fn-ct-article-validp *ct-c1* *ct-digest-c* (list *ct-c1* *ct-c2*)
                            (list *ct-digest-c* *ct-digest-d*) nil *ct-profile* 2)))
(assert-event
 (not (fn-ct-article-validp *ct-c2* *ct-digest-d* (list *ct-c1* *ct-c2*)
                            (list *ct-digest-c* *ct-digest-d*) nil *ct-profile* 2)))
(defconst *ct-oversize*
  (fn-ct-make-article "<o@example.invalid>" *ct-id-c*
                      (make-list 65 :initial-element 0) nil))
(assert-event (not (fn-ct-article-shapep *ct-oversize* *ct-profile*)))
(defconst *ct-aborted*
  (fn-ct-publish-article *ct-node* *ct-a* *ct-digest-a* (list *ct-a*)
                         (list *ct-digest-a*) nil *ct-profile* 1 *ct-groups*
                         "release" *ct-obligation-1* :aborted))
(assert-event (equal (fn-ct-result-status *ct-aborted*) :not-durable))
(assert-event (equal (fn-ct-result-receipt *ct-aborted*) nil))
(assert-event (not (fn-acceptedp "<a@example.invalid>"
                                 (fn-state-articles
                                  (fn-node-acceptance (fn-ct-result-state *ct-aborted*))))))

; OBJ-004: one Message-ID with two content ids is evidence, and the node
; publishes only the first.
(defconst *ct-a-prime* (fn-ct-make-article "<a@example.invalid>" *ct-id-c* '(67) nil))
(defconst *ct-conflict-run*
  (fn-ct-publish-container
   *ct-node* (fn-ct-make-container 1 (list *ct-a* *ct-a-prime*) nil)
   (list *ct-digest-a* *ct-digest-c*) (list *ct-obligation-1* *ct-obligation-2*)
   '(:durable :durable) nil *ct-profile* 1 *ct-groups* "release"))
(assert-event (equal (fn-frame-item 3 *ct-conflict-run*) (list *ct-a* *ct-a-prime*)))
(assert-event (equal (fn-frame-item 1 (nth 0 (fn-frame-item 2 *ct-conflict-run*)))
                     :accepted))
(assert-event (equal (fn-frame-item 1 (nth 1 (fn-frame-item 2 *ct-conflict-run*)))
                     :refused))

; -----------------------------------------------------------------------------
; Teeth for fn-ct-receipt-implies-validated: the tampered article gets no
; receipt and is not valid, so dropping the hypothesis loses the conclusion.
(defconst *ct-t-result*
  (fn-ct-publish-article *ct-node* *ct-t* *ct-digest-t* (fn-ct-articles *ct-container*)
                         *ct-digests* nil *ct-profile* 1 *ct-groups* "release"
                         *ct-obligation-1* :durable))
(assert-event (not (fn-ct-receiptp (fn-ct-result-receipt *ct-t-result*))))
(assert-event (equal (fn-ct-result-receipt *ct-t-result*) nil))
(local
 (must-fail
  (defthm ct-teeth-validated-without-receipt
    (fn-ct-article-validp *ct-t* *ct-digest-t* (fn-ct-articles *ct-container*)
                          *ct-digests* nil *ct-profile* 3))))

; Teeth for fn-ct-accepted-is-complete-of-prepare: the node would have
; accepted the tampered article; validation, not the node, stopped it.  The
; composition applied to it is not the result state.
(assert-event
 (not (equal (fn-node-complete
              (fn-node-prepare *ct-node* 1 "<t@example.invalid>" '(72 105 33)
                               *ct-groups* (fn-ct-obligation-string *ct-obligation-1*)
                               (fn-ct-subject-string *ct-t*) "release"
                               (fn-ct-charge *ct-t*))
              0 1 :durable)
             *ct-node*)))
(assert-event (equal (fn-ct-result-state *ct-t-result*) *ct-node*))
(local
 (must-fail
  (defthm ct-teeth-composition-without-accepted
    (equal (fn-ct-result-state *ct-t-result*)
           (fn-node-complete
            (fn-node-prepare *ct-node* 1 "<t@example.invalid>" '(72 105 33)
                             *ct-groups* (fn-ct-obligation-string *ct-obligation-1*)
                             (fn-ct-subject-string *ct-t*) "release"
                             (fn-ct-charge *ct-t*))
            0 1 :durable)))))

; Teeth for fn-ct-invalid-article-leaves-node-unchanged: a valid article
; moves the node.
(defconst *ct-a-result*
  (fn-ct-publish-article *ct-node* *ct-a* *ct-digest-a* (fn-ct-articles *ct-container*)
                         *ct-digests* nil *ct-profile* 1 *ct-groups* "release"
                         *ct-obligation-2* :durable))
(assert-event (equal (fn-ct-result-status *ct-a-result*) :accepted))
(assert-event (not (equal (fn-ct-result-state *ct-a-result*) *ct-node*)))
(local
 (must-fail
  (defthm ct-teeth-unchanged-without-invalid
    (equal (fn-ct-result-state *ct-a-result*) *ct-node*))))

; Teeth for fn-ct-store-resolved-verdict-ignores-siblings: B resolves its
; dependency only through its sibling, so its verdict does depend on the
; container.
(assert-event (not (fn-ct-all-in-store (fn-ct-article-deps *ct-b*) nil)))
(assert-event
 (not (equal (fn-ct-article-validp *ct-b* *ct-digest-b* (fn-ct-articles *ct-container*)
                                   *ct-digests* nil *ct-profile* 3)
             (fn-ct-article-validp *ct-b* *ct-digest-b* nil nil nil *ct-profile* 3))))
(local
 (must-fail
  (defthm ct-teeth-independence-without-store-resolution
    (equal (fn-ct-article-validp *ct-b* *ct-digest-b* (fn-ct-articles *ct-container*)
                                 *ct-digests* nil *ct-profile* 3)
           (fn-ct-article-validp *ct-b* *ct-digest-b* nil nil nil *ct-profile* 3)))))

; Teeth for fn-ct-self-dependency-never-validates
;   (implies (and (not (member-equal id store))
;                 (member-equal id (fn-ct-article-deps
;                                   (car (fn-ct-find-provider id articles digests)))))
;            (not (fn-ct-article-validp (car (fn-ct-find-provider id articles digests))
;                                       digest articles digests store profile fuel)))
(defconst *ct-s* (fn-ct-make-article "<s@example.invalid>" *ct-id-c* '(67)
                                     (list *ct-id-c*)))
(assert-event (equal (fn-ct-find-provider *ct-id-c* (list *ct-s*) (list *ct-digest-c*))
                     (cons *ct-s* *ct-digest-c*)))
(assert-event (not (fn-ct-article-validp *ct-s* *ct-digest-c* (list *ct-s*)
                                         (list *ct-digest-c*) nil *ct-profile* 5)))
; Hypothesis 1 dropped: with the id in the local store the dependency is
; satisfied outside the container and the article validates.
(assert-event (fn-ct-article-validp *ct-s* *ct-digest-c* (list *ct-s*)
                                    (list *ct-digest-c*) (list *ct-id-c*)
                                    *ct-profile* 5))
(local
 (must-fail
  (defthm ct-teeth-cycle-with-store
    (not (fn-ct-article-validp
          (car (fn-ct-find-provider *ct-id-c* (list *ct-s*) (list *ct-digest-c*)))
          *ct-digest-c* (list *ct-s*) (list *ct-digest-c*) (list *ct-id-c*)
          *ct-profile* 5)))))
; Hypothesis 2 dropped: when the container's provider of the id is another
; article with the same octets and no self-dependency, that provider is the
; subject of the conclusion and it validates.  S itself also validates in
; this container, because its dependency is on content the container does
; provide: the limitation that dependencies are container metadata, not
; identified bytes (specs/container.md).
(defconst *ct-s-provider* (fn-ct-make-article "<p@example.invalid>" *ct-id-c* '(67) nil))
(assert-event
 (equal (fn-ct-find-provider *ct-id-c* (list *ct-s-provider* *ct-s*)
                             (list *ct-digest-c* *ct-digest-c*))
        (cons *ct-s-provider* *ct-digest-c*)))
(assert-event (not (member-equal *ct-id-c* (fn-ct-article-deps *ct-s-provider*))))
(assert-event (fn-ct-article-validp *ct-s-provider* *ct-digest-c*
                                    (list *ct-s-provider* *ct-s*)
                                    (list *ct-digest-c* *ct-digest-c*) nil
                                    *ct-profile* 5))
(assert-event (fn-ct-article-validp *ct-s* *ct-digest-c* (list *ct-s-provider* *ct-s*)
                                    (list *ct-digest-c* *ct-digest-c*) nil
                                    *ct-profile* 5))
(local
 (must-fail
  (defthm ct-teeth-cycle-without-self-dependency
    (not (fn-ct-article-validp
          (car (fn-ct-find-provider *ct-id-c* (list *ct-s-provider* *ct-s*)
                                    (list *ct-digest-c* *ct-digest-c*)))
          *ct-digest-c* (list *ct-s-provider* *ct-s*)
          (list *ct-digest-c* *ct-digest-c*) nil *ct-profile* 5)))))

; Teeth for fn-ct-conflict-is-evidence
;   (implies (and (member-equal a candidates) (member-equal b articles)
;                 (equal (fn-ct-article-msgid a) (fn-ct-article-msgid b))
;                 (not (equal (fn-ct-article-content-id a) (fn-ct-article-content-id b))))
;            (member-equal a (fn-ct-conflict-evidence candidates articles)))
; Hypothesis 1 dropped: an article that is not a candidate is not evidence.
(assert-event (not (member-equal *ct-a* (fn-ct-conflict-evidence (list *ct-b*)
                                                                 (list *ct-a* *ct-a-prime*)))))
(local
 (must-fail
  (defthm ct-teeth-conflict-without-candidate
    (member-equal *ct-a* (fn-ct-conflict-evidence (list *ct-b*)
                                                  (list *ct-a* *ct-a-prime*))))))
; Hypothesis 2 dropped: without the rival among the articles there is none.
(assert-event (equal (fn-ct-conflict-evidence (list *ct-a*) (list *ct-a* *ct-b*)) nil))
(local
 (must-fail
  (defthm ct-teeth-conflict-without-rival-present
    (member-equal *ct-a* (fn-ct-conflict-evidence (list *ct-a*) (list *ct-a* *ct-b*))))))
; Hypothesis 3 dropped: different Message-IDs with different content are not
; a conflict.
(assert-event (equal (fn-ct-conflict-evidence (list *ct-a* *ct-b*) (list *ct-a* *ct-b*))
                     nil))
(local
 (must-fail
  (defthm ct-teeth-conflict-without-same-msgid
    (member-equal *ct-a* (fn-ct-conflict-evidence (list *ct-a* *ct-b*)
                                                  (list *ct-a* *ct-b*))))))
; Hypothesis 4 dropped: two identical copies of one article share the
; Message-ID and the content id; they are duplicates, not evidence.
(assert-event (equal (fn-ct-conflict-evidence (list *ct-a* *ct-a*) (list *ct-a* *ct-a*))
                     nil))
(local
 (must-fail
  (defthm ct-teeth-conflict-without-different-content
    (member-equal *ct-a* (fn-ct-conflict-evidence (list *ct-a* *ct-a*)
                                                  (list *ct-a* *ct-a*))))))

; Teeth for fn-ct-invalid-head-does-not-block-siblings: a valid head changes
; the state its siblings see.
(assert-event
 (not (equal (fn-frame-item 0 (fn-ct-publish-list
                                *ct-node* (list *ct-a* *ct-b*)
                                (list *ct-digest-a* *ct-digest-b*)
                                (list *ct-obligation-1* *ct-obligation-2*)
                                '(:durable :durable)
                                (list *ct-a* *ct-b*) (list *ct-digest-a* *ct-digest-b*)
                                nil *ct-profile* 1 *ct-groups* "release"))
             (fn-frame-item 0 (fn-ct-publish-list
                                *ct-node* (list *ct-b*)
                                (list *ct-digest-b*)
                                (list *ct-obligation-2*)
                                '(:durable)
                                (list *ct-a* *ct-b*) (list *ct-digest-a* *ct-digest-b*)
                                nil *ct-profile* 1 *ct-groups* "release")))))
(local
 (must-fail
  (defthm ct-teeth-siblings-with-valid-head
    (equal (fn-frame-item 0 (fn-ct-publish-list
                              *ct-node* (list *ct-a* *ct-b*)
                              (list *ct-digest-a* *ct-digest-b*)
                              (list *ct-obligation-1* *ct-obligation-2*)
                              '(:durable :durable)
                              (list *ct-a* *ct-b*) (list *ct-digest-a* *ct-digest-b*)
                              nil *ct-profile* 1 *ct-groups* "release"))
           (fn-frame-item 0 (fn-ct-publish-list
                              *ct-node* (list *ct-b*)
                              (list *ct-digest-b*)
                              (list *ct-obligation-2*)
                              '(:durable)
                              (list *ct-a* *ct-b*) (list *ct-digest-a* *ct-digest-b*)
                              nil *ct-profile* 1 *ct-groups* "release"))))))

; Teeth for fn-ct-accepted-article-is-in-the-node: a node refusal (no
; retention capacity for the charge) is :refused, and the article is absent.
(defconst *ct-tiny-node* (fn-node-initial-state *ct-groups* 1))
(defconst *ct-refused*
  (fn-ct-publish-article *ct-tiny-node* *ct-a* *ct-digest-a* (list *ct-a*)
                         (list *ct-digest-a*) nil *ct-profile* 1 *ct-groups*
                         "release" *ct-obligation-1* :durable))
(assert-event (equal (fn-ct-result-status *ct-refused*) :refused))
(assert-event (equal (fn-ct-result-receipt *ct-refused*) nil))
(assert-event (not (fn-acceptedp "<a@example.invalid>"
                                 (fn-state-articles
                                  (fn-node-acceptance (fn-ct-result-state *ct-refused*))))))
(local
 (must-fail
  (defthm ct-teeth-published-without-accepted
    (fn-acceptedp "<a@example.invalid>"
                  (fn-state-articles
                   (fn-node-acceptance (fn-ct-result-state *ct-refused*)))))))

; Teeth for fn-ct-unknowns-are-never-consulted: an unknown over the bound is
; a container refusal, so the two containers no longer agree.
(defconst *ct-big-unknown* (list 7 (make-list 17 :initial-element 0)))
(assert-event (not (fn-ct-unknowns-okp (list *ct-big-unknown*) *ct-profile*)))
(assert-event
 (equal (fn-ct-publish-container
         *ct-node* (fn-ct-make-container 1 (list *ct-a*) (list *ct-big-unknown*))
         (list *ct-digest-a*) (list *ct-obligation-1*) '(:durable) nil
         *ct-profile* 1 *ct-groups* "release")
        '(:refused :container)))
(assert-event
 (not (equal (fn-ct-publish-container
              *ct-node* (fn-ct-make-container 1 (list *ct-a*) (list *ct-unknown*))
              (list *ct-digest-a*) (list *ct-obligation-1*) '(:durable) nil
              *ct-profile* 1 *ct-groups* "release")
             (fn-ct-publish-container
              *ct-node* (fn-ct-make-container 1 (list *ct-a*) (list *ct-big-unknown*))
              (list *ct-digest-a*) (list *ct-obligation-1*) '(:durable) nil
              *ct-profile* 1 *ct-groups* "release"))))
(local
 (must-fail
  (defthm ct-teeth-unknowns-over-bound
    (equal (fn-ct-publish-container
            *ct-node* (fn-ct-make-container 1 (list *ct-a*) (list *ct-unknown*))
            (list *ct-digest-a*) (list *ct-obligation-1*) '(:durable) nil
            *ct-profile* 1 *ct-groups* "release")
           (fn-ct-publish-container
            *ct-node* (fn-ct-make-container 1 (list *ct-a*) (list *ct-big-unknown*))
            (list *ct-digest-a*) (list *ct-obligation-1*) '(:durable) nil
            *ct-profile* 1 *ct-groups* "release")))))

; Teeth for fn-ct-identity-okp-is-spec-okp: with a digest that is not the
; digest of the octets the executable check answers for a different payload,
; and nothing relates it to the constrained digest of the octets.
(assert-event (not (fn-ct-identity-okp *ct-a* *ct-digest-b*)))
(assert-event (fn-ct-identity-okp *ct-a* *ct-digest-a*))
(local
 (must-fail
  (defthm ct-teeth-identity-without-the-digest-of-the-octets
    (equal (fn-ct-identity-okp *ct-a* *ct-digest-a*)
           (fn-ct-identity-spec-okp *ct-a*)))))
