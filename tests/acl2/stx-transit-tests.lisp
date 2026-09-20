; Witnesses and teeth for the transit half of the substrate: the lace as the
; store projected, the bridge, equivocation, the index, policy confinement
; and the commit carrier.
;
; specs/substrate-transport.md sections 2 to 4; keystones S3-1, S3-2, S3-3,
; S4-1, S5-1.
;
; The seam is constrained, so this book inherits crypto-seam-tests' TOY
; realiser (a polynomial mix digest and a sign-by-public-key scheme, neither
; cryptographic -- A-CRYPTO).  Every witness below is a statement about the
; composition, never about unforgeability or collision resistance.  A
; defconst may not call an attached function (:DOC ignored-attachment), so
; every constant that reaches the realiser is built by make-event.

(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "../../books/stx-epochs")
(include-book "../../books/stx-authority")

; -----------------------------------------------------------------------------
; Two principals, one keyring, and a store made of article records

(defun fn-stxt-line (str)
  (declare (xargs :guard t))
  (append (fn-record-string-octets (if (stringp str) str "")) '(13 10)))

(defconst *stxt-sk-a* (make-list 32 :initial-element 11))
(defconst *stxt-sk-b* (make-list 32 :initial-element 23))
(defconst *stxt-token* '(9 9))

(make-event (list 'defconst '*stxt-pk-a* (list 'quote (fn-sig-public-key *stxt-sk-a*))))
(make-event (list 'defconst '*stxt-pk-b* (list 'quote (fn-sig-public-key *stxt-sk-b*))))
(make-event (list 'defconst '*stxt-a* (list 'quote (fn-prin-id *stxt-pk-a* *stxt-token*))))
(make-event (list 'defconst '*stxt-b* (list 'quote (fn-prin-id *stxt-pk-b* *stxt-token*))))
(make-event (list 'defconst '*stxt-keyring*
                  (list 'quote (list (cons *stxt-a* *stxt-pk-a*)
                                     (cons *stxt-b* *stxt-pk-b*)))))

(assert-event (fn-prin-keyringp *stxt-keyring*))
(assert-event (not (equal *stxt-a* *stxt-b*)))

(defun fn-stxt-authored (subject body)
  (declare (xargs :guard t))
  (append (fn-stxt-line "From: someone@example.invalid")
          (append (fn-stxt-line "Newsgroups: fn.test")
                  (append (fn-stxt-line (if (stringp subject) subject "Subject: s"))
                          (append (fn-stxt-line "Message-ID: <x@example.invalid>")
                                  (append '(13 10)
                                          (fn-record-string-octets
                                           (if (stringp body) body ""))))))))

(defun fn-stxt-received (field authored)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "FN-Statement: ")
          (append (if (true-listp field) field nil)
                  (append '(13 10) (if (true-listp authored) authored nil)))))

; An article record as the acceptance machine holds it: the received octets
; are the payload, which is what fn-stx-delta projects from.
(defun fn-stxt-record (msgid octets)
  (declare (xargs :guard t))
  (fn-make-article msgid octets nil nil t))

; A node whose store is exactly `articles`.
(defun fn-stxt-node (articles)
  (declare (xargs :guard t))
  (fn-node-make-state (fn-make-state nil nil articles 0 nil nil) nil nil nil))

(assert-event (equal (fn-stx-store (fn-stxt-node '(1 2 3))) '(1 2 3)))

; -----------------------------------------------------------------------------
; One verified article, one unverified one

(make-event (list 'defconst '*stxt-src-1* (list 'quote (fn-stxt-authored "Subject: one" "first"))))
(make-event (list 'defconst '*stxt-s1*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 1 1 nil :article
                                             *stxt-src-1*))))
(make-event (list 'defconst '*stxt-r1*
                  (list 'quote (fn-stxt-record "<1>"
                                (fn-stxt-received (fn-stx-header-value *stxt-s1*)
                                                  *stxt-src-1*)))))

; The verified article contributes exactly its statement.
(assert-event (equal (fn-stx-delta (fn-article-payload *stxt-r1*) *stxt-keyring*)
                     (list *stxt-s1*)))

; The SPINE, as a witness: the same bytes under a keyring that does not know
; the creator are stored and contribute nothing to the lace.  Not refused --
; the record is identical; only the authority is gone.
(assert-event (equal (fn-stx-delta (fn-article-payload *stxt-r1*) nil) nil))

; An article with no field at all: :absent, and again no authority.
(make-event (list 'defconst '*stxt-r0*
                  (list 'quote (fn-stxt-record "<0>" (fn-stxt-authored "Subject: bare" "b")))))
(assert-event (equal (fn-stx-delta (fn-article-payload *stxt-r0*) *stxt-keyring*) nil))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict (fn-stx-parse (fn-article-payload *stxt-r0*))
                                      *stxt-keyring* 3))
                     :absent))

; -----------------------------------------------------------------------------
; S3-1: the bridge and the union of ids, on a reachable run
;
; The store is newest-first, so accepting *stxt-r1* onto a store holding
; *stxt-r0* is (cons *stxt-r1* (list *stxt-r0*)).

(make-event (list 'defconst '*stxt-node-0* (list 'quote (fn-stxt-node (list *stxt-r0*)))))
(make-event (list 'defconst '*stxt-node-1*
                  (list 'quote (fn-stxt-node (list *stxt-r1* *stxt-r0*)))))

(assert-event (fn-stx-acceptedp *stxt-node-0* *stxt-node-1* *stxt-r1*))
(assert-event (equal (fn-stx-lace *stxt-node-0* *stxt-keyring*) nil))
(assert-event (equal (fn-stx-lace *stxt-node-1* *stxt-keyring*) (list *stxt-s1*)))
(assert-event (fn-stx-delta-freshp (fn-stx-lace *stxt-node-0* *stxt-keyring*)
                                   (fn-stx-delta (fn-article-payload *stxt-r1*)
                                                 *stxt-keyring*)))
(assert-event (equal (fn-stx-lace *stxt-node-1* *stxt-keyring*)
                     (fn-lace-merge (fn-stx-lace *stxt-node-0* *stxt-keyring*)
                                    (fn-stx-delta (fn-article-payload *stxt-r1*)
                                                  *stxt-keyring*))))

; The `:have` path, exercised rather than assumed: the SAME statement offered
; again under a second Message-ID.  The store grows, the lace's ids do not,
; and the freshness hypothesis of the bridge is FALSE on this run -- which is
; why it is a hypothesis and not a comment.
(make-event (list 'defconst '*stxt-r1-again*
                  (list 'quote (fn-stxt-record "<1b>"
                                (fn-stxt-received (fn-stx-header-value *stxt-s1*)
                                                  *stxt-src-1*)))))
(make-event (list 'defconst '*stxt-node-1b*
                  (list 'quote (fn-stxt-node (list *stxt-r1-again* *stxt-r1* *stxt-r0*)))))
(assert-event (fn-stx-acceptedp *stxt-node-1* *stxt-node-1b* *stxt-r1-again*))
(assert-event (not (fn-stx-delta-freshp
                    (fn-stx-lace *stxt-node-1* *stxt-keyring*)
                    (fn-stx-delta (fn-article-payload *stxt-r1-again*) *stxt-keyring*))))
(assert-event (equal (fn-lace-ids (fn-stx-lace *stxt-node-1b* *stxt-keyring*))
                     (list (fn-stmt-id *stxt-s1*) (fn-stmt-id *stxt-s1*))))

; The tooth for the durable-completion hypothesis: a transaction that did not
; publish leaves the store equal, so fn-stx-acceptedp is false and the lace
; does not move.
(assert-event (not (fn-stx-acceptedp *stxt-node-0* *stxt-node-0* *stxt-r1*)))
(assert-event (equal (fn-stx-lace *stxt-node-0* *stxt-keyring*)
                     (fn-stx-lace *stxt-node-0* *stxt-keyring*)))

; -----------------------------------------------------------------------------
; S3-2: equivocation.  One key, one (creator, incarnation, sequence), two
; payloads: the D10 restore-from-snapshot fork, arriving at transit.

(make-event (list 'defconst '*stxt-src-f1* (list 'quote (fn-stxt-authored "Subject: fork" "left"))))
(make-event (list 'defconst '*stxt-src-f2* (list 'quote (fn-stxt-authored "Subject: fork" "right"))))
(make-event (list 'defconst '*stxt-f1*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 2 5 nil :article *stxt-src-f1*))))
(make-event (list 'defconst '*stxt-f2*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 2 5 nil :article *stxt-src-f2*))))
(make-event (list 'defconst '*stxt-rf1*
                  (list 'quote (fn-stxt-record "<f1>"
                                (fn-stxt-received (fn-stx-header-value *stxt-f1*) *stxt-src-f1*)))))
(make-event (list 'defconst '*stxt-rf2*
                  (list 'quote (fn-stxt-record "<f2>"
                                (fn-stxt-received (fn-stx-header-value *stxt-f2*) *stxt-src-f2*)))))

; The A-CRYPTO edge is not assumed away: the two forks have distinct content
; ids under the toy digest, which is the hypothesis fn-lace-merge-drops-at-
; collision says is needed.
(assert-event (not (equal (fn-stmt-id *stxt-f1*) (fn-stmt-id *stxt-f2*))))
(assert-event (fn-lace-same-slotp *stxt-f1* *stxt-f2*))

(make-event (list 'defconst '*stxt-fork-a* (list 'quote (fn-stxt-node (list *stxt-rf1*)))))
(make-event (list 'defconst '*stxt-fork-ab*
                  (list 'quote (fn-stxt-node (list *stxt-rf2* *stxt-rf1*)))))

(assert-event (fn-stx-acceptedp *stxt-fork-a* *stxt-fork-ab* *stxt-rf2*))
; BOTH FORKS ARE KEPT, and the equivocation is visible after the merge.
(assert-event (member-equal *stxt-f1* (fn-stx-lace *stxt-fork-ab* *stxt-keyring*)))
(assert-event (member-equal *stxt-f2* (fn-stx-lace *stxt-fork-ab* *stxt-keyring*)))
(assert-event (fn-lace-equivocatorp (fn-stx-lace *stxt-fork-ab* *stxt-keyring*)
                                    *stxt-a* 2))
; And it was not visible before: the hypothesis that the two are distinct and
; share a slot is doing the work.
(assert-event (not (fn-lace-equivocatorp (fn-stx-lace *stxt-fork-a* *stxt-keyring*)
                                         *stxt-a* 2)))
; A different incarnation is not an equivocation of this one.
(assert-event (not (fn-lace-equivocatorp (fn-stx-lace *stxt-fork-ab* *stxt-keyring*)
                                         *stxt-a* 1)))
; Nor is another principal implicated.
(assert-event (not (fn-lace-equivocatorp (fn-stx-lace *stxt-fork-ab* *stxt-keyring*)
                                         *stxt-b* 2)))

; -----------------------------------------------------------------------------
; S3-3: the index twin, on the same run.  The record names both ids.

(make-event
 (list 'defconst '*stxt-index-ab*
       (list 'quote (fn-stx-index-of-store (fn-stx-store *stxt-fork-ab*) *stxt-keyring*))))

(assert-event (fn-stx-index-invariantp *stxt-index-ab* *stxt-fork-ab* *stxt-keyring*))
(assert-event (equal (fn-stx-index-lookup *stxt-index-ab* (fn-stmt-id *stxt-f1*))
                     (fn-lace-lookup (fn-stx-lace *stxt-fork-ab* *stxt-keyring*)
                                     (fn-stmt-id *stxt-f1*))))
(assert-event (fn-stx-index-equivocatorp *stxt-index-ab* *stxt-a* 2))
(assert-event (fn-stx-recorded-equivocationp *stxt-index-ab* *stxt-a* 2))
(assert-event (not (fn-stx-index-equivocatorp *stxt-index-ab* *stxt-a* 1)))
; The record is a discovery aid that names the pair, oldest id first.
(assert-event (equal (fn-stx-index-records *stxt-index-ab*)
                     (list (fn-stx-equivocation-record *stxt-f1* *stxt-f2*))))
(assert-event (equal (fn-stx-record-id-held
                      (car (fn-stx-index-records *stxt-index-ab*)))
                     (fn-stmt-id *stxt-f1*)))
(assert-event (equal (fn-stx-record-id-new
                      (car (fn-stx-index-records *stxt-index-ab*)))
                     (fn-stmt-id *stxt-f2*)))
; The invariant is load-bearing: an index that is not this store's index says
; nothing about this store's lace.
(assert-event (not (fn-stx-index-invariantp (fn-stx-index-empty) *stxt-fork-ab*
                                            *stxt-keyring*)))
(assert-event (not (fn-stx-index-equivocatorp (fn-stx-index-empty) *stxt-a* 2)))

; -----------------------------------------------------------------------------
; S4-1: a peer cannot widen a group's policy
;
; A is the configured authority for fn.test at this node.  B is a hostile
; peer with a perfectly valid signature over a perfectly valid policy for the
; same group -- and it changes nothing, because B is not the authority.

(defconst *stxt-group* (fn-record-string-octets "fn.test"))

(make-event (list 'defconst '*stxt-policy-a*
                  (list 'quote (fn-pol-policy-encode
                                (fn-pol-make-policy *stxt-group* (list *stxt-b*) nil)))))
(make-event (list 'defconst '*stxt-pol-stmt-a*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 1 9 nil :policy
                                             *stxt-policy-a*))))
(make-event (list 'defconst '*stxt-pol-stmt-b*
                  (list 'quote (fn-stmt-sign *stxt-sk-b* *stxt-b* 1 9 nil :policy
                                             *stxt-policy-a*))))

(defun fn-stxt-policy-record (msgid statement source)
  (declare (xargs :guard t))
  (fn-stxt-record msgid (fn-stxt-received (fn-stx-header-value statement) source)))

(make-event (list 'defconst '*stxt-src-p* (list 'quote (fn-stxt-authored "Subject: policy" "p"))))
(make-event (list 'defconst '*stxt-rp-a*
                  (list 'quote (fn-stxt-policy-record "<pa>" *stxt-pol-stmt-a* *stxt-src-p*))))
(make-event (list 'defconst '*stxt-rp-b*
                  (list 'quote (fn-stxt-policy-record "<pb>" *stxt-pol-stmt-b* *stxt-src-p*))))

; A policy statement travels as an ordinary article: it decodes to a policy
; and is a candidate only for its own creator.
(assert-event (fn-pol-candidatep *stxt-pol-stmt-a* *stxt-keyring* *stxt-group* *stxt-a*))
(assert-event (not (fn-pol-candidatep *stxt-pol-stmt-b* *stxt-keyring* *stxt-group* *stxt-a*)))

; The hostile batch: B's signed policy for A's group.
(make-event (list 'defconst '*stxt-hostile-batch* (list 'quote (list *stxt-rp-b*))))
(assert-event (fn-pol-delta-without-authority-p
               (fn-stx-batch-delta *stxt-hostile-batch* *stxt-keyring*)
               *stxt-keyring* *stxt-a*))
(assert-event (equal (fn-pol-current
                      (fn-stx-lace-of-store
                       (fn-stx-accept-batch nil *stxt-hostile-batch*) *stxt-keyring*)
                      *stxt-keyring* *stxt-group* *stxt-a*)
                     (fn-pol-current (fn-stx-lace-of-store nil *stxt-keyring*)
                                     *stxt-keyring* *stxt-group* *stxt-a*)))
(assert-event (equal (fn-pol-current
                      (fn-stx-lace-of-store
                       (fn-stx-accept-batch nil *stxt-hostile-batch*) *stxt-keyring*)
                      *stxt-keyring* *stxt-group* *stxt-a*)
                     nil))

; The genuine authority's batch DOES change it, so the theorem is not vacuous.
(make-event (list 'defconst '*stxt-real-batch* (list 'quote (list *stxt-rp-a*))))
(assert-event (not (fn-pol-delta-without-authority-p
                    (fn-stx-batch-delta *stxt-real-batch* *stxt-keyring*)
                    *stxt-keyring* *stxt-a*)))
(assert-event (equal (fn-pol-current
                      (fn-stx-lace-of-store
                       (fn-stx-accept-batch nil *stxt-real-batch*) *stxt-keyring*)
                      *stxt-keyring* *stxt-group* *stxt-a*)
                     *stxt-pol-stmt-a*))
; And the offender is named.
(assert-event (equal (fn-pol-first-authority-stmt
                      (fn-stx-batch-delta *stxt-real-batch* *stxt-keyring*)
                      *stxt-keyring* *stxt-a*)
                     *stxt-pol-stmt-a*))

; The gate, on a node that holds A's policy admitting B.
(make-event (list 'defconst '*stxt-pol-node*
                  (list 'quote (fn-stxt-node (list *stxt-rp-a*)))))
(make-event (list 'defconst '*stxt-src-post* (list 'quote (fn-stxt-authored "Subject: post" "hi"))))
(make-event (list 'defconst '*stxt-post-b*
                  (list 'quote (fn-stmt-sign *stxt-sk-b* *stxt-b* 1 1 nil :article
                                             *stxt-src-post*))))
(make-event (list 'defconst '*stxt-r-post-b*
                  (list 'quote (fn-stxt-record "<pb1>"
                                (fn-stxt-received (fn-stx-header-value *stxt-post-b*)
                                                  *stxt-src-post*)))))
(make-event (list 'defconst '*stxt-article-post-b*
                  (list 'quote (fn-stx-parse (fn-article-payload *stxt-r-post-b*)))))

(assert-event (fn-stx-transit-authority-ok *stxt-pol-node* *stxt-article-post-b*
                                           *stxt-keyring* *stxt-group* *stxt-a*))
; With no policy in force the same article admits nothing.
(assert-event (not (fn-stx-transit-authority-ok (fn-stxt-node nil) *stxt-article-post-b*
                                                *stxt-keyring* *stxt-group* *stxt-a*)))
; And an unverified statement admits nothing whatever the policy says.
(assert-event (not (fn-stx-transit-authority-ok *stxt-pol-node* *stxt-article-post-b*
                                                nil *stxt-group* *stxt-a*)))

; -----------------------------------------------------------------------------
; S5-1: the commit carrier
;
; A commit enters the merge only from a verified statement.

(defconst *stxt-commit*
  (fn-me-commit '(1 1 1) 0 '(2 2) :remove '(3 3)))
(assert-event (fn-me-commitp *stxt-commit*))
(assert-event (fn-stmt-okp (fn-stx-commit-decode-exact
                            (fn-stx-commit-encode *stxt-commit*))))
(assert-event (equal (fn-stmt-value (fn-stx-commit-decode-exact
                                     (fn-stx-commit-encode *stxt-commit*)))
                     *stxt-commit*))

(make-event (list 'defconst '*stxt-commit-stmt-a*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 3 1 nil :policy
                                             (fn-stx-commit-encode *stxt-commit*)))))
(make-event (list 'defconst '*stxt-commit-stmt-x*
                  (list 'quote (fn-stmt-sign *stxt-sk-b* *stxt-b* 3 1 nil :policy
                                             (fn-stx-commit-encode *stxt-commit*)))))
(make-event (list 'defconst '*stxt-rc-ok*
                  (list 'quote (fn-stxt-policy-record "<c1>" *stxt-commit-stmt-a*
                                                      *stxt-src-p*))))
(make-event (list 'defconst '*stxt-rc-bad*
                  (list 'quote (fn-stxt-policy-record "<c2>" *stxt-commit-stmt-x*
                                                      *stxt-src-p*))))

; One verified and one unverified commit-bearing article: under a keyring
; that knows only A, the delta is the singleton.
(make-event (list 'defconst '*stxt-keyring-a* (list 'quote (list (cons *stxt-a* *stxt-pk-a*)))))
(make-event (list 'defconst '*stxt-commit-batch* (list 'quote (list *stxt-rc-ok* *stxt-rc-bad*))))

(assert-event (equal (fn-stx-commits-of-batch *stxt-commit-batch* *stxt-keyring-a*)
                     (list *stxt-commit*)))
; The tooth: an unverified article contributes NO commit.
(assert-event (equal (fn-stx-commits-of-batch (list *stxt-rc-bad*) *stxt-keyring-a*)
                     nil))
; And with both known, both contribute -- so the keyring hypothesis is what
; is doing the work, not the shape of the batch.
(assert-event (equal (len (fn-stx-commits-of-batch *stxt-commit-batch* *stxt-keyring*)) 2))

; The merge moves commits and NOT the chain: adoption stays local.
(defconst *stxt-site*
  (fn-me-site '(7) '(8) nil nil 4 4 nil))
(assert-event (fn-me-sitep *stxt-site*))
(assert-event (equal (fn-me-chain (fn-me-site-merge
                                   *stxt-site*
                                   (fn-stx-commits-of-batch *stxt-commit-batch*
                                                            *stxt-keyring-a*)))
                     (fn-me-chain *stxt-site*)))
(assert-event (equal (fn-me-epoch (fn-me-site-merge
                                   *stxt-site*
                                   (fn-stx-commits-of-batch *stxt-commit-batch*
                                                            *stxt-keyring-a*)))
                     0))
(assert-event (consp (fn-me-commits (fn-me-site-merge
                                     *stxt-site*
                                     (fn-stx-commits-of-batch *stxt-commit-batch*
                                                              *stxt-keyring-a*)))))
; Adoption, by contrast, does extend the chain -- so the contrast is real.
(assert-event (equal (len (fn-me-chain (fn-me-adopt *stxt-site* *stxt-commit*))) 1))
