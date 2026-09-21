; Witnesses and teeth for the carried statement index (decision D21).
;
; The seam this book exists for is store-node x substrate: the index of
; books/stx-index is a slot on fn-sn-state, and what has to be exhibited is a
; run of the REAL store transitions that reaches a store with one article in
; it and a carried index that agrees with the lace projection over that store.
; No hand-built state appears below.  (w11/node-index found that every S3
; witness in tests/acl2/stx-transit-tests reached its "next" node with a value
; that was not a node state at all; this book takes acceptance steps.)
;
; It lives in its own file because its two halves sit in different clusters:
; the crypto realiser and the statement come from tests/acl2/crypto-seam-tests
; (Makefile line 255) and the store machine from books/store-node-invariants
; (line 87), so neither cluster's existing test book can hold it without
; inverting the certification order.
;
; The seam is constrained, so this book inherits crypto-seam-tests' TOY
; realiser -- a polynomial mix digest and a sign-by-public-key scheme, neither
; cryptographic (A-CRYPTO).  Every assertion below is about the composition,
; never about unforgeability.  A defconst may not call an attached function
; (:DOC ignored-attachment), so every constant downstream of the realiser is
; built by make-event.

(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "../../books/store-node-invariants")

; -----------------------------------------------------------------------------
; One principal, one keyring, one signed article

(defun fn-sni-line (str)
  (declare (xargs :guard t))
  (append (fn-record-string-octets (if (stringp str) str "")) '(13 10)))

(defconst *sni-sk* (make-list 32 :initial-element 11))
(defconst *sni-token* '(9 9))
(defconst *sni-groups* '("fn.letters" "fn.test"))

(make-event (list 'defconst '*sni-pk* (list 'quote (fn-sig-public-key *sni-sk*))))
(make-event (list 'defconst '*sni-creator*
                  (list 'quote (fn-prin-id *sni-pk* *sni-token*))))
(make-event (list 'defconst '*sni-keyring*
                  (list 'quote (list (cons *sni-creator* *sni-pk*)))))

(assert-event (fn-prin-keyringp *sni-keyring*))

(defun fn-sni-authored (subject body)
  (declare (xargs :guard t))
  (append (fn-sni-line "From: someone@example.invalid")
          (append (fn-sni-line "Newsgroups: fn.test")
                  (append (fn-sni-line (if (stringp subject) subject "Subject: s"))
                          (append (fn-sni-line "Message-ID: <sni@example>")
                                  (append '(13 10)
                                          (fn-record-string-octets
                                           (if (stringp body) body ""))))))))

(defun fn-sni-received (field authored)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "FN-Statement: ")
          (append (if (true-listp field) field nil)
                  (append '(13 10) (if (true-listp authored) authored nil)))))

(make-event (list 'defconst '*sni-src*
                  (list 'quote (fn-sni-authored "Subject: one" "first"))))
(make-event (list 'defconst '*sni-stmt*
                  (list 'quote (fn-stmt-sign *sni-sk* *sni-creator* 1 1 nil
                                             :article *sni-src*))))
(make-event (list 'defconst '*sni-octets*
                  (list 'quote (fn-sni-received
                                (fn-stx-header-value *sni-stmt*) *sni-src*))))

; The delta these bytes contribute under each of the two keyrings.  This is
; the SPINE, and it is why the keyring is a carried field and not a constant:
; the SAME bytes give a one-statement delta under a keyring that knows the
; creator and an EMPTY one under a keyring that does not.
(assert-event (equal (fn-stx-delta *sni-octets* *sni-keyring*) (list *sni-stmt*)))
(assert-event (equal (fn-stx-delta *sni-octets* nil) nil))

(make-event (list 'defconst '*sni-record*
                  (list 'quote (fn-record-make 0 0 0 "<sni@example>" *sni-octets*
                                               *sni-groups* "sni-pin"
                                               "sni-content" "sni-release" 2))))
(assert-event (fn-record-p *sni-record*))

; -----------------------------------------------------------------------------
; The run.  Every step below is a real transition of books/store-node; the
; four io words drive the file kernel exactly as tests/acl2/store-node-tests
; drives it.

(defun fn-sni-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun fn-sni-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))

(defconst *sni-initial* (fn-sn-initial *sni-groups* 10))

; The empty node is indexed under the empty keyring it starts with.
(assert-event (fn-sn-indexedp *sni-initial*))
(assert-event (equal (fn-sn-keyring *sni-initial*) nil))
(assert-event (equal (fn-sn-index *sni-initial*) (fn-stx-index-empty)))
(assert-event (equal (fn-sn-keyring-generation *sni-initial*) 0))
(assert-event (equal (fn-sn-verdicts *sni-initial*) nil))

; Reconfiguration installs the verification context.
(make-event (list 'defconst '*sni-keyed*
                  (list 'quote (fn-sn-set-keyring *sni-initial* *sni-keyring*))))
(assert-event (fn-sn-indexedp *sni-keyed*))
(assert-event (equal (fn-sn-keyring *sni-keyed*) *sni-keyring*))
(assert-event (equal (fn-sn-index *sni-keyed*) (fn-stx-index-empty)))
(assert-event (equal (fn-sn-keyring-generation *sni-keyed*) 1))

; TOOTH on fn-sn-set-keyring's fn-prin-keyringp test: a malformed keyring is
; refused, the state is unchanged, and the old context still stands.
(assert-event (equal (fn-sn-set-keyring *sni-keyed* '(bad)) *sni-keyed*))

(make-event (list 'defconst '*sni-reserved*
                  (list 'quote (fn-sni-reserve *sni-keyed*))))
(make-event (list 'defconst '*sni-prepared*
                  (list 'quote (fn-sn-prepare *sni-reserved* *sni-record*))))
(assert-event (not (equal *sni-prepared* *sni-reserved*)))
(assert-event (fn-sn-indexedp *sni-prepared*))

(make-event (list 'defconst '*sni-completing*
                  (list 'quote (fn-sni-publish *sni-prepared*))))
(assert-event (equal (fn-sf-phase (fn-sn-files *sni-completing*)) :completing))
(assert-event (fn-sn-indexedp *sni-completing*))

; The store is still empty here: nothing has been accepted yet.
(assert-event (equal (len (fn-stx-store (fn-sn-node *sni-completing*))) 0))
(assert-event (equal (len (fn-stx-index-bindings (fn-sn-index *sni-completing*))) 0))

(make-event (list 'defconst '*sni-finished*
                  (list 'quote (fn-sn-finish *sni-completing*))))

; -----------------------------------------------------------------------------
; What the durable completion did, on a state the transitions reached

(assert-event (equal (fn-sf-phase (fn-sn-files *sni-finished*)) :ready))
(assert-event (fn-sn-statep *sni-finished*))

; The store grew by exactly the signed article, and the payload it holds is
; the signed one -- not the empty delta that made two earlier substrate
; witnesses vacuous.
(assert-event (equal (len (fn-stx-store (fn-sn-node *sni-finished*))) 1))
(assert-event (equal (fn-article-payload (car (fn-stx-store (fn-sn-node *sni-finished*))))
                     *sni-octets*))

; THE CARRIED INVARIANT, on a reached state: the index fn-sn-finish consed
; equals the index recomputed over the grown store.
(assert-event (fn-sn-indexedp *sni-finished*))

; Acceptance records the verdict once, with the verification context in
; force at that boundary.  Retrieval is by Message-ID and does not parse the
; article or consult the current keyring.
(assert-event
 (equal (fn-stx-verdict-token
         (fn-sn-verdict-lookup *sni-finished* "<sni@example>"))
        :verified))
(assert-event
 (equal (fn-stx-verdict-generation
         (fn-sn-verdict-lookup *sni-finished* "<sni@example>"))
        1))
(assert-event
 (equal (fn-sn-verdict-lookup *sni-finished* "<missing@example>") nil))

; It grew by exactly one binding, which is the D3 property the index exists
; for: no walk of the store happened at the transition.
(assert-event (equal (len (fn-stx-index-bindings (fn-sn-index *sni-finished*))) 1))
(assert-event (<= (len (fn-stx-index-bindings (fn-sn-index *sni-finished*)))
                  (+ 1 (len (fn-stx-index-bindings (fn-sn-index *sni-completing*))))))

; The lace grew with it.
(assert-event (equal (fn-stx-lace (fn-sn-node *sni-finished*)
                                  (fn-sn-keyring *sni-finished*))
                     (list *sni-stmt*)))

; -----------------------------------------------------------------------------
; The served queries, and the keystone instance on this run

(assert-event (equal (fn-sn-statement-lookup *sni-finished*
                                             (fn-stmt-id *sni-stmt*))
                     *sni-stmt*))
(assert-event (equal (fn-sn-statement-lookup *sni-finished* '(1 2 3)) nil))
(assert-event (not (fn-sn-equivocatorp *sni-finished* *sni-creator* 1)))

; fn-sn-statement-lookup-is-the-lace-lookup, instantiated at this state and
; this id, evaluated rather than assumed.
(assert-event (equal (fn-sn-statement-lookup *sni-finished*
                                             (fn-stmt-id *sni-stmt*))
                     (fn-lace-lookup (fn-stx-lace (fn-sn-node *sni-finished*)
                                                  (fn-sn-keyring *sni-finished*))
                                     (fn-stmt-id *sni-stmt*))))
; The equivocator half of the keystone is instantiated in the FORK section
; below, where both of its sides are true.  Asserting it here, where both are
; NIL, would distinguish nothing (tools/teeth_check.py --report,
; both-sides-degenerate), so the single-statement run states the negative
; case directly instead, beside the fork.

; -----------------------------------------------------------------------------
; TEETH.  fn-sn-statement-lookup-is-the-lace-lookup has one hypothesis,
; fn-sn-indexedp, so there is one tooth per hypothesis and it is this: a
; concrete state whose index is stale, for which the conclusion FAILS.

(make-event (list 'defconst '*sni-stale*
                  (list 'quote (fn-sn-make (fn-sn-groups *sni-finished*)
                                           (fn-sn-capacity *sni-finished*)
                                           (fn-sn-files *sni-finished*)
                                           (fn-sn-node *sni-finished*)
                                           (fn-sn-keyring *sni-finished*)
                                           (fn-stx-index-empty)))))

; It is still a state -- fn-sn-statep does NOT see the staleness, which is
; the point of the second recognizer (D21).
(assert-event (fn-sn-statep *sni-stale*))
(assert-event (not (fn-sn-indexedp *sni-stale*)))
(assert-event (equal (fn-sn-statement-lookup *sni-stale* (fn-stmt-id *sni-stmt*))
                     nil))
(assert-event (not (equal (fn-sn-statement-lookup *sni-stale*
                                                  (fn-stmt-id *sni-stmt*))
                          (fn-lace-lookup (fn-stx-lace (fn-sn-node *sni-stale*)
                                                       (fn-sn-keyring *sni-stale*))
                                          (fn-stmt-id *sni-stmt*)))))

; -----------------------------------------------------------------------------
; The SEPARATING witness: the same run under the empty keyring.  The article
; is accepted and stored BYTE-IDENTICALLY, and contributes nothing to the
; index, to the lace, or to any query.  This separates the two runs by the
; keyring field alone, not by the weakest clause of anything.

(make-event (list 'defconst '*sni-unkeyed-finished*
                  (list 'quote (fn-sn-finish
                                (fn-sni-publish
                                 (fn-sn-prepare (fn-sni-reserve *sni-initial*)
                                                *sni-record*))))))

(assert-event (fn-sn-indexedp *sni-unkeyed-finished*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sni-unkeyed-finished*)) :ready))

; Same bytes in the store.
(assert-event (equal (fn-stx-store (fn-sn-node *sni-unkeyed-finished*))
                     (fn-stx-store (fn-sn-node *sni-finished*))))

; No authority: an empty index, an empty lace, and a query that answers
; absent for the very id the keyed run answers.
(assert-event (equal (fn-sn-index *sni-unkeyed-finished*) (fn-stx-index-empty)))
(assert-event (equal (fn-stx-lace (fn-sn-node *sni-unkeyed-finished*)
                                  (fn-sn-keyring *sni-unkeyed-finished*))
                     nil))
(assert-event (equal (fn-sn-statement-lookup *sni-unkeyed-finished*
                                             (fn-stmt-id *sni-stmt*))
                     nil))
(assert-event
 (equal (fn-stx-verdict-token
         (fn-sn-verdict-lookup *sni-unkeyed-finished* "<sni@example>"))
        :unverified))
(assert-event
 (equal (fn-stx-verdict-generation
         (fn-sn-verdict-lookup *sni-unkeyed-finished* "<sni@example>"))
        0))

; The two runs are separated by the keyring field and by nothing else: the
; same id, the same store, two different answers.  (The keystone instance on
; the unkeyed run is not asserted here: both of its sides are NIL, so it
; would distinguish nothing -- tools/teeth_check.py --report calls that
; both-sides-degenerate and it is right.)
; The keyed run's answer for the same id is asserted above, at the S-lookup
; section: it is *sni-stmt*.  So the two runs differ on one id over one
; store, and the keyring field is the only thing that differs between them.
(assert-event (null (fn-sn-statement-lookup *sni-unkeyed-finished*
                                            (fn-stmt-id *sni-stmt*))))
(assert-event (equal (fn-stx-store (fn-sn-node *sni-unkeyed-finished*))
                     (fn-stx-store (fn-sn-node *sni-finished*))))

; -----------------------------------------------------------------------------
; Reconfiguration after the fact: installing the keyring on the unkeyed run's
; state recomputes the index over the store it already holds, and lands on
; the keyed run's index.  This is the cost D21 names -- a whole-store walk at
; a reconfiguration event, never on a served path.

(make-event (list 'defconst '*sni-rekeyed*
                  (list 'quote (fn-sn-set-keyring *sni-unkeyed-finished*
                                                  *sni-keyring*))))
(assert-event (fn-sn-indexedp *sni-rekeyed*))
(assert-event (equal (fn-sn-index *sni-rekeyed*) (fn-sn-index *sni-finished*)))
(assert-event (equal (fn-sn-statement-lookup *sni-rekeyed*
                                             (fn-stmt-id *sni-stmt*))
                     *sni-stmt*))
; Current trust changed, historical acceptance evidence did not.
(assert-event (equal (fn-sn-keyring-generation *sni-rekeyed*) 1))
(assert-event
 (equal (fn-sn-verdict-lookup *sni-rekeyed* "<sni@example>")
        (fn-sn-verdict-lookup *sni-unkeyed-finished* "<sni@example>")))
(assert-event
 (equal (fn-stx-verdict-generation
         (fn-sn-verdict-lookup *sni-rekeyed* "<sni@example>"))
        0))

; -----------------------------------------------------------------------------
; -----------------------------------------------------------------------------
; A FORK, accepted.  The same creator signs a second, different article at
; the same (incarnation, sequence) slot.  Both articles are accepted and
; stored -- refusing the second would let a hostile peer delete content by
; replaying a fork, and would destroy the evidence -- and what the index
; records is the equivocation.  This is the witness that keeps
; fn-sn-equivocatorp from being satisfiable by a constantly-false
; definition, which tools/teeth_check.py --report is right to demand.

(make-event (list 'defconst '*sni-src-2*
                  (list 'quote (fn-sni-authored "Subject: two" "second"))))
(make-event (list 'defconst '*sni-stmt-2*
                  (list 'quote (fn-stmt-sign *sni-sk* *sni-creator* 1 1 nil
                                             :article *sni-src-2*))))
(assert-event (not (equal (fn-stmt-id *sni-stmt-2*) (fn-stmt-id *sni-stmt*))))
; Same slot, different content: a fork of the first, not a second slot.
(assert-event (equal (fn-stx-slot-key *sni-stmt-2*)
                     (fn-stx-slot-key *sni-stmt*)))

(make-event (list 'defconst '*sni-octets-2*
                  (list 'quote (fn-sni-received
                                (fn-stx-header-value *sni-stmt-2*) *sni-src-2*))))
(make-event (list 'defconst '*sni-record-2*
                  (list 'quote (fn-record-make 1 1 1 "<sni2@example>"
                                               *sni-octets-2* *sni-groups*
                                               "sni-pin-2" "sni-content-2"
                                               "sni-release-2" 2))))
(assert-event (fn-record-p *sni-record-2*))

(make-event (list 'defconst '*sni-forked*
                  (list 'quote (fn-sn-finish
                                (fn-sni-publish
                                 (fn-sn-prepare (fn-sni-reserve *sni-finished*)
                                                *sni-record-2*))))))
(assert-event (equal (fn-sf-phase (fn-sn-files *sni-forked*)) :ready))
(assert-event (fn-sn-indexedp *sni-forked*))

; Both articles are in the store and both statements are in the index.
(assert-event (equal (len (fn-stx-store (fn-sn-node *sni-forked*))) 2))
(assert-event (equal (len (fn-stx-index-bindings (fn-sn-index *sni-forked*))) 2))

; THE EQUIVOCATION.  fn-sn-equivocatorp answers T here and NIL on the
; single-statement run, so the predicate is anchored on both sides.
(assert-event (fn-sn-equivocatorp *sni-forked* *sni-creator* 1))
(assert-event (not (fn-sn-equivocatorp *sni-finished* *sni-creator* 1)))
(assert-event (not (fn-sn-equivocatorp *sni-forked* '(1 2 3) 1)))

; The keystone instance, with BOTH sides true rather than both nil.
(assert-event (iff (fn-sn-equivocatorp *sni-forked* *sni-creator* 1)
                   (fn-lace-equivocatorp
                    (fn-stx-lace (fn-sn-node *sni-forked*)
                                 (fn-sn-keyring *sni-forked*))
                    *sni-creator* 1)))

; Neither fork is dropped: each is still reachable by its own content id, and
; the slot still answers with the OLDER one, which is what fn-lace-lookup
; reads.
(assert-event (equal (fn-sn-statement-lookup *sni-forked*
                                             (fn-stmt-id *sni-stmt*))
                     *sni-stmt*))
(assert-event (equal (fn-sn-statement-lookup *sni-forked*
                                             (fn-stmt-id *sni-stmt-2*))
                     *sni-stmt-2*))
(assert-event (equal (fn-stx-index-slot-first (fn-sn-index *sni-forked*)
                                              (fn-stx-slot-key *sni-stmt*))
                     *sni-stmt*))

; And the lookup keystone on the forked run, with both sides NON-nil.
(assert-event (equal (fn-sn-statement-lookup *sni-forked*
                                             (fn-stmt-id *sni-stmt-2*))
                     (fn-lace-lookup (fn-stx-lace (fn-sn-node *sni-forked*)
                                                  (fn-sn-keyring *sni-forked*))
                                     (fn-stmt-id *sni-stmt-2*))))

; A crash resets the store, so it resets the index; recovery replays the
; store and RECOMPUTES the index over it.  This is the one transition whose
; node does not come from a step of this machine, and it is the reason
; fn-sn-recover recomputes rather than carries.

(make-event (list 'defconst '*sni-crashed*
                  (list 'quote (fn-sn-crash *sni-finished* :new :present))))
(assert-event (fn-sn-indexedp *sni-crashed*))
(assert-event (not (equal *sni-crashed* *sni-finished*)))
(assert-event (equal (fn-stx-store (fn-sn-node *sni-crashed*)) nil))
(assert-event (equal (fn-sn-index *sni-crashed*) (fn-stx-index-empty)))
; The verification context is configuration, so it survives the crash.
(assert-event (equal (fn-sn-keyring *sni-crashed*) *sni-keyring*))

(make-event (list 'defconst '*sni-recovered*
                  (list 'quote (fn-sn-recover *sni-crashed*))))
(assert-event (equal (fn-sf-phase (fn-sn-files *sni-recovered*)) :recovering))
(assert-event (fn-sn-indexedp *sni-recovered*))
; The replay put the article back, and the recomputation put its statement
; back with it: the index after recovery is the index before the crash.
(assert-event (equal (len (fn-stx-store (fn-sn-node *sni-recovered*))) 1))
(assert-event (equal (fn-sn-index *sni-recovered*) (fn-sn-index *sni-finished*)))
(assert-event (equal (fn-sn-statement-lookup *sni-recovered*
                                             (fn-stmt-id *sni-stmt*))
                     *sni-stmt*))
