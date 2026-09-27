; Teeth for books/post-retain-carried.lisp.
;
; The owner is owner-prepare-carried-tests' live owner *pcar-t-o* (as in
; post-identity-index-tests, whose records are rebuilt here: that test book
; is on the batch AU flip-red list, PKT-821), whose view and Store index
; satisfy PRF-191's three hypotheses.  The
; ledger R0 is its Store node's; R1 is the ledger a durable commit of the
; fresh record installs (R0 with the pin "own-pin:pit" consed), built by the
; node's own prepare and completion.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/post-retain-carried")
(include-book "owner-prepare-carried-tests")

(defconst *pit-o* *pcar-t-o*)
(defconst *pit-oc* *pcar-t-oc*)
(defconst *pit-record* *pcar-t-record*)
; Held rows (records flip), as owner-served-invariants-tests' osi-record-of.
(defun pit-record-under (msgid)
  (fn-hrt-row-at
   (fn-record-make 2 2 2 msgid (fn-own-sub-octets *osi-sub*) '("fn.letters")
                   "own-pin:pit" "own-content:pit" "own-release:pit" 2 841000000)
   2))
; "<one@example>" is held by the owner's node; "<fresh@example>" is not.
(defconst *pit-dup-record* (pit-record-under "<one@example>"))
(defconst *pit-fresh-record* (pit-record-under "<fresh@example>"))
(defun pit-phase (oc)
  (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))

(defconst *prct-node0* (fn-sn-node (fn-own-store *pit-o*)))
(defconst *prct-r0* (fn-node-retention *prct-node0*))

; The host's first POST: the carry is refreshed from nil (the global's value
; before any POST), which builds the trie of R0.
(defconst *prct-carry0* (fn-prc-refresh nil *prct-r0*))

; -----------------------------------------------------------------------------
; Positive witness, reachable (fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-
; prepare, hence fn-prc-sbud-prepare-is-pidx-sbud-prepare): every hypothesis
; holds, and the host's call with the refreshed carry is the carried
; prepare, which stages the fresh record and refuses the duplicate.
(assert-event
 (and (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner *pit-oc*)))
      (fn-scar-view-indexedp (fn-ocfg-owner *pit-oc*))
      (fn-ceis-indexedp (fn-sbud-oc-store *pit-oc*))
      (equal (car *prct-carry0*) *prct-r0*)
      (equal (fn-rii-kbuild *prct-r0*) (cdr *prct-carry0*))))
(assert-event (fn-prc-carryp *prct-carry0*))

(assert-event
 (let ((a (fn-prc-sbud-prepare *pit-oc* *pit-fresh-record* 100 *prct-carry0*))
       (b (fn-prc-sbud-prepare *pit-oc* *pit-dup-record* 100 *prct-carry0*))
       (c (fn-prc-sbud-prepare *pit-oc* *pit-record* 100 *prct-carry0*)))
   (and (equal a (fn-pcar-sbud-prepare *pit-oc* *pit-fresh-record* 100))
        (equal (pit-phase a) :record-staged)
        (equal a (fn-pidx-sbud-prepare *pit-oc* *pit-fresh-record* 100))
        (equal b (fn-pcar-sbud-prepare *pit-oc* *pit-dup-record* 100))
        (equal b *pit-oc*)
        (equal c (fn-pcar-sbud-prepare *pit-oc* *pit-record* 100))
        (equal (pit-phase c) :record-staged))))

; The carried trie was the one asked: the ledger in hand is the carried one.
(assert-event
 (equal (fn-node-retention (fn-replay-advance-txid
                            *prct-node0* (fn-record-txid *pit-fresh-record*)))
        (car *prct-carry0*)))

; -----------------------------------------------------------------------------
; The commit's ledger: the refresh's one-put branch, and the carried trie
; refusing a known obligation id.

(defconst *prct-staged*
  (fn-pidx-sn-prepare-node *prct-node0* *pit-fresh-record*
                           (fn-own-view *pit-o*)))
(defconst *prct-node1*
  (fn-node-complete *prct-staged*
                    (fn-pending-txid (fn-state-pending
                                      (fn-node-acceptance *prct-staged*)))
                    (fn-record-generation *pit-fresh-record*)
                    :durable))
(defconst *prct-r1* (fn-node-retention *prct-node1*))
(defconst *prct-carry1* (fn-prc-refresh *prct-carry0* *prct-r1*))

(assert-event
 (and (consp (fn-node-stage *prct-staged*))
      (null (fn-node-stage *prct-node1*))
      ; R1 is R0 under one new pin, the releases unchanged: the one-put branch.
      (equal (cdr (fn-retain-pins *prct-r1*)) (fn-retain-pins *prct-r0*))
      (equal (fn-retain-releases *prct-r1*) (fn-retain-releases *prct-r0*))
      (equal (fn-retain-obligation-id (car (fn-retain-pins *prct-r1*)))
             "own-pin:pit")
      (equal *prct-carry1*
             (cons *prct-r1* (fn-rii-id-put "own-pin:pit" (cdr *prct-carry0*))))
      (fn-rii-id-hasp "own-pin:pit" (cdr *prct-carry1*))
      (fn-rii-knownp "own-pin:pit" *prct-r1*)))

; A record under a fresh Message-ID and the committed obligation id: the
; carried admission refuses it, as the reference does.
(defconst *prct-reuse-record*
  (fn-hrt-row-at
   (fn-record-make 3 3 3 "<prct-reuse@example>" (fn-own-sub-octets *osi-sub*)
                   '("fn.letters") "own-pin:pit" "own-content:pit"
                   "own-release:pit" 2 841000000)
   3))
(assert-event
 (let ((view (fn-own-view *pit-o*)))
   (and (equal (fn-prc-sn-prepare-node *prct-node1* *pit-fresh-record* view *prct-carry1*)
               (fn-sn-prepare-node *prct-node1* *pit-fresh-record*))
        (equal (fn-prc-sn-prepare-node *prct-node1* *prct-reuse-record* view
                                       *prct-carry1*)
               (fn-sn-prepare-node *prct-node1* *prct-reuse-record*))
        ; refused by retention, not by the Message-ID
        (not (fn-retain-admissiblep *prct-r1* "own-pin:pit" "own-content:pit"
                                    :archive "own-release:pit" 2))
        (not (fn-acceptedp "<prct-reuse@example>"
                           (fn-state-articles (fn-node-acceptance *prct-node1*))))
        (null (fn-node-stage (fn-prc-sn-prepare-node
                              *prct-node1* *prct-reuse-record* view
                              *prct-carry1*))))))

(assert-event (fn-prc-carryp *prct-carry1*))

; -----------------------------------------------------------------------------
; Stale carry (the node moved on and the carry was not refreshed): the carry
; still satisfies the recognizer, names R0, and so is not asked about R1;
; the admission takes the reference scan and refuses the committed id.  Its
; trie, asked, would have admitted it: the EQUAL key is what keeps it out.
(assert-event
 (let ((view (fn-own-view *pit-o*)))
   (and (not (equal (car *prct-carry0*) *prct-r1*))
        (not (fn-rii-id-hasp "own-pin:pit" (cdr *prct-carry0*)))
        (equal (fn-prc-admissiblep *prct-r1* "own-pin:pit" "own-content:pit"
                                   :archive "own-release:pit" 2 *prct-carry0*)
               (fn-retain-admissiblep *prct-r1* "own-pin:pit" "own-content:pit"
                                      :archive "own-release:pit" 2))
        (fn-rii-admissiblep *prct-r1* "own-pin:pit" "own-content:pit"
                            :archive "own-release:pit" 2 (cdr *prct-carry0*))
        (equal (fn-prc-sn-prepare-node *prct-node1* *prct-reuse-record* view
                                       *prct-carry0*)
               (fn-sn-prepare-node *prct-node1* *prct-reuse-record*)))))

; -----------------------------------------------------------------------------
; Hypothesis removal (CORRUPTED carry: no refresh builds it): a trie that
; claims R0 knows "own-pin:pit".  The recognizer fails; the host's call then
; refuses the fresh record (retention says its id is known) where the
; reference stages it; so the keystone is false without its hypothesis.
(defconst *prct-bad-carry*
  (cons *prct-r0* (fn-rii-id-put "own-pin:pit" (cdr *prct-carry0*))))
; The host's call is raw (no guard is evaluated per POST); here the
; corrupted run evaluates without guard checking, as that call would.
(make-event
 `(defconst *prct-bad-prepared*
    ',(with-guard-checking
       :none
       (fn-prc-sbud-prepare *pit-oc* *pit-fresh-record* 100 *prct-bad-carry*))))
(assert-event
 (and (not (fn-prc-carryp *prct-bad-carry*))
      (not (fn-rii-knownp "own-pin:pit" *prct-r0*))
      (fn-rii-id-hasp "own-pin:pit" (cdr *prct-bad-carry*))
      (equal *prct-bad-prepared* *pit-oc*)
      (equal (pit-phase (fn-pidx-sbud-prepare *pit-oc* *pit-fresh-record* 100))
             :record-staged)))
(must-fail
 (defthm prct-prepare-without-carryp
   (equal (fn-prc-sbud-prepare *pit-oc* *pit-fresh-record* 100 *prct-bad-carry*)
          (fn-pidx-sbud-prepare *pit-oc* *pit-fresh-record* 100))
   :hints (("Goal" :in-theory (disable (:e fn-prc-sbud-prepare))))))

; -----------------------------------------------------------------------------
; The host's calls run compiled code: every function is guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-prc-carryp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-refresh (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-admissiblep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-node-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-sn-prepare-node (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-spc-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-opc-owner-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-opc-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-sbud-prepare (w state)) :common-lisp-compliant)
      (equal (guard 'fn-prc-node-prepare nil (w state))
             (guard 'fn-node-prepare nil (w state)))))
