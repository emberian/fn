; Teeth for books/post-retain-carried.lisp.
;
; The owner is owner-prepare-carried-tests' live owner *pcar-t-o* (as in
; post-identity-index-tests, whose records are rebuilt here: that test book
; is on the batch AU flip-red list, PKT-821), whose view and Store index
; satisfy PRF-191's three hypotheses.  The
; ledger R0 is its Store node's; R1 is the ledger a durable commit of the
; fresh record installs (R0 with the pin "own-pin:pit" consed), built by the
; node's own prepare and completion.  RU and RR (section "Retention steps")
; are R1 after a forwarding undertaking and then its release, applied by the
; Store's own retention transition (fn-replay-apply-retention-event).
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/post-retain-carried")
(include-book "owner-prepare-carried-tests")

(defconst *pit-o* *pcar-t-o*)
(defconst *pit-oc* *pcar-t-oc*)
(defconst *pit-record* *pcar-t-record*)
; Held rows (records flip), as owner-served-invariants-tests' osi-record-of.
; Spelled exactly as post-identity-index-tests spells them, which this book
; includes below (a second, different defun of the same name is refused).
(defun pit-record-wire-under (msgid)
  (fn-record-make 2 2 2 msgid (fn-own-sub-octets *osi-sub*) '("fn.letters")
                  "own-pin:pit" "own-content:pit" "own-release:pit" 2 841000000))
(defun pit-record-under (msgid)
  (fn-hrt-row-at (pit-record-wire-under msgid) 2))
; "<one@example>" is held by the owner's node; "<fresh@example>" is not.
(defconst *pit-dup-record* (pit-record-under "<one@example>"))
(defconst *pit-fresh-record* (pit-record-under "<fresh@example>"))
(defun pit-phase (oc)
  (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))

;; Whether the refresh from CARRY to LEDGER takes the delta branch.
(defun prct-delta-okp (carry ledger)
  (declare (xargs :guard (consp carry)))
  (mv-let (ok trie) (fn-prc-delta carry ledger)
    (declare (ignore trie))
    ok))

(defconst *prct-node0* (fn-sn-node (fn-own-store *pit-o*)))
(defconst *prct-r0* (fn-node-retention *prct-node0*))

; The host's first POST: the carry is refreshed from nil (the global's value
; before any POST, and what the owner open installs), which builds the
; trie of R0.
(defconst *prct-carry0* (fn-prc-refresh nil *prct-r0*))

; -----------------------------------------------------------------------------
; Positive witness, reachable (fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-
; prepare, hence fn-prc-sbud-prepare-is-pidx-sbud-prepare): every hypothesis
; holds, and the host's call with the refreshed carry is the carried
; prepare, which stages the fresh record and refuses the duplicate.

(assert-event (fn-prc-carryp *prct-carry0*))

(assert-event
 (let ((a (fn-prc-sbud-prepare *pit-oc* *pit-fresh-record* 100 *prct-carry0*))
       (b (fn-prc-sbud-prepare *pit-oc* *pit-dup-record* 100 *prct-carry0*))
       (c (fn-prc-sbud-prepare *pit-oc* *pit-record* 100 *prct-carry0*)))
   (and (equal a (fn-pcar-sbud-prepare *pit-oc* *pit-fresh-record* 100))
        (equal (pit-phase a) :record-staged)
        (equal a (fn-pcar-sbud-prepare *pit-oc* *pit-fresh-record* 100))
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
; The commit's ledger: the refresh's delta branch (one put), and the carried
; trie refusing a known obligation id.

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
      ; R1 is R0 under one new pin, the releases unchanged: the delta branch.
      (equal (cdr (fn-retain-pins *prct-r1*)) (fn-retain-pins *prct-r0*))
      (equal (fn-retain-releases *prct-r1*) (fn-retain-releases *prct-r0*))
      (equal (fn-retain-obligation-id (car (fn-retain-pins *prct-r1*)))
             "own-pin:pit")
      (prct-delta-okp *prct-carry0* *prct-r1*)
      (equal *prct-carry1*
             (cons *prct-r1* (fn-prc-add-pin (car (fn-retain-pins *prct-r1*))
                                             (cdr *prct-carry0*))))
      (fn-prc-has "own-pin:pit" (cdr *prct-carry1*))
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
        (not (fn-prc-has "own-pin:pit" (cdr *prct-carry0*)))
        (equal (fn-prc-admissiblep *prct-r1* "own-pin:pit" "own-content:pit"
                                   :archive "own-release:pit" 2 *prct-carry0*)
               (fn-retain-admissiblep *prct-r1* "own-pin:pit" "own-content:pit"
                                      :archive "own-release:pit" 2))
        (fn-prc-set-admissiblep *prct-r1* "own-pin:pit" "own-content:pit"
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
  (cons *prct-r0* (fn-prc-add "own-pin:pit" (cdr *prct-carry0*))))
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
      (fn-prc-has "own-pin:pit" (cdr *prct-bad-carry*))
      (equal *prct-bad-prepared* *pit-oc*)
      (equal (pit-phase (fn-pcar-sbud-prepare *pit-oc* *pit-fresh-record* 100))
             :record-staged)))
(must-fail-checked
 (defthm prct-prepare-without-carryp
   (equal (fn-prc-sbud-prepare *pit-oc* *pit-fresh-record* 100 *prct-bad-carry*)
          (fn-pcar-sbud-prepare *pit-oc* *pit-fresh-record* 100))
   :hints (("Goal" :in-theory (disable (:e fn-prc-sbud-prepare))))))

;; The recognizer's other half.  An INCOMPLETE carry (the trie of R0 named
;; as R1's: it lacks R1's new pin): not carryp; the host's call, run raw,
;; stages a record reusing the committed id, which the reference refuses.
(defconst *prct-short-carry* (cons *prct-r1* (cdr *prct-carry0*)))
(make-event
 `(defconst *prct-short-prepared*
    ',(with-guard-checking
       :none
       (fn-prc-sn-prepare-node *prct-node1* *prct-reuse-record*
                               (fn-own-view *pit-o*) *prct-short-carry*))))
(assert-event
 (and (not (fn-prc-carryp *prct-short-carry*))
      (fn-rii-knownp "own-pin:pit" *prct-r1*)
      (not (fn-prc-has "own-pin:pit" (cdr *prct-short-carry*)))
      (consp (fn-node-stage *prct-short-prepared*))
      (null (fn-node-stage (fn-sn-prepare-node *prct-node1* *prct-reuse-record*)))))
(must-fail-checked
 (defthm prct-sn-prepare-without-carryp
   (equal (fn-prc-sn-prepare-node *prct-node1* *prct-reuse-record*
                                  (fn-own-view *pit-o*) *prct-short-carry*)
          (fn-pidx-sn-prepare-node *prct-node1* *prct-reuse-record*
                                   (fn-own-view *pit-o*)))
   :hints (("Goal" :in-theory (disable (:e fn-prc-sn-prepare-node))))))

;; fn-prc-carryp-of-refresh without its hypothesis: the refresh keeps a
;; carry that already names the ledger, so a corrupted one stays corrupted.
(assert-event
 (and (not (fn-prc-carryp *prct-bad-carry*))
      (equal (fn-prc-refresh *prct-bad-carry* *prct-r0*) *prct-bad-carry*)
      (not (fn-prc-carryp (fn-prc-refresh *prct-bad-carry* *prct-r0*)))))

; -----------------------------------------------------------------------------
; Retention steps between POSTs.  NU is node1 after a forwarding undertaking
; of "fwd-pin:pit" and NR is NU after its release, each the Store's own
; retention transition (fn-replay-apply-retention-event); RU and RR are their
; ledgers. The undertaking and release each take the delta branch.
; Undertaking puts a pin record; release replaces it with the id string.
; If both happen between refreshes the old trie has no such pin: rebuild.

(defconst *prct-tx1* (fn-state-next-txid (fn-node-acceptance *prct-node1*)))
(defconst *prct-nu*
  (fn-replay-apply-retention-event
   *prct-node1*
   (fn-store-retention-event-make :undertake 9 *prct-tx1* *prct-tx1*
                                  "fwd-pin:pit" "fwd-content:pit"
                                  "fwd-receipt:pit" 2)))
(defconst *prct-tx2* (fn-state-next-txid (fn-node-acceptance *prct-nu*)))
(defconst *prct-nr*
  (fn-replay-apply-retention-event
   *prct-nu*
   (fn-store-retention-event-make :release 10 *prct-tx2* *prct-tx2*
                                  "fwd-pin:pit" "fwd-content:pit"
                                  "fwd-receipt:pit" 0)))
(defconst *prct-ru* (fn-node-retention *prct-nu*))
(defconst *prct-rr* (fn-node-retention *prct-nr*))
(defconst *prct-carry-u* (fn-prc-refresh *prct-carry1* *prct-ru*))
(defconst *prct-carry-ur* (fn-prc-refresh *prct-carry-u* *prct-rr*))
(defconst *prct-carry-r* (fn-prc-refresh *prct-carry1* *prct-rr*))

(assert-event
 (and (fn-node-statep *prct-nu*) (fn-node-statep *prct-nr*)
      (null (fn-node-stage *prct-nr*))
      ; RR: the pin moved to the releases.
      (equal (fn-retain-pins *prct-rr*) (fn-retain-pins *prct-r1*))
      (equal (cdr (fn-retain-releases *prct-rr*)) (fn-retain-releases *prct-r1*))
      (equal (fn-retain-release-id (car (fn-retain-releases *prct-rr*)))
             "fwd-pin:pit")
      ; The undertaking: delta, one put.
      (prct-delta-okp *prct-carry1* *prct-ru*)
      (equal *prct-carry-u*
             (cons *prct-ru* (fn-prc-add-pin (car (fn-retain-pins *prct-ru*))
                                            (cdr *prct-carry1*))))
      ; The release: delta, the pin leaf replaced by its id.
      (prct-delta-okp *prct-carry-u* *prct-rr*)
      (equal *prct-carry-ur*
             (cons *prct-rr* (fn-prc-release-put "fwd-pin:pit" (cdr *prct-carry-u*))))
      ; Both steps between two POSTs: no old pin to skip; rebuild.
      (not (prct-delta-okp *prct-carry1* *prct-rr*))
      (equal *prct-carry-r*
             (cons *prct-rr* (fn-prc-build *prct-rr*)))
      (fn-prc-carryp *prct-carry-u*)
      (fn-prc-carryp *prct-carry-ur*)
      (fn-prc-carryp *prct-carry-r*)))

; A POST after the release, through either carry: the record reusing the
; released id is refused by retention exactly as the reference refuses it,
; and a fresh one is staged exactly as the reference stages it.
(defconst *prct-tx3* (fn-state-next-txid (fn-node-acceptance *prct-nr*)))
(defun prct-record-at (msgid oid)
  (fn-hrt-row-at
   (fn-record-make *prct-tx3* *prct-tx3* *prct-tx3* msgid
                   (fn-own-sub-octets *osi-sub*) '("fn.letters")
                   oid "own-content:pit" "own-release:pit" 2 841000000)
   *prct-tx3*))
(defconst *prct-released-record*
  (prct-record-at "<prct-released@example>" "fwd-pin:pit"))
(defconst *prct-after-record*
  (prct-record-at "<prct-after@example>" "after-pin:pit"))
(assert-event
 (let ((view (fn-own-view *pit-o*)))
   (and (not (fn-retain-admissiblep *prct-rr* "fwd-pin:pit" "own-content:pit"
                                    :archive "own-release:pit" 2))
        (fn-prc-has "fwd-pin:pit" (cdr *prct-carry-ur*))
        (not (fn-prc-has "after-pin:pit" (cdr *prct-carry-ur*)))
        (equal (fn-prc-sn-prepare-node *prct-nr* *prct-released-record* view
                                       *prct-carry-ur*)
               (fn-sn-prepare-node *prct-nr* *prct-released-record*))
        (null (fn-node-stage (fn-prc-sn-prepare-node
                              *prct-nr* *prct-released-record* view
                              *prct-carry-ur*)))
        (equal (fn-prc-sn-prepare-node *prct-nr* *prct-after-record* view
                                       *prct-carry-ur*)
               (fn-sn-prepare-node *prct-nr* *prct-after-record*))
        (consp (fn-node-stage (fn-prc-sn-prepare-node
                               *prct-nr* *prct-after-record* view
                               *prct-carry-ur*)))
        (equal (fn-prc-sn-prepare-node *prct-nr* *prct-released-record* view
                                       *prct-carry-r*)
               (fn-sn-prepare-node *prct-nr* *prct-released-record*))
        (equal (fn-prc-sn-prepare-node *prct-nr* *prct-after-record* view
                                       *prct-carry-r*)
               (fn-sn-prepare-node *prct-nr* *prct-after-record*)))))

; An unknown ledger (a recovery back to R0: a pin gone without a release):
; no delta, the rebuild branch, and the recognizer still holds.
(assert-event
 (and (not (prct-delta-okp *prct-carry-r* *prct-r0*))
      (equal (fn-prc-refresh *prct-carry-r* *prct-r0*)
             (cons *prct-r0* (fn-prc-build *prct-r0*)))
      (fn-prc-carryp (fn-prc-refresh *prct-carry-r* *prct-r0*))))

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
      (eq (symbol-class 'fn-prc-delta (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-pins-walk (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-build (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-set-admissiblep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rit-hasp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rit-put (w state)) :common-lisp-compliant)
      (equal (guard 'fn-prc-node-prepare nil (w state))
             (guard 'fn-node-prepare nil (w state)))))

; -----------------------------------------------------------------------------
; fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-prepare: removal of each view
; and index hypothesis (audit packet G2-P5, lane audit-fixes).  The CORRUPTED
; owners are post-identity-index-tests' (no owner transition builds them):
; a visible list holding a fake article, a trie holding it, and a Store
; index claiming 100 records.  The carry is the host's refresh of a carry
; with the recognizer (R0's), so fn-prc-carryp holds; in each the omitted
; hypothesis alone fails, and the host's call (run raw, as the host runs it)
; refuses the fresh record where fn-pcar-sbud-prepare stages it.
(include-book "post-identity-index-tests")
(defconst *prct-host-carry* (fn-prc-refresh *prct-carry0* *prct-r0*))


; Positive (reachable owner): every hypothesis, and the equality.

; Without fn-ocl-view-visiblep.

; Without fn-ceis-indexedp.


; fn-prc-set-okp-of-delta (audit packet G2-P5).  Positive (reached): the
; carry R0's refresh builds, and the delta to R1 (after the pit record's
; stage).  Removal of (fn-prc-set-okp (car carry) (cdr carry)), CORRUPTED
; carry *prct-bad-carry* (its trie claims an id R0 does not know): the delta
; to R0 is ok and the trie it answers is still unsound.  Removal of the
; delta's ok flag: *prct-carry-r* to R0 (a pin gone without a release) takes
; no delta, and the trie it answers is not sound for R0.
(defun prct-delta-trie (carry ledger)
  (declare (xargs :guard (consp carry)))
  (mv-let (ok trie) (fn-prc-delta carry ledger)
    (declare (ignore ok))
    trie))
(assert-event
 (and (consp *prct-carry0*)
      (fn-prc-set-okp (car *prct-carry0*) (cdr *prct-carry0*))
      (prct-delta-okp *prct-carry0* *prct-r1*)
      (fn-prc-set-okp *prct-r1* (prct-delta-trie *prct-carry0* *prct-r1*))))
(assert-event
 (and (consp *prct-bad-carry*)
      (not (fn-prc-set-okp (car *prct-bad-carry*) (cdr *prct-bad-carry*)))
      (prct-delta-okp *prct-bad-carry* *prct-r0*)
      (not (fn-prc-set-okp *prct-r0* (prct-delta-trie *prct-bad-carry* *prct-r0*)))))
(assert-event
 (and (consp *prct-carry-r*)
      (fn-prc-set-okp (car *prct-carry-r*) (cdr *prct-carry-r*))
      (not (prct-delta-okp *prct-carry-r* *prct-r0*))
      (not (fn-prc-set-okp *prct-r0* (prct-delta-trie *prct-carry-r* *prct-r0*)))))

; D14 Part A: concrete find witnesses, reached through retention transitions.
; Subject and archive evidence are bp-release-tests' concrete values.
(defconst *d14-prct-l0*
  (fn-retain-release
   (fn-retain-admit (fn-retain-initial-state 100)
                    "c3" "subject-rl" :archive "operator-release" 4)
   "c3" "subject-rl" :archive "operator-release"))
(defconst *d14-prct-l1*
  (fn-retain-admit
   (fn-retain-admit *d14-prct-l0* "a1" "subject-rl" :archive "operator-release" 4)
   "b2" "subject-rl" :archive "operator-release" 4))
(defconst *d14-prct-c1* (fn-prc-refresh nil *d14-prct-l1*))
(defconst *d14-prct-a1* (fn-retain-find-id "a1" (fn-retain-pins *d14-prct-l1*)))
(defconst *d14-prct-b2* (fn-retain-find-id "b2" (fn-retain-pins *d14-prct-l1*)))
; SAT: whole antecedent, mark, and pin/released/unknown conclusions.
(with-guard-checking-event
 :none
 (assert-event
  (and (fn-retain-statep *d14-prct-l0*) (fn-retain-statep *d14-prct-l1*)
       (fn-prc-carryp *d14-prct-c1*) (fn-prc-carry-findsp *d14-prct-c1*)
       (consp *d14-prct-a1*) (consp *d14-prct-b2*)
       (equal (fn-prc-find-pin "a1" *d14-prct-l1* *d14-prct-c1*) *d14-prct-a1*)
       (equal (fn-prc-find-pin "c3" *d14-prct-l1* *d14-prct-c1*)
              (fn-retain-find-id "c3" (fn-retain-pins *d14-prct-l1*)))
       (equal (fn-prc-find-pin "zz" *d14-prct-l1* *d14-prct-c1*)
              (fn-retain-find-id "zz" (fn-retain-pins *d14-prct-l1*)))
       (not (fn-prc-find-pin "c3" *d14-prct-l1* *d14-prct-c1*))
       (not (fn-prc-find-pin "zz" *d14-prct-l1* *d14-prct-c1*)))) )
(defconst *d14-prct-l2*
  (fn-retain-release *d14-prct-l1* "a1" "subject-rl" :archive "operator-release"))
(defconst *d14-prct-c2* (fn-prc-refresh *d14-prct-c1* *d14-prct-l2*))
; DELTA: MV-LET is the executable spelling of (mv-nth 0 (fn-prc-delta c L)).
(with-guard-checking-event
 :none
 (assert-event
  (mv-let (ok trie) (fn-prc-delta *d14-prct-c1* *d14-prct-l2*)
    (and (equal ok t) (equal *d14-prct-c2* (cons *d14-prct-l2* trie))
         (fn-retain-statep *d14-prct-l2*)
         (fn-prc-carryp *d14-prct-c2*) (fn-prc-carry-findsp *d14-prct-c2*)
         (equal (fn-prc-find-pin "a1" *d14-prct-l2* *d14-prct-c2*) nil)
         (equal (fn-prc-find-pin "b2" *d14-prct-l2* *d14-prct-c2*) *d14-prct-b2*)))))
(defconst *d14-prct-l3*
  (fn-retain-admit *d14-prct-l1* "d4" "subject-rl" :archive "operator-release" 4))
(defconst *d14-prct-c3* (fn-prc-refresh *d14-prct-c1* *d14-prct-l3*))
; COMMIT: same positive delta requirement; the shared old pin tail is kept.
(with-guard-checking-event
 :none
 (assert-event
  (mv-let (ok trie) (fn-prc-delta *d14-prct-c1* *d14-prct-l3*)
    (and (equal ok t) (equal *d14-prct-c3* (cons *d14-prct-l3* trie))
         (fn-retain-statep *d14-prct-l3*)
         (fn-prc-carryp *d14-prct-c3*) (fn-prc-carry-findsp *d14-prct-c3*)
         (consp (fn-prc-find-pin "d4" *d14-prct-l3* *d14-prct-c3*))
         (equal (fn-prc-find-pin "d4" *d14-prct-l3* *d14-prct-c3*)
                (fn-retain-find-id "d4" (fn-retain-pins *d14-prct-l3*)))))))
(defconst *d14-prct-id-only*
  (cons *d14-prct-l1*
        (fn-prc-mark (fn-prc-add "a1" (fn-prc-add "b2" (fn-prc-add "c3" nil))) t)))
; T-FIND and T-HYP: membership alone admits a marked PRF-289 string trie.
(with-guard-checking-event
 :none
 (assert-event
  (and (fn-prc-set-okp *d14-prct-l1* (cdr *d14-prct-id-only*))
       (not (fn-prc-carryp *d14-prct-id-only*))
       (equal (fn-prc-find-pin "a1" *d14-prct-l1* *d14-prct-id-only*) nil)
       (not (equal (fn-prc-find-pin "a1" *d14-prct-l1* *d14-prct-id-only*)
                   (fn-retain-find-id "a1" (fn-retain-pins *d14-prct-l1*)))))))
; T-LEDGER: a valid carry cannot simply be renamed to a ledger with more pins.
(with-guard-checking-event
 :none
 (assert-event
  (and (fn-prc-carryp (fn-prc-refresh nil *d14-prct-l0*))
       (not (fn-prc-carryp
             (cons *d14-prct-l1* (cdr (fn-prc-refresh nil *d14-prct-l0*))))))))
; T-MUT exact mutated release writer:
; (defun fn-prc-release-put (id trie)
;   (declare (xargs :guard t))
;   (fn-prc-add id trie))
; This keeps a released pin leaf. The release-cleared check then rejects
; the delta, so DELTA's (equal ok t) fails. Without that check the marked
; trie would return the released pin, the PRF-289 mutation in the spec.

; RED 1 and L16: record/branch/bucket recognizer boundaries, with evaluated
; fn-rit-hasp-of-leaf/-of-branch/-of-atom and strings lemma instances.
(defconst *d14-prct-record* '("a1" "subject-rl" :archive "operator-release" 4))
(defconst *d14-prct-branch* (fn-rit-lift *d14-prct-record* 0))
(defconst *d14-prct-bucket* (list :end *d14-prct-record*))
(with-guard-checking-event
 :none
 (assert-event
  (and
   ; Leaf recognizer: record accepted; branch rejected.
   (fn-rit-leafp *d14-prct-record*) (not (fn-rit-leafp *d14-prct-branch*))
   (equal (fn-rit-hasp "a1" 0 *d14-prct-record*)
          (equal (fn-rit-leaf-id *d14-prct-record*) "a1"))
   (implies (fn-rit-leafp *d14-prct-branch*)
            (equal (fn-rit-hasp "a1" 0 *d14-prct-branch*)
                   (equal (fn-rit-leaf-id *d14-prct-branch*) "a1")))
   ; Removing the leaf hypothesis makes this same instance false.
   (not (equal (fn-rit-hasp "a1" 0 *d14-prct-branch*)
               (equal (fn-rit-leaf-id *d14-prct-branch*) "a1")))
   ; Branch recognizer: lifted record accepted; record rejected.
   (fn-rit-branchp *d14-prct-branch*) (not (fn-rit-branchp *d14-prct-record*))
   (equal (fn-rit-hasp "a1" 0 *d14-prct-branch*)
          (fn-rit-hasp "a1" 1 (fn-midx-branch-get #\a *d14-prct-branch*)))
   (implies (fn-rit-branchp *d14-prct-record*)
            (equal (fn-rit-hasp "a1" 0 *d14-prct-record*)
                   (fn-rit-hasp "a1" 1 (fn-midx-branch-get #\a *d14-prct-record*))))
   ; RED 1: the old CONSP hypothesis accepts the record and gives t /= nil.
   (consp *d14-prct-record*)
   (equal (fn-rit-hasp "a1" 0 *d14-prct-record*) t)
   (equal (fn-rit-hasp "a1" 1 (fn-midx-branch-get #\a *d14-prct-record*)) nil)
   ; Bucket tag: accepted on the bucket; rejected on a record.
   (equal (car *d14-prct-bucket*) :end)
   (not (equal (car *d14-prct-record*) :end))
   (not (fn-rit-leafp *d14-prct-bucket*))
   (not (fn-rit-branchp *d14-prct-bucket*))
   (not (fn-rit-hasp "a1" 0 *d14-prct-bucket*))
   (implies (and (not (fn-rit-leafp *d14-prct-record*))
                 (not (fn-rit-branchp *d14-prct-record*)))
            (not (fn-rit-hasp "a1" 0 *d14-prct-record*)))
   ; End bucket lookup and leaf-ID enumeration through its branch.
   (equal (fn-rit-hasp "a1" 2 (list (cons :end *d14-prct-bucket*))) t)
   (equal (fn-rit-strings (list (cons :end *d14-prct-bucket*))) '("a1"))
   (equal (fn-rit-strings *d14-prct-record*) '("a1"))
   (equal (fn-rit-strings *d14-prct-bucket*) nil))))
; RED 2: uniqueness and disjointness alone let the non-string pin ID through.
(defconst *d14-prct-nonstring-pin* '(7 "subject-rl" :archive "operator-release" 4))
(defconst *d14-prct-nonstring-ledger*
  (fn-retain-make-state 16 4 (list *d14-prct-nonstring-pin*) nil))
(with-guard-checking-event
 :none
 (assert-event
  (let ((carry (fn-prc-refresh nil *d14-prct-nonstring-ledger*)))
    (and (fn-retain-no-duplicatesp '(7)) (fn-retain-ids-disjointp '(7) nil)
         (not (fn-prc-ledger-findsp *d14-prct-nonstring-ledger*))
         (fn-prc-carryp carry) (not (fn-prc-carry-findsp carry))
         (equal (fn-prc-find 7 (cdr carry)) nil)
         (equal (fn-prc-find-pin 7 *d14-prct-nonstring-ledger* carry)
                *d14-prct-nonstring-pin*)
         (not (equal (fn-prc-find 7 (cdr carry))
                     (fn-retain-find-id 7 (fn-retain-pins *d14-prct-nonstring-ledger*))))))))

; RED 3: the original A3 recognizer admits duplicate pins.
; A3's two find-agreement scans, without the draft's extra uniqueness test.
(defun d14-a3-carryp (carry)
  (declare (xargs :guard t))
  (or (atom carry)
      (and (fn-prc-set-okp (car carry) (cdr carry))
           (implies
            (fn-prc-carry-findsp carry)
            (and (not (fn-prc-find-miss
                       (fn-prc-pin-ids (fn-retain-pins (car carry)))
                       (fn-retain-pins (car carry)) (cdr carry)))
                 (not (fn-prc-find-miss
                       (fn-rit-strings (cdr carry))
                       (fn-retain-pins (car carry)) (cdr carry))))))))
(defconst *d14-red3-pin* '("a1" "subject-rl" :archive "operator-release" 4))
(defconst *d14-red3-old*
  (fn-retain-make-state 100 8 (list *d14-red3-pin* *d14-red3-pin*) nil))
(defconst *d14-red3-new*
  (fn-retain-make-state 100 5 (list *d14-red3-pin*)
                        (list '("a1" "subject-rl" :archive "operator-release"))))
; Deliberately forged carry; the theorem quantifies over all carries that
; satisfy its recognizer, not just carries reachable from refresh.
(defconst *d14-red3-carry*
  (cons *d14-red3-old* (fn-prc-mark *d14-red3-pin* t)))
(defconst *d14-red3-refreshed*
  (fn-prc-refresh *d14-red3-carry* *d14-red3-new*))
(with-guard-checking-event
 :none
 (assert-event
  (and (d14-a3-carryp *d14-red3-carry*)
       (fn-prc-carry-findsp *d14-red3-carry*)
       (mv-let (ok trie) (fn-prc-delta *d14-red3-carry* *d14-red3-new*)
         (declare (ignore trie))
         (equal ok t))
       (fn-prc-carry-findsp *d14-red3-refreshed*)
       (equal (fn-prc-find-pin "a1" *d14-red3-new* *d14-red3-refreshed*) nil)
       (equal (fn-retain-find-id "a1" (fn-retain-pins *d14-red3-new*))
              *d14-red3-pin*)
       (not (d14-a3-carryp *d14-red3-refreshed*))
       ; The RED 3 amendment now requires this fit condition.
       (not (fn-prc-carryp *d14-red3-carry*)))) )
(value-triple :d14-red3-confirmed)

; RED 3 amendment: duplicate releases force an unmarked rebuild, and a
; forged mark on an overlapping ledger cannot satisfy the recognizer.
(defconst *d14-prct-double-release*
  (fn-retain-make-state
   100 (fn-retain-reserved *d14-prct-l2*) (fn-retain-pins *d14-prct-l2*)
   (cons (car (fn-retain-releases *d14-prct-l2*))
         (fn-retain-releases *d14-prct-l2*))))
(with-guard-checking-event
 :none
 (assert-event
  (let ((carry (fn-prc-refresh *d14-prct-c1* *d14-prct-double-release*)))
    (and (mv-let (ok trie) (fn-prc-delta *d14-prct-c1* *d14-prct-double-release*)
           (declare (ignore trie)) (equal ok nil))
         (not (fn-prc-carry-findsp carry)) (fn-prc-carryp carry)
         (not (fn-prc-carryp
               (cons *d14-prct-double-release* (fn-prc-mark (cdr carry) t))))
         (not (fn-prc-carryp
               (cons *d14-red3-new* (fn-prc-mark *d14-red3-pin* t))))))))
; A1: release strings are inserted first; a pin replaces a release at the
; same ID, and the first pin wins even on a ledger whose mark is false.
(with-guard-checking-event
 :none
 (assert-event
  (let* ((second '("a1" "other-subject" :archive "other-evidence" 8))
         (ledger (fn-retain-make-state
                  100 13 (list *d14-prct-a1* second)
                  (list '("a1" "subject-rl" :archive "operator-release"))))
         (carry (fn-prc-refresh nil ledger)))
    (and (fn-prc-carryp carry) (not (fn-prc-carry-findsp carry))
         (equal (fn-prc-find "a1" (cdr carry)) *d14-prct-a1*)
         (equal (fn-prc-find-pin "a1" ledger carry) *d14-prct-a1*)))))
; T-MUT's retained-record mechanism and the delta's rejection of it.
(with-guard-checking-event
 :none
 (assert-event
  (let ((mutated (fn-prc-add "a1" (cdr *d14-prct-c1*))))
    (and (equal (fn-prc-find "a1" mutated) *d14-prct-a1*)
         (not (fn-prc-new-releases-clearedp
               (fn-retain-releases *d14-prct-l2*) (fn-retain-releases *d14-prct-l1*)
               (cdr *d14-prct-c1*) mutated))))))
; The new readers, like the served membership path, have guard t and are
; compiled/guard-verified; the recognizer remains an executable test only.
(assert-event
 (and (equal (guard 'fn-prc-find nil (w state)) '(quote t))
      (equal (guard 'fn-prc-find-scan nil (w state)) '(quote t))
      (equal (guard 'fn-prc-find-pin nil (w state)) '(quote t))
      (eq (symbol-class 'fn-prc-find (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-find-scan (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-find-pin (w state)) :common-lisp-compliant)))

; BEGIN D14 GENERATED T-MUT (build/d14/make_mutation_test.py)
; Exact mutation at every release writer in the copied walk/adder:
; (fn-prc-release-put id trie) -> (fn-prc-add id trie).
; This is PRF-289's insert-if-absent step: it keeps the released pin.
; The unchanged release-cleared check rejects the mutant's delta, breaking
; DELTA's required success flag. If that check were removed, its marked
; walk result would return the released pin. Control: the real delta is t.
(local
 (encapsulate ()
(defun d14-mut-add-new-releases (r1 r0 trie)
  (declare (xargs :guard t))
  (cond ((equal r1 r0) trie)
        ((atom r1) trie)
        (t (d14-mut-add-new-releases
            (cdr r1) r0 (fn-prc-add (fn-retain-release-id (car r1)) trie)))))

(defun d14-mut-pins-walk (p1 p0 rtrie trie check)
  (declare (xargs :guard t :measure (+ (len p1) (len p0))))
  (cond ((and check (equal p1 p0)) (mv t trie))
        ((and (atom p1) (atom p0)) (mv t trie))
        ((and (consp p1) (consp p0) (equal (car p1) (car p0)))
         (d14-mut-pins-walk (cdr p1) (cdr p0) rtrie trie nil))
        ((and (consp p0)
              (fn-prc-has (fn-retain-obligation-id (car p0)) rtrie))
         (let ((id (fn-retain-obligation-id (car p0))))
           (if (and (consp (car p0))
                    (equal (fn-prc-find id trie) (car p0)))
               (d14-mut-pins-walk p1 (cdr p0) rtrie
                                 (fn-prc-add id trie) t)
             (mv nil trie))))
        ((consp p1)
         (let ((id (fn-retain-obligation-id (car p1))))
           (if (and (stringp id) (not (fn-prc-has id trie)))
               (d14-mut-pins-walk (cdr p1) p0 rtrie
                                 (fn-prc-add-pin (car p1) trie) t)
             (mv nil trie))))
        (t (mv nil trie))))

(defun d14-mut-delta (carry ledger)
  (declare (xargs :guard (consp carry)))
  (let* ((l0 (car carry))
         (r0 (fn-retain-releases l0))
         (r1 (fn-retain-releases ledger)))
    (if (and (fn-prc-carry-findsp carry) (fn-prc-releases-tailp r1 r0))
        (mv-let (ok trie)
          (d14-mut-pins-walk (fn-retain-pins ledger) (fn-retain-pins l0)
                            (d14-mut-add-new-releases r1 r0 nil)
                            (cdr carry) t)
          (if (and ok (fn-prc-new-releases-clearedp r1 r0 (cdr carry) trie))
              (mv t (d14-mut-add-new-releases r1 r0 trie))
            (mv nil nil)))
      (mv nil nil))))
(with-guard-checking-event
 :none
 (assert-event
  (mv-let (real-ok real-trie) (fn-prc-delta *d14-prct-c1* *d14-prct-l2*)
   (mv-let (mut-ok mut-trie) (d14-mut-delta *d14-prct-c1* *d14-prct-l2*)
    (declare (ignore mut-trie))
    (mv-let (walk-ok walk-trie)
      (d14-mut-pins-walk
       (fn-retain-pins *d14-prct-l2*) (fn-retain-pins *d14-prct-l1*)
       (fn-prc-add-new-releases (fn-retain-releases *d14-prct-l2*)
                                (fn-retain-releases *d14-prct-l1*) nil)
       (cdr *d14-prct-c1*) t)
     (and (equal real-ok t) (equal mut-ok nil) (equal walk-ok t)
          (fn-prc-carry-findsp (cons *d14-prct-l2* real-trie))
          (equal (fn-prc-find-pin "a1" *d14-prct-l2* (cons *d14-prct-l2* real-trie)) nil)
          (fn-prc-carry-findsp (cons *d14-prct-l2* walk-trie))
          (equal (fn-prc-find-pin "a1" *d14-prct-l2* (cons *d14-prct-l2* walk-trie))
                 *d14-prct-a1*)
          (not (fn-prc-carryp (cons *d14-prct-l2* walk-trie)))))))))
))
; END D14 GENERATED T-MUT

; Phase 3: total collectors preserve order even on malformed ledger fields.
(with-guard-checking-event
 :none
 (assert-event
  (and (equal (fn-prc-pin-ids '(("a1" . 7) 3 ("b2") . end)) '("a1" nil "b2"))
       (equal (fn-prc-release-ids '(("c3") 3 ("d4" . 7) . end)) '("c3" nil "d4"))
       (equal (fn-prc-pin-ids (fn-retain-pins *d14-prct-l1*))
              (fn-retain-obligation-ids (fn-retain-pins *d14-prct-l1*)))
       (equal (fn-prc-release-ids (fn-retain-releases *d14-prct-l1*))
              (fn-retain-release-ids (fn-retain-releases *d14-prct-l1*))))))
; Re-anchoring is value-preserving and keeps the old trie. Physical EQ of
; a separately allocated equal ledger is checked by build/d14/phase3-raw.lsp.
(assert-event
 (let* ((ledger (fn-retain-make-state
                 (fn-retain-capacity *d14-prct-l1*) (fn-retain-reserved *d14-prct-l1*)
                 (fn-retain-pins *d14-prct-l1*) (fn-retain-releases *d14-prct-l1*)))
        (refreshed (fn-prc-refresh *d14-prct-c1* ledger)))
   (and (equal refreshed *d14-prct-c1*)
        (equal (car refreshed) ledger)
        (equal (cdr refreshed) (cdr *d14-prct-c1*))
        (fn-prc-carryp refreshed))))
(assert-event
 (and (equal (guard 'fn-prc-pin-ids nil (w state)) '(quote t))
      (equal (guard 'fn-prc-release-ids nil (w state)) '(quote t))
      (eq (symbol-class 'fn-prc-pin-ids (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-release-ids (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-pin-ids-loop (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-release-ids-loop (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prc-refresh (w state)) :common-lisp-compliant)))

; Host-premise establishment: nonempty record/release reads, the bucket
; reader, empty/nonempty built roots, and both build and delta refreshes.
(with-guard-checking-event
 :none
 (assert-event
  (mv-let (ok delta-trie) (fn-prc-delta *d14-prct-c1* *d14-prct-l2*)
   (let* ((trie (fn-prc-build *d14-prct-l1*))
         (pin (fn-rit-get "a1" 0 trie))
         (release (fn-rit-get "c3" 0 trie))
         (bucket (fn-rit-bucket-find "a1" (list 7 *d14-prct-a1*)))
         (built (fn-prc-refresh nil *d14-prct-l1*))
         (delta (fn-prc-refresh *d14-prct-c1* *d14-prct-l2*)))
    (and pin (equal pin *d14-prct-a1*) (fn-rit-leafp pin)
         release (equal release "c3") (fn-rit-leafp release)
         bucket (equal bucket *d14-prct-a1*) (fn-rit-leafp bucket)
         (not (fn-rit-get "zz" 0 trie))
         (fn-rit-branchp trie)
         (fn-rit-branchp (fn-prc-build (fn-retain-initial-state 100)))
         (fn-prc-carryp nil) (fn-prc-carryp *d14-prct-c1*)
         (equal ok t) (equal delta (cons *d14-prct-l2* delta-trie))
         (fn-prc-carry-findsp built) (fn-prc-carry-findsp delta)
         (fn-prc-ledger-findsp (car built))
         (fn-prc-ledger-findsp (car delta)))))))
