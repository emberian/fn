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
(assert-event
 (and (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner *pit-oc*)))
      (fn-scar-view-indexedp (fn-ocfg-owner *pit-oc*))
      (fn-ceis-indexedp (fn-sbud-oc-store *pit-oc*))
      (equal (car *prct-carry0*) *prct-r0*)
      (equal (fn-prc-build *prct-r0*) (cdr *prct-carry0*))))
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
             (cons *prct-r1* (fn-prc-add "own-pin:pit" (cdr *prct-carry0*))))
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
      (equal (pit-phase (fn-pidx-sbud-prepare *pit-oc* *pit-fresh-record* 100))
             :record-staged)))
(must-fail-checked
 (defthm prct-prepare-without-carryp
   (equal (fn-prc-sbud-prepare *pit-oc* *pit-fresh-record* 100 *prct-bad-carry*)
          (fn-pidx-sbud-prepare *pit-oc* *pit-fresh-record* 100))
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
; ledgers.  Every refresh takes the delta branch (no rebuild): the
; undertaking puts one id, the release puts none (the released id is still
; known, now through the releases), and the two steps at once put one.

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
             (cons *prct-ru* (fn-prc-add "fwd-pin:pit" (cdr *prct-carry1*))))
      ; The release: delta, the trie unchanged.
      (prct-delta-okp *prct-carry-u* *prct-rr*)
      (equal *prct-carry-ur* (cons *prct-rr* (cdr *prct-carry-u*)))
      ; Both steps between two POSTs: delta, one put.
      (prct-delta-okp *prct-carry1* *prct-rr*)
      (equal *prct-carry-r*
             (cons *prct-rr* (fn-prc-add "fwd-pin:pit" (cdr *prct-carry1*))))
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
(defun prct-refresh-hyps (oc)
  (list (fn-prc-carryp *prct-carry0*)
        (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc)))
        (fn-scar-view-indexedp (fn-ocfg-owner oc))
        (fn-ceis-indexedp (fn-sbud-oc-store oc))))
(make-event
 `(defconst *prct-host-answers*
    ',(with-guard-checking
       :none
       (list (fn-prc-sbud-prepare *pit-oc* *pit-fresh-record* 100 *prct-host-carry*)
             (fn-prc-sbud-prepare *pit-bad-visible-oc* *pit-fresh-record* 100 *prct-host-carry*)
             (fn-prc-sbud-prepare *pit-bad-index-oc* *pit-fresh-record* 100 *prct-host-carry*)
             (fn-prc-sbud-prepare *pit-bad-count-oc* *pit-fresh-record* 100 *prct-host-carry*)))))
; Positive (reachable owner): every hypothesis, and the equality.
(assert-event
 (and (equal (prct-refresh-hyps *pit-oc*) '(t t t t))
      (equal (nth 0 *prct-host-answers*) (fn-pcar-sbud-prepare *pit-oc* *pit-fresh-record* 100))
      (equal (pit-phase (nth 0 *prct-host-answers*)) :record-staged)))
; Without fn-ocl-view-visiblep.
(assert-event
 (and (equal (prct-refresh-hyps *pit-bad-visible-oc*) '(t nil t t))
      (not (equal (nth 1 *prct-host-answers*)
                  (fn-pcar-sbud-prepare *pit-bad-visible-oc* *pit-fresh-record* 100)))))
; Without fn-scar-view-indexedp.
(assert-event
 (and (equal (prct-refresh-hyps *pit-bad-index-oc*) '(t t nil t))
      (not (equal (nth 2 *prct-host-answers*)
                  (fn-pcar-sbud-prepare *pit-bad-index-oc* *pit-fresh-record* 100)))))
; Without fn-ceis-indexedp.
(assert-event
 (and (equal (prct-refresh-hyps *pit-bad-count-oc*) '(t t t nil))
      (not (equal (nth 3 *prct-host-answers*)
                  (fn-pcar-sbud-prepare *pit-bad-count-oc* *pit-fresh-record* 100)))))

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
