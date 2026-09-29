; Teeth for books/identity-retain-carried.lisp (served-costs-4, Q5b).
;
; The owners and the signed composite are owner-identity-served-tests':
; *pse-k2-reserved* (a configured owner at :reserved, fn.test served, the
; author enrolled), the wire composite *pse-comp* at the arena's count
; *ois-h*, the staged owner *ois-staged* and its ordered owner *ois-ordered*
; (at :completing).  The carry is what the host stores: fn-prc-refresh of the
; global's value (nil at first) to the Store node's ledger.
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/identity-retain-carried")
(include-book "owner-identity-served-tests")
(include-book "post-retain-carried-tests")

(defun irct-retention (oc)
  (fn-node-retention (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
(defun irct-phase (oc)
  (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))

; fn-irc-rix-ocfg-complete over a history stobj loaded with the history it
; reads (fn-hist-of-storep holds by construction), as
; owner-refresh-indexed-tests' fn-rix-ocfg-complete-h.
(defun irct-complete-h (oc carry)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load
                      (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                      0 fn-hist)))
        (mv (fn-irc-rix-ocfg-complete oc fn-hist carry) fn-hist))
      ans)))
(defun irct-rix-complete-h (oc)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load
                      (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                      0 fn-hist)))
        (mv (fn-rix-ocfg-complete oc fn-hist) fn-hist))
      ans)))

; The host's carry at the signed POST's prepare: the refresh of nil (the
; global's first value) to the Store node's ledger.  It names that ledger,
; so fn-prc-admissiblep takes the trie branch (EQUAL ledgers).
(defconst *irct-carry* (fn-prc-refresh nil (irct-retention *pse-k2-reserved*)))
(assert-event (fn-prc-carryp nil))
(assert-event (fn-prc-carryp *irct-carry*))
(assert-event (consp *irct-carry*))
(assert-event (equal (car *irct-carry*) (irct-retention *pse-k2-reserved*)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-irc-pout-prepare-identity-of-refresh-is-pout.  REACHABLE
; POSITIVE WITNESS: carry nil (fn-prc-carryp), ledger the Store node's; the
; host's call stages the composite's row (word :prepared, owner
; *ois-staged*), and word and owner are fn-pout-prepare-identity's.
; (The record decoder is an attachment, which a defconst may not evaluate:
; the values are asserted in place, as the host computes them.)
(defun irct-prep (carry)
  (declare (xargs :verify-guards nil))
  (mv-list 2 (fn-irc-pout-prepare-identity *pse-k2-reserved* *pse-comp* *ois-h*
                                           (fn-prc-refresh carry (irct-retention *pse-k2-reserved*)))))
(assert-event (equal (car (irct-prep nil)) :prepared))
(assert-event (equal (cadr (irct-prep nil)) *ois-staged*))
(assert-event (equal (irct-phase (cadr (irct-prep nil))) :record-staged))
(assert-event (equal (irct-prep nil)
                     (mv-list 2 (fn-pout-prepare-identity *pse-k2-reserved* *pse-comp* *ois-h*))))
; The intermediate twins at the same point.
(assert-event (equal (fn-irc-sn-prepare-identity (lgt-store *pse-k2-reserved*) *ois-row* *irct-carry*)
                     (fn-ccar-sn-prepare-identity (lgt-store *pse-k2-reserved*) *ois-row*)))
(assert-event (equal (fn-irc-apply-record (fn-sn-node (lgt-store *pse-k2-reserved*)) *ois-row* *irct-carry*)
                     (fn-replay-apply-record (fn-sn-node (lgt-store *pse-k2-reserved*)) *ois-row*)))
(assert-event (consp (fn-irc-apply-record (fn-sn-node (lgt-store *pse-k2-reserved*)) *ois-row* *irct-carry*)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-irc-rix-ocfg-complete-of-refresh-is-ocfg-step-complete.
; REACHABLE POSITIVE WITNESS: the ordered owner (the prepare left the node,
; hence the carry's ledger, unchanged), at :completing, its history loaded
; (fn-hist-of-storep by construction), carry the refresh of nil: the gate
; holds through the carry, the completion reaches :ready, and it is the
; reference completion (fn-rix-ocfg-complete, fn-ccar-ocfg-complete, which is
; fn-ocfg-step of (:complete) for every arena).
(assert-event (equal (irct-phase *ois-ordered*) :completing))
(assert-event (equal (irct-retention *ois-ordered*) (irct-retention *pse-k2-reserved*)))
(defconst *irct-fcarry* (fn-prc-refresh nil (irct-retention *ois-ordered*)))
(assert-event (fn-irc-completion-enabledp (lgt-store *ois-ordered*) *irct-fcarry*))
(assert-event (equal (fn-irc-completion-core-enabledp (lgt-store *ois-ordered*) *irct-fcarry*)
                     (fn-ccar-completion-core-enabledp (lgt-store *ois-ordered*))))
(assert-event (equal (irct-phase (irct-complete-h *ois-ordered* *irct-fcarry*)) :ready))
(assert-event (equal (irct-complete-h *ois-ordered* *irct-fcarry*)
                     (irct-rix-complete-h *ois-ordered*)))
(assert-event (equal (irct-complete-h *ois-ordered* *irct-fcarry*)
                     (fn-ccar-ocfg-complete *ois-ordered*)))
(assert-event (equal (fn-irc-sn-finish-enabled (lgt-store *ois-ordered*) *irct-fcarry*)
                     (fn-ccar-sn-finish-enabled (lgt-store *ois-ordered*))))

; -----------------------------------------------------------------------------
; HYPOTHESIS-REMOVAL WITNESS for fn-prc-carryp (both keystones' only
; hypothesis).  A carry that names the Store node's ledger but whose trie
; also answers the composite's own obligation id (unsound: that id is no pin
; or release of the ledger).  The omitted hypothesis fails, the refresh keeps
; the carry (same ledger), and both conclusions fail: the prepare refuses
; the composite the reference stages, and the completion gate refuses the
; completion the reference makes.
(defconst *irct-oid*
  (fn-record-obligation-id (fn-replay-composite-held *ois-row*)))
(assert-event (stringp *irct-oid*))
(assert-event (not (fn-rii-knownp *irct-oid* (irct-retention *pse-k2-reserved*))))
(defconst *irct-bad*
  (cons (irct-retention *pse-k2-reserved*) (fn-prc-add *irct-oid* (cdr *irct-carry*))))
(assert-event (not (fn-prc-carryp *irct-bad*)))
(assert-event (equal (fn-prc-refresh *irct-bad* (irct-retention *pse-k2-reserved*)) *irct-bad*))
; Outside the twins' guard (the carry is not fn-prc-carryp): evaluated
; under `with-guard-checking :none', as acceptance-tests' refusals are.
(assert-event
 (with-guard-checking :none
  (not (equal (car (irct-prep *irct-bad*)) :prepared))))
(assert-event
 (with-guard-checking :none
  (not (equal (irct-prep *irct-bad*)
                          (mv-list 2 (fn-pout-prepare-identity *pse-k2-reserved* *pse-comp* *ois-h*))))))
(assert-event
 (with-guard-checking :none
  (not (fn-irc-completion-enabledp (lgt-store *ois-ordered*) *irct-bad*))))
(assert-event
 (with-guard-checking :none
  (not (equal (irct-complete-h *ois-ordered* *irct-bad*)
                          (fn-ccar-ocfg-complete *ois-ordered*)))))
(assert-event
 (with-guard-checking :none
  (equal (irct-phase (irct-complete-h *ois-ordered* *irct-bad*)) :completing)))

; -----------------------------------------------------------------------------
; fn-irc-apply-retention-event-is-reference.  REACHABLE POSITIVE WITNESS:
; post-retain-carried-tests' node NODE1 and its forwarding undertaking of
; "fwd-pin:pit" (then its release), carry the refresh of nil to NODE1's
; ledger: the twin undertakes (a node, the pin admitted) exactly as the
; Store's retention transition, and releases exactly as it.
(defconst *irct-u-ev*
  (fn-store-retention-event-make :undertake 9 *prct-tx1* *prct-tx1*
                                 "fwd-pin:pit" "fwd-content:pit"
                                 "fwd-receipt:pit" 2))
(defconst *irct-r-ev*
  (fn-store-retention-event-make :release 10 *prct-tx2* *prct-tx2*
                                 "fwd-pin:pit" "fwd-content:pit"
                                 "fwd-receipt:pit" 0))
(defconst *irct-rcarry* (fn-prc-refresh nil (fn-node-retention *prct-node1*)))
(assert-event (fn-prc-carryp *irct-rcarry*))
(assert-event (equal (car *irct-rcarry*) (fn-node-retention *prct-node1*)))
(assert-event (consp (fn-irc-apply-retention-event *prct-node1* *irct-u-ev* *irct-rcarry*)))
(assert-event (equal (fn-irc-apply-retention-event *prct-node1* *irct-u-ev* *irct-rcarry*)
                     *prct-nu*))
(assert-event (equal (fn-irc-apply-retention-event
                      *prct-nu* *irct-r-ev* (fn-prc-refresh *irct-rcarry* *prct-ru*))
                     *prct-nr*))
(assert-event (consp *prct-nr*))
; ... and through the record application the completion runs.
(assert-event (equal (fn-irc-apply-record *prct-node1* *irct-u-ev* *irct-rcarry*)
                     *prct-nu*))

; HYPOTHESIS-REMOVAL WITNESS (fn-prc-carryp): the carry names NODE1's ledger
; but its trie also answers "fwd-pin:pit", which no pin or release of that
; ledger holds; the undertaking the reference admits is refused.
(defconst *irct-rbad*
  (cons (fn-node-retention *prct-node1*) (fn-prc-add "fwd-pin:pit" (cdr *irct-rcarry*))))
(assert-event (not (fn-rii-knownp "fwd-pin:pit" (fn-node-retention *prct-node1*))))
(assert-event (not (fn-prc-carryp *irct-rbad*)))
(assert-event
 (with-guard-checking :none
  (null (fn-irc-apply-retention-event *prct-node1* *irct-u-ev* *irct-rbad*))))
(assert-event
 (with-guard-checking :none
  (not (equal (fn-irc-apply-retention-event *prct-node1* *irct-u-ev* *irct-rbad*)
              (fn-replay-apply-retention-event *prct-node1* *irct-u-ev*)))))
