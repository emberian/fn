;; fn: a POST's retention admission answered from a carried obligation-id trie.
;
; After PRF-191 (books/post-identity-index.lisp) one test in the owner's
; prepare still walked a list that grows with the history: the retention
; admission, fn-retain-admissiblep -> fn-retain-known-id-scanp, which asks
; whether the submission's obligation id is already known to the ledger by
; walking every pin (EQUAL + STRING= per pin) and every release.  At
; N = 10,000 it was 205 of 1,741 sb-sprof :cpu samples of an owner POST run
; (11.8 percent, every one under fn-pidx-node-prepare; lane post-alloc's
; hbox profile work/after-cpu10k); PRF-191's own header left it open as
; test (3) (PKT-549).
;
; books/replay-identity-index.lisp (PRF-242) already has the answer for the
; open's fold: an id trie KTRIE with fn-rii-known-okp KTRIE LEDGER (for every
; string id, the trie holds it exactly when the ledger knows it) and
; fn-rii-admissiblep, equal to fn-retain-admissiblep under that relation
; (fn-rii-admissiblep-is-admissiblep).  This book carries such a trie across
; POSTs.
;
; The carry is (LEDGER . KTRIE).  fn-prc-carryp says KTRIE is the id trie
; fn-rii-kbuild builds from LEDGER (or the carry is an atom: nil, before the
; first POST), so it answers LEDGER's known ids (fn-prc-carryp-is-known-okp).
; It is executable (a test or a guard can ask it; the host never does).  It mentions
; neither the owner nor the Store, so NO owner transition can falsify it:
; whatever the owner did between two POSTs (commit, abort, recovery, a
; retention verb, a reconfiguration, a reopen), the carry still describes
; the ledger it names.  The recognizer is keyed by the ledger it was built
; for; a reader uses KTRIE only when the ledger in hand is EQUAL to the
; carried one (one EQ test when the carry was refreshed from this node), and
; the reference scan otherwise.
;
; fn-prc-refresh brings the carry to the node's current ledger before each
; prepare, preserving fn-prc-carryp for every input carry that has it
; (fn-prc-carryp-of-refresh): the same ledger keeps the trie; a ledger that
; is the carried one with one pin consed (a durable commit installs the
; staged ledger, whose pins are the old list under one new pin,
; fn-node-complete) puts that one id; anything else (the first POST, a
; release, a recovery) rebuilds the trie from the ledger (fn-rii-kbuild,
; linear, and correct whatever happened).
;
; The one writer is host/owner-host.lisp fn-owner-prepare-buffer: it refreshes
; the global fn-owner-retain-carry from the owner's Store node and passes the
; result to fn-prc-sbud-prepare.  Every value it writes is fn-prc-refresh of
; a value it read, and nil satisfies the recognizer, so the global always
; satisfies it (fn-prc-carryp-of-refresh, fn-prc-carryp-when-atom).
;
; KEYSTONE (the host calls the left-hand side):
;   fn-prc-sbud-prepare-is-pidx-sbud-prepare
;     (fn-prc-sbud-prepare oc record budget carry)
;       = (fn-pidx-sbud-prepare oc record budget)     under fn-prc-carryp carry
; hence, by fn-pidx-sbud-prepare-is-pcar-sbud-prepare and
; fn-pcar-sbud-prepare-is-sbud-prepare, every theorem about fn-sbud-prepare
; is about the host's call (fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-prepare
; states the composition with the writer).

(in-package "ACL2")
(include-book "post-identity-index")
(include-book "replay-identity-index")

; -----------------------------------------------------------------------------
; 1. The carry.

(defun fn-prc-carryp (carry)
  (declare (xargs :guard t))
  (or (atom carry)
      (equal (cdr carry) (fn-rii-kbuild (car carry)))))

(defthm fn-prc-carryp-when-atom
  (implies (atom carry) (fn-prc-carryp carry)))

; What a reader uses: the carried trie answers exactly the carried ledger's
; known ids (fn-rii-kbuild-is-known-okp).
(defthm fn-prc-carryp-is-known-okp
  (implies (and (fn-prc-carryp carry) (consp carry))
           (fn-rii-known-okp (cdr carry) (car carry)))
  :hints (("Goal" :in-theory (disable fn-rii-kbuild fn-rii-known-okp))))

(defun fn-prc-refresh (carry ledger)
  (declare (xargs :guard t))
  (if (and (consp carry) (equal (car carry) ledger))
      carry
    (let ((pins (fn-retain-pins ledger)))
      (if (and (consp carry)
               (consp pins)
               (equal (cdr pins) (fn-retain-pins (car carry)))
               (equal (fn-retain-releases ledger)
                      (fn-retain-releases (car carry))))
          (cons ledger
                (fn-rii-id-put (fn-retain-obligation-id (car pins))
                               (cdr carry)))
        (cons ledger (fn-rii-kbuild ledger))))))

; The trie of a ledger whose pins are another's under one new pin, with the
; same releases, is the other's trie with that pin's id put.
(local
 (defthm fn-prc-kbuild-of-pin-cons
   (implies (and (consp (fn-retain-pins r1))
                 (equal (cdr (fn-retain-pins r1)) (fn-retain-pins r0))
                 (equal (fn-retain-releases r1) (fn-retain-releases r0)))
            (equal (fn-rii-kbuild r1)
                   (fn-rii-id-put (fn-retain-obligation-id
                                   (car (fn-retain-pins r1)))
                                  (fn-rii-kbuild r0))))
   :hints (("Goal" :in-theory (disable fn-rii-kbuild-releases fn-rii-id-put)
            :expand ((fn-rii-kbuild-pins (fn-retain-pins r1)
                                         (fn-rii-kbuild-releases
                                          (fn-retain-releases r0))))))))

(defthm fn-prc-carryp-of-refresh
  (implies (fn-prc-carryp carry)
           (fn-prc-carryp (fn-prc-refresh carry ledger)))
  :hints (("Goal" :in-theory (disable fn-rii-kbuild-releases fn-rii-kbuild-pins
                                      fn-rii-id-put))))

(defthm fn-prc-refresh-names-the-ledger
  (and (consp (fn-prc-refresh carry ledger))
       (equal (car (fn-prc-refresh carry ledger)) ledger)))

(in-theory (disable fn-prc-carryp fn-prc-refresh))

; -----------------------------------------------------------------------------
; 2. The admission through the carry.

; fn-retain-admissiblep, with the known-id test answered by the carried trie
; when the carry names this ledger.
(defun fn-prc-admissiblep (s id subject kind evidence charge carry)
  (declare (xargs :guard (fn-retain-statep s)))
  (if (and (consp carry) (equal (car carry) s))
      (fn-rii-admissiblep s id subject kind evidence charge (cdr carry))
    (fn-retain-admissiblep s id subject kind evidence charge)))

(defthm fn-prc-admissiblep-is-admissiblep
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-admissiblep s id subject kind evidence charge carry)
                  (fn-retain-admissiblep s id subject kind evidence charge)))
  :hints (("Goal" :in-theory (disable fn-rii-admissiblep fn-retain-admissiblep
                                      fn-rii-known-okp fn-prc-carryp)
           :use ((:instance fn-rii-admissiblep-is-admissiblep
                            (ktrie (cdr carry)))))))

; Where the carried test holds, so do the reference's conjuncts the admitted
; ledger's construction reads.
(defthm fn-prc-admissiblep-facts
  (implies (fn-prc-admissiblep s id subject kind evidence charge carry)
           (and (fn-retain-statep s) (stringp id) (stringp subject)
                (fn-retain-kindp kind) (fn-provp evidence) (posp charge)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-admissiblep))))

(in-theory (disable fn-prc-admissiblep))

; -----------------------------------------------------------------------------
; 3. The prepare chain: fn-pidx-* (books/post-identity-index.lisp) with the
; admission through the carry.

(defun fn-prc-node-prepare (s generation msgid payload groups
                              obligation-id subject evidence charge stamp
                              view carry)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-node-statep s)) :exec nil)
      s
    (let ((retention (fn-node-retention s)))
      (if (not (fn-prc-admissiblep retention obligation-id subject :archive
                                   evidence charge carry))
          s
        (let ((next-acceptance
               (fn-pidx-accept-prepare (fn-node-acceptance s)
                                       generation msgid payload groups stamp
                                       view)))
          (if (equal next-acceptance (fn-node-acceptance s))
              s
            (fn-node-make-state
             next-acceptance
             retention
             (fn-node-make-stage
              msgid generation obligation-id subject evidence charge
              (fn-retain-make-state
               (fn-retain-capacity retention)
               (+ (fn-retain-reserved retention) charge)
               (cons (fn-retain-make-obligation obligation-id subject :archive
                                                evidence charge)
                     (fn-retain-pins retention))
               (fn-retain-releases retention)))
             (fn-node-bindings s))))))))

(defthm fn-prc-node-prepare-is-pidx-node-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-node-prepare s generation msgid payload groups
                                       obligation-id subject evidence charge
                                       stamp view carry)
                  (fn-pidx-node-prepare s generation msgid payload groups
                                        obligation-id subject evidence charge
                                        stamp view)))
  :hints (("Goal" :in-theory (e/d (fn-prc-node-prepare fn-pidx-node-prepare)
                                  (fn-node-statep fn-retain-admissiblep
                                   fn-pidx-accept-prepare fn-retain-make-state
                                   fn-retain-make-obligation
                                   fn-node-make-state fn-node-make-stage)))))

(verify-guards fn-prc-node-prepare
  :hints (("Goal" :in-theory (enable fn-node-statep))))

(in-theory (disable fn-prc-node-prepare))

(defun fn-prc-sn-prepare-node (node record view carry)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-prc-node-prepare (fn-replay-advance-txid node (fn-record-txid record))
                       (fn-record-generation record) (fn-record-msgid record)
                       (fn-record-payload record) (fn-record-groups record)
                       (fn-record-obligation-id record)
                       (fn-record-content-subject record)
                       (fn-record-release-evidence record)
                       (fn-record-charge record)
                       (fn-record-stamp record)
                       view carry))

(verify-guards fn-prc-sn-prepare-node)

(defthm fn-prc-sn-prepare-node-is-pidx-sn-prepare-node
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-sn-prepare-node node record view carry)
                  (fn-pidx-sn-prepare-node node record view)))
  :hints (("Goal" :in-theory (e/d (fn-prc-sn-prepare-node fn-pidx-sn-prepare-node)
                                  (fn-pidx-node-prepare fn-replay-advance-txid)))))

(in-theory (disable fn-prc-sn-prepare-node))

(defun fn-prc-spc-prepare (s record view carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-pidx-view-okp view)
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-held-p record)
           (not (equal (fn-record-stamp record) :legacy))
           (equal (fn-hc-generation (fn-held-context record))
                  (fn-sn-keyring-generation s))
           (eq (car (fn-rcon-cpe-projection-step
                     (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok))
      (let* ((node (fn-prc-sn-prepare-node (fn-sn-node s) record view carry))
             (files (fn-pcar-stage-record (fn-sn-files s) record)))
        (if (and (fn-rcon-sn-record-bindsp node record)
                 (equal (fn-sf-phase files) :record-staged))
            (fn-sn-update s files node)
          s))
    s))

(defthm fn-prc-spc-prepare-is-pidx-spc-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-spc-prepare s record view carry)
                  (fn-pidx-spc-prepare s record view)))
  :hints (("Goal" :in-theory (e/d (fn-prc-spc-prepare fn-pidx-spc-prepare)
                                  (fn-sn-statep fn-pcar-stage-record
                                   fn-pidx-sn-prepare-node fn-rcon-sn-record-bindsp
                                   fn-held-p fn-rcon-cpe-projection-step
                                   fn-sn-update)))))

(verify-guards fn-prc-spc-prepare
  :hints (("Goal" :use ((:instance fn-prc-spc-prepare-is-pidx-spc-prepare)
                        (:instance fn-pidx-spc-prepare-is-pcar-spc-prepare)
                        (:instance fn-pcar-spc-prepare-is-spc-prepare))
           :in-theory (e/d (fn-sn-statep)
                           (fn-sf-statep fn-node-statep fn-node-pending-matchesp
                            fn-sn-pending-record fn-sn-prepare-node
                            fn-pidx-view-okp fn-prc-carryp)))))

(in-theory (disable fn-prc-spc-prepare))

(defun fn-prc-opc-owner-prepare (o record carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store o))
                              (fn-pidx-view-okp (fn-own-view o))
                              (fn-prc-carryp carry))))
  (fn-own-refresh
   (fn-own-make (fn-prc-spc-prepare (fn-own-store o) record (fn-own-view o) carry)
                (fn-own-view o) (fn-own-conns o)
                (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger-field o)
                (fn-own-clock o) (fn-own-facts o)
                (fn-own-config o) (fn-own-queue o)
                (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))

(defthm fn-prc-opc-owner-prepare-is-pidx-opc-owner-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-opc-owner-prepare o record carry)
                  (fn-pidx-opc-owner-prepare o record)))
  :hints (("Goal" :in-theory (e/d (fn-prc-opc-owner-prepare
                                   fn-pidx-opc-owner-prepare)
                                  (fn-own-refresh fn-pidx-spc-prepare)))))

(in-theory (disable fn-prc-opc-owner-prepare))

(defun fn-prc-opc-prepare (oc record carry)
  (declare (xargs :guard (and (fn-sn-statep
                               (fn-own-store (fn-ocfg-owner oc)))
                              (fn-pidx-view-okp
                               (fn-own-view (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))))
  (fn-ocfg-with-owner
   oc (fn-prc-opc-owner-prepare (fn-ocfg-owner oc) record carry)))

(defthm fn-prc-opc-prepare-is-pidx-opc-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-opc-prepare oc record carry)
                  (fn-pidx-opc-prepare oc record)))
  :hints (("Goal" :in-theory (e/d (fn-prc-opc-prepare fn-pidx-opc-prepare)
                                  (fn-pidx-opc-owner-prepare)))))

(in-theory (disable fn-prc-opc-prepare))

; The function host/owner-host.lisp fn-owner-prepare-buffer installs, with
; CARRY = (fn-prc-refresh <the global fn-owner-retain-carry> <the ledger of
; the owner's Store node>).
(defun fn-prc-sbud-prepare (oc record budget carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-pidx-view-okp
                               (fn-own-view (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))))
  (if (fn-sbud-admitp budget (fn-sbud-count (fn-sbud-oc-store oc)))
      (fn-prc-opc-prepare oc record carry)
    oc))

; KEYSTONE.  Under the carry's recognizer (which no owner step can falsify),
; the host's prepare is PRF-191's, for every owner, record and budget.
(defthm fn-prc-sbud-prepare-is-pidx-sbud-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-sbud-prepare oc record budget carry)
                  (fn-pidx-sbud-prepare oc record budget)))
  :hints (("Goal" :in-theory (e/d (fn-prc-sbud-prepare fn-pidx-sbud-prepare)
                                  (fn-pidx-opc-prepare fn-sbud-admitp
                                   fn-sbud-count fn-sbud-oc-store)))))

; The composition with the host's writer: the carry the host passes is the
; refresh of a value that has the recognizer; so the host's call is the
; carried prepare fn-pcar-sbud-prepare under PRF-191's three hypotheses.
(defthm fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-prepare
  (implies (and (fn-prc-carryp carry)
                (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc)))
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-ceis-indexedp (fn-sbud-oc-store oc)))
           (equal (fn-prc-sbud-prepare oc record budget
                                       (fn-prc-refresh carry ledger))
                  (fn-pcar-sbud-prepare oc record budget)))
  :hints (("Goal" :in-theory (disable fn-prc-sbud-prepare fn-pidx-sbud-prepare
                                      fn-pcar-sbud-prepare))))

(in-theory (disable fn-prc-sbud-prepare))
