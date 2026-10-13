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
; PRF-277 carried the open fold's character trie (books/replay-identity-
; index.lisp fn-rii-kbuild) across POSTs.  PRF-289 replaces it: that trie
; cost ~2 KB of live heap per pin (1,246,448 conses for 10,000 random 64-hex
; ids) and was rebuilt whole (24 MB allocated) after every release.
;
; The set is a path-compressed id trie (retain-carried, fn-rit-*): a leaf is the
; ledger's own pin record or release id string, so an id is only as deep as the prefix it shares
; with another (about four levels for random hex ids) and the trie holds no
; copy of any id.  fn-rit-hasp-of-put holds for every node.
;
; The carry is (LEDGER . TRIE).  fn-prc-carryp says the trie answers exactly
; LEDGER's known ids: every pin and release id is in it (complete) and every
; string stored in it is a known id (sound) (fn-prc-set-okp,
; fn-prc-carryp-is-knownp). A marked trie also carries exact pin finds and
; the ID invariants described in retain-carried. It is executable (a test or a guard can ask it;
; the host never does).  It mentions neither the owner nor the Store, so NO
; owner transition can falsify it: whatever the owner did between two POSTs,
; the carry still describes the ledger it names.  A reader uses the trie
; only when the ledger in hand is EQUAL to the carried one (one EQ test when
; the carry was refreshed from this node), and the reference scan otherwise.
;
; fn-prc-refresh brings the carry to the node's current ledger, preserving
; fn-prc-carryp (fn-prc-carryp-of-refresh): the same ledger keeps the carry;
; a ledger reached from the carried one by retention steps -- releases consed
; on the carried releases (fn-retain-release), pins that are new pins over
; the carried ones less released ones (a durable commit's cons,
; fn-node-complete; a release's fn-retain-remove-id) -- applies that delta
; (fn-prc-delta: new ids put, nothing rebuilt; a commit costs O(1), a release
; O(position of the released pin) + O(depth), k steps between POSTs one walk); anything
; else (the first POST, a recovery, a reopen) rebuilds (fn-prc-build).
;
; The writers are host/owner-host.lisp: fn-owner-install-extended builds the
; carry for the ledger the owner opens with (so the first POST pays nothing),
; and fn-owner-prepare-buffer refreshes it from the owner's Store node and
; passes the result to fn-prc-sbud-prepare.  Every value either writes is
; fn-prc-refresh of nil or of a value it read, and nil satisfies the
; recognizer, so the global always satisfies it (fn-prc-carryp-of-refresh,
; fn-prc-carryp-when-atom).
;
; KEYSTONE (the host calls the left-hand side):
;   fn-prc-sbud-prepare-is-pidx-sbud-prepare
;     (fn-prc-sbud-prepare oc record budget carry)
;       = (fn-pcar-sbud-prepare oc record budget)     under fn-prc-carryp carry
; hence, by fn-pcar-sbud-prepare-is-sbud-prepare, every theorem about fn-sbud-prepare
; is about the host's call (fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-prepare
; states the composition with the writer).

(in-package "ACL2")
(include-book "post-identity-index")
(include-book "replay-identity-index")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-ctl-visible-articles)
                          (:definition fn-ctl-visible-filter)
                          (:definition fn-midx-branch-get))))

(include-book "retain-carried")

(defthm fn-prc-carryp-is-knownp
  (implies (and (fn-prc-carryp carry) (consp carry) (stringp x))
           (iff (fn-prc-has x (cdr carry))
                (fn-rii-knownp x (car carry))))
  :hints (("Goal" :in-theory (e/d (fn-prc-carryp) (fn-prc-find-okp fn-prc-set-okp))
           :use ((:instance fn-prc-set-okp-is-knownp
                                   (ledger (car carry)) (trie (cdr carry)))))))

; -----------------------------------------------------------------------------
; 4. The admission through the carry.

; fn-retain-admissiblep, with the known-id test answered by the carried trie
; when the carry names this ledger.
(defun fn-prc-set-admissiblep (s id subject kind evidence charge trie)
  (declare (xargs :guard (fn-retain-statep s)
                  :guard-hints (("Goal" :in-theory (enable fn-retain-statep)))))
  (and (mbe :logic (fn-retain-statep s) :exec t)
       (stringp id)
       (stringp subject)
       (fn-retain-kindp kind)
       (fn-provp evidence)
       (posp charge)
       (not (fn-rit-hasp id 0 trie))
       (<= (+ (fn-retain-reserved s) charge)
           (fn-retain-capacity s))))

(defun fn-prc-admissiblep (s id subject kind evidence charge carry)
  (declare (xargs :guard (fn-retain-statep s)))
  (if (and (consp carry) (equal (car carry) s))
      (fn-prc-set-admissiblep s id subject kind evidence charge (cdr carry))
    (fn-retain-admissiblep s id subject kind evidence charge)))

(defthm fn-prc-admissiblep-is-admissiblep
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-admissiblep s id subject kind evidence charge carry)
                  (fn-retain-admissiblep s id subject kind evidence charge)))
  :hints (("Goal" :in-theory (e/d (fn-retain-admissiblep fn-prc-has)
                                  (fn-retain-statep fn-prc-carryp-is-knownp))
           :use ((:instance fn-prc-carryp-is-knownp (x id))
                 (:instance fn-rii-knownp-is-known-idp (retention s))))))

; Where the carried test holds, so do the reference's conjuncts the admitted
; ledger's construction reads.
(defthm fn-prc-admissiblep-facts
  (implies (fn-prc-admissiblep s id subject kind evidence charge carry)
           (and (fn-retain-statep s) (stringp id) (stringp subject)
                (fn-retain-kindp kind) (fn-provp evidence) (posp charge)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-admissiblep))))

(in-theory (disable fn-prc-admissiblep fn-prc-set-admissiblep))

; -----------------------------------------------------------------------------
; 5. The prepare chain: fn-pidx-* (books/post-identity-index.lisp) with the
; admission through the carry.

(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
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
(local (in-theory (disable (tau-system))))

(defthm fn-prc-node-prepare-is-pidx-node-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-node-prepare s generation msgid payload groups
                                       obligation-id subject evidence charge
                                       stamp view carry)
                  (fn-pidx-node-prepare s generation msgid payload groups
                                        obligation-id subject evidence charge
                                        stamp view)))
  :hints (("Goal" :in-theory (e/d (fn-prc-node-prepare fn-node-prepare
                                   fn-retain-admit)
                                  (fn-node-statep fn-retain-admissiblep
                                   fn-accept-prepare fn-retain-make-state
                                   fn-retain-make-obligation
                                   fn-node-make-state fn-node-make-stage)))))

(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
(verify-guards fn-prc-node-prepare
  :hints (("Goal" :in-theory (enable fn-node-statep))))
(local (in-theory (disable (tau-system))))

(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
(in-theory (disable fn-prc-node-prepare))
(local (in-theory (disable (tau-system))))

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
  :hints (("Goal" :in-theory (e/d (fn-prc-sn-prepare-node fn-sn-prepare-node)
                                  (fn-replay-advance-txid)))))

(in-theory (disable fn-prc-sn-prepare-node))

(defun fn-prc-spc-prepare (s record view carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-pidx-view-okp view)
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-held-p record)
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
  :hints (("Goal" :in-theory (e/d (fn-prc-spc-prepare fn-spc-prepare)
                                  (fn-sn-statep fn-pcar-stage-record
                                   fn-rcon-sn-record-bindsp
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
                                   fn-opc-owner-prepare)
                                  (fn-own-refresh)))))

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
  :hints (("Goal" :in-theory (e/d (fn-prc-opc-prepare fn-opc-prepare)
                                  (fn-opc-owner-prepare)))))

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
                  (fn-pcar-sbud-prepare oc record budget)))
  :hints (("Goal" :in-theory (e/d (fn-prc-sbud-prepare fn-sbud-prepare)
                                  (fn-opc-prepare fn-sbud-admitp
                                   fn-sbud-count fn-sbud-oc-store)))))

; The composition with the host's writer: the carry the host passes is the
; refresh of a value that has the recognizer; so the host's call is the
; carried prepare fn-pcar-sbud-prepare under PRF-191's two hypotheses.
(defthm fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-prepare
  (implies (and (fn-prc-carryp carry)
                (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc))))
           (equal (fn-prc-sbud-prepare oc record budget
                                       (fn-prc-refresh carry ledger))
                  (fn-pcar-sbud-prepare oc record budget)))
  :hints (("Goal" :in-theory (disable fn-prc-sbud-prepare fn-pcar-sbud-prepare))))

(in-theory (disable fn-prc-sbud-prepare))
