; Teeth for books/post-identity-index.lisp (PRF-191).
(in-package "ACL2")
(include-book "../../books/post-identity-index")
(include-book "must-fail-checked")
(include-book "owner-prepare-carried-tests")

; -----------------------------------------------------------------------------
; The reachable witness: owner-prepare-carried-tests' *pcar-t-o*, the owner
; the host's POST events reach with the Store :reserved for connection 4's
; submission, one article ("<one@example>") and a second one committed.  Its
; view is the one fn-own-refresh built from this node: the raw list IS the
; node's article list.

(defconst *pit-o* *pcar-t-o*)
(defconst *pit-oc* *pcar-t-oc*)
(defconst *pit-view* (fn-own-view *pit-o*))
(defconst *pit-arts*
  (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store *pit-o*)))))
(defconst *pit-held* "<one@example>")
(defconst *pit-fresh* "<fresh@example>")
(defconst *pit-held-article* (fn-find-article *pit-held* *pit-arts*))

(assert-event (and (equal (len *pit-arts*) 2)
                   (consp *pit-held-article*)
                   (not (fn-find-article *pit-fresh* *pit-arts*))
                   (equal *pit-arts* (fn-own-view-raw *pit-view*))
                   (null (fn-own-view-withdrawals *pit-view*))))
; The named premise of the prepare chain's guards holds.
(assert-event (and (fn-ocl-view-visiblep *pit-view*)
                   (fn-pidx-view-okp *pit-view*)))

;; -----------------------------------------------------------------------------
; fn-pidx-find-article-is-find-article-by-definition, reachable: a held and a
; fresh Message-ID are found as the scan finds them, and the answer is the
; scan's for another article list too.

(assert-event (and (equal (fn-pidx-find-article *pit-held* *pit-arts* *pit-view*)
                          *pit-held-article*)
                   (equal (fn-pidx-find-article *pit-held* *pit-arts* *pit-view*)
                          (fn-find-article *pit-held* *pit-arts*))))
(assert-event (and (null (fn-pidx-find-article *pit-fresh* *pit-arts* *pit-view*))
                   (null (fn-find-article *pit-fresh* *pit-arts*))))
(assert-event (equal (fn-pidx-find-article *pit-held* (cdr *pit-arts*) *pit-view*)
                     (fn-find-article *pit-held* (cdr *pit-arts*))))

; A withdrawal record naming the held Message-ID (constructed: the record is
; no withdrawal, so the visible list is unchanged) leaves the answer the
; scan's.
(defun pit-view-with (v archive withdrawals)
  (fn-own-view-make-visible
   (fn-own-view-version v) (fn-own-view-frontier v) archive
   (fn-own-view-verdicts v) (fn-own-view-group-index v) withdrawals
   (fn-own-view-raw v) (fn-own-view-withdrawn v) (fn-own-view-keyring v)))

(defconst *pit-targeted-view*
  (pit-view-with *pit-view* (fn-own-view-archive *pit-view*)
                 (list (list :not-a-withdrawal *pit-held*))))
(assert-event (and (fn-ocl-view-visiblep *pit-targeted-view*)
                   (fn-pidx-targetedp *pit-held*
                                      (fn-own-view-withdrawals *pit-targeted-view*))
                   (equal (fn-pidx-find-article *pit-held* *pit-arts*
                                                *pit-targeted-view*)
                          *pit-held-article*)))

; -----------------------------------------------------------------------------
; The view is no premise of any equation (CORRUPTED views: no owner transition
; builds them).  Each adds an article under the fresh Message-ID to the
; visible list only, which the lookup and the decisions below never read.

(defconst *pit-fake-article*
  (fn-make-article *pit-fresh* (fn-article-payload *pit-held-article*)
                   (fn-article-groups *pit-held-article*)
                   (fn-article-memberships *pit-held-article*)
                   (fn-article-pin *pit-held-article*)
                   (fn-article-stamp *pit-held-article*)))
(defconst *pit-fake-visible*
  (cons *pit-fake-article* (fn-state-articles (fn-own-view-archive *pit-view*))))

(defconst *pit-bad-visible-view*
  (pit-view-with *pit-view*
                 (fn-ctl-visible-state-of (fn-own-view-archive *pit-view*)
                                          *pit-fake-visible*)
                 nil))
(assert-event (and (not (fn-ocl-view-visiblep *pit-bad-visible-view*))
                   (equal (fn-pidx-find-article *pit-fresh* *pit-arts*
                                                *pit-bad-visible-view*)
                          (fn-find-article *pit-fresh* *pit-arts*))
                   (null (fn-pidx-find-article *pit-fresh* *pit-arts*
                                               *pit-bad-visible-view*))))

; -----------------------------------------------------------------------------
; fn-pidx-existing-action-is-store-existing-action, on a live local buffer as
; the host runs it.

(defun pit-owner-with-view (o v)
  (fn-own-make (fn-own-store o) v (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))

; by specification: the flip -- the host's call reads the stored bytes
; through the arena by the article's handle, and its keystone's reference is
; the Store's entry fn-store-existing-action over that arena
; (books/store-intern.lisp).  The arena here is the one that interned the
; owner's journal in order (owner-served-invariants-tests osi-prior: the two
; records "<one@example>" and "<two@example>" at handles 0 and 1).
(defconst *pit-prior* (osi-prior nil))

(defun pit-existing-in (msgid payload groups o fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
  (mv-let (ignored fn-arena)
    (fn-hrt-events *pit-prior* nil 0 fn-arena)
    (declare (ignore ignored))
    (let ((fn-octets (fn-octets-from-list payload fn-octets)))
      (mv (fn-pidx-existing-action msgid fn-octets groups o fn-arena)
          fn-octets fn-arena))))

(defun pit-existing (msgid payload groups o)
  (declare (xargs :guard (fn-cbor-octet-listp payload) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (with-local-stobj fn-arena
        (mv-let (r fn-octets fn-arena)
          (pit-existing-in msgid payload groups o fn-octets fn-arena)
          (mv r fn-octets)))
      r)))

(defun pit-store-existing-in (msgid payload groups s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (ignored fn-arena)
    (fn-hrt-events *pit-prior* nil 0 fn-arena)
    (declare (ignore ignored))
    (mv (fn-store-existing-action msgid payload groups s fn-arena) fn-arena)))

(defun pit-store-existing (msgid payload groups s)
  (declare (xargs :guard (fn-cbor-octet-listp payload) :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (pit-store-existing-in msgid payload groups s fn-arena)
      r)))

; The held article's own bytes: those under its handle.
(assert-event (natp (fn-article-payload *pit-held-article*)))
(defconst *pit-payload*
  (fn-hrt-bytes *pit-prior* (fn-article-payload *pit-held-article*)))
(assert-event (consp *pit-payload*))
(defconst *pit-groups* (fn-article-groups *pit-held-article*))
(defconst *pit-changed* (append *pit-payload* (list 88)))
(defconst *pit-store* (fn-own-store *pit-o*))

; Reachable: the held article's own bytes are :duplicate, changed bytes
; :conflict, a fresh Message-ID nil; each equal to the Store's entry over the
; arena (the keystone's reference).
(assert-event
 (and (equal (pit-existing *pit-held* *pit-payload* *pit-groups* *pit-o*) :duplicate)
      (equal (pit-store-existing *pit-held* *pit-payload* *pit-groups* *pit-store*)
             :duplicate)
      (equal (pit-existing *pit-held* *pit-changed* *pit-groups* *pit-o*) :conflict)
      (equal (pit-store-existing *pit-held* *pit-changed* *pit-groups* *pit-store*)
             :conflict)
      (null (pit-existing *pit-fresh* *pit-payload* *pit-groups* *pit-o*))
      (null (pit-store-existing *pit-fresh* *pit-payload* *pit-groups* *pit-store*))))

; PRF-191's keystone, literally, at the reached owner (audit-fixes item 1):
; both view hypotheses hold and the host's decision equals
; fn-store-existing-action over the same arena for all three answers.
; (fn-octets-p fn-octets) is the stobj's recognizer: no executable buffer
; violates it, so no removal witness is claimed for it.
(assert-event
 (and (fn-ocl-view-visiblep (fn-own-view *pit-o*))
      (equal (pit-existing *pit-held* *pit-payload* *pit-groups* *pit-o*)
             (pit-store-existing *pit-held* *pit-payload* *pit-groups* *pit-store*))
      (equal (pit-existing *pit-held* *pit-changed* *pit-groups* *pit-o*)
             (pit-store-existing *pit-held* *pit-changed* *pit-groups* *pit-store*))
      (equal (pit-existing *pit-fresh* *pit-payload* *pit-groups* *pit-o*)
             (pit-store-existing *pit-fresh* *pit-payload* *pit-groups* *pit-store*))))

; The corrupted view above changes neither the decision nor the Store's entry:
; the fresh Message-ID is answered nil by both.
(defconst *pit-bad-visible-o* (pit-owner-with-view *pit-o* *pit-bad-visible-view*))
(assert-event
 (and (equal (fn-own-store *pit-bad-visible-o*) *pit-store*)
      (not (fn-ocl-view-visiblep (fn-own-view *pit-bad-visible-o*)))
      (null (pit-existing *pit-fresh* *pit-payload* *pit-groups* *pit-bad-visible-o*))
      (equal (pit-existing *pit-fresh* *pit-payload* *pit-groups* *pit-bad-visible-o*)
             (pit-store-existing *pit-fresh* *pit-payload* *pit-groups* *pit-store*))))

; -----------------------------------------------------------------------------
; fn-pidx-sbud-prepare-is-pcar-sbud-prepare, reachable: the submission's own
; record stages; a record under the held Message-ID (its own obligation id,
; so retention admits it) is refused by the duplicate test; at the budget
; both are the identity.

(defconst *pit-record* *pcar-t-record*)
(defun pit-record-wire-under (msgid)
  (fn-record-make 2 2 2 msgid (fn-own-sub-octets *osi-sub*) '("fn.letters")
                  "own-pin:pit" "own-content:pit" "own-release:pit" 2 841000000))
; by specification: the flip -- the owner stages the held row the entry
; interns (host/owner-host.lisp fn-owner-prepare-buffer: fn-apc-intern-row-at
; at the arena's next handle), here handle 2 after owner-tests' two records
; (owner-served-invariants-tests osi-record-of's convention).
(defun pit-record-under (msgid)
  (fn-hrt-row-at (pit-record-wire-under msgid) 2))
(defconst *pit-dup-record* (pit-record-under *pit-held*))
(defconst *pit-fresh-record* (pit-record-under *pit-fresh*))

(defun pit-phase (oc)
  (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))

; The third hypothesis (PRF-242): the owner's Store is indexed, so the count
; the prepare reads is the committed record count.


(assert-event
 (let ((a (fn-pidx-sbud-prepare *pit-oc* *pit-record* 100))
       (b (fn-pidx-sbud-prepare *pit-oc* *pit-fresh-record* 100))
       (c (fn-pidx-sbud-prepare *pit-oc* *pit-dup-record* 100)))
   (and (equal a (fn-pcar-sbud-prepare *pit-oc* *pit-record* 100))
        (equal (pit-phase a) :record-staged)
        (equal b (fn-pcar-sbud-prepare *pit-oc* *pit-fresh-record* 100))
        (equal (pit-phase b) :record-staged)
        (equal c (fn-pcar-sbud-prepare *pit-oc* *pit-dup-record* 100))
        (equal c *pit-oc*)
        ; The duplicate test is what refused it: the retention ledger admits
        ; its obligation, and the acceptance machine refuses the Message-ID.
        (fn-retain-admissiblep
         (fn-node-retention (fn-sn-node (fn-own-store *pit-o*)))
         "own-pin:pit" "own-content:pit" :archive "own-release:pit" 2)
        (fn-acceptedp *pit-held* *pit-arts*)
        (equal (fn-pidx-sbud-prepare *pit-oc* *pit-record* 2) *pit-oc*)
        (equal (fn-pidx-sbud-prepare *pit-oc* *pit-record* 2)
               (fn-pcar-sbud-prepare *pit-oc* *pit-record* 2)))))

; The staged proposal carries the ledger fn-retain-admit builds (the second
; admissibility test removed, the ledger unchanged).
(assert-event
 (let* ((node (fn-sn-node (fn-own-store *pit-o*)))
        (after (fn-sn-node (fn-own-store (fn-ocfg-owner
                                          (fn-pidx-sbud-prepare *pit-oc* *pit-fresh-record* 100))))))
   (equal (fn-node-stage-retention (fn-node-stage after))
          (fn-retain-admit (fn-node-retention node)
                           "own-pin:pit" "own-content:pit" :archive
                           "own-release:pit" 2))))

; The corrupted view changes neither prepare: the fresh record stages under
; both.  The prepare's guard carries the view facts, so the corrupted run
; evaluates without guard checking, as the host's raw call would.
(defconst *pit-bad-visible-oc* (fn-ocfg-with-owner *pit-oc* *pit-bad-visible-o*))
(make-event
 `(defconst *pit-bad-visible-prepared*
    ',(with-guard-checking
       :none
       (fn-pidx-sbud-prepare *pit-bad-visible-oc* *pit-fresh-record* 100))))
(assert-event
 (equal *pit-bad-visible-prepared*
        (with-guard-checking
         :none
         (fn-pcar-sbud-prepare *pit-bad-visible-oc* *pit-fresh-record* 100))))
(assert-event (equal (pit-phase *pit-bad-visible-prepared*) :record-staged))

; Removal of the third hypothesis, CORRUPTED (no Store transition builds it):
; the reachable owner whose Store's event index claims 100 records while the
; history holds fewer.  Both view facts hold; the index does not describe the
; history; the prepare refuses at budget 100 (the carried count says the
; budget is spent) where the reference, counting the history, stages.
(defun pit-owner-with-store (o s)
  (fn-own-make s (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
               (fn-own-node-secret o) (fn-own-refused o)))





; -----------------------------------------------------------------------------
; The host's calls run compiled code: every function is guard-verified; the
; lookup and the buffer decision under guard t, each prepare twin under its
; reference's guard (plus the carried view facts on the chain the host
; enters).

(assert-event
 (and (eq (symbol-class 'fn-pidx-targetedp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pidx-find-article (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pidx-existing-action (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pidx-accept-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pidx-node-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pidx-sn-prepare-node (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pidx-spc-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pidx-opc-owner-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pidx-opc-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pidx-sbud-prepare (w state)) :common-lisp-compliant)))
(assert-event (and (equal (guard 'fn-pidx-accept-prepare nil (w state))
                          (guard 'fn-accept-prepare nil (w state)))
                   (equal (guard 'fn-pidx-node-prepare nil (w state))
                          (guard 'fn-node-prepare nil (w state)))
                   ; by specification: the flip -- the decision also reads
                   ; the arena, so its guard is the buffer decision's
                   ; (fn-octets-p) and the Store entry's (fn-arena-p), the
                   ; two stobj recognizers and nothing more.
                   (equal (guard 'fn-pidx-existing-action nil (w state))
                          (list 'if (guard 'fn-rclb-same-articlep nil (w state))
                                (guard 'fn-store-existing-action nil (w state))
                                ''nil))))

(include-book "../../books/defkeystone")
;; A prepare mutation skips staging and returns the reserved input owner.
(defun pitt-prepare-skipped (oc record budget)
 (declare (ignore record budget)) oc)
(defteeth fn-pidx-sbud-prepare-is-pcar-sbud-prepare
 :subject fn-pidx-sbud-prepare
 :claim (() (equal (fn-pidx-sbud-prepare oc record budget)
                   (fn-pcar-sbud-prepare oc record budget)))
 :witness ((oc *pit-oc*) (record *pit-fresh-record*) (budget 100))
 :mutations ((prepare-skipped
              (:conclusion (equal (pitt-prepare-skipped oc record budget)
                                  (fn-pcar-sbud-prepare oc record budget)))
              () :fault "POST prepare returns without staging the admitted record")))
(defteeth-check (fn-pidx-sbud-prepare-is-pcar-sbud-prepare))

(defun pitt-existing-check (msgid groups o fn-octets fn-arena)
 (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
 (mv (equal (fn-pidx-existing-action msgid fn-octets groups o fn-arena)
            (fn-store-existing-action msgid (fn-octets-list fn-octets) groups
                                      (fn-own-store o) fn-arena))
     fn-octets fn-arena))
;; Implementation mutation: an existing Message-ID is called duplicate
;; without comparing its content and group identity.
(defun pitt-existing-no-bytes (msgid fn-octets groups o fn-arena)
 (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil)
          (ignore fn-octets groups fn-arena))
 (if (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o)))))
     :duplicate nil))
(defun pitt-existing-mutant-check (msgid groups o fn-octets fn-arena)
 (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
 (mv (equal (pitt-existing-no-bytes msgid fn-octets groups o fn-arena)
            (fn-store-existing-action msgid (fn-octets-list fn-octets) groups
                                      (fn-own-store o) fn-arena))
     fn-octets fn-arena))
(defteeth fn-pidx-existing-action-is-store-existing-action
 :subject fn-pidx-existing-action
 :claim (((buffer (fn-octets-p fn-octets)))
         (equal (fn-pidx-existing-action msgid fn-octets groups o fn-arena)
                (fn-store-existing-action msgid fn-octets groups (fn-own-store o) fn-arena)))
 :witness ((msgid *pit-held*) (groups *pit-groups*) (o *pit-o*) (payload *pit-changed*))
 :stobjs ((fn-octets (fn-octets-from-list payload fn-octets))
          (fn-arena (fn-hrt-events *pit-prior* nil 0 fn-arena)))
 :stobj-checks
 (((equal (fn-pidx-existing-action msgid fn-octets groups o fn-arena)
          (fn-store-existing-action msgid fn-octets groups (fn-own-store o) fn-arena))
   (pitt-existing-check msgid groups o fn-octets fn-arena)
   :hints (("Goal" :in-theory (e/d (pitt-existing-check)
                                  (fn-pidx-existing-action fn-store-existing-action)))))
  ((equal (pitt-existing-no-bytes msgid fn-octets groups o fn-arena)
          (fn-store-existing-action msgid fn-octets groups (fn-own-store o) fn-arena))
   (pitt-existing-mutant-check msgid groups o fn-octets fn-arena)
   :hints (("Goal" :in-theory (e/d (pitt-existing-mutant-check)
                                  (pitt-existing-no-bytes fn-store-existing-action))))))
 :breaks ((buffer ((payload (append *pit-payload* 'bad-tail)))
                  :logical "corrupted logical buffer: its improper tail is ignored by the bounded byte comparison"))
 :hints (("Goal" :in-theory (e/d (fn-pidx-existing-action fn-rclb-same-articlep
                                   fn-rclb-same-as-tombstonep fn-pbb-same-articlep)
                                  ((:e fn-pidx-existing-action)))))
 :mutations ((bytes-unchecked
   (:conclusion (equal (pitt-existing-no-bytes msgid fn-octets groups o fn-arena)
                       (fn-store-existing-action msgid fn-octets groups (fn-own-store o) fn-arena)))
   () :fault "duplicate Message-ID bypasses content and group comparison")))
(defteeth-check (fn-pidx-existing-action-is-store-existing-action))
