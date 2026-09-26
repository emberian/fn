; Teeth for books/post-identity-index.lisp (PRF-191).
(in-package "ACL2")
(include-book "../../books/post-identity-index")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-prepare-carried-tests")

; -----------------------------------------------------------------------------
; The reachable witness: owner-prepare-carried-tests' *pcar-t-o*, the owner
; the host's POST events reach with the Store :reserved for connection 4's
; submission, one article ("<one@example>") and a second one committed.  Its
; view is the one fn-own-refresh built from this node: the raw list IS the
; node's article list, so the lookup takes the trie.

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
; Both hypotheses hold, and so does the named premise of the prepare chain.
(assert-event (and (fn-ocl-view-visiblep *pit-view*)
                   (fn-midx-correspondencep
                    (fn-own-view-index *pit-view*)
                    (fn-state-articles (fn-own-view-archive *pit-view*)))
                   (fn-scar-view-indexedp *pit-o*)
                   (fn-pidx-view-okp *pit-view*)))

; -----------------------------------------------------------------------------
; fn-pidx-find-article-is-find-article, reachable: a held and a fresh
; Message-ID, both answered by the trie (every test of the fast path holds).

(defun pit-fast-pathp (msgid arts view)
  (and (stringp msgid) (< 0 (length msgid))
       (equal arts (fn-own-view-raw view))
       (not (fn-pidx-targetedp msgid (fn-own-view-withdrawals view)))))

(assert-event (and (pit-fast-pathp *pit-held* *pit-arts* *pit-view*)
                   (equal (fn-pidx-find-article *pit-held* *pit-arts* *pit-view*)
                          *pit-held-article*)
                   (equal (fn-mxc-lookup *pit-held* (fn-own-view-index *pit-view*))
                          *pit-held-article*)))
(assert-event (and (pit-fast-pathp *pit-fresh* *pit-arts* *pit-view*)
                   (null (fn-pidx-find-article *pit-fresh* *pit-arts* *pit-view*))))
; Another article list takes the scan and is answered for that list.
(assert-event (and (not (pit-fast-pathp *pit-held* (cdr *pit-arts*) *pit-view*))
                   (equal (fn-pidx-find-article *pit-held* (cdr *pit-arts*) *pit-view*)
                          (fn-find-article *pit-held* (cdr *pit-arts*)))))

; A withdrawal record naming the held Message-ID (constructed: the record is
; no withdrawal, so the visible list is unchanged and both hypotheses still
; hold) sends the lookup to the scan, which answers the same.
(defun pit-view-with (v archive index withdrawals)
  (fn-own-view-make-visible
   (fn-own-view-version v) (fn-own-view-frontier v) archive
   (fn-own-view-verdicts v) index (fn-own-view-group-index v) withdrawals
   (fn-own-view-raw v) (fn-own-view-withdrawn v) (fn-own-view-keyring v)))

(defconst *pit-targeted-view*
  (pit-view-with *pit-view* (fn-own-view-archive *pit-view*)
                 (fn-own-view-index *pit-view*)
                 (list (list :not-a-withdrawal *pit-held*))))
(assert-event (and (fn-ocl-view-visiblep *pit-targeted-view*)
                   (fn-midx-correspondencep
                    (fn-own-view-index *pit-targeted-view*)
                    (fn-state-articles (fn-own-view-archive *pit-targeted-view*)))
                   (fn-pidx-targetedp *pit-held*
                                      (fn-own-view-withdrawals *pit-targeted-view*))
                   (equal (fn-pidx-find-article *pit-held* *pit-arts*
                                                *pit-targeted-view*)
                          *pit-held-article*)))

; -----------------------------------------------------------------------------
; Hypothesis removal (CORRUPTED views: no owner transition builds them).  Each
; adds an article under the fresh Message-ID to one side of the view only.

(defconst *pit-fake-article*
  (fn-make-article *pit-fresh* (fn-article-payload *pit-held-article*)
                   (fn-article-groups *pit-held-article*)
                   (fn-article-memberships *pit-held-article*)
                   (fn-article-pin *pit-held-article*)
                   (fn-article-stamp *pit-held-article*)))
(defconst *pit-fake-visible*
  (cons *pit-fake-article* (fn-state-articles (fn-own-view-archive *pit-view*))))

; Without fn-ocl-view-visiblep: the visible list (and its trie) holds the
; fake article, the raw list does not.
(defconst *pit-bad-visible-view*
  (pit-view-with *pit-view*
                 (fn-ctl-visible-state-of (fn-own-view-archive *pit-view*)
                                          *pit-fake-visible*)
                 (fn-midx-build *pit-fake-visible*)
                 nil))
(assert-event (and (not (fn-ocl-view-visiblep *pit-bad-visible-view*))
                   (fn-midx-correspondencep
                    (fn-own-view-index *pit-bad-visible-view*)
                    (fn-state-articles (fn-own-view-archive *pit-bad-visible-view*)))
                   (equal (fn-pidx-find-article *pit-fresh* *pit-arts*
                                                *pit-bad-visible-view*)
                          *pit-fake-article*)
                   (not (equal (fn-pidx-find-article *pit-fresh* *pit-arts*
                                                     *pit-bad-visible-view*)
                               (fn-find-article *pit-fresh* *pit-arts*)))))
(must-fail
 (defthm pit-find-without-visible
   (equal (fn-pidx-find-article *pit-fresh* *pit-arts* *pit-bad-visible-view*)
          (fn-find-article *pit-fresh* *pit-arts*))))

; Without the trie's correspondence: the visible list is right, the trie
; holds the fake article.
(defconst *pit-bad-index-view*
  (pit-view-with *pit-view* (fn-own-view-archive *pit-view*)
                 (fn-midx-build *pit-fake-visible*)
                 nil))
(assert-event (and (fn-ocl-view-visiblep *pit-bad-index-view*)
                   (not (fn-midx-correspondencep
                         (fn-own-view-index *pit-bad-index-view*)
                         (fn-state-articles (fn-own-view-archive *pit-bad-index-view*))))
                   (not (equal (fn-pidx-find-article *pit-fresh* *pit-arts*
                                                     *pit-bad-index-view*)
                               (fn-find-article *pit-fresh* *pit-arts*)))))
(must-fail
 (defthm pit-find-without-index
   (equal (fn-pidx-find-article *pit-fresh* *pit-arts* *pit-bad-index-view*)
          (fn-find-article *pit-fresh* *pit-arts*))))

; -----------------------------------------------------------------------------
; fn-pidx-existing-action-is-rclb-existing-action, on a live local buffer as
; the host runs it.

(defun pit-owner-with-view (o v)
  (fn-own-make (fn-own-store o) v (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)))

(defun pit-existing (msgid payload groups o)
  (declare (xargs :guard (fn-cbor-octet-listp payload) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (let ((fn-octets (fn-octets-from-list payload fn-octets)))
        (mv (fn-pidx-existing-action msgid fn-octets groups o) fn-octets))
      r)))

(defun pit-rclb-existing (msgid payload groups s)
  (declare (xargs :guard (fn-cbor-octet-listp payload) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (let ((fn-octets (fn-octets-from-list payload fn-octets)))
        (mv (fn-rclb-existing-action msgid fn-octets groups s) fn-octets))
      r)))

(defconst *pit-payload* (fn-article-payload *pit-held-article*))
(defconst *pit-groups* (fn-article-groups *pit-held-article*))
(defconst *pit-changed* (append *pit-payload* (list 88)))
(defconst *pit-store* (fn-own-store *pit-o*))

; Reachable: the held article's own bytes are :duplicate, changed bytes
; :conflict, a fresh Message-ID nil; each equal to the buffer decision.
(assert-event
 (and (equal (pit-existing *pit-held* *pit-payload* *pit-groups* *pit-o*) :duplicate)
      (equal (pit-rclb-existing *pit-held* *pit-payload* *pit-groups* *pit-store*)
             :duplicate)
      (equal (pit-existing *pit-held* *pit-changed* *pit-groups* *pit-o*) :conflict)
      (equal (pit-rclb-existing *pit-held* *pit-changed* *pit-groups* *pit-store*)
             :conflict)
      (null (pit-existing *pit-fresh* *pit-payload* *pit-groups* *pit-o*))
      (null (pit-rclb-existing *pit-fresh* *pit-payload* *pit-groups* *pit-store*))))

; Hypothesis removal (corrupted views, as above): the fresh Message-ID is
; answered :duplicate from the fake article where the Store holds none.
(defconst *pit-bad-visible-o* (pit-owner-with-view *pit-o* *pit-bad-visible-view*))
(defconst *pit-bad-index-o* (pit-owner-with-view *pit-o* *pit-bad-index-view*))
(assert-event
 (and (equal (fn-own-store *pit-bad-visible-o*) *pit-store*)
      (not (fn-ocl-view-visiblep (fn-own-view *pit-bad-visible-o*)))
      (fn-scar-view-indexedp *pit-bad-visible-o*)
      (equal (pit-existing *pit-fresh* *pit-payload* *pit-groups* *pit-bad-visible-o*)
             :duplicate)
      (equal (fn-own-store *pit-bad-index-o*) *pit-store*)
      (fn-ocl-view-visiblep (fn-own-view *pit-bad-index-o*))
      (not (fn-scar-view-indexedp *pit-bad-index-o*))
      (equal (pit-existing *pit-fresh* *pit-payload* *pit-groups* *pit-bad-index-o*)
             :duplicate)))
(must-fail
 (defthm pit-existing-without-visible
   (equal (pit-existing *pit-fresh* *pit-payload* *pit-groups* *pit-bad-visible-o*)
          (pit-rclb-existing *pit-fresh* *pit-payload* *pit-groups* *pit-store*))))
(must-fail
 (defthm pit-existing-without-index
   (equal (pit-existing *pit-fresh* *pit-payload* *pit-groups* *pit-bad-index-o*)
          (pit-rclb-existing *pit-fresh* *pit-payload* *pit-groups* *pit-store*))))

; -----------------------------------------------------------------------------
; fn-pidx-sbud-prepare-is-pcar-sbud-prepare, reachable: the submission's own
; record stages; a record under the held Message-ID (its own obligation id,
; so retention admits it) is refused by the duplicate test; at the budget
; both are the identity.

(defconst *pit-record* *pcar-t-record*)
(defun pit-record-under (msgid)
  (fn-record-make 2 2 2 msgid (fn-own-sub-octets *osi-sub*) '("fn.letters")
                  "own-pin:pit" "own-content:pit" "own-release:pit" 2 841000000))
(defconst *pit-dup-record* (pit-record-under *pit-held*))
(defconst *pit-fresh-record* (pit-record-under *pit-fresh*))

(defun pit-phase (oc)
  (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))

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

; Hypothesis removal (corrupted views, as above): the fresh record is
; refused as a duplicate of the fake article; the reference stages it.  The
; prepare's guard carries the view facts, so the corrupted runs evaluate
; without guard checking, as the host's raw call would.
(defconst *pit-bad-visible-oc* (fn-ocfg-with-owner *pit-oc* *pit-bad-visible-o*))
(defconst *pit-bad-index-oc* (fn-ocfg-with-owner *pit-oc* *pit-bad-index-o*))
(make-event
 `(defconst *pit-bad-visible-prepared*
    ',(with-guard-checking
       :none
       (fn-pidx-sbud-prepare *pit-bad-visible-oc* *pit-fresh-record* 100))))
(make-event
 `(defconst *pit-bad-index-prepared*
    ',(with-guard-checking
       :none
       (fn-pidx-sbud-prepare *pit-bad-index-oc* *pit-fresh-record* 100))))
(assert-event
 (and (not (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner *pit-bad-visible-oc*))))
      (fn-scar-view-indexedp (fn-ocfg-owner *pit-bad-visible-oc*))
      (equal *pit-bad-visible-prepared* *pit-bad-visible-oc*)
      (equal (pit-phase (fn-pcar-sbud-prepare *pit-bad-visible-oc* *pit-fresh-record* 100))
             :record-staged)
      (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner *pit-bad-index-oc*)))
      (not (fn-scar-view-indexedp (fn-ocfg-owner *pit-bad-index-oc*)))
      (equal *pit-bad-index-prepared* *pit-bad-index-oc*)
      (equal (pit-phase (fn-pcar-sbud-prepare *pit-bad-index-oc* *pit-fresh-record* 100))
             :record-staged)))
(must-fail
 (defthm pit-prepare-without-visible
   (equal (fn-pidx-sbud-prepare *pit-bad-visible-oc* *pit-fresh-record* 100)
          (fn-pcar-sbud-prepare *pit-bad-visible-oc* *pit-fresh-record* 100))))
(must-fail
 (defthm pit-prepare-without-index
   (equal (fn-pidx-sbud-prepare *pit-bad-index-oc* *pit-fresh-record* 100)
          (fn-pcar-sbud-prepare *pit-bad-index-oc* *pit-fresh-record* 100))))

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
                   (equal (guard 'fn-pidx-existing-action nil (w state))
                          (guard 'fn-rclb-existing-action nil (w state)))))
