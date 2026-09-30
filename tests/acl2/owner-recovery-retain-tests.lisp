; PRF-1072: actual successful cold install and actual reclaim carry effect.
(in-package "ACL2")
(include-book "../../books/owner-recovery-retain")
(include-book "owner-reclaim-carry-tests")
(include-book "identity-retain-carried-tests")

(defconst *orr-oc* (nth 1 *orc-carry-rebuilt*))
(defconst *orr-bad-carry* (cons (car (nth 2 *orc-carry-rebuilt*)) nil))
(defconst *orr-key* (fn-mpxt-key-of-entry nil))
; Damaged-state hypothesis-removal witness, not an admitted history:
; change only acceptance's next-number map to exceed RFC 3977's bound.
(defconst *orr-over-oc*
  (let* ((owner (fn-ocfg-owner *orr-oc*))
         (store (fn-own-store owner))
         (node (fn-sn-node store))
         (a (fn-node-acceptance node))
         (nexts (list (cons "damaged" (+ 1 *fn-nntp-max-article-number*))))
         (bad-node (fn-node-make-state
                    (fn-make-state (strip-cars nexts) nexts (fn-state-articles a)
                                   (fn-state-next-txid a) (fn-state-pending a)
                                   (fn-state-fenced a))
                    (fn-node-retention node) (fn-node-stage node)
                    (fn-node-bindings node)))
         (bad-owner (update-nth 0 (fn-sn-update store (fn-sn-files store) bad-node) owner)))
    (fn-ocfg-make bad-owner (fn-ocfg-config *orr-oc*)
                  (fn-ocfg-pins *orr-oc*) (fn-ocfg-staged *orr-oc*))))

(defun orr-open (oc state)
  (declare (xargs :stobjs state :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena state)
      (with-local-stobj fn-cat
        (mv-let (result fn-cat fn-arena state)
          (with-local-stobj fn-hist
            (mv-let (result fn-hist fn-cat fn-arena state)
              (let* ((nonfault (not (equal oc :fault)))
                     (number-ok (fn-onb-open-okp (fn-ocfg-owner oc)))
                     (state (fn-owner-retain-carry-put *orr-bad-carry* state)))
                (mv-let (erp word fn-arena fn-cat fn-hist state)
                  (fn-owner-install-extended oc (nth 0 *orc-carry-rebuilt*) *orr-key*
                                             fn-arena fn-cat fn-hist state)
                  (mv (list nonfault number-ok
                            (fn-prc-carryp (fn-owner-retain-carry state)) erp word
                            (boundp-global 'fn-owner state)
                            (fn-lgoc-invariantp oc)
                            (fn-owner-retain-statep state)
                            (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                            (and (fn-mpxt-keyp *orr-key*)
                                 (equal (len *orr-key*) *fn-mpxt-key-octets*)))
                      fn-hist fn-cat fn-arena state)))
              (mv result fn-cat fn-arena state)))
          (mv result fn-arena state)))
      (mv result state))))

(defun orr-swap (rebuilt state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (fn-owner-install-open-ocfg *orr-oc* state))
         (guards (and (true-listp rebuilt) (boundp-global 'fn-owner state)))
         (valid (fn-prc-carryp (nth 2 rebuilt))))
    (mv-let (erp count state) (fn-owner-orcp-swap rebuilt state)
      (mv (list guards valid
                (equal (fn-owner-retain-carry state) (nth 2 rebuilt))
                (fn-prc-carryp (fn-owner-retain-carry state)) erp count)
          state))))

; Save every global the two actual functions write. The witness operates on
; local concrete stobjs and restores its state-global values afterwards.
(defconst *orr-keys*
  '(fn-owner fn-owner-obligation-view fn-owner-retain-carry
    fn-owner-feed-intents fn-owner-store-profile fn-owner-profile-carry
    fn-owner-feed-inputs fn-owner-sco-base fn-owner-sco-base-payloads
    fn-owner-sco-durable fn-owner-sco-attempted fn-owner-sco-deferred
    fn-owner-sco-inflight fn-owner-sco-pending fn-owner-sco-requested
    fn-owner-orc-pass fn-owner-cat-pending fn-owner-record-octets
    fn-owner-record-debt fn-owner-carried-usage fn-owner-credits))
(defun orr-save (keys state)
  (declare (xargs :stobjs state :mode :program))
  (if (endp keys) nil
    (cons (cons (car keys) (and (boundp-global (car keys) state)
                               (f-get-global (car keys) state)))
          (orr-save (cdr keys) state))))
(defun orr-restore (saved state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner (cdr (assoc-eq 'fn-owner saved)) state))
         (state (f-put-global 'fn-owner-obligation-view (cdr (assoc-eq 'fn-owner-obligation-view saved)) state))
         (state (f-put-global 'fn-owner-retain-carry (cdr (assoc-eq 'fn-owner-retain-carry saved)) state))
         (state (f-put-global 'fn-owner-feed-intents (cdr (assoc-eq 'fn-owner-feed-intents saved)) state))
         (state (f-put-global 'fn-owner-store-profile (cdr (assoc-eq 'fn-owner-store-profile saved)) state))
         (state (f-put-global 'fn-owner-profile-carry (cdr (assoc-eq 'fn-owner-profile-carry saved)) state))
         (state (f-put-global 'fn-owner-feed-inputs (cdr (assoc-eq 'fn-owner-feed-inputs saved)) state))
         (state (f-put-global 'fn-owner-sco-base (cdr (assoc-eq 'fn-owner-sco-base saved)) state))
         (state (f-put-global 'fn-owner-sco-base-payloads (cdr (assoc-eq 'fn-owner-sco-base-payloads saved)) state))
         (state (f-put-global 'fn-owner-sco-durable (cdr (assoc-eq 'fn-owner-sco-durable saved)) state))
         (state (f-put-global 'fn-owner-sco-attempted (cdr (assoc-eq 'fn-owner-sco-attempted saved)) state))
         (state (f-put-global 'fn-owner-sco-deferred (cdr (assoc-eq 'fn-owner-sco-deferred saved)) state))
         (state (f-put-global 'fn-owner-sco-inflight (cdr (assoc-eq 'fn-owner-sco-inflight saved)) state))
         (state (f-put-global 'fn-owner-sco-pending (cdr (assoc-eq 'fn-owner-sco-pending saved)) state))
         (state (f-put-global 'fn-owner-sco-requested (cdr (assoc-eq 'fn-owner-sco-requested saved)) state))
         (state (f-put-global 'fn-owner-orc-pass (cdr (assoc-eq 'fn-owner-orc-pass saved)) state))
         (state (f-put-global 'fn-owner-cat-pending (cdr (assoc-eq 'fn-owner-cat-pending saved)) state))
         (state (f-put-global 'fn-owner-record-octets (cdr (assoc-eq 'fn-owner-record-octets saved)) state))
         (state (f-put-global 'fn-owner-record-debt (cdr (assoc-eq 'fn-owner-record-debt saved)) state))
         (state (f-put-global 'fn-owner-carried-usage (cdr (assoc-eq 'fn-owner-carried-usage saved)) state))
         (state (f-put-global 'fn-owner-credits (cdr (assoc-eq 'fn-owner-credits saved)) state)))
    state))
(defun orr-live-witness (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((saved (orr-save *orr-keys* state)))
    (mv-let (opened state) (orr-open *orr-oc* state)
      (mv-let (faulted state) (orr-open :fault state)
        (mv-let (damaged state) (orr-open *orr-over-oc* state)
          (mv-let (swapped state) (orr-swap *orc-carry-rebuilt* state)
            (mv-let (bad-swap state)
              (orr-swap (update-nth 2 *orr-bad-carry* *orc-carry-rebuilt*) state)
              (let ((state (orr-restore saved state)))
                (mv (and (not (fn-prc-carryp *orr-bad-carry*))
                         ; Complete successful-install antecedent/conclusion.
                         (nth 0 opened) (nth 1 opened) (nth 2 opened)
                         (null (nth 3 opened)) (equal (nth 4 opened) :recovering)
                         (nth 5 opened)
                         ; Omit nonfault, affirm bound and refute conclusion.
                         (not (nth 0 faulted)) (nth 1 faulted)
                         (not (nth 2 faulted)) (equal (nth 4 faulted) :fault)
                         ; Omit number bound, affirm nonfault, refute conclusion.
                         (nth 0 damaged) (not (nth 1 damaged))
                         (not (nth 2 damaged))
                         (equal (nth 4 damaged) :article-numbers-damaged)
                         ; Actual proved-builder output installed exactly.
                         (nth 0 swapped) (nth 1 swapped) (nth 2 swapped)
                         (nth 3 swapped) (null (nth 4 swapped))
                         ; Corrupt rebuilt carry: both entry guard premises
                         ; and the exact installation equation still hold,
                         ; while omitted carry validity and conclusion fail.
                         (nth 0 bad-swap) (not (nth 1 bad-swap))
                         (nth 2 bad-swap) (not (nth 3 bad-swap)))
                    state)))))))))
(make-event
 (mv-let (ok state) (orr-live-witness state)
   (value (list 'assert-event ok))))

; Full initialization invariant. The staged owner is reachable and has the
; invariant, but the cold-entry open check correctly refuses its in-flight
; transaction. The damaged configuration retains a typed Store and valid
; key but omits the configured-owner relation.
(defun orr-full-state-witness (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((saved (orr-save *orr-keys* state)))
    (mv-let (opened state) (orr-open *orr-oc* state)
      (mv-let (staged state) (orr-open *ois-staged* state)
        (mv-let (bad-config state) (orr-open (update-nth 1 nil *orr-oc*) state)
          (let ((state (orr-restore saved state)))
            (mv (and
                 ; Full antecedent, guard and conclusion; nonempty carry.
                 (consp (nth 2 *orc-carry-rebuilt*))
                 (nth 1 opened) (nth 6 opened) (nth 7 opened)
                 (nth 8 opened) (nth 9 opened)
                 ; Omit open-ok: retained invariant holds, conclusion fails.
                 (not (nth 1 staged)) (nth 6 staged) (not (nth 7 staged))
                 (equal (nth 4 staged) :article-numbers-damaged)
                 ; Corrupted configuration: omit relation, retain open-ok
                 ; and the complete successful-arm entry guard.
                 (nth 1 bad-config) (not (nth 6 bad-config))
                 (not (nth 7 bad-config))
                 (nth 8 bad-config) (nth 9 bad-config)
                 (equal (nth 4 bad-config) :recovering))
                state)))))))
(make-event
 (mv-let (ok state) (orr-full-state-witness state)
   (value (list 'assert-event ok))))
