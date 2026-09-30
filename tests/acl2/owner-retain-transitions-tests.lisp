; PRF-1072: exact live owner transitions, reachable signed composite.
; Corrupted carry witnesses affirm the remaining actual entry guard facts;
; guard checking is disabled only for the deliberate missing-carry case.
(in-package "ACL2")
(include-book "../../books/owner-retain-transitions")
(include-book "identity-retain-carried-tests")

(defun ort-prepare-in-local-arena (carry state)
  (declare (xargs :stobjs state :mode :program))
  (with-local-stobj fn-arena
    (mv-let (ok fn-arena state)
      (let* ((fn-arena (fn-arn-seal-many *sr-arena* fn-arena))
             (state (fn-owner-install-open-ocfg *pse-k2-reserved* state))
             (state (fn-owner-retain-carry-put carry state))
             (retained-guards
              (and (boundp-global 'fn-owner state)
                   (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))))
             (antecedent (fn-prc-carryp (fn-owner-retain-carry state)))
             (state-antecedent (fn-owner-retain-statep state)))
        (mv-let (erp word state)
          (fn-owner-prepare-identity *pse-comp* fn-arena state)
          (mv (list retained-guards antecedent
                    (fn-prc-carryp (fn-owner-retain-carry state))
                    erp word (fn-owner-ocfg state)
                    state-antecedent (fn-owner-retain-statep state))
              fn-arena state)))
      (mv ok state))))

(defun ort-finish-in-local-history (carry state)
  (declare (xargs :stobjs state :mode :program))
  (with-local-stobj fn-hist
    (mv-let (ok fn-hist state)
      (let* ((fn-hist (fn-hist-load
                       (true-list-fix (fn-sf-records
                         (fn-sn-files (lgt-store *ois-ordered*)))) 0 fn-hist))
             (state (fn-owner-install-open-ocfg *ois-ordered* state))
             (state (fn-owner-retain-carry-put carry state))
             (retained-guards
              (and (boundp-global 'fn-owner state)
                   (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))))
             (antecedent (fn-prc-carryp (fn-owner-retain-carry state)))
             (state-antecedent (fn-owner-retain-statep state)))
        (mv-let (erp word state) (fn-owner-finish-synced fn-hist state)
          (mv (list retained-guards antecedent
                    (fn-prc-carryp (fn-owner-retain-carry state))
                    erp word (fn-owner-ocfg state)
                    state-antecedent (fn-owner-retain-statep state))
              fn-hist state)))
      (mv ok state))))

(defun ort-bad-prepare (state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (result state) (ort-prepare-in-local-arena *irct-bad* state)
    (value result)))
(defun ort-bad-finish (state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (result state) (ort-finish-in-local-history *irct-bad* state)
    (value result)))

(defun ort-live-transitions-witness (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((old-owner (if (boundp-global 'fn-owner state)
                        (f-get-global 'fn-owner state) nil))
         (old-carry (fn-owner-retain-carry state))
         (old-view (fn-owner-obligation-view state))
         (old-candidate (if (boundp-global 'fn-owner-cat-candidate state)
                            (f-get-global 'fn-owner-cat-candidate state) nil)))
    (mv-let (prep state) (ort-prepare-in-local-arena *irct-carry* state)
      (mv-let (finish state) (ort-finish-in-local-history *irct-fcarry* state)
        (mv-let (bad-prep-erp bad-prep state)
          (with-guard-checking-error-triple :none (ort-bad-prepare state))
          (mv-let (bad-finish-erp bad-finish state)
            (with-guard-checking-error-triple :none (ort-bad-finish state))
            (let* ((state (f-put-global 'fn-owner old-owner state))
                   (state (fn-owner-retain-carry-put old-carry state))
                   (state (fn-owner-obligation-view-put old-view state))
                   (state (f-put-global 'fn-owner-cat-candidate old-candidate state)))
              (mv (and (consp *irct-carry*)
                       (null bad-prep-erp) (null bad-finish-erp)
                       ; Entire actual antecedent and carry conclusion.
                       (nth 0 prep) (nth 1 prep) (nth 2 prep)
                       (null (nth 3 prep))
                       (equal (nth 4 prep)
                              (list :seal (fn-oii-identity-payload *pse-comp*)))
                       (equal (nth 5 prep) *ois-staged*)
                       (nth 6 prep) (nth 7 prep)
                       (nth 0 finish) (nth 1 finish) (nth 2 finish)
                       (null (nth 3 finish)) (equal (nth 4 finish) :durable)
                       (equal (lgt-phase (nth 5 finish)) :ready)
                       ; Corrupted-state hypothesis removal: other entry
                       ; guards true, omitted hypothesis false, conclusion false.
                       (nth 0 bad-prep) (not (nth 1 bad-prep))
                       (not (nth 2 bad-prep))
                       (not (nth 6 bad-prep)) (not (nth 7 bad-prep))
                       (nth 0 bad-finish) (not (nth 1 bad-finish))
                       (not (nth 2 bad-finish)))
                  state))))))))

(make-event
 (mv-let (ok state) (ort-live-transitions-witness state)
   (value (list 'assert-event ok))))
