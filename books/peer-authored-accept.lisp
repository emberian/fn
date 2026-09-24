; Receiver-local selection for a portable signed carrier at a protected peer
; ingress.  A portable signature by itself is not a B-local enrollment or a
; historical Store verdict.  The latter exists only after kind-4 publication.
(in-package "ACL2")
(include-book "hybrid-lifecycle")
(include-book "hybrid-carrier")

; The classifier prevents a malformed or unauthorized FN-Authorship field
; from falling through to the legacy article-only Store path.  An article
; that cannot be parsed is invalid here too, never carrier-absent.
(defun fn-pa-carrier-kind (received)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse received)))
    (if (not (fn-article-result-okp parsed))
        :invalid
      (let ((article (fn-article-result-article parsed)))
        (if (not (true-listp article)) :invalid
          (if (equal (fn-hc-count-name
                      *fn-hc-name* (fn-article-fields article)) 0)
              :absent
            :present))))))

; Syntax and exact-source projection before any current local key policy.
; This allows byte-identical already-stored bytes to report the Store's
; historical duplicate outcome after a later key rotation or tombstone.
; If the old record was legacy fn-r, this does not upgrade it or create a
; historical verdict.  A present but malformed field has no such path.
(defun fn-pa-carrier-form (received)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-pa-carrier-kind
                                          fn-hc-received-plan)))))
  (let ((kind (fn-pa-carrier-kind received)))
    (if (eq kind :absent) :absent
      (if (eq kind :invalid) (list :refused :article)
        (let ((parsed (fn-hc-received-plan received)))
          (if (not (fn-hc-okp parsed))
              (list :refused :carrier)
            (let ((value (fn-hc-value parsed)))
              (if (not (and (true-listp value) (equal (len value) 2)))
                  (list :refused :carrier-shape)
                (let ((carrier (cadr value)))
                  (if (not (and (true-listp carrier)
                                (equal (len carrier) 3)))
                      (list :refused :carrier-shape)
                    (list :ok (car value) (car carrier) (cadr carrier)
                          (caddr carrier))))))))))))

; (:ok source principal keys signatures exact-current-snapshot generation).
; The current B-local per-principal selection (including a revocation
; tombstone) is made by ACL2 against the carried Store snapshot history.
(defun fn-pa-current-plan (received snapshots)
  (declare (xargs :guard t))
  (let ((form (fn-pa-carrier-form received)))
    (if (not (and (consp form) (eq (car form) :ok))) form
            (let* ((source (nth 1 form))
                   (principal (nth 2 form))
                   (keys (nth 3 form))
                   (signatures (nth 4 form))
                   (current (fn-hl-current-for-principal
                             principal snapshots))
                   (generation (if (fn-stxk-p current)
                                   (fn-stxk-keyring-generation current) nil))
                   (enrolled (fn-hl-current-enrollment
                              generation snapshots)))
              (if (and (true-listp enrolled)
                       (equal (len enrolled) 3)
                       (equal (car enrolled) current)
                       (equal (cadr enrolled) principal)
                       (equal (caddr enrolled) keys))
                  (list :ok source principal keys signatures
                        current generation)
                (list :refused :local-enrollment))))))

; The caller supplies primitive observations, not an authorization Boolean.
; This constructor reselects the exact carrier and current enrollment itself,
; and retains B's relayed payload and peer-derived evidence in the article
; record.  Store publication is the separate durable acceptance decision.
(defun fn-pa-authorized-event
    (sequence txid generation msgid received groups obligation-id
              content-subject release-evidence charge snapshots
              observed-ml-key ed-observation ml-observation clock-observation)
  (declare (xargs :guard t))
  (let ((plan (fn-pa-current-plan received snapshots)))
    (if (not (and (consp plan) (eq (car plan) :ok))) nil
      (fn-hsig-authorized-carried-submission-event-base
       sequence txid generation (nth 6 plan)
       (fn-stxk-snapshot (nth 5 plan))
       msgid (nth 1 plan) received groups obligation-id content-subject
       release-evidence charge (nth 2 plan) (nth 3 plan) (nth 4 plan)
       observed-ml-key ed-observation ml-observation clock-observation
       (fn-hc-okp (fn-hc-received-plan received))))))

(defthm fn-pa-absent-is-only-parser-confirmed-absence
  (implies (equal (fn-pa-current-plan received snapshots) :absent)
           (equal (fn-pa-carrier-kind received) :absent))
  :hints (("Goal" :in-theory (enable fn-pa-current-plan
                                     fn-pa-carrier-form))))

(defthm fn-pa-authorized-event-requires-current-plan-by-definition
  (implies (fn-pa-authorized-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots
            observed-ml-key ed-observation ml-observation clock-observation)
           (equal (car (fn-pa-current-plan received snapshots)) :ok))
  :hints (("Goal" :in-theory
           (e/d (fn-pa-authorized-event)
                (fn-pa-current-plan fn-hc-received-plan
                 fn-hsig-authorized-carried-submission-event-base)))))

(in-theory (disable (:d fn-pa-current-plan) (:d fn-pa-authorized-event)))
