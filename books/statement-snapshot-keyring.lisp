; Snapshot-to-statement key boundary. The existing FN-Statement native suite
; is A-SIG-NATIVE ML-DSA-65, distinct from FN-Authorship's hybrid suite.
; This projection reuses the operator-enrolled stable principal; it never
; derives or substitutes a second principal from either public key.
(in-package "ACL2")
(include-book "hybrid-lifecycle")
(include-book "principal")

(defun fn-ssk-remove-principal-loop (principal keyring acc)
  (declare (xargs :guard t))
  (if (consp keyring)
      (fn-ssk-remove-principal-loop principal (cdr keyring)
        (if (equal principal (fn-cbor-ag-car (car keyring))) acc
          (cons (car keyring) acc)))
    (revappend (true-list-fix acc) nil)))
(defun fn-ssk-remove-principal (principal keyring)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp keyring)
           (if (equal principal (fn-cbor-ag-car (car keyring)))
               (fn-ssk-remove-principal principal (cdr keyring))
             (cons (car keyring) (fn-ssk-remove-principal principal (cdr keyring))))
         nil)
       :exec (fn-ssk-remove-principal-loop principal keyring nil)))
(local (defthm fn-ssk-remove-loop-is-revappend
 (equal (fn-ssk-remove-principal-loop p k acc)
        (revappend (true-list-fix acc) (fn-ssk-remove-principal p k)))
 :hints (("Goal" :induct (fn-ssk-remove-principal-loop p k acc)
                 :in-theory (enable fn-ssk-remove-principal)))))
(verify-guards fn-ssk-remove-principal)
(defthm fn-ssk-remove-preserves-keyringp
 (implies (fn-prin-keyringp keyring)
          (fn-prin-keyringp (fn-ssk-remove-principal principal keyring)))
 :hints (("Goal" :in-theory (enable fn-ssk-remove-principal fn-prin-keyringp))))

(defun fn-ssk-snapshot-binding (snapshot)
  (declare (xargs :guard t))
  (let* ((value (fn-hsig-keyring-snapshot-value snapshot))
         (principal (fn-cbor-ag-car value))
         (keys (fn-cbor-ag-car (fn-cbor-ag-cdr value)))
         (ml-key (fn-cbor-ag-cdr (fn-cbor-ag-car (fn-cbor-ag-cdr keys)))))
    ; Defensive totality at the representation boundary; neither malformed
    ; snapshots nor another signature-suite key can enter the legacy table.
    (if (and value (fn-prin-idp principal) (fn-sig-public-key-p ml-key))
        (cons principal ml-key)
      nil)))
(defthm fn-ssk-snapshot-binding-is-keyring-entry
 (implies (fn-ssk-snapshot-binding snapshot)
          (fn-prin-keyringp (list (fn-ssk-snapshot-binding snapshot))))
 :hints (("Goal" :in-theory (enable fn-ssk-snapshot-binding fn-prin-keyringp))))

(defun fn-ssk-apply-snapshot (snapshot keyring)
  (declare (xargs :guard t))
  (let ((binding (fn-ssk-snapshot-binding snapshot))
        (principal (fn-hl-snapshot-principal snapshot)))
    (cond (binding (cons binding (fn-ssk-remove-principal (car binding) keyring)))
          ((and (fn-stxk-p snapshot)
                (equal (fn-stxk-profile snapshot) *fn-hl-revoked-profile*)
                (fn-prin-idp principal))
           (fn-ssk-remove-principal principal keyring))
          (t keyring))))
(defthm fn-ssk-apply-snapshot-preserves-keyringp
 (implies (fn-prin-keyringp keyring)
          (fn-prin-keyringp (fn-ssk-apply-snapshot snapshot keyring)))
 :hints (("Goal" :in-theory (enable fn-ssk-apply-snapshot fn-ssk-snapshot-binding fn-prin-keyringp))))

; Reconstruction oracle, snapshots NEWEST first. Runtime publication applies
; one snapshot to its carried table; this reference walk is not a served entry.
(defun fn-ssk-keyring-oldest-loop (snapshots keyring)
  (declare (xargs :guard t))
  (if (consp snapshots)
      (fn-ssk-keyring-oldest-loop (cdr snapshots)
                                  (fn-ssk-apply-snapshot (car snapshots) keyring))
    keyring))
(defun fn-ssk-keyring-of-snapshots (snapshots)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp snapshots)
           (fn-ssk-apply-snapshot (car snapshots)
                                 (fn-ssk-keyring-of-snapshots (cdr snapshots)))
         nil)
       :exec (fn-ssk-keyring-oldest-loop (revappend (true-list-fix snapshots) nil) nil)))
(local (defthm fn-ssk-oldest-loop-of-append
 (equal (fn-ssk-keyring-oldest-loop (append a b) keyring)
        (fn-ssk-keyring-oldest-loop b (fn-ssk-keyring-oldest-loop a keyring)))
 :hints (("Goal" :induct (fn-ssk-keyring-oldest-loop a keyring)
                 :in-theory (disable fn-ssk-apply-snapshot)))))
(local (defthm fn-ssk-reverse-loop-is-snapshot-keyring
 (equal (fn-ssk-keyring-oldest-loop (revappend (true-list-fix snapshots) nil) nil)
        (fn-ssk-keyring-of-snapshots snapshots))
 :hints (("Goal" :induct (fn-ssk-keyring-of-snapshots snapshots)
                 :in-theory (enable fn-ssk-keyring-of-snapshots revappend)))))
(verify-guards fn-ssk-keyring-of-snapshots
 :hints (("Goal" :use fn-ssk-reverse-loop-is-snapshot-keyring
                 :expand ((fn-ssk-keyring-of-snapshots snapshots))
                 :in-theory (disable fn-ssk-reverse-loop-is-snapshot-keyring
                                    fn-ssk-oldest-loop-of-append
                                    fn-ssk-keyring-oldest-loop fn-ssk-keyring-of-snapshots
                                    fn-ssk-apply-snapshot fn-ssk-snapshot-binding))))
(defthm fn-ssk-keyring-of-snapshots-is-keyring
 (fn-prin-keyringp (fn-ssk-keyring-of-snapshots snapshots))
 :hints (("Goal" :in-theory (disable fn-ssk-apply-snapshot fn-prin-keyringp))))
(defthm fn-ssk-newest-snapshot-publishes-incremental-keyring-by-definition
 (equal (fn-ssk-keyring-of-snapshots (cons snapshot snapshots))
        (fn-ssk-apply-snapshot snapshot (fn-ssk-keyring-of-snapshots snapshots))))
(defun fn-ssk-generation (snapshots)
  (declare (xargs :guard t))
  (if (and (consp snapshots) (fn-stxk-p (car snapshots)))
      (nfix (fn-stxk-keyring-generation (car snapshots)))
    0))
(in-theory (disable fn-ssk-keyring-oldest-loop fn-ssk-remove-principal-loop fn-ssk-remove-principal
                    fn-ssk-snapshot-binding fn-ssk-apply-snapshot
                    fn-ssk-keyring-of-snapshots fn-ssk-generation))
