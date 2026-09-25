; Operator-local lifecycle for principals in ordered hybrid snapshots.
; Durable kind-3 snapshots keep their historical meaning. A tombstone is a
; new profile, never a replacement or reinterpretation of enrolled v1 bytes.

(in-package "ACL2")
(include-book "hybrid-store")

(defconst *fn-hl-revoked-profile* *fn-hsig-revoked-profile*)
; "fn-hybrid-revoked-v1"; payload is exactly the 32-octet principal
; (books/hybrid-store.lisp owns the value; replay reads it there).

(defun fn-hl-current-snapshot (snapshots)
  (declare (xargs :guard t))
  (if (and (consp snapshots) (fn-stxk-p (car snapshots)))
      (car snapshots)
    nil))

(defun fn-hl-snapshot-principal (snapshot)
  (declare (xargs :guard t))
  (let ((enrollment (fn-hsig-keyring-snapshot-value snapshot)))
    (cond (enrollment (car enrollment))
          ((and (fn-stxk-p snapshot)
                (equal (fn-stxk-profile snapshot) *fn-hl-revoked-profile*)
                (fn-hsig-exact-octets-p (fn-stxk-snapshot snapshot) 32))
           (fn-stxk-snapshot snapshot))
          (t nil))))

(defun fn-hl-current-for-principal (principal snapshots)
  (declare (xargs :guard t))
  (if (consp snapshots)
      (if (equal principal (fn-hl-snapshot-principal (car snapshots)))
          (car snapshots)
        (fn-hl-current-for-principal principal (cdr snapshots)))
    nil))

(defun fn-hl-next-generationp (requested current)
  (declare (xargs :guard t))
  (and (fn-record-uint32p requested)
       (if (fn-stxk-p current)
           (equal requested (1+ (fn-stxk-keyring-generation current)))
         (equal requested 1))))

;; PRF-098: the next keyring generation is ACL2's, never the operator's
;; spelling.  The control codec's next-generation requests
;; (books/native-hybrid-control.lisp, kinds 7 and 8) and the key-statement
;; executor (books/key-statements.lisp) ask for it; generation 0 means
;; nothing.
(defun fn-hl-next-generation (snapshots)
  (declare (xargs :guard t))
  (let ((current (fn-hl-current-snapshot snapshots)))
    (if (fn-stxk-p current)
        (1+ (nfix (fn-stxk-keyring-generation current)))
      1)))

(defun fn-hl-enroll-event
    (sequence txid store-generation keyring-generation principal keys snapshots)
  (declare (xargs :guard t))
  (if (fn-hl-next-generationp keyring-generation
                           (fn-hl-current-snapshot snapshots))
      (fn-hsig-keyring-event sequence txid store-generation
                             keyring-generation principal keys)
    nil))

(defun fn-hl-revoke-event
    (sequence txid store-generation keyring-generation principal snapshots)
  (declare (xargs :guard t))
  (let ((current (fn-hl-current-for-principal principal snapshots)))
    (if (and (fn-hl-next-generationp keyring-generation
                                     (fn-hl-current-snapshot snapshots))
             (fn-hsig-exact-octets-p principal 32)
             (fn-hsig-keyring-snapshot-value current))
        (let ((event
               (fn-stxk-make sequence txid store-generation
                              keyring-generation *fn-hl-revoked-profile*
                              principal)))
          (if (fn-stxk-p event) event nil))
      nil)))

(defun fn-hl-current-enrollment (requested snapshots)
  "Only this principal's newest enrolled generation can authorize locally."
  (declare (xargs :guard t))
  (let* ((selected (fn-stxk-find requested snapshots))
         (value (fn-hsig-keyring-snapshot-value selected))
         (current (and value (fn-hl-current-for-principal
                              (car value) snapshots))))
    (if (and selected value current
             (equal requested (fn-stxk-keyring-generation current)))
        (list selected (car value) (cadr value))
      nil)))

(defun fn-hl-history-row (snapshot history)
  (declare (xargs :guard t))
  (let ((principal (fn-hl-snapshot-principal snapshot)))
    (if (not (fn-stxk-p snapshot)) nil
      (list (fn-stxk-keyring-generation snapshot)
            (cond ((not principal) :opaque)
                  ((equal (fn-stxk-profile snapshot)
                          *fn-hl-revoked-profile*) :revoked)
                  ((equal snapshot
                          (fn-hl-current-for-principal principal history))
                   :active)
                  (t :retired))
            principal))))

(defun fn-hl-history-rows (remaining history)
  (declare (xargs :guard t))
  (if (consp remaining)
      (cons (fn-hl-history-row (car remaining) history)
            (fn-hl-history-rows (cdr remaining) history))
    nil))

(defthm fn-hl-current-for-principal-of-other-principal
  (implies (not (equal principal
                       (fn-hl-snapshot-principal next)))
           (equal (fn-hl-current-for-principal principal
                                               (cons next history))
                  (fn-hl-current-for-principal principal history)))
  :hints (("Goal" :in-theory (enable fn-hl-current-for-principal))))

(defthm fn-hl-current-for-principal-of-its-new-snapshot
  (implies (equal principal (fn-hl-snapshot-principal next))
           (equal (fn-hl-current-for-principal principal
                                               (cons next history))
                  next))
  :hints (("Goal" :in-theory (enable fn-hl-current-for-principal))))

(defthm fn-hl-next-generation-is-the-next-generation
  (implies (fn-record-uint32p (fn-hl-next-generation snapshots))
           (fn-hl-next-generationp (fn-hl-next-generation snapshots)
                                   (fn-hl-current-snapshot snapshots)))
  :hints (("Goal" :in-theory (enable fn-stxk-p fn-stxk-shapep
                                     fn-stxk-keyring-generation
                                     fn-record-uint32p))))

; The enrollment the selector returns is a key snapshot with a value, never
; a tombstone.
(defthm fn-hl-current-enrollment-selects-an-enrolled-snapshot
  (implies (fn-hl-current-enrollment requested snapshots)
           (and (fn-hsig-keyring-snapshot-value
                 (car (fn-hl-current-enrollment requested snapshots)))
                (equal (cadr (fn-hl-current-enrollment requested snapshots))
                       (car (fn-hsig-keyring-snapshot-value
                             (car (fn-hl-current-enrollment requested
                                                            snapshots)))))
                (equal (caddr (fn-hl-current-enrollment requested snapshots))
                       (cadr (fn-hsig-keyring-snapshot-value
                              (car (fn-hl-current-enrollment requested
                                                             snapshots)))))))
  :hints (("Goal" :in-theory (e/d (fn-hl-current-enrollment)
                                  (fn-hsig-keyring-snapshot-value
                                   fn-hl-current-for-principal)))))

; A revocation event is a tombstone of exactly its principal at exactly its
; requested generation.
(defthm fn-hl-revoke-event-is-the-principals-tombstone
  (let ((e (fn-hl-revoke-event sequence txid store-generation
                               keyring-generation principal snapshots)))
    (implies e
             (and (fn-stxk-p e)
                  (equal (fn-stxk-profile e) *fn-hl-revoked-profile*)
                  (equal (fn-stxk-snapshot e) principal)
                  (equal (fn-stxk-keyring-generation e) keyring-generation)
                  (not (fn-hsig-keyring-snapshot-value e))
                  (equal (fn-hl-snapshot-principal e) principal))))
  :hints (("Goal" :in-theory (e/d (fn-hl-revoke-event fn-hl-snapshot-principal)
                                  (fn-stxk-p fn-hsig-keyring-snapshot-value
                                   fn-hl-current-for-principal))
           :use ((:instance fn-hsig-keyring-snapshot-value-requires-the-key-profile
                            (snapshot (fn-stxk-make sequence txid store-generation
                                                    keyring-generation
                                                    *fn-hl-revoked-profile*
                                                    principal)))))))

(defthm fn-hl-revoke-event-generation-is-positive
  (implies (fn-hl-revoke-event sequence txid store-generation
                               keyring-generation principal snapshots)
           (posp keyring-generation))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-hl-revoke-event fn-hl-next-generationp
                                     fn-record-uint32p))))

; An enrollment event is a key snapshot of exactly its principal and keys.
(defthm fn-hl-enroll-event-enrolls-its-keys
  (let ((e (fn-hl-enroll-event sequence txid store-generation
                               keyring-generation principal keys snapshots)))
    (implies e
             (and (fn-stxk-p e)
                  (equal (fn-stxk-keyring-generation e) keyring-generation)
                  (equal (fn-hsig-keyring-snapshot-value e)
                         (list principal keys))
                  (equal (fn-hl-snapshot-principal e) principal))))
  :hints (("Goal" :in-theory (e/d (fn-hl-enroll-event fn-hl-snapshot-principal)
                                  (fn-stxk-p fn-hsig-keyring-snapshot-value
                                   fn-hsig-keyring-event
                                   fn-hsig-keyring-event-shape
                                   fn-hsig-keyring-snapshot-value-of-keyring-event))
           :use ((:instance fn-hsig-keyring-snapshot-value-of-keyring-event
                            (generation store-generation))
                 (:instance fn-hsig-keyring-event-shape
                            (generation store-generation))))))
