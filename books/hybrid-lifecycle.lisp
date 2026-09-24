; Operator-local lifecycle for principals in ordered hybrid snapshots.
; Durable kind-3 snapshots keep their historical meaning. A tombstone is a
; new profile, never a replacement or reinterpretation of enrolled v1 bytes.

(in-package "ACL2")
(include-book "hybrid-store")

(defconst *fn-hl-revoked-profile*
  '(102 110 45 104 121 98 114 105 100 45 114 101 118 111 107 101 100 45 118 49))
; "fn-hybrid-revoked-v1"; payload is exactly the 32-octet principal.

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
