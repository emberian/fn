; A-SELECTED-RUNTIME-BP-CREATORS, PRF-1184. Fixed object requests only.
(in-package "ACL2")
(defconst *fn-srbc-coordinate*
 '(:sbcl-2.6.8 :x86-64-linux :tls65536 :dynamic4096 :stack64
 :sbcl "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5"
 :sbcl-core "1024f0a505044cae4de084e77a654aade844dfa546b51cc90dc9e2a09c903aba"
 :saved_acl2-core "3f5b101bb9437d66366dc2a299b7f9cb98fdaf40d1add5caf8baef9e451dd07d"
 :acl2-literal-4g-tls64k "30583c3d9988ea23cf5edfac828b4ddea984a9a7db9c3b44aaa9c399cf4fdbc5"
 :policy ((inhibit-warnings 3) (speed 3) (space 1) (safety 0) (debug 1) (compilation-speed 0))
 :declarations-lisp "2e60f3389fcdcce52d91e90e3b69ef5bb5ee7ac6251336c4d39af82788408501"
 :native-record12-subject-lisp "facaad842496aedf9de1bcbe1872e7a0b0c91e40190e591f95f0d5db01ff3b33"
 :native-record12-full-log "47237a00f127247bfa8043a163c17a0797caea29ea956cc92472aa94ef8efa96"
 :raw-creators-defaults-log "ea3807e0c8c676aa4619931f431cb012d6434c008c0c5fc2dd337ef1022796f0"
 :hash-closure-log "4735aadc11eb9e7a632529073380b77611e4f4c15c3652c45d4ca0a2a674444f"
 :acl2-hash-defaults-subject-lisp "0ba275bb7b343b9e9b39a52c1ce69d6f75610224fc4bfa0912bde8991017ca0c"
 :successful-fixed-creator-object-scope :not-installed-authority))
(defun fn-srbc-unitp (kind)
 (declare (xargs :guard t))
 (if (member-eq kind '(:record12 :digest16 :carry6 :node16 :left16 :right16)) t nil))
(defun fn-srbc-allocated-octets (kind)
 (declare (xargs :guard t))
 (case kind (:record12 144) (:digest16 672) (:carry6 64)
  ((:node16 :left16 :right16) 704) (otherwise 0)))
(defun fn-srbc-request-count (kind)
 (declare (xargs :guard t))
 (case kind (:record12 2) (:digest16 2) (:carry6 1)
  ((:node16 :left16 :right16) 10) (otherwise 0)))
(defun fn-srbc-retained-owned-octets (kind)
 (declare (xargs :guard t))
 (case kind (:record12 144) (:digest16 672) (:carry6 64)
  ((:node16 :left16 :right16) 608) (otherwise 0)))
(defun fn-srbc-domain-p (kind coordinate)
 (declare (xargs :guard t))
 (and (fn-srbc-unitp kind) (equal coordinate *fn-srbc-coordinate*)))
; Coordinate matching is a qualification obligation, never an installed claim.
; Borrowed graph roots and pre-existing live defaults are charged separately.
; Node object608 plus six temporary16-byte keyword/APPEND2 cells gives704.
(encapsulate
 (((fn-assume-srbc-constructor-object-octets * *) => *)
  ((fn-assume-srbc-constructor-object-requests * *) => *))
 (local (defun fn-assume-srbc-constructor-object-octets (kind coordinate)
  (declare (ignore coordinate)) (fn-srbc-allocated-octets kind)))
 (local (defun fn-assume-srbc-constructor-object-requests (kind coordinate)
  (declare (ignore coordinate)) (fn-srbc-request-count kind)))
 (defthm fn-assume-srbc-object-octets-natural
  (natp (fn-assume-srbc-constructor-object-octets kind coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-srbc-object-requests-natural
  (natp (fn-assume-srbc-constructor-object-requests kind coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-srbc-qualified-object-octets-bound
  (implies (fn-srbc-domain-p kind coordinate)
   (<= (fn-assume-srbc-constructor-object-octets kind coordinate)
       (fn-srbc-allocated-octets kind))) :rule-classes nil)
 (defthm fn-assume-srbc-qualified-object-requests-bound
  (implies (fn-srbc-domain-p kind coordinate)
   (<= (fn-assume-srbc-constructor-object-requests kind coordinate)
       (fn-srbc-request-count kind))) :rule-classes nil))
(defun fn-srbc-constructor-object-request (kind coordinate)
 (declare (xargs :guard t))
 (if (fn-srbc-domain-p kind coordinate)
  (mv :creator-objects (fn-srbc-allocated-octets kind)
      (fn-srbc-request-count kind) (fn-srbc-retained-owned-octets kind))
  (mv :unavailable nil nil nil)))
(verify-guards fn-srbc-constructor-object-request)
