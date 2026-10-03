; Conservative fixed backing inventory for the private decoded constructor.
; Selected fn-crl SBCL layout projection, NOT complete allocation funding.
(in-package "ACL2")
(include-book "cold-read-layout")

(defun fn-dwb-parent-octets ()
  (declare (xargs :guard t))
  (fn-crl-array-octets 8 8))

(defun fn-dwb-carry-octets ()
  (declare (xargs :guard t))
  (fn-crl-array-octets 12 8))

(defun fn-dwb-digest-octets ()
  (declare (xargs :guard t))
  (+ (fn-crl-array-octets 16 8) (fn-crl-array-octets 64 8)))

; Actual ACL2 native lowering represents the single-array stobj directly as
; its 20-register vector. Retain 32 extra projected octets conservatively;
; this logical one-field parent is not a second native backing object.
(defun fn-dwb-decoder-register-octets ()
  (declare (xargs :guard t))
  (+ (fn-crl-array-octets 1 8) (fn-crl-array-octets 20 8)))

; Likewise the actual requested-window child is the direct 16384-byte vector.
; The 32 parent allowance is conservative, not an observed native allocation.
(defun fn-dwb-requested-window-octets ()
  (declare (xargs :guard t))
  (+ (fn-crl-array-octets 1 8) (fn-crl-array-octets 16384 1)))

(defun fn-dwb-octet-buffers-octets ()
  (declare (xargs :guard t))
  ; Four two-field wrappers and their four original empty arrays. Include
  ; the empty arrays even though exact reserve replaces them: no collection
  ; receipt exists here. Assign reserves input64; initialize reserves win,
  ; tab and out. fn-octets-reserve grows exactly, unlike append's policy.
  (+ (* 4 (fn-crl-array-octets 2 8))
     (* 4 (fn-crl-array-octets 0 1))
     (fn-crl-array-octets 64 1)
     (fn-crl-array-octets 65536 1)
     (fn-crl-array-octets 3494 1)
     (fn-crl-array-octets 64 1)))

(defun fn-dwb-fixed-storage-octets ()
  (declare (xargs :guard t))
  (+ (fn-dwb-parent-octets) (fn-dwb-carry-octets)
     (fn-dwb-digest-octets) (fn-dwb-decoder-register-octets)
     (fn-dwb-requested-window-octets) (fn-dwb-octet-buffers-octets)))

(defun fn-dwb-fixed-storage-vector ()
  (declare (xargs :guard t))
  ; Existing five-component page-read projection: storage/work/descriptors/
  ; workers/read identities. The token and physical worker still come from
  ; the SAME pool; this is not a second permit authority.
  (list (fn-dwb-fixed-storage-octets) 0 0 1 1))

(defun fn-dwb-coverage ()
  (declare (xargs :guard t))
  :partial-fixed-storage)

; Excluded: pointed-to integer/cons payloads, controller/token/borrowed
; graphs, source/pool registry slots, constructor transients, and collector
; copying/reclamation. In particular this does not open a complete profile.
