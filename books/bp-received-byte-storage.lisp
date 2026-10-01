; Concrete leaf for the actual received-ciphertext provider. 256 is an
; allocation unit, never a bundle/profile ceiling. A directory may hold any
; operator-supported number of leaves. No public issuer/factory is installed.
; Source nonce comes from SAME PRS; no host-supplied backing ID is authority.
(in-package "ACL2")
(set-verify-guards-eagerness 2)

(defstobj fn-bprx-segment
 (fn-bprx-bytes :type (array (integer 0 255) (256)) :initially 0)
 (fn-bprx-nonce :type (integer 0 *) :initially 0)
 (fn-bprx-ordinal :type (integer 0 *) :initially 0)
 (fn-bprx-used :type (integer 0 256) :initially 0)
 (fn-bprx-phase :initially :uninstalled)
 :inline t)

; Internal after admitted constructor only. Installed allocation-family and
; source registration are separate antecedents in the eventual actual caller.
(defun fn-bprx-segment-begin (nonce ordinal fn-bprx-segment)
 (declare (xargs :stobjs fn-bprx-segment :guard (and (natp nonce) (natp ordinal))))
 (if (not (eq (fn-bprx-phase fn-bprx-segment) :uninstalled))
  (mv :source-busy fn-bprx-segment)
  (let* ((fn-bprx-segment (update-fn-bprx-nonce nonce fn-bprx-segment))
         (fn-bprx-segment (update-fn-bprx-ordinal ordinal fn-bprx-segment)))
   (let ((fn-bprx-segment (update-fn-bprx-phase :filling fn-bprx-segment)))
    (mv :source-filling fn-bprx-segment)))))

(defun fn-bprx-segment-put (nonce ordinal expected-used octet fn-bprx-segment)
 (declare (xargs :stobjs fn-bprx-segment
  :guard (and (natp nonce) (natp ordinal) (natp expected-used)
              (integerp octet) (<= 0 octet) (< octet 256))))
 (cond
  ((not (and (equal nonce (fn-bprx-nonce fn-bprx-segment))
             (equal ordinal (fn-bprx-ordinal fn-bprx-segment))))
   (mv :stale-source fn-bprx-segment))
  ((not (eq (fn-bprx-phase fn-bprx-segment) :filling))
   (mv :source-immutable fn-bprx-segment))
  ((not (equal expected-used (fn-bprx-used fn-bprx-segment)))
   (mv :stale-source-offset fn-bprx-segment))
  ((>= (fn-bprx-used fn-bprx-segment) 256) (mv :segment-full fn-bprx-segment))
  (t
   (let* ((at (fn-bprx-used fn-bprx-segment))
          (fn-bprx-segment (update-fn-bprx-bytesi at octet fn-bprx-segment)))
    (let ((fn-bprx-segment (update-fn-bprx-used (1+ at) fn-bprx-segment)))
     (mv :source-byte fn-bprx-segment))))))

(defun fn-bprx-segment-freeze (nonce ordinal expected-used fn-bprx-segment)
 (declare (xargs :stobjs fn-bprx-segment
  :guard (and (natp nonce) (natp ordinal) (natp expected-used))))
 (cond
  ((not (and (equal nonce (fn-bprx-nonce fn-bprx-segment))
             (equal ordinal (fn-bprx-ordinal fn-bprx-segment))))
   (mv :stale-source fn-bprx-segment))
  ((not (equal expected-used (fn-bprx-used fn-bprx-segment)))
   (mv :stale-source-offset fn-bprx-segment))
  ((eq (fn-bprx-phase fn-bprx-segment) :frozen)
   (mv :source-already-frozen fn-bprx-segment))
  ((not (eq (fn-bprx-phase fn-bprx-segment) :filling))
   (mv :source-fenced fn-bprx-segment))
  (t (let ((fn-bprx-segment (update-fn-bprx-phase :frozen fn-bprx-segment)))
      (mv :source-frozen fn-bprx-segment)))))

; Result list is the bounded logical observation at the concrete array
; boundary. Source storage is never reconstructed as a whole octet list.
(defun fn-bprx-segment-window-bytes (at count fn-bprx-segment)
 (declare (xargs :stobjs fn-bprx-segment :measure (nfix count)
  :guard (and (natp at) (natp count) (<= count 64) (<= (+ at count) 256))))
 (if (zp count) nil
  (cons (fn-bprx-bytesi at fn-bprx-segment)
        (fn-bprx-segment-window-bytes (1+ at) (1- count) fn-bprx-segment))))

; Core-only segment reader. Token-only registered parent must derive nonce,
; ordinal, local offset and absolute backing coordinate from retained source.
; No constructor/default GET and no complete-source scan is performed here.
(defun fn-bprx-segment-window (nonce ordinal at count fn-bprx-segment)
 (declare (xargs :stobjs fn-bprx-segment
  :guard (and (natp nonce) (natp ordinal) (natp at) (natp count) (<= count 64))))
 (cond
  ((not (and (equal nonce (fn-bprx-nonce fn-bprx-segment))
             (equal ordinal (fn-bprx-ordinal fn-bprx-segment))))
   (mv :stale-source nil))
  ((not (eq (fn-bprx-phase fn-bprx-segment) :frozen))
   (mv :source-unpublished nil))
  ((> (+ at count) (fn-bprx-used fn-bprx-segment))
   (mv :source-range nil))
  (t (mv :source-window (fn-bprx-segment-window-bytes at count fn-bprx-segment)))))
