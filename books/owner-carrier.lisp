; Private structural owner carrier. It becomes authoritative only at the
; atomic caller-threading migration: the live state globals remain the
; authority until then. This book alone is not a served-path completion.
; Untyped semantic fields do not assert the owner invariant; the real
; construction and writer boundaries must establish and preserve it.
(in-package "ACL2")

(defstobj fn-owner-st
  (fn-ost-ocfg :initially nil)
  (fn-ost-installedp :type (satisfies booleanp) :initially nil)
  (fn-ost-carry :initially nil))

(defun fn-ost-boundp (fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (fn-ost-installedp fn-owner-st))

(defun fn-ost-owner (fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (fn-ost-ocfg fn-owner-st))

(defun fn-ost-install-owner (oc fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (let ((fn-owner-st (update-fn-ost-ocfg oc fn-owner-st)))
    (update-fn-ost-installedp t fn-owner-st)))

(defun fn-ost-retention (fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (fn-ost-carry fn-owner-st))

(defun fn-ost-install-retention (carry fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (update-fn-ost-carry carry fn-owner-st))

(defthm fn-ost-owner-of-install-owner
  (equal (fn-ost-owner (fn-ost-install-owner oc fn-owner-st)) oc))
(defthm fn-ost-bound-of-install-owner
  (fn-ost-boundp (fn-ost-install-owner oc fn-owner-st)))
(defthm fn-ost-retention-of-install-owner
  (equal (fn-ost-retention (fn-ost-install-owner oc fn-owner-st))
         (fn-ost-retention fn-owner-st)))
(defthm fn-ost-retention-of-install-retention
  (equal (fn-ost-retention (fn-ost-install-retention carry fn-owner-st)) carry))
(defthm fn-ost-owner-of-install-retention
  (equal (fn-ost-owner (fn-ost-install-retention carry fn-owner-st))
         (fn-ost-owner fn-owner-st)))
(defthm fn-ost-bound-of-install-retention
  (equal (fn-ost-boundp (fn-ost-install-retention carry fn-owner-st))
         (fn-ost-boundp fn-owner-st)))

; Construction preserves the physical recognizer, independently of the
; configured-owner and retention semantic relations.
(defthm fn-ost-install-owner-preserves-physical-state
  (implies (fn-owner-stp fn-owner-st)
           (fn-owner-stp (fn-ost-install-owner oc fn-owner-st))))
(defthm fn-ost-install-retention-preserves-physical-state
  (implies (fn-owner-stp fn-owner-st)
           (fn-owner-stp (fn-ost-install-retention carry fn-owner-st))))

(in-theory (disable fn-ost-boundp fn-ost-owner fn-ost-install-owner
                    fn-ost-retention fn-ost-install-retention))
