; fn: the local control socket's launch decision is ACL2's (lane
; host-decisions-2, 2026-09-27; packet B of
; planning/evidence/host-decisions-2026-09-27.md).
;
; host/native/control.lisp fnn-control-launch-client decided, in host code,
; whether an accepted control connection gets a worker: :stopping when the
; control plane is stopping, :busy when the live workers already number the
; ceiling of the store's profile (fn-bs-profile-max-control-clients, field
; 16: PKT-700), else a worker.  The comparison is a decision over the
; profile's ceiling, so it is ACL2's: the host passes the two observations
; (stopping, the live worker count) and the profile the owner opened, and
; relays the disposition.
;
; This book has the prefix `fn-ncla-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "native-control")
(include-book "byte-store-frame")

; THE DECISION the host calls (host/native-control-host.lisp
; fn-native-control-host-launch-disposition, from fnn-control-launch-client
; under the control lock).  STOPPINGP is the control plane's stop flag and
; ACTIVE the number of live workers, both host observations; PROFILE the
; store profile the owner opened (the control plane reads it after the open,
; fnn-control-start).
(defun fn-ncla-launch-disposition (stoppingp active profile)
  (declare (xargs :guard t))
  (cond (stoppingp :stopping)
        ((not (natp active)) :busy)
        ((< active (fn-bs-profile-max-control-clients profile)) :launch)
        (t :busy)))

; KEYSTONE.  A worker is launched exactly when the control plane is not
; stopping and the live workers are below the profile's ceiling; so a launch
; never takes the live workers past the ceiling.  Every answer is one of
; three.
(defthm fn-ncla-launch-exactly-below-the-ceiling
  (and (iff (equal (fn-ncla-launch-disposition stoppingp active profile) :launch)
            (and (not stoppingp) (natp active)
                 (< active (fn-bs-profile-max-control-clients profile))))
       (implies (equal (fn-ncla-launch-disposition stoppingp active profile) :launch)
                (<= (+ 1 active) (fn-bs-profile-max-control-clients profile)))
       (member-equal (fn-ncla-launch-disposition stoppingp active profile)
                     '(:stopping :busy :launch)))
  :hints (("Goal" :in-theory (disable fn-bs-profile-max-control-clients))))

; At or past the ceiling a live control plane answers :busy by name.
(defthm fn-ncla-at-the-ceiling-is-busy
  (implies (and (not stoppingp)
                (<= (fn-bs-profile-max-control-clients profile) active))
           (equal (fn-ncla-launch-disposition stoppingp active profile) :busy))
  :hints (("Goal" :in-theory (disable fn-bs-profile-max-control-clients))))
