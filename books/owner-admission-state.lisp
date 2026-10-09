; Admission configuration carried by the owner. Other admission fields move
; as their complete decisions migrate; reclaim-live is the launcher's opt-in.
; Props: configure observes exactly (and live t), default is false, and the
; setter frames every unrelated global. Recovery does not reset this slot.
(in-package "ACL2")
(include-book "state-globals")

(defun fn-oadm-initial ()
  (declare (xargs :guard t))
  (list nil))

(defun fn-oadm-configure-reclaim (live)
  (declare (xargs :guard t))
  (list (and live t)))

(defun fn-oadm-reclaim-live (r)
  (declare (xargs :guard t))
  (and (consp r) (car r) t))

(defun fn-oadm-recordp (r)
  (declare (xargs :guard t))
  (and (consp r) (null (cdr r)) (booleanp (car r))))

(defthm fn-oadm-initial-is-record
  (fn-oadm-recordp (fn-oadm-initial)))

(defthm fn-oadm-configure-reclaim-establishes-record
  (fn-oadm-recordp (fn-oadm-configure-reclaim live)))

(defthm fn-oadm-configure-reclaim-composition-by-definition
  (equal (fn-oadm-reclaim-live (fn-oadm-configure-reclaim live))
         (and live t)))

(defthm fn-oadm-initial-reclaim-disabled-by-definition
  (not (fn-oadm-reclaim-live (fn-oadm-initial))))

(defthm fn-oadm-configure-reclaim-requires-opt-in
  (implies (not live)
           (not (fn-oadm-reclaim-live (fn-oadm-configure-reclaim live)))))

(defun fn-ost-admission (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-admission state)
      (f-get-global 'fn-owner-admission state)
    (fn-oadm-initial)))

(defun fn-ost-install-admission (r state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-admission r state))

(defthm fn-ost-admission-of-install
  (equal (fn-ost-admission (fn-ost-install-admission r state)) r))

(defthm fn-ost-admission-of-other-global-put
  (implies (not (equal key 'fn-owner-admission))
           (equal (fn-ost-admission (f-put-global key value state))
                  (fn-ost-admission state))))

(defthm fn-ost-install-admission-frames-get-global
  (implies (not (equal key 'fn-owner-admission))
           (equal (get-global key (fn-ost-install-admission r state))
                  (get-global key state))))

(defthm fn-ost-install-admission-frames-boundp-global
  (implies (not (equal key 'fn-owner-admission))
           (equal (boundp-global key (fn-ost-install-admission r state))
                  (boundp-global key state))))

(defthm fn-ost-install-admission-frames-global-association
  (implies (not (equal key 'fn-owner-admission))
           (equal (assoc-equal key (nth 2 (fn-ost-install-admission r state)))
                  (assoc-equal key (nth 2 state)))))

(defthm fn-ost-install-admission-preserves-state-p1
  (implies (state-p1 state)
           (state-p1 (fn-ost-install-admission r state)))
  :hints (("Goal" :in-theory (disable state-p1))))

(in-theory (disable fn-ost-admission fn-ost-install-admission))
