; Admission is checked after all machine declarations, so the supported
; profile cannot silently promise a quantum smaller than an actual arm needs.
(in-package "ACL2")
(include-book "assembly")

(defun fn2-exec-kinds-descriptor-max (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) 0
    (max (nfix (fn2-arm-get :descriptors
                (fn2-machine-property (car names) :budget world)))
         (fn2-exec-kinds-descriptor-max (cdr names) world))))

(make-event
 `(defconst *fn2-exec-descriptor-reserve*
    ,(max 1 ; protected grant service can enqueue one arm-wake descriptor
          (fn2-exec-kinds-descriptor-max (fn2-machine-names (w state)) (w state)))))

(defun fn2-execution-profilep (profile)
  (declare (xargs :guard t))
  (and (fn2-core-profilep profile)
       (<= *fn2-exec-descriptor-reserve* (fn2-profile-aturn profile))
       (<= *fn2-exec-descriptor-reserve* (fn2-profile-qa profile))))

(defun fn2-turn-descriptor-room-p (actions limit)
  (declare (xargs :guard t))
  (<= (+ (nfix actions) *fn2-exec-descriptor-reserve*) (nfix limit)))

(defthm fn2-turn-descriptor-room-gives-residual
  (implies (and (natp actions) (natp limit)
                (fn2-turn-descriptor-room-p actions limit))
           (<= *fn2-exec-descriptor-reserve* (- limit actions)))
  :rule-classes (:rewrite :linear))

(assert-event (fn2-execution-profilep *fn2-profile-tiny*))
(assert-event (fn2-execution-profilep *fn2-profile-concrete*))

; The older structural profile admits this quantum; execution admission
; rejects it because no turn could run a largest-budget continuation.
(assert-event
 (let ((profile (acons :aturn (- *fn2-exec-descriptor-reserve* 1) *fn2-profile-tiny*)))
  (and (fn2-core-profilep profile) (not (fn2-execution-profilep profile)))))
