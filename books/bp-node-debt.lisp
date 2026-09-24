; Exact FNBS received-namespace journal debt for the implemented held state.
; The reference fold is for cold replay and proof.  Served transitions carry
; its value and update it from the single row or handoff they change.
(in-package "ACL2")
(include-book "bp-fnbs-namespace")
(include-book "bp-app-handoff")

(defconst *fn-bpnd-rotation-reserve* 0)

(defun fn-bpnd-held-terminal-owedp (h)
  (declare (xargs :guard t))
  (and (equal (fn-cbor-ag-car h) :bpnf-held)
       (null (fn-bpn-nth 14 h))
       (consp (fn-bpn-nth 12 h))
       (not (equal (fn-bpn-nth 12 h) '(:dispatch-done)))))

(defun fn-bpnd-held-active-attemptp (h)
  (declare (xargs :guard t))
  (and (equal (fn-cbor-ag-car h) :bpnf-held)
       (null (fn-bpn-nth 14 h))
       (equal (fn-cbor-ag-car (fn-bpn-nth 13 h)) :forwarding)))

(defun fn-bpnd-local-request-undeliveredp (h node)
  (declare (xargs :guard t))
  (and (equal (fn-cbor-ag-car h) :bpnf-held)
       (null (fn-bpn-nth 14 h))
       (not (equal (fn-bpn-nth 12 h) '(:dispatch-done)))
       (not (equal (fn-cbor-ag-car (fn-bpn-nth 10 h)) :delivered))
       (let* ((bundle (fn-bpnf-held-bundle h))
              (primary (fn-bpb-bundle-primary bundle)))
         (and (fn-bpb-bundlep bundle)
              (fn-bpp-blockp primary)
              (natp (fn-bpp-flags primary))
              (not (fn-bpp-fragmentp (fn-bpp-flags primary)))
              (equal (fn-bpp-destination primary) node)
              (equal (fn-bpah-held-class h) :request)))))

(defun fn-bpnd-held-debt (h node)
  (declare (xargs :guard t))
  (if (not (equal (fn-cbor-ag-car h) :bpnf-held)) 0
    (+ 1                             ; eventual kind 11 discard
       (if (fn-bpnd-held-terminal-owedp h) 1 0)
       (if (fn-bpnd-held-active-attemptp h) 1 0)
       (if (fn-bpnd-local-request-undeliveredp h node) 3 0))))

(defun fn-bpnd-held-list-debt (held node)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (consp held)
      (+ (fn-bpnd-held-debt (car held) node)
         (fn-bpnd-held-list-debt (cdr held) node))
    0))

(defun fn-bpnd-handoff-debt (handoff)
  (declare (xargs :guard t))
  (if (and (equal (fn-cbor-ag-car handoff) :bpnf-handoff)
           (equal (fn-bpn-nth 3 handoff) :owed))
      3 0))

(defun fn-bpnd-handoffs-debt (handoffs)
  (declare (xargs :guard t :measure (acl2-count handoffs)))
  (if (consp handoffs)
      (+ (fn-bpnd-handoff-debt (car handoffs))
         (fn-bpnd-handoffs-debt (cdr handoffs)))
    0))

; No open forwarding/fragment plan is represented in the current FNBS
; state: kind 18 replaces a complete family atomically.  The separate plan
; term is explicit for the later persisted-plan transition: each open plan
; costs one kind 17 plus three records per unmaterialized child.
(defun fn-bpnd-open-plans-debt (unmaterialized-counts)
  (declare (xargs :guard t :measure (acl2-count unmaterialized-counts)))
  (if (consp unmaterialized-counts)
      (+ 1 (* 3 (nfix (car unmaterialized-counts)))
         (fn-bpnd-open-plans-debt (cdr unmaterialized-counts)))
    0))

(defun fn-bpnd-debt-with-plans (st node unmaterialized-counts)
  (declare (xargs :guard t))
  (+ (fn-bpnd-held-list-debt (fn-bpnf-held-list st) node)
     (fn-bpnd-handoffs-debt (fn-bpnf-handoffs st))
     (fn-bpnd-open-plans-debt unmaterialized-counts)))

(defun fn-bpnd-debt (st node)
  (declare (xargs :guard t))
  (fn-bpnd-debt-with-plans st node nil))

; The serving engine computes these deltas from the one admitted row.  The
; host never supplies a debt value.  A kind-7 accepted request transfers its
; three reserved handoff credits from the undelivered row to the new :owed
; handoff, rather than creating three unbudgeted credits.
(defun fn-bpnd-held-delta (before after node)
  (declare (xargs :guard t))
  (- (fn-bpnd-held-debt after node)
     (fn-bpnd-held-debt before node)))

(defun fn-bpnd-held-handoff-delta (before after handoff node)
  (declare (xargs :guard t))
  (+ (fn-bpnd-held-delta before after node)
     (fn-bpnd-handoff-debt handoff)))

(defun fn-bpnd-family-delta (consumed new-held node)
  (declare (xargs :guard t))
  (- (fn-bpnd-held-debt new-held node)
     (fn-bpnd-held-list-debt consumed node)))

(defun fn-bpnd-remaining (used)
  (declare (xargs :guard t))
  (if (and (natp used) (<= used *fn-bpnf-received-max-records*))
      (- *fn-bpnf-received-max-records* used)
    0))

(defun fn-bpnd-free (used debt margin)
  (declare (xargs :guard t))
  (- (fn-bpnd-remaining used)
     (+ (nfix debt) *fn-bpnd-rotation-reserve* (nfix margin))))

(defun fn-bpnd-coverp (used debt)
  (declare (xargs :guard t))
  (and (natp used) (<= used *fn-bpnf-received-max-records*)
       (natp debt)
       (<= (+ debt *fn-bpnd-rotation-reserve*)
           (fn-bpnd-remaining used))))

; MODE names the spec's three admission rules.  :pay is permitted for a
; recovered old history already below cover, provided a physical slot exists;
; it never promises settlement when the physical namespace is exhausted.
; :spend covers cost 1 plus the exact nonnegative change to D.  Kinds 12/13
; use :control and may consume the control margin but not owed debt.
(defun fn-bpnd-admitp (used debt margin delta mode)
  (declare (xargs :guard t))
  (and (natp used) (<= used *fn-bpnf-received-max-records*)
       (natp debt) (natp margin) (integerp delta)
       (<= 0 (+ debt delta))
       (< used *fn-bpnf-received-max-records*)
       (cond ((equal mode :pay) (< delta 0))
             ((equal mode :spend)
              (and (<= 0 delta)
                   (<= (+ 1 delta) (fn-bpnd-free used debt margin))))
             ((equal mode :control)
              (and (equal delta 0)
                   (<= 1 (- (fn-bpnd-remaining used)
                            (+ debt *fn-bpnd-rotation-reserve*)))))
             (t nil))))

(defthm fn-bpnd-spend-admission-preserves-cover
  (implies (fn-bpnd-admitp used debt margin delta :spend)
           (<= (+ (+ debt delta) *fn-bpnd-rotation-reserve* margin)
               (fn-bpnd-remaining (1+ used))))
  :hints (("Goal" :in-theory (enable fn-bpnd-admitp fn-bpnd-free
                                    fn-bpnd-remaining)))
  :rule-classes nil)

(defthm fn-bpnd-paying-admission-preserves-existing-cover
  (implies (and (fn-bpnd-coverp used debt)
                (fn-bpnd-admitp used debt margin delta :pay))
           (fn-bpnd-coverp (1+ used) (+ debt delta)))
  :hints (("Goal" :in-theory (enable fn-bpnd-admitp fn-bpnd-coverp
                                    fn-bpnd-remaining)))
  :rule-classes nil)
