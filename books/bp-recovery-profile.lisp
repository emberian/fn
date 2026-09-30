; PKT-311a: judge the actual recovered held data under the current ADU
; profile before installation, including rows restored from a checkpoint.
(in-package "ACL2")
(include-book "bp-node-profile-admission")
(include-book "bp-held-projection")

; This is an open-time pass, not a served-state invariant revalidation.
; The existing decoder has established held-row shape.  The ADU reading is
; the same ACL2 decision used by receive admission: fragment total length,
; otherwise payload length.
(defun fn-bprpf-held-adus-fitp (held limit)
  (declare (xargs :guard (natp limit)))
  (if (consp held)
      (and (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle (car held))) limit)
           (fn-bprpf-held-adus-fitp (cdr held) limit))
    (null held)))

(defthm fn-bprpf-held-adus-fitp-bounds-every-member
  (implies (and (fn-bprpf-held-adus-fitp held limit)
                (member-equal h held))
           (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h)) limit))
  :hints (("Goal" :induct (fn-bprpf-held-adus-fitp held limit)
           :in-theory (e/d (fn-bprpf-held-adus-fitp)
                           (fn-bpnpf-bundle-adu-length fn-bpnf-held-bundle))))
  :rule-classes nil)

; EVENT is the exact fn-bphp-recover-auto-event result.  A preexisting
; replay fault is preserved; no failed replay is changed into readiness.
(defun fn-bprpf-admit-recovery (event profile)
  (declare (xargs :guard t))
  (let ((replay (fn-bpn-nth 4 event)))
    (cond ((not (equal (fn-bpn-nth 0 replay) :ready)) event)
          ((not (fn-bpnpf-profilep profile))
           (update-nth 4 '(:fault :profile) (true-list-fix event)))
          ((not (fn-bprpf-held-adus-fitp (fn-bpn-nth 1 replay)
                                        (fn-bpnpf-adu-octets profile)))
           (update-nth 4 '(:fault :adu-beyond-profile) (true-list-fix event)))
          (t event))))

(defthm fn-bprpf-ready-recovery-bounds-every-held-adu
  (let ((replay (fn-bpn-nth 4 (fn-bprpf-admit-recovery event profile))))
    (implies (and (equal (fn-bpn-nth 0 replay) :ready)
                  (member-equal h (fn-bpn-nth 1 replay)))
             (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h))
                 (fn-bpnpf-adu-octets profile))))
  :hints (("Goal"
           :use ((:instance fn-bprpf-held-adus-fitp-bounds-every-member
                   (held (fn-bpn-nth 1 (fn-bpn-nth 4 event)))
                   (limit (fn-bpnpf-adu-octets profile))))
           :in-theory (e/d (fn-bprpf-admit-recovery fn-bpn-nth)
                           (fn-bprpf-held-adus-fitp fn-bpnpf-bundle-adu-length
                            fn-bpnf-held-bundle fn-bpnpf-profilep
                            fn-bpnpf-adu-octets))))
  :rule-classes nil)

; The host calls this on every bounded input frame before retaining the
; frame for replay.  In particular a later deletion cannot hide an ADU
; that would already have exceeded the profile during family replay.
(defun fn-bprpf-row-admit (octets profile)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory
                    (disable fn-bpnf-stored-record-unframe
                             fn-bpnf-family-replay-unframe
                             fn-bpnpf-profilep fn-bpnpf-adu-octets
                             fn-bpnpf-bundle-octets fn-bpnpf-bundle-adu-length
                             fn-bpnf-held-bundle fn-bpnf-held-wire)))))
  (cond
   ((not (fn-bpnpf-profilep profile)) '(:fault :profile))
   (t
    (let* ((stored (fn-bpnf-stored-record-unframe octets))
           (h (fn-bpn-nth 3 stored)))
      (cond
       ((and stored
              (< (fn-bpnpf-adu-octets profile)
                 (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h))))
        '(:fault :adu-beyond-profile))
       ((and stored
              (< (fn-bpnpf-bundle-octets profile) (len (fn-bpnf-held-wire h))))
        '(:fault :bundle-beyond-profile))
       (t
        (let ((family (fn-bpnf-family-replay-unframe octets)))
          (if (and family
                    (< (fn-bpnpf-bundle-octets profile)
                       (len (fn-bpn-nth 5 family))))
              '(:fault :bundle-beyond-profile)
            '(:ready)))))))))

(defthm fn-bprpf-admitted-row-has-bounded-adu
  (implies (equal (fn-bprpf-row-admit octets profile) '(:ready))
           (<= (fn-bpnpf-bundle-adu-length
                (fn-bpnf-held-bundle
                 (fn-bpn-nth 3 (fn-bpnf-stored-record-unframe octets))))
               (fn-bpnpf-adu-octets profile)))
  :hints (("Goal" :cases ((fn-bpnf-stored-record-unframe octets))
           :in-theory (e/d (fn-bprpf-row-admit fn-bpn-nth fn-bpnf-held-bundle)
                                   (fn-bpnf-stored-record-unframe
                                    fn-bpnf-family-replay-unframe
                                    fn-bpnpf-profilep fn-bpnpf-adu-octets
                                    fn-bpnpf-bundle-octets))))
  :rule-classes nil)

; Read the checkpoint through the same selector the actual replay uses.
; No reassembly/fold can run before this decision.  Existing damaged-plan
; handling stays with the recovery interpreter.
(defun fn-bprpf-selection-admit (plan profile)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (fn-bpnpf-profilep profile)) '(:fault :profile))
        ((not (fn-bprpf-held-adus-fitp
                (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint plan))
                (fn-bpnpf-adu-octets profile)))
         '(:fault :adu-beyond-profile))
        (t '(:ready))))

(verify-guards fn-bprpf-selection-admit
  :hints (("Goal" :in-theory (disable fn-bpnpf-profilep
                                      fn-bpnpf-adu-octets
                                      fn-bprpf-held-adus-fitp
                                      fn-bpnr-plan-checkpoint
                                      fn-bpnr-checkpoint-held))))

(defthm fn-bprpf-admitted-checkpoint-bounds-every-held-adu
  (implies
   (and (equal (fn-bprpf-selection-admit plan profile) '(:ready))
        (member-equal h (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint plan))))
   (<= (fn-bpnpf-bundle-adu-length (fn-bpnf-held-bundle h))
       (fn-bpnpf-adu-octets profile)))
  :hints (("Goal"
           :use ((:instance fn-bprpf-held-adus-fitp-bounds-every-member
                   (held (fn-bpnr-checkpoint-held (fn-bpnr-plan-checkpoint plan)))
                   (limit (fn-bpnpf-adu-octets profile))))
           :in-theory (e/d (fn-bprpf-selection-admit)
                           (fn-bprpf-held-adus-fitp fn-bpnr-plan-checkpoint
                            fn-bpnr-checkpoint-held fn-bpnpf-bundle-adu-length
                            fn-bpnf-held-bundle fn-bpnpf-adu-octets))))
  :rule-classes nil)

(in-theory (disable fn-bprpf-held-adus-fitp fn-bprpf-admit-recovery))
