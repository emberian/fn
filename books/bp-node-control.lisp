; The serialized BP node's bounded, route-only local control boundary.
(in-package "ACL2")
(include-book "native-config")
(include-book "native-control")
(include-book "native-admin")

(defun fn-bpnc-config-bound ()
  (declare (xargs :guard t))
  *fn-ncfg-max-octets*)

(defun fn-bpnc-startup (config-octets store-octets)
  (declare (xargs :guard t))
  (let* ((loaded (fn-native-config-load config-octets))
         (config (fn-ncfg-nth 1 loaded))
         (root (fn-native-config-store config))
         (path (fn-native-config-control-path config)))
    (cond ((not (equal (fn-ncfg-nth 0 loaded) :accepted))
           (list :refused :invalid-runtime-config))
          ((not (and (stringp root)
                     (equal (fn-record-string-octets root) store-octets)))
           (list :refused :control-store-mismatch))
          ((not (and (stringp path) (consp (fn-record-string-octets path))
                     (<= (len (fn-record-string-octets path)) *fn-ncfg-max-path*)))
           (list :refused :control-path-invalid))
          (t (let* ((octets (fn-record-string-octets path))
                    (lease (fn-native-control-lease-path octets)))
               (list :ready octets lease *fn-nctrl-max-command-frame*))))))

; ADMIN is the bounded FNCT decoder's exact (:admin ARGV) projection.
; The selected parser is the same one the ordinary operator calls.  No
; arbitrary POST/consumer machinery becomes available on a BP node.
(defun fn-bpnc-turn-plan (ownerp admin)
  (declare (xargs :guard t))
  (let* ((argv (fn-ncfg-nth 1 admin))
         (plan (fn-native-admin-plan argv)))
    (cond ((not (equal ownerp t)) (list :refused :not-owner))
          ((not (equal (fn-ncfg-nth 0 admin) :admin))
           (list :refused :unsupported-bp-control-request))
          ((not (equal (fn-native-admin-result-status plan) :accepted))
           (list :refused (fn-native-admin-result-reason plan)))
          ((not (member-equal (fn-native-admin-result-kind plan)
                               '(:set-bp-route :remove-bp-route)))
           (list :refused :unsupported-bp-control-operation))
          (t (list :execute plan)))))

(defun fn-bpnc-socket-initial (plan)
  (declare (xargs :guard t))
  (if (equal (fn-ncfg-nth 0 plan) :ready)
      (list :prepared (fn-ncfg-nth 1 plan) (fn-ncfg-nth 2 plan)
            (fn-ncfg-nth 3 plan))
    (list :closed nil nil 0)))

(defun fn-bpnc-socket-action (st)
  (declare (xargs :guard t))
  (case (fn-ncfg-nth 0 st)
    (:prepared (list :bind (fn-ncfg-nth 1 st) (fn-ncfg-nth 2 st)))
    (:bound (list :install (fn-ncfg-nth 1 st) (fn-ncfg-nth 3 st)))
    (:retiring (list :retire (fn-ncfg-nth 1 st) (fn-ncfg-nth 2 st)))
    (otherwise nil)))

(defun fn-bpnc-socket-phase (phase st)
  (declare (xargs :guard t))
  (list phase (fn-ncfg-nth 1 st) (fn-ncfg-nth 2 st) (fn-ncfg-nth 3 st)))

(defun fn-bpnc-socket-step (st event)
  (declare (xargs :guard t))
  (let ((phase (fn-ncfg-nth 0 st))
        (kind (fn-ncfg-nth 0 event)) (outcome (fn-ncfg-nth 1 event)))
    (cond ((and (equal phase :prepared) (equal kind :bind-result))
           (fn-bpnc-socket-phase (if (equal outcome :ok) :bound :retiring) st))
          ((and (equal phase :bound) (equal kind :install-result))
           (fn-bpnc-socket-phase (if (equal outcome :ok) :live :retiring) st))
          ((and (member-equal phase '(:prepared :bound :live)) (equal kind :stop))
           (fn-bpnc-socket-phase :retiring st))
          ((and (equal phase :retiring) (equal kind :retire-result))
           (fn-bpnc-socket-phase (if (equal outcome :ok) :closed :fenced) st))
          (t st))))

(defun fn-bpnc-socket-open-run (plan bind-outcome install-outcome)
  (declare (xargs :guard t))
  (fn-bpnc-socket-step
   (fn-bpnc-socket-step (fn-bpnc-socket-initial plan)
                        (list :bind-result bind-outcome))
   (list :install-result install-outcome)))

; Keystone: the actual startup entry never binds a runtime configuration
; to a different Store than its parsed store path.
(defthm fn-bpnc-ready-startup-binds-the-parsed-store
  (implies (equal (fn-ncfg-nth 0 (fn-bpnc-startup config-octets store-octets)) :ready)
           (let ((loaded (fn-native-config-load config-octets)))
             (and (equal (fn-ncfg-nth 0 loaded) :accepted)
                  (equal (fn-record-string-octets
                          (fn-native-config-store (fn-ncfg-nth 1 loaded)))
                         store-octets))))
  :hints (("Goal" :in-theory (e/d (fn-bpnc-startup)
                                 (fn-native-config-load fn-record-string-octets
                                  fn-native-config-store fn-native-config-control-path
                                  fn-native-control-lease-path fn-ncfg-nth))))
  :rule-classes nil)

; Keystone over the actual host-called authority plan: every granted
; mutation is exactly the parsed route mutation, under same-owner evidence.
(defthm fn-bpnc-grant-is-the-authorized-route-plan
  (let ((r (fn-bpnc-turn-plan ownerp admin)))
    (implies (equal (fn-ncfg-nth 0 r) :execute)
             (and (equal ownerp t)
                  (equal (fn-ncfg-nth 0 admin) :admin)
                  (equal (fn-ncfg-nth 1 r)
                         (fn-native-admin-plan (fn-ncfg-nth 1 admin)))
                  (equal (fn-native-admin-result-status (fn-ncfg-nth 1 r)) :accepted)
                  (member-equal (fn-native-admin-result-kind (fn-ncfg-nth 1 r))
                                '(:set-bp-route :remove-bp-route)))))
  :hints (("Goal" :in-theory (e/d (fn-bpnc-turn-plan fn-ncfg-nth)
                                 (fn-native-admin-plan fn-native-admin-result-status
                                  fn-native-admin-result-kind fn-native-admin-result-reason))))
  :rule-classes nil)

; A complete primitive completion protocol, not a fact about a phase name.
(defthm fn-bpnc-open-run-live-iff-both-completions-succeed
  (equal (equal (fn-ncfg-nth 0
                  (fn-bpnc-socket-open-run plan bind-outcome install-outcome)) :live)
         (and (equal (fn-ncfg-nth 0 plan) :ready)
              (equal bind-outcome :ok) (equal install-outcome :ok)))
  :hints (("Goal" :in-theory (enable fn-bpnc-socket-open-run fn-bpnc-socket-initial
                                     fn-bpnc-socket-step fn-bpnc-socket-phase
                                     fn-ncfg-nth)))
  :rule-classes nil)

(defthm fn-bpnc-retirement-stops-the-control-listener
  (implies (member-equal (fn-ncfg-nth 0 st) '(:prepared :bound :live))
           (let* ((retiring (fn-bpnc-socket-step st '(:stop)))
                  (closed (fn-bpnc-socket-step retiring (list :retire-result outcome))))
             (and (equal (fn-ncfg-nth 0 (fn-bpnc-socket-action retiring)) :retire)
                  (equal (fn-ncfg-nth 0 closed)
                         (if (equal outcome :ok) :closed :fenced))
                  (not (fn-bpnc-socket-action closed)))))
  :hints (("Goal" :in-theory (enable fn-bpnc-socket-step fn-bpnc-socket-phase
                                     fn-bpnc-socket-action fn-ncfg-nth)))
  :rule-classes nil)

(in-theory (disable fn-bpnc-startup fn-bpnc-turn-plan fn-bpnc-socket-initial
                    fn-bpnc-socket-action fn-bpnc-socket-step fn-bpnc-socket-open-run))
