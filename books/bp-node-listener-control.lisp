; Serialized BP listener installation after durable configuration publication.
; The core chooses ports/generation.  The host observes bind/close outcomes.
(in-package "ACL2")
(include-book "bp-listener-set")
(include-book "bp-node-control")
(include-book "defrecord")

(fn-defrecord fn-bplc
  :tag :fn-bplc
  :constructor (fn-bplc-make phase generation ports target-generation target-ports
                            pending staged retiring descriptors peak installedp session)
  :fields ((fn-bplc-phase t) (fn-bplc-generation t) (fn-bplc-ports t)
           (fn-bplc-target-generation t) (fn-bplc-target-ports t)
           (fn-bplc-pending t) (fn-bplc-staged t) (fn-bplc-retiring t)
           (fn-bplc-descriptors t) (fn-bplc-peak t) (fn-bplc-installedp t) (fn-bplc-session t))
  :recognizer nil)

 ; The actual owner already carries configuration validity.  Do not repeat
; fn-cfgp (whole-configuration validation) to project its listener rows.
(defun fn-bplc-owner-listener-ports (cfg)
  (declare (xargs :guard t))
  (let ((rows (fn-cfg-peers (fn-cfg-value cfg))))
    (fn-bpaj-listener-port-list (fn-bpaj-listener-rows rows rows))))

(defthm fn-bplc-owner-listener-ports-refines-the-configured-listener-set
  (implies (fn-cfgp cfg)
           (equal (fn-bplc-owner-listener-ports cfg) (fn-bpaj-listener-ports cfg)))
  :hints (("Goal" :in-theory (enable fn-bplc-owner-listener-ports
                                    fn-bpaj-listener-ports fn-bpaj-listener-set)))
  :rule-classes nil)

; Configuration turns, not per-session scans.  Supported numeric PORT keeps
; its explicit listener; :boundaries follows the actual owner configuration.
(defun fn-bplc-configured-ports (mode cfg)
  (declare (xargs :guard t))
  (cond ((equal mode :boundaries) (fn-bplc-owner-listener-ports cfg))
        ((natp mode) (list mode))
        (t nil)))

(defun fn-bplc-minus-loop (xs ys acc)
  (declare (xargs :guard t))
  (if (consp xs)
      (fn-bplc-minus-loop (cdr xs) ys
                         (if (fn-ag-member (car xs) ys) acc (cons (car xs) acc)))
    (fn-ag-rev-onto acc nil)))

(defun fn-bplc-minus (xs ys)
  (declare (xargs :guard t))
  (fn-bplc-minus-loop xs ys nil))

 ; Admission extends the same bounded parser only to BP boundaries.  A
; generic peer-remove is granted only when the actual configured transport
; of that named peer is BP; NNTP peer administration stays unsupported.
(defun fn-bplc-turn-plan (ownerp admin cfg st)
  (declare (xargs :guard t))
  (let* ((route (fn-bpnc-turn-plan ownerp admin))
         (plan (fn-native-admin-plan (fn-ncfg-nth 1 admin)))
         (kind (fn-native-admin-result-kind plan))
         (peer (fn-cfg-peer-find
                (fn-record-octets-string (fn-native-admin-result-name plan))
                (fn-cfg-peers (fn-cfg-value cfg)))))
    (if (equal (fn-ncfg-nth 0 route) :execute) route
      (if (and (equal ownerp t) (equal (fn-ncfg-nth 0 admin) :admin)
               (equal (fn-native-admin-result-status plan) :accepted)
               (equal (fn-bplc-phase st) :stable)
               (or (equal kind :set-bp-boundary)
                   (and (equal kind :remove-peer)
                        (equal (fn-ag-car (fn-cfg-peer-transport peer)) :bp))))
          (list :execute plan) route))))

; Cold restart has no runtime descriptor.  Persisted CFG, not an in-memory
; pre-crash installed generation, is the sole source of the new target.
(defun fn-bplc-recover (mode cfg)
  (declare (xargs :guard t))
  (let ((ports (fn-bplc-configured-ports mode cfg)))
    (fn-bplc-make (if (and (equal mode :boundaries) (not (consp ports))) :refused :binding)
                  nil nil (fn-cfg-generation cfg) ports
                  ports nil nil 0 0 nil nil)))

(defun fn-bplc-begin (st mode cfg)
  (declare (xargs :guard t))
  (if (not (equal (fn-bplc-phase st) :stable)) st
    (let ((ports (fn-bplc-configured-ports mode cfg)))
      (fn-bplc-make :binding (fn-bplc-generation st) (fn-bplc-ports st)
                    (fn-cfg-generation cfg) ports
                    (fn-bplc-minus ports (fn-bplc-ports st)) nil
                    (fn-bplc-minus (fn-bplc-ports st) ports)
                    (fn-bplc-descriptors st) (fn-bplc-descriptors st) nil (fn-bplc-session st)))))

(defun fn-bplc-action (st)
  (declare (xargs :guard t))
  (case (fn-bplc-phase st)
    (:binding (if (consp (fn-bplc-pending st))
                  (list :prepare-bind (fn-ag-car (fn-bplc-pending st)))
                (list :install (fn-bplc-target-generation st)
                      (fn-bplc-target-ports st))))
    (:binding-active (and (consp (fn-bplc-pending st))
                          (list :bind (fn-ag-car (fn-bplc-pending st)))))
    (:retiring (and (consp (fn-bplc-retiring st))
                    (list :retire (fn-ag-car (fn-bplc-retiring st)))))
    (:stable (list :ready (fn-bplc-generation st) (fn-bplc-ports st)))
    (:refused (list :refused :no-bp-boundary-listener))
    (otherwise nil)))

(defun fn-bplc-with-phase (st phase)
  (declare (xargs :guard t))
  (fn-bplc-make phase (fn-bplc-generation st) (fn-bplc-ports st)
                (fn-bplc-target-generation st) (fn-bplc-target-ports st)
                (fn-bplc-pending st) (fn-bplc-staged st) (fn-bplc-retiring st)
                (fn-bplc-descriptors st) (fn-bplc-peak st) (fn-bplc-installedp st) (fn-bplc-session st)))

(defun fn-bplc-with-session (st session)
  (declare (xargs :guard t))
  (fn-bplc-make (fn-bplc-phase st) (fn-bplc-generation st) (fn-bplc-ports st)
                (fn-bplc-target-generation st) (fn-bplc-target-ports st)
                (fn-bplc-pending st) (fn-bplc-staged st) (fn-bplc-retiring st)
                (fn-bplc-descriptors st) (fn-bplc-peak st) (fn-bplc-installedp st)
                session))

(defun fn-bplc-accept-plan (st index)
  (declare (xargs :guard t))
  (and (equal (fn-bplc-phase st) :stable) (not (fn-bplc-session st))
       (natp index) (< index (len (fn-bplc-ports st)))
       (list :accept (fn-bplc-generation st) (fn-ncfg-nth index (fn-bplc-ports st)))))

(defun fn-bplc-crash (st)
  (declare (xargs :guard t))
  ;; Process death releases descriptors and acceptance pins; durable target
  ;; provenance survives.  Cold startup rederives it from the disk owner.
  (fn-bplc-make :crashed nil nil
                (fn-bplc-target-generation st) (fn-bplc-target-ports st)
                nil nil nil 0 (nfix (fn-bplc-peak st)) t nil))

(defun fn-bplc-step (st event)
  (declare (xargs :guard t))
  (let ((kind (fn-ag-car event)) (outcome (fn-ag-car (fn-ag-cdr event))))
    (cond
     ((equal kind :crash)
      (fn-bplc-crash st))
     ((equal kind :session-closed) (fn-bplc-with-session st nil))
     ((and (equal kind :accept-result)
           (equal (fn-ncfg-nth 2 event) :ok)
           (fn-bplc-accept-plan st outcome))
      (fn-bplc-with-session st (fn-bplc-accept-plan st outcome)))
     ((and (equal (fn-bplc-phase st) :binding)
           (consp (fn-bplc-pending st)) (equal kind :bind-start))
      ;; Reserve the temporary descriptor before socket creation, including
      ;; a bind attempt which fails.  Only one such effect is outstanding.
      (let ((count (1+ (nfix (fn-bplc-descriptors st)))))
        (fn-bplc-make :binding-active (fn-bplc-generation st) (fn-bplc-ports st)
                      (fn-bplc-target-generation st) (fn-bplc-target-ports st)
                      (fn-bplc-pending st) (fn-bplc-staged st) (fn-bplc-retiring st)
                      count (max count (nfix (fn-bplc-peak st))) nil (fn-bplc-session st))))
     ((and (equal (fn-bplc-phase st) :binding-active)
           (consp (fn-bplc-pending st)) (equal kind :bind-result))
      (if (not (equal outcome :ok)) (fn-bplc-with-phase st :fenced)
        (fn-bplc-make :binding (fn-bplc-generation st) (fn-bplc-ports st)
                      (fn-bplc-target-generation st) (fn-bplc-target-ports st)
                      (fn-ag-cdr (fn-bplc-pending st))
                      (cons (fn-ag-car (fn-bplc-pending st)) (fn-bplc-staged st))
                      (fn-bplc-retiring st) (fn-bplc-descriptors st)
                      (fn-bplc-peak st) nil (fn-bplc-session st))))
     ((and (equal (fn-bplc-phase st) :binding)
           (not (consp (fn-bplc-pending st))) (equal kind :install-result))
      (if (not (equal outcome :ok)) (fn-bplc-with-phase st :fenced)
        (fn-bplc-make (if (consp (fn-bplc-retiring st)) :retiring :stable)
                      (fn-bplc-target-generation st) (fn-bplc-target-ports st)
                      (fn-bplc-target-generation st) (fn-bplc-target-ports st)
                      nil nil (fn-bplc-retiring st)
                      (fn-bplc-descriptors st) (fn-bplc-peak st) t (fn-bplc-session st))))
     ((and (equal (fn-bplc-phase st) :retiring)
           (consp (fn-bplc-retiring st)) (equal kind :retire-result))
      (if (not (equal outcome :ok)) (fn-bplc-with-phase st :fenced)
        (fn-bplc-make (if (consp (fn-ag-cdr (fn-bplc-retiring st))) :retiring :stable)
                      (fn-bplc-generation st) (fn-bplc-ports st)
                      (fn-bplc-target-generation st) (fn-bplc-target-ports st)
                      nil nil (fn-ag-cdr (fn-bplc-retiring st))
                      (nfix (1- (nfix (fn-bplc-descriptors st)))) (fn-bplc-peak st) t (fn-bplc-session st))))
     (t st))))

; Descriptor credits name BP listeners and one reserved socket-bind attempt only.  Existing accepted
; sessions and the separately modeled control socket are not retired here.
(defun fn-bplc-accountedp (st)
  (declare (xargs :guard t))
  (and (natp (fn-bplc-descriptors st)) (natp (fn-bplc-peak st))
       (<= (fn-bplc-descriptors st) (fn-bplc-peak st))
       (equal (fn-bplc-descriptors st)
              (+ (len (fn-bplc-ports st))
                 (if (equal (fn-bplc-phase st) :binding-active) 1 0)
                 (if (fn-bplc-installedp st)
                     (len (fn-bplc-retiring st)) (len (fn-bplc-staged st)))))))

; A failed primitive can never permit another acceptance or claim an
; installed runtime; the durable target survives for recovery evidence.
(defthm fn-bplc-failed-completion-fences-without-rollback
  (implies
   (and (member-equal (fn-ag-car (fn-bplc-action st)) '(:bind :install :retire))
        (equal (fn-ag-car event)
               (case (fn-ag-car (fn-bplc-action st))
                 (:bind :bind-result) (:install :install-result)
                 (:retire :retire-result)))
        (not (equal (fn-ag-car (fn-ag-cdr event)) :ok)))
   (let ((next (fn-bplc-step st event)))
     (and (equal (fn-bplc-phase next) :fenced)
          (not (fn-bplc-action next))
          (equal (fn-bplc-target-generation next) (fn-bplc-target-generation st))
          (equal (fn-bplc-target-ports next) (fn-bplc-target-ports st))
          (equal (fn-bplc-generation next) (fn-bplc-generation st)))))
  :hints (("Goal" :in-theory (enable fn-bplc-step fn-bplc-action fn-bplc-with-phase)))
  :rule-classes nil)

; Installation cannot occur until every requested added listener completed.
; Its generation and set come from the carried actual configuration target.
(defthm fn-bplc-installed-runtime-is-the-completed-target
  (implies (and (equal (fn-bplc-phase st) :binding)
                (not (consp (fn-bplc-pending st))))
           (let ((next (fn-bplc-step st '(:install-result :ok))))
             (and (equal (fn-bplc-generation next) (fn-bplc-target-generation st))
                  (equal (fn-bplc-ports next) (fn-bplc-target-ports st))
                  (equal (fn-bplc-phase next)
                         (if (consp (fn-bplc-retiring st)) :retiring :stable)))))
  :hints (("Goal" :in-theory (enable fn-bplc-step)))
  :rule-classes nil)

(defun fn-bplc-creditp (st)
  (declare (xargs :guard t))
  (and (natp (fn-bplc-descriptors st)) (natp (fn-bplc-peak st))
       (<= (fn-bplc-descriptors st) (fn-bplc-peak st))))

(defthm fn-bplc-step-preserves-listener-credit
  (implies (fn-bplc-creditp st) (fn-bplc-creditp (fn-bplc-step st event)))
  :hints (("Goal" :in-theory (enable fn-bplc-creditp fn-bplc-step fn-bplc-with-phase fn-bplc-with-session fn-bplc-crash)))
  :rule-classes nil)

(defthm fn-bplc-bind-and-retire-account-exact-descriptor-completions
  (implies (natp (fn-bplc-descriptors st))
    (and
     (implies (and (equal (fn-bplc-phase st) :binding)
                   (consp (fn-bplc-pending st)))
              (equal (fn-bplc-descriptors (fn-bplc-step st '(:bind-start)))
                     (+ 1 (fn-bplc-descriptors st))))
     (implies (and (equal (fn-bplc-phase st) :retiring)
                   (consp (fn-bplc-retiring st)))
              (equal (fn-bplc-descriptors (fn-bplc-step st '(:retire-result :ok)))
                     (nfix (- (fn-bplc-descriptors st) 1))))))
  :hints (("Goal" :in-theory (enable fn-bplc-step)))
  :rule-classes nil)

(defthm fn-bplc-grant-is-the-authorized-bp-configuration-plan
  (let ((r (fn-bplc-turn-plan ownerp admin cfg st)))
    (implies (equal (fn-ncfg-nth 0 r) :execute)
      (and (equal ownerp t) (equal (fn-ncfg-nth 0 admin) :admin)
           (equal (fn-ncfg-nth 1 r) (fn-native-admin-plan (fn-ncfg-nth 1 admin)))
           (equal (fn-native-admin-result-status (fn-ncfg-nth 1 r)) :accepted)
           (or (member-equal (fn-native-admin-result-kind (fn-ncfg-nth 1 r))
                             '(:set-bp-route :remove-bp-route :set-bp-boundary))
               (and (equal (fn-native-admin-result-kind (fn-ncfg-nth 1 r)) :remove-peer)
                    (equal (fn-ag-car
                             (fn-cfg-peer-transport
                              (fn-cfg-peer-find
                               (fn-record-octets-string
                                (fn-native-admin-result-name (fn-ncfg-nth 1 r)))
                               (fn-cfg-peers (fn-cfg-value cfg))))) :bp))))))
  :hints (("Goal" :use ((:instance fn-bpnc-grant-is-the-authorized-route-plan))
           :in-theory (e/d (fn-bplc-turn-plan fn-ncfg-nth)
                            (fn-bpnc-turn-plan fn-native-admin-plan
                             fn-native-admin-result-kind fn-native-admin-result-status
                             fn-native-admin-result-name fn-record-octets-string
                             fn-cfg-peer-find fn-cfg-peer-transport fn-cfg-peers
                             fn-cfg-value))))
  :rule-classes nil)

(defthm fn-bplc-rebind-retains-the-accepted-session-generation
  (implies (not (member-equal (fn-ag-car event)
                              '(:accept-result :session-closed :crash)))
           (equal (fn-bplc-session (fn-bplc-step st event)) (fn-bplc-session st)))
  :hints (("Goal" :in-theory (enable fn-bplc-step fn-bplc-with-phase)))
  :rule-classes nil)

(defun fn-bplc-runtime-line (st)
  (declare (xargs :guard t))
  (string-append "BP NODE GENERATION "
   (string-append (fn-acct-decimal-text (fn-bplc-generation st))
    (string-append " LISTENER-FDS "
     (string-append (fn-acct-decimal-text (fn-bplc-descriptors st))
      (string-append " PEAK "
       (string-append (fn-acct-decimal-text (fn-bplc-peak st))
        (string-append " SESSION "
         (if (fn-bplc-session st)
             (fn-acct-decimal-text (fn-ncfg-nth 1 (fn-bplc-session st))) "none")))))))))

(defconst *fn-bplc-death-cuts*
  '(:configuration-published :before-bind :after-bind :before-install
    :after-install :before-retire :after-retire))

(defun fn-bplc-cut-plan (st selector cut)
  (declare (xargs :guard t))
  (let ((name (case cut
                (:configuration-published "configuration-published")
                (:before-bind "before-bind") (:after-bind "after-bind")
                (:before-install "before-install") (:after-install "after-install")
                (:before-retire "before-retire") (:after-retire "after-retire"))))
    (and name (equal selector (fn-record-string-octets name))
         (case cut
           (:configuration-published (equal (fn-bplc-phase st) :binding))
           (:before-bind (equal (fn-ag-car (fn-bplc-action st)) :bind))
           (:after-bind (equal (fn-bplc-phase st) :binding))
           (:before-install (equal (fn-ag-car (fn-bplc-action st)) :install))
           ((:after-install :after-retire)
            (and (fn-bplc-installedp st) (member-equal (fn-bplc-phase st) '(:retiring :stable))))
           (:before-retire (equal (fn-ag-car (fn-bplc-action st)) :retire)))
         (list :hold (string-append "BP LISTENER CUT " name) (fn-bplc-step st '(:crash))))))

(defthm fn-bplc-every-death-cut-is-a-fenced-process-crash
  (implies (fn-bplc-cut-plan st selector cut)
           (let ((crashed (fn-ncfg-nth 2 (fn-bplc-cut-plan st selector cut))))
             (and (equal (fn-bplc-phase crashed) :crashed)
                  (not (fn-bplc-action crashed)) (not (fn-bplc-session crashed))
                  (equal (fn-bplc-target-generation crashed) (fn-bplc-target-generation st)))))
  :hints (("Goal" :in-theory (enable fn-bplc-cut-plan fn-bplc-step fn-bplc-with-phase
                                    fn-bplc-with-session fn-bplc-crash fn-bplc-action fn-ncfg-nth)))
  :rule-classes nil)

(in-theory (disable fn-bplc-configured-ports fn-bplc-minus fn-bplc-recover
                    fn-bplc-begin fn-bplc-action fn-bplc-step fn-bplc-accountedp))
