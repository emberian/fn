; Actual listener installation/authority machine teeth.  No socket mock is
; promoted to a native claim; native occupied-port/restart is SCN-1001.
(in-package "ACL2")
(include-book "../../books/bp-node-listener-control")
(defun bplc-rows (port)
  (list (fn-cfg-row-make "sender" "path-identity" "sender.invalid" 0)
        (fn-cfg-row-make "sender" "auth-principal" "bp-only-no-nntp-principal" 0)
        (fn-cfg-row-make "sender" "transport-bp" "dtn://sender/" 0)
        (fn-cfg-row-make "sender" "bp-trust" "network" 0)
        (fn-cfg-row-make "sender" "bp-boundary-listener" "127.0.0.1" port)
        (fn-cfg-row-make "sender" "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make "sender" "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make "sender" "bp-boundary-originators" "all-co-resident" 0)))
(defun bplc-cfg (generation port)
  (fn-cfg-make generation (fn-cfg-value-make nil 0 nil nil nil (bplc-rows port) nil nil nil nil)))
(defconst *bplc-old-cfg* (bplc-cfg 9 4101))
(defconst *bplc-new-cfg* (bplc-cfg 10 4102))
(defconst *bplc-cold* (fn-bplc-recover :boundaries *bplc-old-cfg*))
(defconst *bplc-prepared* (fn-bplc-step *bplc-cold* '(:bind-start)))
(defconst *bplc-bound* (fn-bplc-step *bplc-prepared* '(:bind-result :ok)))
(defconst *bplc-live* (fn-bplc-step *bplc-bound* '(:install-result :ok)))
(defconst *bplc-session* (fn-bplc-step *bplc-live* '(:accept-result 0 :ok)))
(defconst *bplc-changing* (fn-bplc-begin *bplc-session* :boundaries *bplc-new-cfg*))
(defconst *bplc-change-prepared* (fn-bplc-step *bplc-changing* '(:bind-start)))
(defconst *bplc-new-bound* (fn-bplc-step *bplc-change-prepared* '(:bind-result :ok)))
(defconst *bplc-installed* (fn-bplc-step *bplc-new-bound* '(:install-result :ok)))
(defconst *bplc-new-live* (fn-bplc-step *bplc-installed* '(:retire-result :ok)))

; Refinement positive: complete antecedent and conclusion.
(assert-event (and (fn-cfgp *bplc-new-cfg*)
                  (equal (fn-bplc-owner-listener-ports *bplc-new-cfg*)
                         (fn-bpaj-listener-ports *bplc-new-cfg*))))
; Corrupted-state hypothesis removal: negative generation, retained rows.
(assert-event (let ((cfg (bplc-cfg -1 4102)))
                (and (not (fn-cfgp cfg))
                     (not (equal (fn-bplc-owner-listener-ports cfg)
                                 (fn-bpaj-listener-ports cfg))))))
(assert-event
 (and (equal (fn-bplc-action *bplc-changing*) '(:prepare-bind 4102))
      (equal (fn-bplc-generation *bplc-changing*) 9)
      (equal (fn-bplc-target-generation *bplc-changing*) 10)
      (equal (fn-bplc-session *bplc-changing*) '(:accept 9 4101))
      (not (fn-bplc-accept-plan *bplc-changing* 0))))

; Failure theorem positive for every primitive branch, all literal clauses.
(assert-event
 (let ((s *bplc-change-prepared*) (e '(:bind-result :failed)))
   (and (member-equal (fn-ag-car (fn-bplc-action s)) '(:bind :install :retire))
        (equal (fn-ag-car e) (case (fn-ag-car (fn-bplc-action s))
                               (:bind :bind-result) (:install :install-result) (:retire :retire-result)))
        (not (equal (fn-ag-car (fn-ag-cdr e)) :ok))
        (let ((n (fn-bplc-step s e)))
          (and (equal (fn-bplc-phase n) :fenced) (not (fn-bplc-action n))
               (equal (fn-bplc-target-generation n) (fn-bplc-target-generation s))
               (equal (fn-bplc-target-ports n) (fn-bplc-target-ports s))
               (equal (fn-bplc-generation n) (fn-bplc-generation s)))))))
(assert-event
 (let ((s *bplc-new-bound*) (e '(:install-result :failed)))
   (and (equal (fn-bplc-action s) '(:install 10 (4102)))
        (not (equal (fn-ag-car (fn-ag-cdr e)) :ok))
        (let ((n (fn-bplc-step s e)))
          (and (equal (fn-bplc-phase n) :fenced) (not (fn-bplc-action n))
               (equal (fn-bplc-target-generation n) (fn-bplc-target-generation s))
               (equal (fn-bplc-target-ports n) (fn-bplc-target-ports s))
               (equal (fn-bplc-generation n) (fn-bplc-generation s)))))))
(assert-event
 (let ((s *bplc-installed*) (e '(:retire-result :failed)))
   (and (equal (fn-bplc-action s) '(:retire 4101))
        (not (equal (fn-ag-car (fn-ag-cdr e)) :ok))
        (let ((n (fn-bplc-step s e)))
          (and (equal (fn-bplc-phase n) :fenced) (not (fn-bplc-action n))
               (equal (fn-bplc-target-generation n) (fn-bplc-target-generation s))
               (equal (fn-bplc-target-ports n) (fn-bplc-target-ports s))
               (equal (fn-bplc-generation n) (fn-bplc-generation s)))))))
; Omit issued-action membership; other failure antecedents retained.
(assert-event
 (let* ((s (fn-bplc-step *bplc-live* '(:crash))) (e nil))
   (and (not (member-equal (fn-ag-car (fn-bplc-action s)) '(:bind :install :retire)))
        (equal (fn-ag-car e) (case (fn-ag-car (fn-bplc-action s))
                               (:bind :bind-result) (:install :install-result) (:retire :retire-result)))
        (not (equal (fn-ag-car (fn-ag-cdr e)) :ok))
        (not (equal (fn-bplc-phase (fn-bplc-step s e)) :fenced)))))
; Omit event-kind matching: admitted bind action and failed outcome retained.
(assert-event
 (and (member-equal (fn-ag-car (fn-bplc-action *bplc-change-prepared*)) '(:bind :install :retire))
      (not (equal :retire-result :bind-result)) (not (equal :failed :ok))
      (not (equal (fn-bplc-phase (fn-bplc-step *bplc-change-prepared* '(:retire-result :failed))) :fenced))))
; Omit failed-outcome: both other literal antecedents retained.
(assert-event
 (and (member-equal (fn-ag-car (fn-bplc-action *bplc-change-prepared*)) '(:bind :install :retire))
      (equal :bind-result :bind-result) (not (not (equal :ok :ok)))
      (not (equal (fn-bplc-phase *bplc-new-bound*) :fenced))))

; Installation theorem: both antecedents, all three conclusions.
(assert-event
 (and (equal (fn-bplc-phase *bplc-new-bound*) :binding)
      (not (consp (fn-bplc-pending *bplc-new-bound*)))
      (equal (fn-bplc-generation *bplc-installed*) (fn-bplc-target-generation *bplc-new-bound*))
      (equal (fn-bplc-ports *bplc-installed*) (fn-bplc-target-ports *bplc-new-bound*))
      (equal (fn-bplc-phase *bplc-installed*)
             (if (consp (fn-bplc-retiring *bplc-new-bound*)) :retiring :stable))))
; Omit drained pending queue: retain binding phase, installation cannot run.
(assert-event
 (and (equal (fn-bplc-phase *bplc-changing*) :binding)
      (not (not (consp (fn-bplc-pending *bplc-changing*))))
      (not (equal (fn-bplc-generation (fn-bplc-step *bplc-changing* '(:install-result :ok)))
                  (fn-bplc-target-generation *bplc-changing*)))))
 ; Omit binding phase: install failure leaves a reachable fenced state;
; the empty pending queue is retained but the target was never installed.
(assert-event
 (let ((s (fn-bplc-step *bplc-new-bound* '(:install-result :failed))))
   (and (not (equal (fn-bplc-phase s) :binding))
        (not (consp (fn-bplc-pending s)))
        (not (equal (fn-bplc-generation (fn-bplc-step s '(:install-result :ok)))
                    (fn-bplc-target-generation s))))))

; Resource accounting asserts transient peak, decrement and invariant.
(assert-event
 (and (natp (fn-bplc-descriptors *bplc-changing*))
      (equal (fn-bplc-phase *bplc-changing*) :binding)
      (consp (fn-bplc-pending *bplc-changing*))
      (natp (fn-bplc-descriptors *bplc-installed*))
      (equal (fn-bplc-phase *bplc-installed*) :retiring)
      (consp (fn-bplc-retiring *bplc-installed*))
      (fn-bplc-creditp *bplc-changing*) (fn-bplc-creditp *bplc-new-bound*)
      (fn-bplc-creditp *bplc-installed*) (fn-bplc-creditp *bplc-new-live*)
      (equal (fn-bplc-descriptors *bplc-change-prepared*) (+ 1 (fn-bplc-descriptors *bplc-changing*)))
      (equal (fn-bplc-descriptors *bplc-new-live*) (nfix (- (fn-bplc-descriptors *bplc-installed*) 1)))
      (equal (fn-bplc-descriptors *bplc-new-live*) 1) (equal (fn-bplc-peak *bplc-new-live*) 2)
      (fn-bplc-accountedp *bplc-new-bound*) (fn-bplc-accountedp *bplc-new-live*)))
; Corrupted-credit witness removes creditp, unchanged event leaves it false.
(assert-event
 (let ((s (fn-bplc-make :stable 9 '(4101) 9 '(4101) nil nil nil 1 0 t nil)))
   (and (not (fn-bplc-creditp s)) (not (fn-bplc-creditp (fn-bplc-step s nil))))))
; Corrupted-count witness: all binding branch conditions retained; omitting
; natp changes the +1 conclusion (negative owned descriptor is not real).
(assert-event
 (let ((s (fn-bplc-make :binding 9 '(4101) 10 '(4102) '(4102) nil '(4101) -1 0 nil nil)))
   (and (not (natp (fn-bplc-descriptors s))) (equal (fn-bplc-phase s) :binding)
        (consp (fn-bplc-pending s))
        (not (equal (fn-bplc-descriptors (fn-bplc-step s '(:bind-start)))
                    (+ 1 (fn-bplc-descriptors s)))))))

; Session pin retained by the actual rebind step, including old-generation
; provenance after installation of generation 10.  Revocation still uses
; the current owner cfg at each application authorization.
(assert-event
 (and (not (member-equal :install-result '(:accept-result :session-closed :crash)))
      (equal (fn-bplc-session *bplc-installed*) (fn-bplc-session *bplc-new-bound*))
      (equal (fn-bplc-session *bplc-new-live*) '(:accept 9 4101))
      (not (fn-bplc-accept-plan *bplc-new-live* 0))))
; Remove event exclusion: a real close must clear the accepted session.
(assert-event
 (and (not (not (member-equal :session-closed '(:accept-result :session-closed :crash))))
      (not (equal (fn-bplc-session (fn-bplc-step *bplc-new-live* '(:session-closed)))
                  (fn-bplc-session *bplc-new-live*)))))
; Every listener process-death cut is the same explicit crash transition;
; cold reconciliation ignores ephemeral ownership and derives persisted cfg.
(assert-event
 (let ((crashed (fn-bplc-step *bplc-installed* '(:crash))))
   (and (equal (fn-bplc-phase crashed) :crashed) (not (fn-bplc-action crashed))
        (not (fn-bplc-session crashed))
        (equal (fn-bplc-descriptors crashed) 0)
        (equal (fn-bplc-target-generation (fn-bplc-recover :boundaries *bplc-new-cfg*)) 10)
        (equal (fn-bplc-action (fn-bplc-recover :boundaries *bplc-new-cfg*)) '(:prepare-bind 4102)))))

(defun bplc-words (words)
  (if (consp words) (cons (fn-record-string-octets (car words)) (bplc-words (cdr words))) nil))
(defconst *bplc-boundary-admin*
  (list :admin (bplc-words '("bp-boundary" "add" "sender" "sender.invalid" "dtn://sender/" "4102"))))
(defconst *bplc-boundary-grant*
  (fn-bplc-turn-plan t *bplc-boundary-admin* *bplc-old-cfg* *bplc-live*))
; Authority theorem complete antecedent and all conclusion literals.
(assert-event
 (let ((r *bplc-boundary-grant*) (admin *bplc-boundary-admin*) (cfg *bplc-old-cfg*))
   (and (equal (fn-ncfg-nth 0 r) :execute) (equal t t)
        (equal (fn-ncfg-nth 0 admin) :admin)
        (equal (fn-ncfg-nth 1 r) (fn-native-admin-plan (fn-ncfg-nth 1 admin)))
        (equal (fn-native-admin-result-status (fn-ncfg-nth 1 r)) :accepted)
        (or (member-equal (fn-native-admin-result-kind (fn-ncfg-nth 1 r))
                          '(:set-bp-route :remove-bp-route :set-bp-boundary))
            (and (equal (fn-native-admin-result-kind (fn-ncfg-nth 1 r)) :remove-peer)
                 (equal (fn-ag-car (fn-cfg-peer-transport
                                    (fn-cfg-peer-find
                                     (fn-record-octets-string (fn-native-admin-result-name (fn-ncfg-nth 1 r)))
                                     (fn-cfg-peers (fn-cfg-value cfg))))) :bp))))))
; Remove :execute: parsed accepted admin retained, nonowner conclusion false.
(assert-event
 (and (equal (fn-ncfg-nth 0 *bplc-boundary-admin*) :admin)
      (equal (fn-native-admin-result-status (fn-native-admin-plan (fn-ncfg-nth 1 *bplc-boundary-admin*))) :accepted)
      (not (equal nil t))
      (not (equal (fn-ncfg-nth 0 (fn-bplc-turn-plan nil *bplc-boundary-admin* *bplc-old-cfg* *bplc-live*)) :execute))))
; Mutation teeth: direct generic peer mutation cannot cross the BP surface.
(assert-event
 (let ((admin (list :admin (bplc-words '("peer" "remove" "sender")))))
   (and (equal (fn-ncfg-nth 0 (fn-bplc-turn-plan t admin *bplc-old-cfg* *bplc-live*)) :execute)
        (not (equal (fn-ncfg-nth 0 (fn-bplc-turn-plan t admin (fn-cfg-make 9 (fn-cfg-value-make nil 0 nil nil nil nil nil nil nil nil)) *bplc-live*)) :execute)))))
; Every named physical cut has a positive complete modeled-crash witness.
(assert-event
 (let* ((s *bplc-new-bound*) (selector (fn-record-string-octets "before-install"))
        (r (fn-bplc-cut-plan s selector :before-install)) (crashed (fn-ncfg-nth 2 r)))
   (and r (equal (fn-bplc-phase crashed) :crashed)
        (not (fn-bplc-action crashed)) (not (fn-bplc-session crashed))
        (equal (fn-bplc-target-generation crashed) (fn-bplc-target-generation s)))))
(assert-event
 (and (fn-bplc-cut-plan *bplc-changing* (fn-record-string-octets "configuration-published") :configuration-published)
      (fn-bplc-cut-plan *bplc-change-prepared* (fn-record-string-octets "before-bind") :before-bind)
      (fn-bplc-cut-plan *bplc-new-bound* (fn-record-string-octets "after-bind") :after-bind)
      (fn-bplc-cut-plan *bplc-installed* (fn-record-string-octets "after-install") :after-install)
      (fn-bplc-cut-plan *bplc-installed* (fn-record-string-octets "before-retire") :before-retire)
      (fn-bplc-cut-plan *bplc-new-live* (fn-record-string-octets "after-retire") :after-retire)))
; Remove admitted cut: retained generation exists, but there is no crash
; conclusion for a wrong selector or a site not reached in this phase.
(assert-event
 (let ((r (fn-bplc-cut-plan *bplc-changing* (fn-record-string-octets "before-install") :before-install)))
   (and (not r) (not (equal (fn-bplc-phase (fn-ncfg-nth 2 r)) :crashed)))))
