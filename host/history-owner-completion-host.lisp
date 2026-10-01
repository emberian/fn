; Internal serialized dense E completion. Preparation owns every result and
; allowance before persistence. This entry accepts no host completion packet.
; No native declaration/activation until the actual preparation issuer exists.
(in-package "ACL2")
(include-book "owner-host")
(include-book "../books/history-event-backing")

(defun fn-odhc-publication-matches (publication source)
 (declare (xargs :guard t))
 (and (fn-hed-fixedp publication 5)
      (eq (fn-hed-at 0 publication) :history-installed)
      (fn-hep-sourcep source)
      (equal (fn-hed-at 1 publication) (fn-hed-at 1 source))
      (equal (fn-hed-at 2 publication) (fn-hed-at 2 source))
      (equal (fn-hed-at 3 publication) (fn-hed-at 3 source))
      (equal (fn-hed-at 4 publication) (fn-hed-at 8 source))))

 ; Fixed semantic Store template; FILES always comes from the actual
; completing Store, never a simulated successful file state.
(defun fn-odhc-store-from-plan (fields files)
 (declare (xargs :guard t))
 (fn-sn-make-v6 (fn-hed-at 1 fields) (fn-hed-at 2 fields) files
  (fn-hed-at 3 fields) (fn-hed-at 4 fields) (fn-hed-at 5 fields)
  (fn-hed-at 6 fields) (fn-hed-at 7 fields) (fn-hed-at 8 fields)
  (fn-hed-at 9 fields) (fn-hed-at 10 fields) (fn-hed-at 11 fields)
  (fn-hed-at 12 fields) (fn-hed-at 13 fields)))

(defun fn-odhc-owner-current-shell (current store view pair)
 (declare (xargs :guard t))
 (fn-own-make store view (fn-own-conns current)
  (fn-own-next-id current) (fn-own-max-conns current) nil
  (fn-sl-snoc (fn-own-ledger-field current) pair)
  (fn-own-clock current) (fn-own-facts current) (fn-own-config current)
  (fn-own-queue current) (fn-own-inflight current) (fn-own-feeds current)
  (fn-own-node-secret current) (fn-own-refused current)))

(defun fn-owner-history-completion-fence (token reason fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program))
 (mv-let (word fn-history-backing)
  (fn-hep-fence-current token fn-history-backing)
  (declare (ignore word))
  ; Keep the actual Store, candidate and every alias. A durability mismatch
  ; cannot become a refused append followed by new mutation.
  (let ((state (f-put-global 'fn-owner-history-completion-fault reason state)))
   (mv :recovery-required fn-history-backing state))))

(defun fn-owner-history-complete-current (fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program))
 (mv-let (word token txid ready)
  (fn-hep-operation-readout fn-history-backing)
  (cond
   ((not (eq word :operation))
    ; There is no registered preparation. Do not synthesize a completion.
    (mv :unavailable fn-history-backing state))
   ((not (boundp-global 'fn-owner state))
    (fn-owner-history-completion-fence token :owner-absent fn-history-backing state))
   (t
    (let* ((files (fn-sn-files (fn-owner-store state)))
           (epoch (fn-owner-canonical-epoch state))
           (phase (fn-hep-producer-phase fn-history-backing))
           (publication (and (boundp-global 'fn-owner-history-publication state)
                              (f-get-global 'fn-owner-history-publication state)))
           (pair (fn-sf-completion files))
           (plan (fn-hed-at 4 ready))
           (store-fields (fn-hed-at 2 plan))
           (prepared-view (fn-hed-at 3 plan))
           (prepared-config (fn-hed-at 4 plan))
           (next-canonical (fn-hed-at 7 ready))
           (next-publication (fn-hed-at 9 ready)))
     (cond
      ((not (and (fn-hed-fixedp ready 10)
                  (eq (fn-hed-at 0 ready) :history-owner-ready)
                  (natp epoch) (equal epoch (fn-hed-at 1 ready))
                  (natp (fn-hed-at 2 ready)) (natp txid)
                  (fn-hed-fixedp plan 5)
                  (eq (fn-hed-at 0 plan) :history-install-plan)
                  (eq (fn-hed-at 1 plan) :E)
                  (fn-hed-fixedp store-fields 14)
                  (eq (fn-hed-at 0 store-fields) :history-store-fields)
                  (fn-hed-fixedp prepared-view 10)))
       (fn-owner-history-completion-fence token :owner-result-lineage fn-history-backing state))
      ((eq phase :published)
       ; Publication identity is installed with the owner in this same call.
       ; A repeated callback never registers or appends a second event.
       (if (and (eq (fn-sf-phase files) :ready)
                 (equal (fn-sf-records-count files) (+ 1 (fn-hed-at 2 ready)))
                 (equal publication next-publication)
                 (fn-odhc-publication-matches publication (fn-hep-current fn-history-backing)))
        (mv :consumed fn-history-backing state)
        (fn-owner-history-completion-fence token :published-owner-mismatch fn-history-backing state)))
      ((not (and (member-eq phase '(:prepared :completed))
                  (eq (fn-sf-phase files) :completing)
                  (equal (fn-sf-records-count files) (+ 1 (fn-hed-at 2 ready)))
                  (consp pair) (equal pair (fn-hed-at 3 ready))
                  (equal (cdr pair) txid)
                  (fn-odhc-publication-matches publication (fn-hep-current fn-history-backing))
                  (equal (fn-hed-at 7 (fn-hep-current fn-history-backing)) (fn-hed-at 2 ready))
                  (null (fn-ocfg-staged (fn-owner-ocfg state)))
                  (equal (fn-cfg-generation (fn-owner-config state))
                         (fn-cfg-generation prepared-config))
                  ; Actual current FILES, not a saved next-owner snapshot.
                  (fn-hed-fixedp next-canonical 10)
                  (eq (fn-hed-at 0 next-canonical) :ready)
                  (equal (fn-hed-at 1 next-canonical) epoch)
                  (equal (fn-hed-at 2 next-canonical) (fn-sf-records-count files))))
       (fn-owner-history-completion-fence token :durable-completion-mismatch fn-history-backing state))
      (t
       (let* ((receipt (list :history-completion token (cdr pair)))
              (next-files (fn-sf-emit-success
                            (fn-sf-core-completion files (car pair) (cdr pair))
                            (car pair) (cdr pair))))
        (if (not (eq (fn-sf-phase next-files) :ready))
         (fn-owner-history-completion-fence token :actual-file-completion fn-history-backing state)
         (mv-let (registered fn-history-backing)
         (fn-hep-register-completion-internal receipt token fn-history-backing)
         (if (not (member-eq registered '(:completed :already-completed)))
          (fn-owner-history-completion-fence token :completion-registration fn-history-backing state)
          (mv-let (published fn-history-backing)
           (fn-hep-publish-current receipt fn-history-backing)
           (if (not (and (eq published :published)
                          (fn-odhc-publication-matches next-publication (fn-hep-current fn-history-backing))
                          (equal (fn-hed-at 7 (fn-hep-current fn-history-backing))
                                 (fn-sf-records-count next-files))))
            (fn-owner-history-completion-fence token :backing-publication fn-history-backing state)
            ; No replay, projection or obligation recomputation after the
            ; durable boundary. The actual preparer retained these results.
            (let* ((current-oc (fn-owner-ocfg state))
                   (next-store (fn-odhc-store-from-plan store-fields next-files))
                   (next-owner (fn-odhc-owner-current-shell
                                 (fn-ocfg-owner current-oc) next-store prepared-view pair))
                   (next-oc (fn-ocfg-make next-owner prepared-config
                                         (fn-ocfg-pins current-oc) nil))
                   (state (f-put-global 'fn-owner next-oc state))
                   (state (f-put-global 'fn-owner-obligation-view (fn-hed-at 8 ready) state))
                   (state (f-put-global 'fn-owner-account-carries (fn-hed-at 5 ready) state))
                   (state (f-put-global 'fn-owner-account-root-state (fn-hed-at 6 ready) state))
                   (state (f-put-global 'fn-owner-canonical-state next-canonical state))
                   (state (f-put-global 'fn-owner-history-publication next-publication state)))
             (mv :durable fn-history-backing state)))))))))))))))
