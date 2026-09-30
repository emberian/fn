(in-package "ACL2")
(include-book "../../books/bp-node-checkpoint-resources")

(defun fn-bpck-test-transfer (ledger job control source aliases fd)
  (declare (xargs :guard t))
  (mv-let (word next) (fn-bpck-publish-transfer ledger job control source aliases fd)
    (list word next)))
(defun fn-bpck-test-grow (ledger token delta)
  (declare (xargs :guard t))
  (mv-let (word next) (fn-pmn-grow ledger token delta) (list word next)))

; Typed observation teeth: an unexpected word cannot advance an effect.
(assert-event (equal (fn-bpck-io-step '(:open :pending) :trailer-ready)
                     '(:open :pending)))
(assert-event (equal (fn-bpck-io-step '(:barrier :pending) :prefix-end)
                     '(:barrier :pending)))
(assert-event (equal (fn-bpck-io-step '(:prefix :pending) :cancel)
                     '(:close :cancelled)))
(assert-event (equal (fn-bpck-io-step '(:close :cancelled) :ok)
                     '(:done :cancelled)))
(assert-event (equal (fn-bpck-io-step '(:close :pending) :error)
                     '(:fenced :uncertain)))
(assert-event (equal (fn-bpck-io-step '(:fenced :uncertain) :ok)
                     '(:fenced :uncertain)))

; Ambiguous stage creation owes cleanup even if the caller never saw an FD.
(assert-event
 (let* ((job (fn-bpck-begin '(:maintenance 0 7 0) 7 1 8 nil nil 0 0 1000))
        (uncertain (fn-bpck-stage-observation job :ambiguous)))
   (and (equal (fn-bpn-nth 11 uncertain) :uncertain)
        (equal (fn-bpck-cleanup-word uncertain :returned :relinquished :closed
                                     :pending) :uncertain))))

; Actual initial admission, census and growth supply the transfer's row.
; This is a source-algebra witness, not a runtime adequacy/native observation.
(assert-event
 (mv-let (admitted token ledger)
   (fn-pmn-admit (fn-prl-make '(10000 10000 10 10 100)) 7 0 '(100 0 0 1 1))
   (let* ((initial (fn-bpck-begin token 7 1 8 nil nil 0 0 10000))
          (counted (fn-bpck-census-step initial 100)))
     (mv-let (grown ledger1)
       (fn-pmn-grow ledger token (fn-bpck-stage-demand counted))
       (let* ((emitting (fn-bpck-stage-granted counted (list grown token)))
              (published (fn-bpck-stage-observation
                           (fn-bpck-stage-observation emitting :created) :published))
              (disk (+ 46 (fn-bpn-nth 8 published))))
         (mv-let (transferred ledger2)
           (fn-bpck-publish-transfer ledger1 published '(:done :written)
                                     :returned :relinquished :closed)
           (mv-let (released ledger3)
             (fn-bpck-release-action ledger2 published '(:done :written)
                                      :returned :relinquished :closed)
             (and (equal admitted :admitted) (equal grown :grown)
                  (equal (fn-bpn-nth 6 counted) :stage-demand)
                  (fn-bpck-census-invariantp counted)
                  (equal (fn-bpn-nth 8 counted)
                         (len (fn-bpnr-enc (fn-bpn-nth 5 counted) 8)))
                  (equal transferred :transferred) (equal released :released)
                  (equal (fn-prl-nth 1 ledger2) '(100 0 1 1 1))
                  (equal (fn-prl-baseline ledger2) (list 0 disk 0 0 0))
                  (equal (fn-prl-nth 1 ledger3) '(0 0 0 0 1))
                  (equal (fn-prl-baseline ledger3) (list 0 disk 0 0 0))
                  (fn-prl-binding (fn-bpck-installed-key token)
                                  (fn-prl-nth 3 ledger3))
                  (not (fn-prl-binding token (fn-prl-nth 3 ledger3)))
                  (equal (fn-prl-nth 2 ledger3) 1)
                  ; Missing active-action join does not publish or release.
                  (equal (nth 0 (fn-bpck-test-transfer
                                    ledger1 published '(:prefix :pending)
                                    :returned :relinquished :closed)) :pending)
                  (equal (nth 1 (fn-bpck-test-transfer
                                    ledger1 published '(:prefix :pending)
                                    :returned :relinquished :closed)) ledger1)
                  ; Duplicate transfer and generic growth retain the exact row.
                  (equal (nth 0 (fn-bpck-test-transfer
                                    ledger2 published '(:done :written)
                                    :returned :relinquished :closed)) :stale)
                  (equal (nth 1 (fn-bpck-test-grow ledger2 token '(0 1 0 0 0)))
                         ledger2)))))))))

; Foreign Store INITIAL custody removal is a corrupted-role witness, not a
; BP constructor/admission claim. Start with real ordinary3field admission.
(defun fn-bpck-test-foreign-custody (ledger token)
 (declare (xargs :guard t))
 (let* ((bindings (fn-prl-nth 3 ledger))
        (row (cdr (fn-prl-binding token bindings))))
  (fn-prl-build (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger)
   (fn-prl-nth 2 ledger)
   (cons (cons token (list (fn-prl-nth 0 row) (fn-prl-nth 1 row)
                          (fn-prl-nth 2 row) '(:store-initial-custody)))
         (fn-prl-remove token bindings)) (fn-prl-nth 4 ledger))))
(assert-event
 (mv-let (admitted token ledger)
  (fn-pmn-admit (fn-prl-make '(10000 10000 10 10 100)) 7 0 '(100 1000 1 1 1))
  (let* ((counted (fn-bpck-census-step
                  (fn-bpck-begin token 7 1 8 nil nil 0 0 10000) 100))
         (published (fn-bpck-stage-observation
                     (fn-bpck-stage-observation counted :created) :published))
         (foreign (fn-bpck-test-foreign-custody ledger token)))
   (mv-let (refused retained)
    (fn-bpck-publish-transfer foreign published '(:done :written)
                             :returned :relinquished :closed)
    (mv-let (ordinary ordinary-ledger)
     (fn-bpck-publish-transfer ledger published '(:done :written)
                              :returned :relinquished :closed)
     (and (equal admitted :admitted) (equal ordinary :transferred)
          (not (equal ordinary-ledger ledger))
          (equal refused :foreign-initial-custody) (equal retained foreign)))))))
(assert-event
 (mv-let (admitted token ledger)
  (fn-pmn-admit (fn-prl-make '(10000 10000 10 10 100)) 7 0 '(100 0 0 1 1))
  (let* ((job (fn-bpck-begin token 7 1 8 nil nil 0 0 10000))
         (foreign (fn-bpck-test-foreign-custody ledger token)))
   (mv-let (refused retained)
    (fn-bpck-release-action foreign job '(:done :cancelled)
                           :returned :relinquished :closed)
    (mv-let (ordinary ordinary-ledger)
     (fn-bpck-release-action ledger job '(:done :cancelled)
                            :returned :relinquished :closed)
     (and (equal admitted :admitted) (equal ordinary :released)
          (not (equal ordinary-ledger ledger))
          (equal refused :foreign-initial-custody) (equal retained foreign)))))))
