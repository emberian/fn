; Actual actor return tuples on terminal paths. These accepted-input controls
; do not establish physical-work counting or authenticated-client reachability.
(in-package "ACL2")
(include-book "cns-article-slice-unit")

(defun fn2-cta-drive (fuel id held bound fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv nil fn2-core)
  (b* (((mv bytes steps descriptors & fn2-core) (fn2-cns-run id 4 fn2-core))
       (terminal (if held
                     (equal (fn2-cns-row-lease id fn2-core) *fn2-cns-lease-none*)
                   (equal (fn2-cns-row-phase id fn2-core) *fn2-cns-state-draining*))))
   (if terminal
       (mv (and (equal bytes (+ bound (if held 0 512)))
                (natp steps) (<= steps 32) (equal descriptors 0)
                (not (fn2-core-stopped-p fn2-core))) fn2-core)
    (fn2-cta-drive (1- fuel) id held bound fn2-core)))))
(defun fn2-cta-body (mode held fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv setup id gen x fn2-core) (fn2-cas-setup fn2-core))
      ((unless setup) (mv nil fn2-core))
      ; End is an actual scan past the last fixture key. Missing FETCH is an
      ; actual XL absent result followed by the unchanged FETCH item policy.
      (fn2-core (cond ((eq mode :end) (fn2-cns-put-core id (ipos 100)))
                      ((eq mode :missing-fetch)
                       (fn2-cns-put-core id (verb *fn2-cns-verb-fetch*) (to 100)))
                      (t fn2-core)))
      ((mv selected fn2-core)
       (if (eq mode :missing-fetch)
           (fn2-cas-to-phase 300 id *fn2-cns-state-article* fn2-core)
         (mv t fn2-core)))
      ((unless selected) (mv nil fn2-core))
      ((mv reserved slot slotgen fn2-core)
       (if held
           (let ((class (fn2-cns-lease-class fn2-core)))
            (if class (fn2-core-reserve class *fn2-cns-kind* id gen fn2-core)
              (mv :bounds *fn2-none* 0 fn2-core)))
         (mv :ok *fn2-none* 0 fn2-core)))
      ((unless (eq reserved :ok)) (mv nil fn2-core))
      (fn2-core (if held
                    (fn2-cns-put-core id (lease *fn2-cns-lease-held*) (lslot slot) (lgen slotgen))
                  fn2-core))
      ; A bounded START failure after the real actor admission. No read
      ; result, cursor phase or :more word is supplied by this control.
      (fn2-core (if (eq mode :fault)
                    (stobj-let ((fn2-fields (fn2-core-fields fn2-core))) (fn2-fields)
                     (fn2-fields-init 1 fn2-fields) fn2-core)
                  fn2-core))
      (bound (if (eq mode :missing-fetch) *fn2-cns-article-next-pool-work-bound*
               *fn2-cns-addr-next-1-pool-read-bound*))
      ((mv charged fn2-core) (fn2-cta-drive 300 id held bound fn2-core))
      (idle (fn2-cas-read-idlep x fn2-core))
      ((mv old-slot fn2-core)
       (if held (fn2-core-write slot slotgen 0 1 *fn2-cns-kind* id gen fn2-core)
         (mv :stale fn2-core))))
  (mv (and charged idle (not (eq old-slot :ok))) fn2-core)))
(defun fn2-cns-terminal-accounting-control (mode held)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (yes fn2-core) (fn2-cta-body mode held fn2-core) yes)))
(assert-event (and (fn2-cns-terminal-accounting-control :end t)
                   (fn2-cns-terminal-accounting-control :end nil)
                   (fn2-cns-terminal-accounting-control :fault t)
                   (fn2-cns-terminal-accounting-control :fault nil)
                   (fn2-cns-terminal-accounting-control :missing-fetch t)
                   (fn2-cns-terminal-accounting-control :missing-fetch nil)))
