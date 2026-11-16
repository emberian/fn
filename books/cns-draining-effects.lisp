; Independent application effects lifted through the actual served core
; faces. The original counted CNS obligation keeps its full antecedent.
(in-package "ACL2")
(include-book "cns-release-accounting")
(include-book "cns-draining-contract")
(include-book "machine-reservations")

; This is the actual read-only preflight called before any relevant release.
(defthm fn2-cns-query-held-independent
  (implies (and (fn2-corep core) (fn2-core-wfp core))
           (equal (fn2-cns-query-heldp slot gen core)
                  (fn2-cns-drain-query-heldp slot gen (fn2-core-pool core))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'fn2-cns-pool-readers)
            (e/d (fn2-cns-query-heldp fn2-core-query-heldp fn2-pool-query-heldp
                  fn2-cns-drain-query-heldp
                  fn2-pool-rows fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index)
                 (fn2-core-pool fn2-corep fn2-core-wfp))))))

(defthm fn2-cns-reservation-native-by-definition
  (equal (fn2-cns-draining-reservedp core)
         (fn2-machines-partition-reservedp *fn2-cns-admission-ordinal*
                                         (fn2-core-machines core)))
  :hints (("Goal" :in-theory
           (enable fn2-cns-draining-reservedp fn2-cns-drain-child
             fn2-cns-drain-child-index fn2-cns-drain-cell fn2-cns-drain-get
             fn2-cns-drain-index fn2-machines-partition-reservedp
             fn2-machines-reservation-valuesp fn2-machines-reservation-view
             fn2-machines-active-counti fn2-machines-admission-creditsi
             fn2-machines-connection-counti fn2-core-machines))))

(defthm fn2-cns-draining-domain-snapshot-by-definition
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-draining-domainp id core))
           (equal (fn2-cns-snapshot-read-code id core) :ok))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory
           (e/d (fn2-cns-draining-domainp fn2-cns-snapshot-read-code
                 fn2-machine-phase-read-code fn2-machine-idp
                 fn2-machine-kind fn2-machine-kind-read-code
                 fn2-machine-slot fn2-machine-slot-read-code
                 fn2-machines-kind fn2-machines-slot fn2-machines-rows fn2-cns-rows
                 fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index)
                (fn2-cns-drain-releasablep fn2-core-machines fn2-cns-table
                 fn2-core-pool fn2-core-control fn2-core-sched fn2-corep fn2-core-wfp)))))

; Normalize only the row readers the actual public run/draining bodies
; call. Other arms and their columns stay outside the proof's open theory.
(defun fn2-cns-draining-row-projection-events (columns calls readers)
  (declare (xargs :verify-guards nil))
  (if (atom columns)
      `((deftheory fn2-cns-draining-native-readers ',(reverse readers)))
    (let* ((field (caar columns)) (reader (fn2-machine-row-reader 'fn2-cns field))
           (directoryp (fn2-machine-directory-fieldp field))
           (native (fn2-columns-col-name (if directoryp 'fn2-machines 'fn2-cns) field))
           (table (if directoryp 'fn2-core-machines 'fn2-cns-table))
           (index (if directoryp 'id '(fn2-machine-slot id fn2-core))))
      (if (not (member-eq reader calls))
          (fn2-cns-draining-row-projection-events (cdr columns) calls readers)
        (cons
         `(defthm ,(fn2-columns-sym reader "-BY-DEFINITION")
            (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                          (equal (fn2-cns-snapshot-read-code id fn2-core) :ok))
                     (equal (,reader id fn2-core) (,native ,index (,table fn2-core))))
            :hints (("Goal" :use fn2-cns-row-access-valid
                     :in-theory
                     (e/d (,reader)
                          (fn2-cns-snapshot-read-code fn2-machine-slot ,native ,table
                           fn2-machines-rows fn2-corep fn2-core-wfp)))))
         (fn2-cns-draining-row-projection-events (cdr columns) calls (cons native readers)))))))
(make-event
 (let* ((world (w state))
        (run (getpropc 'fn2-cns-run 'unnormalized-body nil world))
        (drain (getpropc 'fn2-cns-run-draining 'unnormalized-body nil world)))
   (if (or (not run) (not drain))
       (er soft 'fn2-cns-draining-row-projection-events "Actual CNS run bodies are missing.")
     (value (cons 'progn
       (fn2-cns-draining-row-projection-events (fn2-machine-property 'fn2-cns :columns world)
         (union-eq (all-fnnames run) (all-fnnames drain)) nil))))))

(defun fn2-cns-core-reclaim-expected (id ord retire before)
  (fn2-cns-drain-put-child 'fn2-machines
    (car (fn2-machines-reclaim-list-expected id ord retire
           (fn2-cns-drain-child 'fn2-machines before) nil)) before))
(defthm fn2-cns-core-reclaim-independent
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-machines-partition-reservedp ord (fn2-core-machines core))
                (< 0 (fn2-machines-active-counti ord (fn2-core-machines core)))
                (unsigned-byte-p 32 id))
    (equal (fn2-cns-reclaim id ord retire core)
           (fn2-cns-core-reclaim-expected id ord retire core)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-machines-reserved-reclaim-independent
                            (machines (fn2-core-machines core))
                            (control (fn2-core-control core)))
                 (:instance fn2-product-core-shape (fn2-core core)))
           :in-theory
           (e/d (fn2-cns-reclaim fn2-cns-core-reclaim-expected fn2-machines-reclaim-list-expected)
                (fn2-machines-reclaim fn2-machines-reservation-put
                 fn2-core-machines fn2-core-control update-fn2-core-machines update-fn2-core-control
                 fn2-corep fn2-core-wfp fn2-machines-partition-reservedp)))))

(defthm fn2-cns-core-reclaim-reservation-preserved
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-draining-reservedp core)
                (< 0 (fn2-machines-active-counti *fn2-cns-admission-ordinal*
                                                (fn2-core-machines core)))
                (unsigned-byte-p 32 id))
    (fn2-cns-draining-reservedp
      (fn2-cns-reclaim id *fn2-cns-admission-ordinal* retire core)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-cns-core-reclaim-independent (ord *fn2-cns-admission-ordinal*))
                 (:instance fn2-machines-reserved-reclaim-preserved
                            (ord *fn2-cns-admission-ordinal*)
                            (machines (fn2-core-machines core)) (control (fn2-core-control core)))
                 (:instance fn2-machines-reserved-reclaim-independent
                            (ord *fn2-cns-admission-ordinal*)
                            (machines (fn2-core-machines core)) (control (fn2-core-control core))))
           :in-theory
           (e/d (fn2-cns-core-reclaim-expected fn2-machines-reclaim-list-expected)
                (fn2-cns-reclaim fn2-machines-reclaim fn2-machines-reservation-put
                 fn2-cns-draining-reservedp fn2-machines-partition-reservedp
                 fn2-core-machines fn2-core-control)))))

(defthm fn2-cns-release-ns-independent-by-definition
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core)))
    (equal (fn2-cns-release-ns slot gen *fn2-cns-kind* id ogen core)
           (fn2-cns-core-release-expected slot gen *fn2-cns-kind* id ogen core)))
  :rule-classes nil
  :hints (("Goal" :use fn2-cns-core-release-independent
           :in-theory (e/d (fn2-cns-release-ns) (fn2-core-release)))))
(defthm fn2-cns-lease-release-is-core-release-by-definition
  (equal (fn2-cns-lease-release slot gen kind id ogen core)
         (fn2-core-release slot gen kind id ogen core))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn2-cns-lease-release fn2-core-release)
                (fn2-core-release-children fn2-core-pool fn2-core-control
                 update-fn2-core-pool update-fn2-core-control)))))
