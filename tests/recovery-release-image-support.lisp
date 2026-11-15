; The producer side uses the canonical crash simulator. At the exact actual
; RELEASE begin boundary this adapter view reads only the selected descriptor
; sector from that image, then uses the ordinary core/outbox/result harness.
; It invents no disk bytes, digest, selected authority or completion flag.
(in-package "ACL2")
(include-book "../sim/check-recovery")
(include-book "recovery-release-dispatch-support")
(include-book "std/util/bstar" :dir :system)

(defun fn2-rrd-image-bytes (address left fn2-sim-storage)
 (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)))
 (if (zp left) nil
  (cons (fn2-sim-storage-pending address fn2-sim-storage)
        (fn2-rrd-image-bytes (+ 1 address) (- left 1) fn2-sim-storage))))

(defun fn2-rrd-image-packet (fuel id fault fn2-core fn2-sim)
 (declare (xargs :stobjs (fn2-core fn2-sim) :verify-guards nil))
 (b* ((ogen (fn2-machine-generation id fn2-core))
      ((unless (and (= (fn2-machine-rc-stage id fn2-core) 11)
                    (fn2-rp-release-current-p id ogen fn2-core)
                    (fn2-rp-release-installation-metadata-p fn2-core)))
       (mv '(:missing-image-antecedent) fn2-core))
      (address (stobj-let ((fn2-allocation-release (fn2-core-allocation-release fn2-core))) (address)
                  (* (fn2-allocation-release-read-unit 0 fn2-allocation-release)
                     *fn2-commit-unit-bytes*) address))
      ((mv fits bytes)
       (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim))) (fits bytes)
        (if (<= (+ address *fn2-commit-unit-bytes*) (fn2-sim-storage-rows fn2-sim-storage))
            (mv t (fn2-rrd-image-bytes address *fn2-commit-unit-bytes* fn2-sim-storage))
          (mv nil nil)) (mv fits bytes)))
      ((unless fits) (mv '(:missing-image-sector) fn2-core))
      ((mv result & fn2-core)
       (fn2-rrd-packet fuel id fault (list (cons address bytes)) fn2-core)))
  (mv result fn2-core)))
