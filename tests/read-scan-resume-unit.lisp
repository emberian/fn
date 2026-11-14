; Exact resume over the served concrete identity evidence scanner. The
; seeded POSTs provide four facts with original occurrence identities.
(in-package "ACL2")
(include-book "read-unit")

(defun fn2-rsr-next (fuel fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel 0 fn2-core)
   (mv-let (c fn2-core) (fn2-read-scan-next 0 256 fn2-core)
     (if (eq c :more) (fn2-rsr-next (- fuel 1) fn2-core)
       (mv-let (vc occurrence)
         (fn2-read-value 0 *fn2-identity-evidence-entry-field-occurrence* fn2-core)
         (mv (if (eq c :entry) vc c) occurrence fn2-core))))))

(defun fn2-rsr-run (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-rdu-profile* :null nil fn2-core))
      ((mv seeded & fn2-core) (fn2-cs-seed-all *fn2-rdu-seeds* 1 fn2-core))
      ((mv wc wslot wgen fn2-core) (fn2-core-reserve 0 200 0 1 fn2-core))
      ((mv start fn2-core) (fn2-read-scan 0 1 wslot wgen 200 0 1 fn2-core))
      ((mv first a fn2-core) (fn2-rsr-next 200 fn2-core))
      ;; The scan saved all nine key fields, including name and digest,
      ;; in concrete query fields backed by its workspace. Restart there.
      ((mv resumed fn2-core) (fn2-read-scan-from 0 1 wslot wgen 200 0 1 fn2-core))
      ((mv second b fn2-core) (fn2-rsr-next 200 fn2-core))
      ((mv third c fn2-core) (fn2-rsr-next 200 fn2-core))
      ((mv fourth d fn2-core) (fn2-rsr-next 200 fn2-core))
      ((mv ended & fn2-core) (fn2-rsr-next 200 fn2-core))
      ((mv owner fn2-core) (fn2-read-scan-from 0 1 wslot wgen 200 1 1 fn2-core))
      ;; A digest represented as a scalar/empty reference is not a key.
      ((mv kc fn2-core) (fn2-read-key 0 :lo *fn2-identity-evidence-entry-field-digest* 0 fn2-core))
      ((mv malformed fn2-core) (fn2-read-scan-from 0 1 wslot wgen 200 0 1 fn2-core))
      ((mv & fn2-core) (fn2-read-release 0 fn2-core))
      ((mv & fn2-core) (fn2-core-release wslot wgen 200 0 1 fn2-core)))
   (mv (list seeded wc start first a resumed second b third c fourth d ended owner kc malformed) fn2-core)))

(defun fn2-rsr-result ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
   (mv-let (r fn2-core) (fn2-rsr-run fn2-core) r)))

; Key order is by exact Message-ID, not occurrence: a, b, c, z.
(assert-event (equal (fn2-rsr-result)
 '(:ok :ok :ok :ok 1 :ok :ok 3 :ok 4 :ok 2 :end :bounds :ok :bounds)))
