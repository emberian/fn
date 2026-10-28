; Statement packet, never theorem admission. These scoped scout subjects exist;
; none is a claim that fn2-turn reaches the sidecar or that B3 already exists.
(in-package "ACL2")
(include-book "connection")

(defun fn2-sd-inv (fn2-sdconn fn2-core fn2-sprint-c)
 (declare (xargs :stobjs (fn2-sdconn fn2-core fn2-sprint-c) :verify-guards nil))
 (and (fn2-sdconn-wfp fn2-sdconn) (= (fn2-sdconn-rows fn2-sdconn) 1)
      (fn2-core-wfp fn2-core) (fn2-sprint-c-wfp fn2-sprint-c)
      (<= (fn2-sc-count fn2-sprint-c) (fn2-sprint-c-rows fn2-sprint-c))
      (<= (fn2-sdconn-start 0 fn2-sdconn) (fn2-sdconn-scan 0 fn2-sdconn))
      (<= (fn2-sdconn-tx-off 0 fn2-sdconn) (fn2-sdconn-tx-len 0 fn2-sdconn))
      (implies (= (fn2-sdconn-phase 0 fn2-sdconn) *fn2-sdconn-state-publish*)
               (= (fn2-sdconn-outcome 0 fn2-sdconn) 2))))
(defthm-owed fn2-sd-T1-transition-preservation
 (id budget fn2-sdconn fn2-core fn2-sprint-c)
 (implies (fn2-sd-inv fn2-sdconn fn2-core fn2-sprint-c)
  (let ((after (mv-list 7 (fn2-sd-run id budget fn2-sdconn fn2-core fn2-sprint-c))))
   (and (<= (mv-nth 0 after) 4096) (<= (mv-nth 1 after) 32) (<= (mv-nth 2 after) 4)
        (fn2-sd-inv (mv-nth 4 after) (mv-nth 5 after) (mv-nth 6 after)))))
 :teeth "integration-driver asserts the full scoped invariant antecedent and transition conclusion, plus an actual tx-offset invariant-removal control; d-exchange executes GROUP/ARTICLE/POST across 1/7/4096-byte client fragments. Universal preservation and guard safety remain owed."
 :doc "Scoped sidecar transition representation/budget scaffold; not full T1 guard-closure assurance. All nontrivial runtime guards remain deferred in this scout.")
(defthm-owed fn2-sd-T6-outcome-boundary
 (id budget fn2-sdconn fn2-core fn2-sprint-c)
 (implies (and (fn2-sd-inv fn2-sdconn fn2-core fn2-sprint-c)
               (not (= (fn2-sdconn-outcome 0 fn2-sdconn) 3)))
  (let ((after (mv-list 7 (fn2-sd-run id budget fn2-sdconn fn2-core fn2-sprint-c))))
   (and (implies (= (fn2-sdconn-outcome 0 (mv-nth 4 after)) 3)
                 (and (= (fn2-sdconn-phase 0 fn2-sdconn) *fn2-sdconn-state-publish*)
                      (= (fn2-sdconn-outcome 0 fn2-sdconn) 2)))
        (implies (= (fn2-sdconn-outcome 0 (mv-nth 4 after)) 1)
                 (equal (mv-nth 6 after) fn2-sprint-c)))))
 :teeth "d-exchange checks uncertainty was entered before any acceptance, one successful fence publishes one C row, and failed fence retains outcome2/count2. No universal/hypothesis-removal proof yet."
 :doc "Outcomes are 0=no submission,1=refused,2=uncertain,3=accepted. Real B journal/recovery durability implication is missing (GD2), not smuggled into the antecedent.")
(defun fn2-sd-scan-split (a b slot gen start scan cap fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (mv-let (code next end) (fn2-sd-scan-line slot gen start scan cap a fn2-core)
  (if (eq code :yield) (fn2-sd-scan-line slot gen start next cap b fn2-core) (mv code next end))))
(defthm-owed fn2-sd-T8-parser-quantum-invariance
 (a b slot gen start scan cap fn2-core)
 (implies (and (posp a) (posp b) (<= (+ a b) 4096))
  (equal (mv-list 3 (fn2-sd-scan-split a b slot gen start scan cap fn2-core))
         (mv-list 3 (fn2-sd-scan-line slot gen start scan cap (+ a b) fn2-core))))
 :teeth "d-exchange byte-for-byte fixture agrees at three input fragment quanta. All split points and an explicit hypothesis-removal witness remain owed."
 :doc "Parser quantum invariance only. Full arbitrary input fragmentation, observation correspondence and connection privacy are owed; fixed owner250 is expressly not a privacy model.")
(defthm-owed fn2-sd-T9-exact-query-binding
 (slot gen off len start fn2-pool fn2-sprint-c)
 (implies (eq (mv-nth 0 (fn2-sc-lookup slot gen off len 250 0 1 start 4 fn2-pool fn2-sprint-c)) :found)
  (let ((row (mv-nth 1 (fn2-sc-lookup slot gen off len 250 0 1 start 4 fn2-pool fn2-sprint-c))))
   (and (= len (fn2-sc-row-mid-len row fn2-sprint-c))
        (eq (mv-nth 0 (fn2-sc-compare slot gen off (fn2-sc-row-mid-slot row fn2-sprint-c)
              (fn2-sc-row-mid-gen row fn2-sprint-c) (fn2-sc-row-mid-off row fn2-sprint-c) len 250 0 1 fn2-pool)) :equal))))
 :teeth "d-exchange retrieves ARTICLE by exact MID and refuses an absent MID; C's examples separately hold equal content tags on unequal IDs. Reclamation/source-conflict teeth remain owed."
 :doc "C exact-byte query result used by D; no BLAKE3/source identity or post-reclamation assertion.")
(defthm-owed fn2-sd-T10-resident-shape
 (id budget fn2-sdconn fn2-core fn2-sprint-c)
 (implies (fn2-sd-inv fn2-sdconn fn2-core fn2-sprint-c)
  (let ((after (mv-list 7 (fn2-sd-run id budget fn2-sdconn fn2-core fn2-sprint-c))))
   (and (equal (fn2-sdconn-rows (mv-nth 4 after)) 1)
        (equal (fn2-sprint-c-rows (mv-nth 6 after)) (fn2-sprint-c-rows fn2-sprint-c)))))
 :teeth "d-exchange initializes one connection row and eight C slots; no execution calls init/resize. Universal theorem and profile-wide registry memory calculation remain owed."
 :doc "Fixed sidecar row capacities only, not total-core byte allocation/TLS/adapter accounting.")
