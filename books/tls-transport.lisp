; Inductive transport ownership and span obligations for the actual host callees.
; These do not establish the external library's cryptographic or byte-effect truth.
(in-package "ACL2")
(include-book "tls-transport-ops")
(fn2-book-layer :d)

(local (in-theory
 (set-difference-theories (current-theory :here) (theory 'fn2-tls-transport-abstraction))))

(defun fn2-tls-transport-pending-valid-p (action offset requested total copied fed il io ol oo quantum)
 (declare (xargs :guard t))
 (and (natp requested) (natp quantum) (<= requested quantum)
  (case action
   (0 t)
   (1 (and (equal offset copied) (<= (+ (nfix offset) requested) (nfix total))))
   (2 (and (equal offset fed) (<= (+ (nfix offset) requested) (nfix copied))))
   (3 (and (equal offset io) (<= (+ (nfix offset) requested) (nfix il))))
   (4 (equal offset 0))
   (5 (and (equal offset oo) (<= (+ (nfix offset) requested) (nfix ol))))
   (6 (and (equal offset 0) (equal io il)))
   (7 (and (equal offset 0) (equal requested 0)))
   (8 (equal requested 0))
   (9 (and (equal offset 0) (equal requested 0)))
   (otherwise nil))))

(defun fn2-tls-transport-invariant (fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 (and (<= (fn2-tls-transport-seed-total 0 fn2-tls-transport) (fn2-tls-transport-seed-capacity 0 fn2-tls-transport))
      (<= (fn2-tls-transport-copied 0 fn2-tls-transport) (fn2-tls-transport-seed-total 0 fn2-tls-transport))
      (<= (fn2-tls-transport-fed 0 fn2-tls-transport) (fn2-tls-transport-copied 0 fn2-tls-transport))
      (<= (fn2-tls-transport-input-offset 0 fn2-tls-transport) (fn2-tls-transport-input-length 0 fn2-tls-transport))
      (<= (fn2-tls-transport-output-offset 0 fn2-tls-transport) (fn2-tls-transport-output-length 0 fn2-tls-transport))
      (<= (fn2-tls-transport-input-length 0 fn2-tls-transport) (fn2-tls-transport-quantum 0 fn2-tls-transport))
      (<= (fn2-tls-transport-output-length 0 fn2-tls-transport) (fn2-tls-transport-quantum 0 fn2-tls-transport))
      (fn2-tls-transport-pending-valid-p
       (fn2-tls-transport-pending 0 fn2-tls-transport) (fn2-tls-transport-offset 0 fn2-tls-transport)
       (fn2-tls-transport-requested 0 fn2-tls-transport)
       (fn2-tls-transport-seed-total 0 fn2-tls-transport) (fn2-tls-transport-copied 0 fn2-tls-transport)
       (fn2-tls-transport-fed 0 fn2-tls-transport)
       (fn2-tls-transport-input-length 0 fn2-tls-transport) (fn2-tls-transport-input-offset 0 fn2-tls-transport)
       (fn2-tls-transport-output-length 0 fn2-tls-transport) (fn2-tls-transport-output-offset 0 fn2-tls-transport)
       (fn2-tls-transport-quantum 0 fn2-tls-transport))))

(defthm fn2-tls-transport-stale-observation-frame-by-definition
 (implies (or (not (equal cap (fn2-tls-transport-cap 0 fn2-tls-transport)))
              (not (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport)))
              (not (equal slot (fn2-tls-transport-slot 0 fn2-tls-transport)))
              (not (equal generation (fn2-tls-transport-generation 0 fn2-tls-transport)))
              (not (equal serial (fn2-tls-transport-serial 0 fn2-tls-transport)))
              (equal (fn2-tls-transport-pending 0 fn2-tls-transport) 0))
  (equal (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))
         fn2-tls-transport)))

(defthm fn2-tls-transport-handoff-refusal-frame-by-definition
 (implies (not (equal (mv-nth 0 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport)) :ok))
  (equal (mv-nth 7 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport)) fn2-tls-transport)))

(defthm fn2-tls-transport-handoff-loan-copied-by-definition
 (implies (equal (mv-nth 0 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport)) :ok)
  (and (equal cap (fn2-tls-transport-cap 0 fn2-tls-transport))
          (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport))
       (equal slot (fn2-tls-transport-slot 0 fn2-tls-transport))
       (equal generation (fn2-tls-transport-generation 0 fn2-tls-transport))
       (equal (fn2-tls-transport-pending 0 fn2-tls-transport) 0)
       (equal (mv-nth 1 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (fn2-tls-transport-seed-total 0 fn2-tls-transport))
       (equal (mv-nth 2 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (fn2-tls-transport-fed 0 fn2-tls-transport))
       (equal (mv-nth 3 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (fn2-tls-transport-input-length 0 fn2-tls-transport))
       (equal (mv-nth 4 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (fn2-tls-transport-input-offset 0 fn2-tls-transport))
       (equal (mv-nth 5 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (mv-nth 6 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport)))))
 :rule-classes nil)

(defthm fn2-tls-transport-observe-preserves-invariant
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-invariant fn2-tls-transport))
  (fn2-tls-transport-invariant
   (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :hints (("Goal" :in-theory
            (disable fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p))
         (and stable-under-simplificationp
              '(:in-theory (e/d (fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p
                  fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno) (nth update-nth))))))

(defthm fn2-tls-transport-plan-pending-valid
 (implies (equal (mv-nth 0 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) :act)
  (fn2-tls-transport-pending-valid-p
   (mv-nth 1 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))
   (mv-nth 2 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))
   (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))
   total copied fed il io ol oo quantum))
 :hints (("Goal" :in-theory (enable fn2-tls-transport-plan))))

(defthm fn2-tls-transport-pending-allocation-or-free
 (and (equal (fn2-tls-transport-pending-valid-p 8 window 0 total copied fed il io ol oo quantum)
             (natp quantum))
      (equal (fn2-tls-transport-pending-valid-p 9 0 0 total copied fed il io ol oo quantum)
             (natp quantum))))

(defthm fn2-tls-transport-next-preserves-invariant
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-invariant fn2-tls-transport))
  (fn2-tls-transport-invariant
   (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))))
 :hints (("Goal" :in-theory
            (disable fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p))
         (and stable-under-simplificationp
              '(:in-theory (e/d (fn2-tls-transport-invariant
                  fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno)
                  (nth update-nth fn2-tls-transport-pending-valid-p))))))

(defthm-owed fn2-tls-transport-observe-preserves-invariant (cap nonce slot generation serial code count errno fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-invariant fn2-tls-transport))
  (fn2-tls-transport-invariant
   (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-invariant-positive fn2-tls-transport-observe-invariant-negative)
 :doc "The host-called observe preserves staged-seed conservation, bounded input/output buffers, unsent prefixes and the pending action span. Physical byte-prefix correspondence remains a separate primitive boundary obligation.")

(fn2-owed-discharge fn2-tls-transport-observe-preserves-invariant fn2-tls-transport-observe-preserves-invariant)

(defthm-owed fn2-tls-transport-next-preserves-invariant (room pending fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-invariant fn2-tls-transport))
  (fn2-tls-transport-invariant
   (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-invariant-positive fn2-tls-transport-next-invariant-negative)
 :doc "The host-called next preserves staged-seed conservation, bounded input/output buffers, unsent prefixes and the pending action span. Physical byte-prefix correspondence remains a separate primitive boundary obligation.")

(fn2-owed-discharge fn2-tls-transport-next-preserves-invariant fn2-tls-transport-next-preserves-invariant)

(defthm fn2-tls-transport-start-establishes-invariant
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (equal (mv-nth 0 (fn2-tls-transport-start cap nonce slot generation total capacity quantum budget window fn2-tls-transport)) :ok))
  (fn2-tls-transport-invariant
   (mv-nth 1 (fn2-tls-transport-start cap nonce slot generation total capacity quantum budget window fn2-tls-transport))))
 :hints (("Goal" :in-theory
            (disable fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p fn2-tls-transport-init))
         (and stable-under-simplificationp
              '(:in-theory (e/d (fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p
                  fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno)
                  (nth update-nth fn2-tls-transport-init))))))

(defthm fn2-tls-transport-next-spends-one-action
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (equal (mv-nth 0 (fn2-tls-transport-next room pending fn2-tls-transport)) :act))
  (and (equal (fn2-tls-transport-budget 0 (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (- (fn2-tls-transport-budget 0 fn2-tls-transport) 1))
       (equal (fn2-tls-transport-serial 0 (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (+ (fn2-tls-transport-serial 0 fn2-tls-transport) 1))
       (< 0 (fn2-tls-transport-budget 0 fn2-tls-transport))))
 :hints (("Goal" :in-theory
  (e/d (fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-rows)
       (nth update-nth)))))

(defthm-owed fn2-tls-transport-next-spends-one-action (room pending fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (equal (mv-nth 0 (fn2-tls-transport-next room pending fn2-tls-transport)) :act))
  (and (equal (fn2-tls-transport-budget 0 (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (- (fn2-tls-transport-budget 0 fn2-tls-transport) 1))
       (equal (fn2-tls-transport-serial 0 (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (+ (fn2-tls-transport-serial 0 fn2-tls-transport) 1))
       (< 0 (fn2-tls-transport-budget 0 fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-invariant-positive fn2-tls-transport-check-budget)
 :doc "Every action selected for the native handshake spends exactly one admitted budget unit and advances its serial without wrap; exhausted attempts select no physical work.")

(fn2-owed-discharge fn2-tls-transport-next-spends-one-action fn2-tls-transport-next-spends-one-action)

(defun fn2-tls-transport-handle-invariant (fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 (let ((alive (fn2-tls-transport-alive 0 fn2-tls-transport))
       (identity (fn2-tls-transport-handle-id 0 fn2-tls-transport))
       (credit (fn2-tls-transport-cleanup-credit 0 fn2-tls-transport))
       (pending (fn2-tls-transport-pending 0 fn2-tls-transport))
       (terminal (fn2-tls-transport-terminal 0 fn2-tls-transport)))
  (and (equal (= alive 0) (= identity 0))
       (implies (= terminal 0) (= credit 1))
       (implies (member-equal terminal '(1 3)) (= alive 1))
       (implies (member-equal pending '(1 2 3 4 5 6 7 9)) (= alive 1))
       (implies (= pending 8) (and (= alive 0) (= credit 1)))
       (implies (= pending 9) (and (= credit 0) (member-equal terminal '(2 4))))
       (implies (= credit 0) (or (= alive 0) (= pending 9))))))

(defthm fn2-tls-transport-plan-action-bound
 (< (mv-nth 1 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) 8)
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn2-tls-transport-plan))))

(defthm fn2-tls-transport-next-preserves-handle-ownership
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport))
  (fn2-tls-transport-handle-invariant (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-handle-invariant))
         (and stable-under-simplificationp
          '(:in-theory (e/d (fn2-tls-transport-handle-invariant fn2-tls-transport-alive fn2-tls-transport-handle-id fn2-tls-transport-cleanup-credit fn2-tls-transport-pending fn2-tls-transport-terminal fn2-tls-transport-rows)
                           (nth update-nth))))))

(defthm fn2-tls-transport-observe-preserves-handle-ownership
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport))
  (fn2-tls-transport-handle-invariant (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-handle-invariant))
         (and stable-under-simplificationp
          '(:in-theory (e/d (fn2-tls-transport-handle-invariant fn2-tls-transport-alive fn2-tls-transport-handle-id fn2-tls-transport-cleanup-credit fn2-tls-transport-pending fn2-tls-transport-terminal fn2-tls-transport-rows)
                           (nth update-nth))))))

(defthm fn2-tls-transport-retire-preserves-handle-ownership
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport))
  (fn2-tls-transport-handle-invariant (mv-nth 1 (fn2-tls-transport-retire cap nonce fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-handle-invariant))
         (and stable-under-simplificationp
          '(:in-theory (e/d (fn2-tls-transport-handle-invariant fn2-tls-transport-alive fn2-tls-transport-handle-id fn2-tls-transport-cleanup-credit fn2-tls-transport-pending fn2-tls-transport-terminal fn2-tls-transport-rows)
                           (nth update-nth))))))

(defthm fn2-tls-transport-start-establishes-handle-ownership
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (equal (mv-nth 0 (fn2-tls-transport-start cap nonce slot generation total capacity quantum budget window fn2-tls-transport)) :ok))
  (fn2-tls-transport-handle-invariant
   (mv-nth 1 (fn2-tls-transport-start cap nonce slot generation total capacity quantum budget window fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-handle-invariant fn2-tls-transport-init))
         (and stable-under-simplificationp
          '(:in-theory (e/d (fn2-tls-transport-handle-invariant fn2-tls-transport-alive fn2-tls-transport-handle-id fn2-tls-transport-cleanup-credit fn2-tls-transport-pending fn2-tls-transport-terminal fn2-tls-transport-rows)
                           (nth update-nth fn2-tls-transport-init))))))

(defthm-owed fn2-tls-transport-next-preserves-handle-ownership (room pending fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport))
  (fn2-tls-transport-handle-invariant
   (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-owner-positive fn2-tls-transport-next-owner-negative)
 :doc "The actual transport controller preserves opaque-handle ownership and its reserved cleanup credit. External allocation/free postconditions and byte effects remain separate boundary obligations.")
(fn2-owed-discharge fn2-tls-transport-next-preserves-handle-ownership fn2-tls-transport-next-preserves-handle-ownership)

(defthm-owed fn2-tls-transport-observe-preserves-handle-ownership (cap nonce slot generation serial code count errno fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport))
  (fn2-tls-transport-handle-invariant
   (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-owner-positive fn2-tls-transport-observe-owner-negative)
 :doc "The actual transport controller preserves opaque-handle ownership and its reserved cleanup credit. External allocation/free postconditions and byte effects remain separate boundary obligations.")
(fn2-owed-discharge fn2-tls-transport-observe-preserves-handle-ownership fn2-tls-transport-observe-preserves-handle-ownership)

(defthm-owed fn2-tls-transport-retire-preserves-handle-ownership (cap nonce fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport))
  (fn2-tls-transport-handle-invariant
   (mv-nth 1 (fn2-tls-transport-retire cap nonce fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-owner-positive fn2-tls-transport-retire-owner-negative)
 :doc "The actual transport controller preserves opaque-handle ownership and its reserved cleanup credit. External allocation/free postconditions and byte effects remain separate boundary obligations.")
(fn2-owed-discharge fn2-tls-transport-retire-preserves-handle-ownership fn2-tls-transport-retire-preserves-handle-ownership)
