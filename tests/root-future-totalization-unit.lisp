; Prepared source equations, not an executed checkpoint/cut witness.
; Each guarded equation is the unchanged actual one-step transition.
; Off-guard logical controls establish total refusal, not served calls.
(in-package "ACL2")
(include-book "../books/checkpoint-future-working")

(defthm fn2-checkpoint-future-class-demand-guard-implies-domain
 (implies (and (natp i) (<= i 8))
          (and (natp i) (<= i 8))))

(defthm fn2-checkpoint-future-class-demand-guarded-measure-by-definition
 (implies (and (natp i) (<= i 8))
  (equal (nfix (- 8 (nfix i))) (nfix (- 8 i))))
 :hints (("Goal" :in-theory (enable nfix))))

(defthm fn2-checkpoint-future-class-demand-guarded-transition-unfolds
 (implies (and (natp i) (<= i 8))
  (equal (fn2-checkpoint-future-class-demand i class fn2-pool)
   (if (>= i 8) 0
  (+ (if (equal class (fn2-pool-class-for (fn2-checkpoint-future-window-length i) fn2-pool)) 1 0)
     (fn2-checkpoint-future-class-demand (+ i 1) class fn2-pool)))))
 :hints (("Goal" :expand ((fn2-checkpoint-future-class-demand i class fn2-pool))
  :in-theory (disable fn2-checkpoint-future-class-demand))))

(defthm fn2-checkpoint-future-class-demand-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-future-class-demand 1/2 class fn2-pool) 0)
 :hints (("Goal" :expand ((fn2-checkpoint-future-class-demand 1/2 class fn2-pool))
  :in-theory (disable fn2-checkpoint-future-class-demand))))

(defthm fn2-checkpoint-future-roomp-guard-implies-domain
 (implies (and (natp i) (<= i 8))
          (and (natp i) (<= i 8))))

(defthm fn2-checkpoint-future-roomp-guarded-measure-by-definition
 (implies (and (natp i) (<= i 8))
  (equal (nfix (- 8 (nfix i))) (nfix (- 8 i))))
 :hints (("Goal" :in-theory (enable nfix))))

(defthm fn2-checkpoint-future-roomp-guarded-transition-unfolds
 (implies (and (natp i) (<= i 8))
  (equal (fn2-checkpoint-future-roomp i fn2-pool)
   (if (>= i 8) t
  (let ((class (fn2-pool-class-for (fn2-checkpoint-future-window-length i) fn2-pool)))
   (and (natp class) (< class (fn2-pool-nclasses fn2-pool))
        (<= (fn2-checkpoint-future-class-demand 0 class fn2-pool) (fn2-pool-free-count class fn2-pool))
        (fn2-checkpoint-future-roomp (+ i 1) fn2-pool))))))
 :hints (("Goal" :expand ((fn2-checkpoint-future-roomp i fn2-pool))
  :in-theory (disable fn2-checkpoint-future-roomp))))

(defthm fn2-checkpoint-future-roomp-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-future-roomp 1/2 fn2-pool) nil)
 :hints (("Goal" :expand ((fn2-checkpoint-future-roomp 1/2 fn2-pool))
  :in-theory (disable fn2-checkpoint-future-roomp))))

(defthm fn2-checkpoint-future-reserve-loop-guard-implies-domain
 (implies (and (fn2-checkpoint-future-wfp fn2-checkpoint-future) (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future))
              (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
              (fn2-pool-wfp fn2-pool) (natp i) (<= i 8))
          (and (natp i) (<= i 8))))

(defthm fn2-checkpoint-future-reserve-loop-guarded-measure-by-definition
 (implies (and (fn2-checkpoint-future-wfp fn2-checkpoint-future) (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future))
              (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
              (fn2-pool-wfp fn2-pool) (natp i) (<= i 8))
  (equal (nfix (- 8 (nfix i))) (nfix (- 8 i))))
 :hints (("Goal" :in-theory (enable nfix))))

(defthm fn2-checkpoint-future-reserve-loop-guarded-transition-unfolds
 (implies (and (fn2-checkpoint-future-wfp fn2-checkpoint-future) (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future))
              (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
              (fn2-pool-wfp fn2-pool) (natp i) (<= i 8))
  (equal (fn2-checkpoint-future-reserve-loop i kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)
   (if (>= i 8)
  (let* ((fn2-checkpoint-future (fn2-checkpoint-future-set-phase 0 *fn2-checkpoint-future-phase-reserved* fn2-checkpoint-future)))
   (mv :ok fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
  (b* ((class (fn2-pool-class-for (fn2-checkpoint-future-window-length i) fn2-pool))
       ((mv code slot generation fn2-pool) (fn2-pool-reserve class kind owner gen fn2-pool))
       ((unless (eq code :ok))
        (let* ((fn2-checkpoint-future (fn2-checkpoint-future-set-phase 0 *fn2-checkpoint-future-phase-uncertain* fn2-checkpoint-future)))
         (mv :partial fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)))
       (fn2-checkpoint-future-windows (fn2-checkpoint-future-windows-put i (live 1) (slot slot) (generation generation) (borrowed 0)))
       (fn2-checkpoint-future (fn2-checkpoint-future-set-reserved 0 (+ i 1) fn2-checkpoint-future)))
   (fn2-checkpoint-future-reserve-loop (+ i 1) kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)))))
 :hints (("Goal" :expand ((fn2-checkpoint-future-reserve-loop i kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-future-reserve-loop))))

(defthm fn2-checkpoint-future-reserve-loop-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-future-reserve-loop 1/2 kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool) (mv :bounds fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
 :hints (("Goal" :expand ((fn2-checkpoint-future-reserve-loop 1/2 kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-future-reserve-loop))))

(defthm fn2-checkpoint-future-transfer-readyp-guard-implies-domain
 (implies (and (fn2-checkpoint-future-wfp fn2-checkpoint-future) (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (fn2-pool-wfp fn2-pool)
              (natp i) (natp end) (<= i end) (<= end 8))
          (and (natp i) (natp end) (<= i end) (<= end 8))))

(defthm fn2-checkpoint-future-transfer-readyp-guarded-measure-by-definition
 (implies (and (fn2-checkpoint-future-wfp fn2-checkpoint-future) (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (fn2-pool-wfp fn2-pool)
              (natp i) (natp end) (<= i end) (<= end 8))
  (equal (nfix (- (nfix end) (nfix i))) (nfix (- end i))))
 :hints (("Goal" :in-theory (enable nfix))))

(defthm fn2-checkpoint-future-transfer-readyp-guarded-transition-unfolds
 (implies (and (fn2-checkpoint-future-wfp fn2-checkpoint-future) (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (fn2-pool-wfp fn2-pool)
              (natp i) (natp end) (<= i end) (<= end 8))
  (equal (fn2-checkpoint-future-transfer-readyp i end returning token kind owner gen bkind borrower bgen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)
   (if (>= i end) t
  (and (< i (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
       (equal (fn2-checkpoint-future-windows-borrowed i fn2-checkpoint-future-windows) (if returning 1 0))
       (mv-let (code slot generation)
        (fn2-checkpoint-future-lease i token (if returning bkind kind) (if returning borrower owner) (if returning bgen gen)
         fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)
        (declare (ignore slot generation)) (eq code :ok))
       (fn2-checkpoint-future-transfer-readyp (+ i 1) end returning token kind owner gen bkind borrower bgen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)))))
 :hints (("Goal" :expand ((fn2-checkpoint-future-transfer-readyp i end returning token kind owner gen bkind borrower bgen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-future-transfer-readyp))))

(defthm fn2-checkpoint-future-transfer-readyp-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-future-transfer-readyp 1/2 end returning token kind owner gen bkind borrower bgen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool) nil)
 :hints (("Goal" :expand ((fn2-checkpoint-future-transfer-readyp 1/2 end returning token kind owner gen bkind borrower bgen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-future-transfer-readyp))))

(defthm fn2-checkpoint-future-transfer-readyp-logical-nonnatural-end-refuses-by-definition
 (equal (fn2-checkpoint-future-transfer-readyp 0 1/2 returning token kind owner gen bkind borrower bgen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool) nil)
 :hints (("Goal" :expand ((fn2-checkpoint-future-transfer-readyp 0 1/2 returning token kind owner gen bkind borrower bgen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-future-transfer-readyp))))

(defthm fn2-checkpoint-future-transfer-loop-guard-implies-domain
 (implies (and (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (fn2-pool-wfp fn2-pool)
              (natp i) (natp end) (<= i end) (<= end 8) (<= end (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
              (fn2-pool-mrefp kind owner gen) (fn2-pool-mrefp bkind borrower bgen))
          (and (natp i) (natp end) (<= i end) (<= end 8) (<= end (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))))

(defthm fn2-checkpoint-future-transfer-loop-guarded-measure-by-definition
 (implies (and (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (fn2-pool-wfp fn2-pool)
              (natp i) (natp end) (<= i end) (<= end 8) (<= end (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
              (fn2-pool-mrefp kind owner gen) (fn2-pool-mrefp bkind borrower bgen))
  (equal (nfix (- (nfix end) (nfix i))) (nfix (- end i))))
 :hints (("Goal" :in-theory (enable nfix))))

(defthm fn2-checkpoint-future-transfer-loop-guarded-transition-unfolds
 (implies (and (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (fn2-pool-wfp fn2-pool)
              (natp i) (natp end) (<= i end) (<= end 8) (<= end (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
              (fn2-pool-mrefp kind owner gen) (fn2-pool-mrefp bkind borrower bgen))
  (equal (fn2-checkpoint-future-transfer-loop i end returning kind owner gen bkind borrower bgen fn2-checkpoint-future-windows fn2-pool)
   (if (>= i end) (mv :ok fn2-checkpoint-future-windows fn2-pool)
  (b* ((slot (fn2-checkpoint-future-windows-slot i fn2-checkpoint-future-windows))
       (generation (fn2-checkpoint-future-windows-generation i fn2-checkpoint-future-windows))
       ((mv code fn2-pool)
        (fn2-pool-hand slot generation (if returning bkind kind) (if returning borrower owner) (if returning bgen gen)
         (if returning kind bkind) (if returning owner borrower) (if returning gen bgen) fn2-pool))
       ((unless (eq code :ok)) (mv :partial fn2-checkpoint-future-windows fn2-pool))
       ((mv code fn2-pool)
        (fn2-pool-accept-hand slot generation (if returning kind bkind) (if returning owner borrower) (if returning gen bgen) fn2-pool))
       ((unless (eq code :ok)) (mv :partial fn2-checkpoint-future-windows fn2-pool))
       (fn2-checkpoint-future-windows (fn2-checkpoint-future-windows-put i (borrowed (if returning 0 1))
        (borrower-kind (if returning 0 bkind)) (borrower-slot (if returning 0 borrower)) (borrower-gen (if returning 0 bgen)))))
   (fn2-checkpoint-future-transfer-loop (+ i 1) end returning kind owner gen bkind borrower bgen fn2-checkpoint-future-windows fn2-pool)))))
 :hints (("Goal" :expand ((fn2-checkpoint-future-transfer-loop i end returning kind owner gen bkind borrower bgen fn2-checkpoint-future-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-future-transfer-loop))))

(defthm fn2-checkpoint-future-transfer-loop-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-future-transfer-loop 1/2 end returning kind owner gen bkind borrower bgen fn2-checkpoint-future-windows fn2-pool) (mv :bounds fn2-checkpoint-future-windows fn2-pool))
 :hints (("Goal" :expand ((fn2-checkpoint-future-transfer-loop 1/2 end returning kind owner gen bkind borrower bgen fn2-checkpoint-future-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-future-transfer-loop))))

(defthm fn2-checkpoint-future-transfer-loop-logical-nonnatural-end-refuses-by-definition
 (equal (fn2-checkpoint-future-transfer-loop 0 1/2 returning kind owner gen bkind borrower bgen fn2-checkpoint-future-windows fn2-pool) (mv :bounds fn2-checkpoint-future-windows fn2-pool))
 :hints (("Goal" :expand ((fn2-checkpoint-future-transfer-loop 0 1/2 returning kind owner gen bkind borrower bgen fn2-checkpoint-future-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-future-transfer-loop))))

(defthm fn2-checkpoint-future-no-loansp-guard-implies-domain
 (implies (and (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (natp i) (natp end)
              (<= i end) (<= end (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))
          (and (natp i) (natp end) (<= i end) (<= end (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))))

(defthm fn2-checkpoint-future-no-loansp-guarded-measure-by-definition
 (implies (and (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (natp i) (natp end)
              (<= i end) (<= end (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))
  (equal (nfix (- (nfix end) (nfix i))) (nfix (- end i))))
 :hints (("Goal" :in-theory (enable nfix))))

(defthm fn2-checkpoint-future-no-loansp-guarded-transition-unfolds
 (implies (and (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (natp i) (natp end)
              (<= i end) (<= end (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))
  (equal (fn2-checkpoint-future-no-loansp i end fn2-checkpoint-future-windows)
   (if (>= i end) t
  (and (equal (fn2-checkpoint-future-windows-borrowed i fn2-checkpoint-future-windows) 0)
       (fn2-checkpoint-future-no-loansp (+ i 1) end fn2-checkpoint-future-windows)))))
 :hints (("Goal" :expand ((fn2-checkpoint-future-no-loansp i end fn2-checkpoint-future-windows))
  :in-theory (disable fn2-checkpoint-future-no-loansp))))

(defthm fn2-checkpoint-future-no-loansp-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-future-no-loansp 1/2 end fn2-checkpoint-future-windows) nil)
 :hints (("Goal" :expand ((fn2-checkpoint-future-no-loansp 1/2 end fn2-checkpoint-future-windows))
  :in-theory (disable fn2-checkpoint-future-no-loansp))))

(defthm fn2-checkpoint-future-no-loansp-logical-nonnatural-end-refuses-by-definition
 (equal (fn2-checkpoint-future-no-loansp 0 1/2 fn2-checkpoint-future-windows) nil)
 :hints (("Goal" :expand ((fn2-checkpoint-future-no-loansp 0 1/2 fn2-checkpoint-future-windows))
  :in-theory (disable fn2-checkpoint-future-no-loansp))))
