; Prepared source equations, not an executed checkpoint/cut witness.
; Each guarded equation is the unchanged actual one-step transition.
; Off-guard logical controls establish total refusal, not served calls.
(in-package "ACL2")
(include-book "../books/checkpoint-working-reserve")
(include-book "../books/checkpoint-future-working")

(defthm fn2-checkpoint-window-roomp-guard-implies-domain
 (implies (and (natp i) (<= i *fn2-checkpoint-window-count*))
          (and (natp i) (<= i *fn2-checkpoint-window-count*))))

(defthm fn2-checkpoint-window-roomp-guarded-measure-by-definition
 (implies (and (natp i) (<= i *fn2-checkpoint-window-count*))
  (equal (nfix (- *fn2-checkpoint-window-count* (nfix i))) (nfix (- *fn2-checkpoint-window-count* i))))
 :hints (("Goal" :in-theory (enable nfix))))

(defthm fn2-checkpoint-window-roomp-guarded-transition-unfolds
 (implies (and (natp i) (<= i *fn2-checkpoint-window-count*))
  (equal (fn2-checkpoint-window-roomp i fn2-pool)
   (if (>= i *fn2-checkpoint-window-count*) t
  (let ((class (fn2-pool-class-for (fn2-checkpoint-window-length i) fn2-pool)))
   (and (natp class) (< class (fn2-pool-nclasses fn2-pool))
        (<= (fn2-checkpoint-window-class-demand 0 class fn2-pool) (fn2-pool-free-count class fn2-pool))
        (fn2-checkpoint-window-roomp (+ i 1) fn2-pool))))))
 :hints (("Goal" :expand ((fn2-checkpoint-window-roomp i fn2-pool))
  :in-theory (disable fn2-checkpoint-window-roomp))))

(defthm fn2-checkpoint-window-roomp-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-window-roomp 1/2 fn2-pool) nil)
 :hints (("Goal" :expand ((fn2-checkpoint-window-roomp 1/2 fn2-pool))
  :in-theory (disable fn2-checkpoint-window-roomp))))

(defthm fn2-checkpoint-windows-reserve-loop-guard-implies-domain
 (implies (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
              (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows))
              (fn2-pool-wfp fn2-pool) (natp i) (<= i *fn2-checkpoint-window-count*))
          (and (natp i) (<= i *fn2-checkpoint-window-count*) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1)) (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows)))))

(defthm fn2-checkpoint-windows-reserve-loop-guarded-measure-by-definition
 (implies (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
              (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows))
              (fn2-pool-wfp fn2-pool) (natp i) (<= i *fn2-checkpoint-window-count*))
  (equal (nfix (- *fn2-checkpoint-window-count* (nfix i))) (nfix (- *fn2-checkpoint-window-count* i))))
 :hints (("Goal" :in-theory (enable nfix))))

(defthm fn2-checkpoint-windows-reserve-loop-guarded-transition-unfolds
 (implies (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
              (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows))
              (fn2-pool-wfp fn2-pool) (natp i) (<= i *fn2-checkpoint-window-count*))
  (equal (fn2-checkpoint-windows-reserve-loop i nonce kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)
   (if (>= i *fn2-checkpoint-window-count*)
  (let ((fn2-checkpoint-root1 (fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-reserved* fn2-checkpoint-root1)))
   (mv :ok fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool))
  (b* ((class (fn2-pool-class-for (fn2-checkpoint-window-length i) fn2-pool))
       ((mv code slot gen fn2-pool) (if (posp nonce)
          (fn2-pool-reserve-credit *fn2-checkpoint-working-credit-group* nonce class kind owner generation fn2-pool)
        (fn2-pool-reserve class kind owner generation fn2-pool)))
       ((unless (eq code :ok))
        (let ((fn2-checkpoint-root1 (fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-uncertain* fn2-checkpoint-root1)))
         (mv code fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)))
       (fn2-checkpoint-windows (fn2-checkpoint-windows-put i (live 1) (slot slot) (generation gen)))
       (fn2-checkpoint-root1 (fn2-checkpoint-root1-set-reserved 0 (+ i 1) fn2-checkpoint-root1)))
   (fn2-checkpoint-windows-reserve-loop (+ i 1) nonce kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)))))
 :hints (("Goal" :expand ((fn2-checkpoint-windows-reserve-loop i nonce kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-windows-reserve-loop))))

(defthm fn2-checkpoint-windows-reserve-loop-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-windows-reserve-loop 1/2 nonce kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool) (mv :bounds fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool))
 :hints (("Goal" :expand ((fn2-checkpoint-windows-reserve-loop 1/2 nonce kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-windows-reserve-loop))))

(defthm fn2-checkpoint-working-credit-fitp-guard-implies-domain
 (implies (and (fn2-pool-wfp fn2-pool) (natp class))
          (and (natp class))))

(defthm fn2-checkpoint-working-credit-fitp-guarded-measure-by-definition
 (implies (and (fn2-pool-wfp fn2-pool) (natp class))
  (equal (nfix (- (nfix (fn2-pool-nclasses fn2-pool)) (nfix class))) (nfix (- (fn2-pool-nclasses fn2-pool) (nfix class)))))
 :hints (("Goal" :in-theory (enable nfix))))

(defthm fn2-checkpoint-working-credit-fitp-guarded-transition-unfolds
 (implies (and (fn2-pool-wfp fn2-pool) (natp class))
  (equal (fn2-checkpoint-working-credit-fitp class fn2-pool)
   (and (fn2-pool-credit-shapep fn2-pool)
      (equal (fn2-pool-credit-purposei *fn2-checkpoint-working-credit-group* fn2-pool) *fn2-pool-credit-working*)
      (member-equal (fn2-pool-credit-phasei *fn2-checkpoint-working-credit-group* fn2-pool)
       (list *fn2-pool-credit-idle* *fn2-pool-credit-aborted-empty*))
      (fn2-pool-credit-fullp *fn2-checkpoint-working-credit-group* 0 fn2-pool)
      (or (>= class (fn2-pool-nclasses fn2-pool))
          (and (equal (fn2-pool-credit-demandi class fn2-pool)
                      (+ (fn2-checkpoint-window-class-demand 0 class fn2-pool)
                         (fn2-checkpoint-future-class-demand 0 class fn2-pool)))
               (fn2-checkpoint-working-credit-fitp (+ class 1) fn2-pool))))))
 :hints (("Goal" :expand ((fn2-checkpoint-working-credit-fitp class fn2-pool))
  :in-theory (disable fn2-checkpoint-working-credit-fitp))))

(defthm fn2-checkpoint-working-credit-fitp-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-working-credit-fitp 1/2 fn2-pool) nil)
 :hints (("Goal" :expand ((fn2-checkpoint-working-credit-fitp 1/2 fn2-pool))
  :in-theory (disable fn2-checkpoint-working-credit-fitp))))

(defthm fn2-checkpoint-future-reserve-loop-guard-implies-domain
 (implies (and (fn2-checkpoint-future-wfp fn2-checkpoint-future) (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future))
              (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
              (fn2-pool-wfp fn2-pool) (natp i) (<= i 8))
          (and (natp i) (<= i 8) (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future)) (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))))

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
  (equal (fn2-checkpoint-future-reserve-loop i nonce kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)
   (if (>= i 8)
  (let* ((fn2-checkpoint-future (fn2-checkpoint-future-set-phase 0 *fn2-checkpoint-future-phase-reserved* fn2-checkpoint-future)))
   (mv :ok fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
  (b* ((class (fn2-pool-class-for (fn2-checkpoint-future-window-length i) fn2-pool))
       ((mv code slot generation fn2-pool) (if (posp nonce)
          (fn2-pool-reserve-credit *fn2-checkpoint-working-credit-group* nonce class kind owner gen fn2-pool)
        (fn2-pool-reserve class kind owner gen fn2-pool)))
       ((unless (eq code :ok))
        (let* ((fn2-checkpoint-future (fn2-checkpoint-future-set-phase 0 *fn2-checkpoint-future-phase-uncertain* fn2-checkpoint-future)))
         (mv :partial fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)))
       (fn2-checkpoint-future-windows (fn2-checkpoint-future-windows-put i (live 1) (slot slot) (generation generation) (borrowed 0)))
       (fn2-checkpoint-future (fn2-checkpoint-future-set-reserved 0 (+ i 1) fn2-checkpoint-future)))
   (fn2-checkpoint-future-reserve-loop (+ i 1) nonce kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)))))
 :hints (("Goal" :expand ((fn2-checkpoint-future-reserve-loop i nonce kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
  :in-theory (disable fn2-checkpoint-future-reserve-loop))))

(defthm fn2-checkpoint-future-reserve-loop-logical-nonnatural-index-refuses-by-definition
 (equal (fn2-checkpoint-future-reserve-loop 1/2 nonce kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool) (mv :bounds fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
 :hints (("Goal" :expand ((fn2-checkpoint-future-reserve-loop 1/2 nonce kind owner gen fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
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

; Actual public preconditions and factory instantiations, extracted from source.
(defthm fn2-checkpoint-root1-reserve-actual-zero-entry-domain
 (implies (and (unsigned-byte-p 32 c) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
                    (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows))
                    (< 0 (fn2-csnapshot-rows fn2-csnapshot))
                    (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
                    (posp token)
                    (fn2-csnapshot-ownerp token kind owner generation fn2-csnapshot)
                    (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-idle*)
                    (equal (fn2-checkpoint-root1-reserved 0 fn2-checkpoint-root1) 0)
                    (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future))
                    (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
                    (equal (fn2-checkpoint-future-phase 0 fn2-checkpoint-future) *fn2-checkpoint-future-phase-idle*)
                    (equal (fn2-checkpoint-future-reserved 0 fn2-checkpoint-future) 0)
                    (fn2-pool-mrefp kind owner generation))
          (and (natp 0) (<= 0 *fn2-checkpoint-window-count*) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1)) (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows)))))

(defthm fn2-checkpoint-future-reserve-with-credit-actual-zero-entry-domain
 (implies (and (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future))
                    (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
                    (equal (fn2-checkpoint-future-phase 0 fn2-checkpoint-future) *fn2-checkpoint-future-phase-idle*)
                    (equal (fn2-checkpoint-future-reserved 0 fn2-checkpoint-future) 0) (unsigned-byte-p 32 c) (fn2-pool-mrefp kind owner gen)
                    (unsigned-byte-p 60 nonce)
                    (if (equal (fn2-pool-credit-configured fn2-pool) 1)
                        (and (fn2-pool-credit-ownerp *fn2-checkpoint-working-credit-group* nonce kind owner gen fn2-pool)
                             (equal (fn2-pool-credit-phasei *fn2-checkpoint-working-credit-group* fn2-pool) *fn2-pool-credit-redeeming*))
                      (equal nonce 0)))
          (and (natp 0) (<= 0 8) (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future)) (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))))

(defthm fn2-checkpoint-future-borrow-journal-actual-transfer-entry-domain
 (implies (and (fn2-checkpoint-future-ownerp kind owner gen fn2-checkpoint-future)
            (fn2-pool-mrefp kind owner gen) (fn2-pool-mrefp bkind borrower bgen) (posp token)
            (equal token (fn2-checkpoint-future-token 0 fn2-checkpoint-future))
            (<= 5 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
            (fn2-checkpoint-future-transfer-readyp 1 5 nil token kind owner gen bkind borrower bgen
             fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
          (and (natp 1) (natp 5) (<= 1 5) (<= 5 8) (<= 5 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))))

(defthm fn2-checkpoint-future-return-journal-actual-transfer-entry-domain
 (implies (and (fn2-checkpoint-future-ownerp kind owner gen fn2-checkpoint-future)
            (fn2-pool-mrefp kind owner gen) (fn2-pool-mrefp bkind borrower bgen) (posp token)
            (equal token (fn2-checkpoint-future-token 0 fn2-checkpoint-future))
            (<= 5 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
            (fn2-checkpoint-future-transfer-readyp 1 5 t token kind owner gen bkind borrower bgen
             fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
          (and (natp 1) (natp 5) (<= 1 5) (<= 5 8) (<= 5 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))))

(defthm fn2-checkpoint-future-borrow-anchor-actual-transfer-entry-domain
 (implies (and (fn2-checkpoint-future-ownerp kind owner gen fn2-checkpoint-future)
            (fn2-pool-mrefp kind owner gen) (fn2-pool-mrefp bkind borrower bgen) (posp token)
            (equal token (fn2-checkpoint-future-token 0 fn2-checkpoint-future))
            (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
            (fn2-checkpoint-future-transfer-readyp 5 8 nil token kind owner gen bkind borrower bgen
             fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
          (and (natp 5) (natp 8) (<= 5 8) (<= 8 8) (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))))

(defthm fn2-checkpoint-future-return-anchor-actual-transfer-entry-domain
 (implies (and (fn2-checkpoint-future-ownerp kind owner gen fn2-checkpoint-future)
            (fn2-pool-mrefp kind owner gen) (fn2-pool-mrefp bkind borrower bgen) (posp token)
            (equal token (fn2-checkpoint-future-token 0 fn2-checkpoint-future))
            (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
            (fn2-checkpoint-future-transfer-readyp 5 8 t token kind owner gen bkind borrower bgen
             fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
          (and (natp 5) (natp 8) (<= 5 8) (<= 8 8) (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))))

(defthm fn2-checkpoint-future-release-one-actual-prefix-domain
 (implies (and (posp left) (<= left 8) (<= left (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))
          (and (natp 0) (natp left) (<= 0 left) (<= left (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows)))))
