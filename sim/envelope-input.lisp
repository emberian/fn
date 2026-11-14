; Physical input effects recorded by ENVELOPE. This is a replay boundary,
; not a theorem about the raw host or the kernel supplying these bytes.
(in-package "ACL2")
(include-book "../books/pool")
(include-book "../books/vocab")

(defun fn2-envelope-input-effect-p (kind outcome)
  (declare (xargs :guard t))
  (or (and (equal kind *fn2-action-receive*)
           (equal outcome *fn2-outcome-done*))
      (and (equal kind *fn2-action-read*)
           (or (equal outcome *fn2-outcome-done*)
               (equal outcome *fn2-outcome-short*)))))

(defun fn2-envelope-write-loan (k octets slot gen op opgen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool) :verify-guards nil :measure (len octets)))
  (if (atom octets) (mv :ok fn2-pool)
    (mv-let (code fn2-pool) (fn2-pool-adapter-write slot gen op opgen k (car octets) fn2-pool)
      (if (not (eq code :ok)) (mv code fn2-pool)
        (fn2-envelope-write-loan (+ 1 (nfix k)) (cdr octets) slot gen op opgen fn2-pool)))))

(defun fn2-envelope-input (kind outcome count octets k slot gen op opgen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool) :verify-guards nil))
  (if (fn2-envelope-input-effect-p kind outcome)
      (if (equal (len octets) count)
          (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool)
        (mv :receive-count fn2-pool))
    (mv :ok fn2-pool)))

; An independent pointwise description: replacement occurs exactly inside
; the recorded prefix, not over the whole admitted loan or pool row.
(defun fn2-envelope-prefix-byte (at address octets old-byte)
  (declare (xargs :guard (and (natp at) (natp address) (true-listp octets))))
  (if (and (<= address at) (< at (+ address (len octets))))
      (nth (- at address) octets)
    old-byte))

(defthm fn2-envelope-write-loan-keeps-base
  (equal (fn2-pool-base other
           (mv-nth 1 (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool)))
         (fn2-pool-base other fn2-pool))
  :hints (("Goal" :induct (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool)
           :in-theory (enable fn2-envelope-write-loan))))

; Metadata and exact-byte statements are proved in this leaf book before
; check-envelope uses the writer. No core callback closure is needed here.
(defthm fn2-envelope-datai-of-update
  (implies (and (natp at) (natp address))
           (equal (fn2-pool-datai at (update-fn2-pool-datai address byte fn2-pool))
                  (if (equal at address) byte (fn2-pool-datai at fn2-pool))))
  :hints (("Goal" :in-theory (enable fn2-pool-datai update-fn2-pool-datai))))

(defthm fn2-envelope-prefix-byte-cons
  (implies (and (natp at) (natp address))
           (equal (fn2-envelope-prefix-byte at address (cons byte rest) old-byte)
                  (fn2-envelope-prefix-byte at (+ 1 address) rest
                    (if (equal at address) byte old-byte))))
  :hints (("Goal" :in-theory (enable fn2-envelope-prefix-byte nth))))

(defthm fn2-envelope-write-loan-metadata
  (implies (and (natp field) (not (equal field *fn2-pool-datai*)))
           (equal (nth field
                    (mv-nth 1 (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool)))
                  (nth field fn2-pool)))
  :hints (("Goal" :induct (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool)
           :in-theory (enable fn2-envelope-write-loan fn2-pool-adapter-write
                              update-fn2-pool-datai))))

(defthm fn2-envelope-prefix-byte-atom
  (implies (atom octets)
           (equal (fn2-envelope-prefix-byte at address octets old-byte) old-byte))
  :hints (("Goal" :in-theory (enable fn2-envelope-prefix-byte))))

(defthm fn2-envelope-write-loan-exact-prefix
  (implies (and (natp at) (natp k) (natp (fn2-pool-base slot fn2-pool))
                (eq (mv-nth 0 (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool)) :ok))
           (equal (fn2-pool-datai at
                    (mv-nth 1 (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool)))
                  (fn2-envelope-prefix-byte at (+ (fn2-pool-base slot fn2-pool) k)
                    octets (fn2-pool-datai at fn2-pool))))
  :hints (("Goal" :induct (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool)
           :in-theory (e/d (fn2-envelope-write-loan fn2-pool-adapter-write)
                           (fn2-pool-base fn2-pool-datai update-fn2-pool-datai
                            fn2-envelope-prefix-byte)))))

(defthm fn2-envelope-input-exact-prefix
  (implies (and (fn2-envelope-input-effect-p kind outcome)
                (natp at) (natp k) (natp (fn2-pool-base slot fn2-pool))
                (eq (mv-nth 0 (fn2-envelope-input kind outcome count octets k slot gen op opgen fn2-pool)) :ok))
           (equal (fn2-pool-datai at
                    (mv-nth 1 (fn2-envelope-input kind outcome count octets k slot gen op opgen fn2-pool)))
                  (fn2-envelope-prefix-byte at (+ (fn2-pool-base slot fn2-pool) k)
                    octets (fn2-pool-datai at fn2-pool))))
  :hints (("Goal" :in-theory (e/d (fn2-envelope-input)
                                 (fn2-envelope-write-loan fn2-envelope-prefix-byte
                                  fn2-pool-datai fn2-pool-base)))))

(defthm fn2-envelope-input-metadata
  (implies (and (natp field) (not (equal field *fn2-pool-datai*)))
           (equal (nth field
                    (mv-nth 1 (fn2-envelope-input kind outcome count octets k slot gen op opgen fn2-pool)))
                  (nth field fn2-pool)))
  :hints (("Goal" :in-theory (e/d (fn2-envelope-input) (fn2-envelope-write-loan)))))

(defthm fn2-envelope-input-count-refusal
  (implies (and (fn2-envelope-input-effect-p kind outcome)
                (not (equal (len octets) count)))
           (equal (fn2-envelope-input kind outcome count octets k slot gen op opgen fn2-pool)
                  (mv :receive-count fn2-pool)))
  :hints (("Goal" :in-theory (enable fn2-envelope-input))))

(defthm fn2-envelope-write-loan-wfp
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
           (fn2-pool-wfp (mv-nth 1 (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool))))
  :hints (("Goal" :induct (fn2-envelope-write-loan k octets slot gen op opgen fn2-pool)
           :in-theory (enable fn2-envelope-write-loan))))

(verify-guards fn2-envelope-write-loan)
(verify-guards fn2-envelope-input)

(in-theory (disable fn2-envelope-write-loan fn2-envelope-input fn2-envelope-prefix-byte))
