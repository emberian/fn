; Match the installed table to every input and identify the version that
; the reader snapshots when it enumerates the runs.
(in-package "ACL2")
(include-book "range-built-sources-proof")
(include-book "range-enumerated-sources-proof")
(include-book "range-visible-streams-proof")

(defthmd fn2-range-setup-build-catalog
  (let* ((build (fn2-range-build-from-setup sid layout inputs))
         (inst (mv-nth 6 build)))
    (implies (and (natp n) (<= n 16) (equal (car build) :ok))
             (fn2-range-input-descriptors-p n sid inputs inst)))
  :hints (("Goal" :induct (fn2-range-nonempty-run-indices n inputs)
           :expand ((:free (inst) (fn2-range-input-descriptors-p n sid inputs inst)))
           :in-theory (e/d (fn2-range-built-source-at-input-index)
                     ((:definition fn2-range-input-descriptors-p) fn2-rga-setup fn2-rga-builds fn2-run-installed-source
                      (:definition fn2-range-nonempty-run-indices) nth len))
           :do-not '(preprocess))))

(local
 (defthm fn2-range-index-outside-input
   (implies (and (natp n) (<= (len xs) n)) (equal (nth n xs) nil))
   :hints (("Goal" :induct (nth n xs)))))

(defthmd fn2-range-run-count-fits-input
  (let ((refs (fn2-range-nonempty-run-indices n inputs)))
    (and (<= (len refs) (nfix n)) (<= (len refs) (len inputs))))
  :hints (("Goal" :induct (fn2-range-nonempty-run-indices n inputs)
           :in-theory (disable nth))))

(defthmd fn2-range-input-catalog-version
  (let* ((refs (fn2-range-nonempty-run-indices n inputs)) (v (fn2-run-version sid n inst)))
    (implies (and (natp n) (fn2-range-input-descriptors-p n sid inputs inst))
             (and (<= v n) (equal v (if (consp refs) (1+ (car refs)) 0)))))
  :hints (("Goal" :induct (fn2-range-nonempty-run-indices n inputs)
           :do-not '(preprocess)
           :expand ((fn2-run-version sid n inst) (fn2-range-input-descriptors-p n sid inputs inst)
                    (fn2-range-nonempty-run-indices n inputs))
           :in-theory (e/d (fn2-run-installed-source)
                       (fn2-run-installed-state fn2-run-installed-schema fn2-run-installed-run
                        fn2-run-installed-entries fn2-run-installed-okind fn2-run-installed-oslot
                        fn2-run-installed-ogen nth len)))))

(defun fn2-range-streams-at-indices (refs inputs acc)
  (declare (xargs :verify-guards nil))
  (if (atom refs) acc
    (fn2-range-streams-at-indices (cdr refs) inputs (cons (nth (car refs) inputs) acc))))

(local
 (defthm fn2-range-take-one-more
   (implies (natp j)
            (equal (take (1+ j) xs) (append (take j xs) (list (nth j xs)))))
   :hints (("Goal" :induct (nth j xs)))))

(local
 (defthm fn2-range-concatenate-visible-runs
   (equal (fn2-range-visible-streams (append a b) nil)
          (append (fn2-range-visible-streams a nil) (fn2-range-visible-streams b nil)))))

(local
 (defthm fn2-range-cons-after-prefix
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defun fn2-range-collected-streams-induct (n inputs acc)
   (declare (xargs :verify-guards nil :measure (nfix n)))
   (if (zp n) acc
     (let ((rows (nth (1- n) inputs)))
       (fn2-range-collected-streams-induct (1- n) inputs (if (consp rows) (cons rows acc) acc))))))

(defthmd fn2-range-enumerated-streams-match-input-prefix
  (implies (natp n)
           (equal (fn2-range-streams-at-indices (fn2-range-nonempty-run-indices n inputs) inputs acc)
                  (append (fn2-range-visible-streams (take n inputs) nil) acc)))
  :hints (("Goal" :induct (fn2-range-collected-streams-induct n inputs acc)
           :expand ((take 0 inputs)) :in-theory (disable nth take))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use ((:instance fn2-range-take-one-more (j (1- n)) (xs inputs)))))))

(local
 (defthm fn2-range-visible-padded-input
   (implies (and (natp n) (<= (len inputs) n))
            (equal (fn2-range-visible-streams (take n inputs) nil)
                   (fn2-range-visible-streams inputs nil)))
   :hints (("Goal" :induct (take n inputs) :in-theory (disable fn2-range-take-one-more)))))

(defthmd fn2-range-enumerated-streams-match-built-input
  (implies (and (natp n) (<= (len inputs) n))
           (equal (fn2-range-streams-at-indices (fn2-range-nonempty-run-indices n inputs) inputs acc)
                  (append (fn2-range-visible-streams inputs nil) acc)))
  :hints (("Goal" :use fn2-range-enumerated-streams-match-input-prefix
           :in-theory (disable fn2-range-visible-streams fn2-range-nonempty-run-indices fn2-range-streams-at-indices))))
