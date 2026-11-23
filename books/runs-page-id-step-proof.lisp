; Following a selected ID through one byte of the checked page window.
(in-package "ACL2")
(include-book "runs-page-window-proof")

(defun fn2-run-id-prefixp (j layout)
 (declare (xargs :guard (natp j)))
 (and (consp layout) (consp (car layout)) (consp (cdar layout))
      (consp (cadar layout)) (eq (caadar layout) :id)
      (or (zp j) (fn2-run-id-prefixp (1- j) (cdr layout)))))

(defthm fn2-run-id-prefix-head
 (implies (fn2-run-id-prefixp j layout)
  (and (consp layout) (consp (cadar layout)) (equal (caadar layout) :id)
       (not (equal (cadar layout) '(:zero 0)))
       (implies (not (zp j)) (fn2-run-id-prefixp (1- j) (cdr layout)))))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :expand ((fn2-run-id-prefixp j layout)))))

(defthm fn2-run-id-prefix-target
 (implies (and (natp j) (fn2-run-id-prefixp j layout))
          (equal (fn2-layout-kind-code (cadr (nth j layout))) 8))
 :hints (("Goal" :induct (fn2-run-id-prefixp j layout) :expand ((nth j layout))
          :in-theory (enable fn2-run-id-prefixp))))

(defun fn2-run-parser-id (layout j xs pos v hi size phase)
 (declare (xargs :verify-guards nil))
 (mv-let (code rest value) (fn2-run-field-result (cadar layout) xs pos v hi size phase)
   (declare (ignore code))
   (if (zp j) value
     (mv-let (code values tail) (fn2-layout-parse (cdr layout) rest)
       (declare (ignore code tail)) (nth (1- j) values)))))

(defthm fn2-run-parser-id-at-start
 (let ((parse (fn2-layout-parse layout xs)))
  (implies (and (consp layout) (natp j)
                (equal (fn2-layout-kind-code (cadr (nth j layout))) 8)
                (equal (car parse) :ok))
           (equal (fn2-run-parser-id layout j xs 0 0 0 0 0)
                  (nth j (mv-nth 1 parse)))))
 :hints (("Goal" :cases ((zp j))
          :expand ((fn2-layout-parse layout xs) (nth j layout))
          :in-theory (e/d (fn2-run-parser-id) (fn2-run-field-result fn2-layout-parse-field
             fn2-layout-kind-code fn2-layout-parse)))) )

(local
 (defthm fn2-run-parser-id-part
 (let* ((k (cadar layout)) (step (fn2-layout-byte k pos v hi size phase byte)) (code (car step)))
  (implies (and (not (equal k '(:zero 0))) (member-eq code '(:part :payload)))
           (equal (fn2-run-parser-id layout j (cons byte xs) pos v hi size phase)
                  (fn2-run-parser-id layout j xs (if (eq code :payload) 0 (1+ (nfix pos)))
                   (mv-nth 1 step) (mv-nth 2 step) (mv-nth 3 step) (mv-nth 4 step)))))
 :hints (("Goal" :expand ((:free (k) (fn2-run-field-result k (cons byte xs) pos v hi size phase)))
          :in-theory (e/d (fn2-run-parser-id) (fn2-layout-byte fn2-run-field-result fn2-layout-parse))))))

(local
 (defthm fn2-run-parser-id-done
 (let* ((k (cadar layout)) (step (fn2-layout-byte k pos v hi size phase byte)))
  (implies (and (consp layout) (not (equal k '(:zero 0))) (equal (car step) :done))
           (equal (fn2-run-parser-id layout j (cons byte xs) pos v hi size phase)
                  (if (zp j) (mv-nth 1 step) (nth (1- j) (mv-nth 1 (fn2-layout-parse (cdr layout) xs)))))))
 :hints (("Goal" :expand ((:free (k) (fn2-run-field-result k (cons byte xs) pos v hi size phase)))
          :in-theory (e/d (fn2-run-parser-id) (fn2-layout-byte fn2-run-field-result fn2-layout-parse))))))

(local
 (defthm fn2-run-id-byte-shape
 (let ((step (fn2-layout-byte k pos v hi size 0 byte)))
  (implies (and (consp k) (eq (car k) :id))
           (and (not (eq (car step) :payload)) (equal (mv-nth 3 step) 0) (equal (mv-nth 4 step) 0))))
 :hints (("Goal" :in-theory (e/d (fn2-layout-byte) (ash mod))))))

(defthm fn2-run-id-window-step
 (let* ((xs (fn2-run-page-window next bound slot gen pk ps pg pool))
        (rest (fn2-run-page-window (1+ next) bound slot gen pk ps pg pool))
        (byte (mv-nth 1 (fn2-pool-read slot gen next pk ps pg pool)))
        (step (fn2-layout-byte (cadar layout) pos v hi size 0 byte)) (code (car step))
        (value (fn2-run-parser-id layout j xs pos v hi size 0)))
  (implies (and (natp j) (fn2-run-id-prefixp j layout)
                (natp next) (natp bound) (<= next bound) (natp (fn2-pool-base slot pool))
                (eq (fn2-layout-range-code slot gen next bound nil pk ps pg pool) :ok)
                (eq (car (fn2-run-parser-span layout xs pos v hi size 0)) :ok))
           (and (< next bound)
                (equal (car (fn2-pool-read slot gen next pk ps pg pool)) :ok)
                (eq (fn2-layout-range-code slot gen (1+ next) bound nil pk ps pg pool) :ok)
                (or (equal code :done) (equal code :part))
                (equal (mv-nth 3 step) 0) (equal (mv-nth 4 step) 0)
                (if (eq code :done)
                    (and (eq (car (fn2-run-parser-span (cdr layout) rest 0 0 0 0 0)) :ok)
                         (equal value (if (zp j) (mv-nth 1 step)
                                       (fn2-run-parser-id (cdr layout) (1- j) rest 0 0 0 0 0))))
                  (and (eq (car (fn2-run-parser-span layout rest (1+ (nfix pos)) (mv-nth 1 step) (mv-nth 2 step) 0 0)) :ok)
                       (equal value (fn2-run-parser-id layout j rest (1+ (nfix pos)) (mv-nth 1 step) (mv-nth 2 step) 0 0)))))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess generalize fertilize eliminate-destructors) :do-not-induct t

          :use ((:instance fn2-run-id-byte-shape (k (cadar layout)) (byte (mv-nth 1 (fn2-pool-read slot gen next pk ps pg pool))))
                (:instance fn2-run-parser-id-part (phase 0) (byte (mv-nth 1 (fn2-pool-read slot gen next pk ps pg pool))) (xs (fn2-run-page-window (1+ next) bound slot gen pk ps pg pool)))
(:instance fn2-run-parser-id-done (phase 0) (byte (mv-nth 1 (fn2-pool-read slot gen next pk ps pg pool))) (xs (fn2-run-page-window (1+ next) bound slot gen pk ps pg pool)))
                (:instance fn2-run-checked-parser-step (phase 0)) fn2-run-page-window-cons
                (:instance fn2-run-parser-span-at-start (layout (cdr layout))
                  (xs (fn2-run-page-window (+ 1 next) bound slot gen pk ps pg pool)))
                (:instance fn2-run-id-prefix-target (j (1- j)) (layout (cdr layout))))
          :in-theory (disable fn2-run-parser-id fn2-layout-byte fn2-run-field-result fn2-layout-parse
                      fn2-layout-kind-code fn2-run-parser-span fn2-run-parser-span-at-start fn2-run-page-window
                      fn2-layout-range-code fn2-pool-base fn2-pool-read fn2-run-id-prefixp
                      nth))))
