; The layout parser and a checked window of pool bytes take the same step.
(in-package "ACL2")
(include-book "runs-load-bytes-proof")
(include-book "runs-page-reader-proof")

(defun fn2-run-field-result (k xs pos v hi size phase)
  (declare (xargs :measure (len xs) :verify-guards nil))
  (cond ((equal k '(:zero 0)) (mv :ok xs nil))
        ((atom xs) (mv :truncated xs nil))
        (t (mv-let (code nv nh ns ph) (fn2-layout-byte k pos v hi size phase (car xs))
             (cond ((eq code :done) (mv :ok (cdr xs) nv))
                   ((member-eq code '(:part :payload))
                    (fn2-run-field-result k (cdr xs) (if (eq code :payload) 0 (1+ (nfix pos)))
                                        nv nh ns ph))
                   (t (mv code (cdr xs) nil)))))))

(defun fn2-run-scalar-kindp (k)
  (declare (xargs :guard t))
  (if (or (member-eq k '(:u8 :u16 :u32 :u64 :u16be :u32be :u64be :varint :u60 :bool))
          (and (consp k) (member-eq (car k) '(:id :enum))))
      t nil))

(defthmd fn2-run-scalar-kind-code
  (equal (fn2-run-scalar-kindp k)
         (not (member-equal (fn2-layout-kind-code k) '(7 10 11 15 16))))
  :hints (("Goal" :in-theory (enable fn2-layout-kind-code))))

(defthm fn2-run-field-result-of-parser
 (let ((parse (fn2-layout-parse-field k bytes xs pos v hi size ref phase next))
       (span (fn2-run-field-result k xs pos v hi size phase)))
  (and (equal (mv-nth 0 parse) (mv-nth 0 span))
       (equal (mv-nth 2 parse) (mv-nth 1 span))
       (implies (fn2-run-scalar-kindp k) (equal (mv-nth 1 parse) (mv-nth 2 span)))))
 :hints (("Goal" :induct (fn2-layout-parse-field k bytes xs pos v hi size ref phase next)
          :in-theory (e/d (fn2-layout-parse-field fn2-run-field-result fn2-run-scalar-kind-code)
                          (fn2-layout-byte fn2-layout-kind-code fn2-run-scalar-kindp take nthcdr mv-nth))
          :expand ((:free (a b c) (mv-nth 0 (list a b c)))
                   (:free (a b c) (mv-nth 2 (list a b c)))
                   (:free (a b c) (mv-nth 1 (list a b c)))))))

(defun fn2-run-parser-span (layout xs pos v hi size phase)
 (declare (xargs :verify-guards nil))
 (if (atom layout) (mv :ok xs)
   (mv-let (code rest value) (fn2-run-field-result (cadar layout) xs pos v hi size phase)
     (declare (ignore value))
     (if (eq code :ok)
         (mv-let (code values tail) (fn2-layout-parse (cdr layout) rest)
           (declare (ignore values)) (mv code tail))
       (mv code rest)))))

(defthm fn2-run-parser-span-at-start
 (let ((spec (fn2-layout-parse layout xs))
       (span (fn2-run-parser-span layout xs 0 0 0 0 0)))
  (and (equal (car span) (car spec))
       (equal (mv-nth 1 span) (mv-nth 2 spec))))
 :hints (("Goal" :expand ((fn2-layout-parse layout xs))
          :in-theory (e/d (fn2-run-parser-span)
                          (fn2-layout-parse fn2-layout-parse-field fn2-run-field-result)))))

(defthm fn2-run-parser-transition-status
 (not (equal (car (fn2-layout-byte k pos v hi size phase byte)) :ok))
 :hints (("Goal" :in-theory (e/d (fn2-layout-byte)
                                 (fn2-layout-kind-code nfix mod ash member-equal)))))

(defthm fn2-run-parser-span-step
 (let* ((k (cadar layout)) (step (fn2-layout-byte k pos v hi size phase byte))
        (code (car step)))
   (implies (and (consp layout) (not (equal k '(:zero 0))))
            (equal (fn2-run-parser-span layout (cons byte xs) pos v hi size phase)
              (cond ((eq code :done) (fn2-run-parser-span (cdr layout) xs 0 0 0 0 0))
                    ((member-eq code '(:part :payload))
                     (fn2-run-parser-span layout xs (if (eq code :payload) 0 (1+ (nfix pos)))
                        (mv-nth 1 step) (mv-nth 2 step) (mv-nth 3 step) (mv-nth 4 step)))
                    (t (list code xs))))))
 :hints (("Goal" :expand ((:free (k) (fn2-run-field-result k (cons byte xs) pos v hi size phase))
                           (fn2-layout-parse (cdr layout) xs))
          :in-theory (e/d (fn2-run-parser-span)
                          (fn2-run-parser-span-at-start fn2-run-field-result fn2-layout-byte
                           fn2-layout-parse fn2-layout-parse-field)))))

(defthm fn2-run-parser-span-boundaries
 (and (implies (atom layout)
               (equal (fn2-run-parser-span layout xs pos v hi size phase) (list :ok xs)))
      (implies (and (consp layout) (equal (cadar layout) '(:zero 0)))
               (equal (fn2-run-parser-span layout xs pos v hi size phase)
                      (fn2-run-parser-span (cdr layout) xs 0 0 0 0 0)))
      (implies (and (consp layout) (not (equal (cadar layout) '(:zero 0))))
               (equal (fn2-run-parser-span layout nil pos v hi size phase) (list :truncated nil))))
 :hints (("Goal" :expand ((fn2-layout-parse (cdr layout) xs))
          :in-theory (e/d (fn2-run-parser-span fn2-run-field-result)
                          (fn2-run-parser-span-at-start fn2-layout-parse-field fn2-layout-byte fn2-layout-parse)))))

(defthm fn2-run-page-window-advance
 (implies (and (natp next) (natp bound) (< next bound) (natp (fn2-pool-base slot pool))
               (eq (fn2-layout-range-code slot gen next bound nil pk ps pg pool) :ok))
          (and (equal (car (fn2-pool-read slot gen next pk ps pg pool)) :ok)
               (equal (fn2-layout-range-code slot gen (+ 1 next) bound nil pk ps pg pool) :ok)))
 :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-read fn2-pool-slot-base
                                    fn2-pool-slot-fill fn2-pool-capacity-bytes)
                                  (fn2-pool-readable-code fn2-pool-base fn2-pool-fill fn2-pool-data-length)))))

(defun-nx fn2-run-page-window (next bound slot gen pk ps pg pool)
 (fn2-run-read-bytes (- bound next) slot gen next pk ps pg pool))

(defthmd fn2-run-page-window-cons
  (implies (and (natp next) (natp bound) (< next bound) (natp (fn2-pool-base slot pool))
                (eq (fn2-layout-range-code slot gen next bound nil pk ps pg pool) :ok))
           (equal (fn2-run-page-window next bound slot gen pk ps pg pool)
                  (cons (mv-nth 1 (fn2-pool-read slot gen next pk ps pg pool))
                        (fn2-run-page-window (+ 1 next) bound slot gen pk ps pg pool))))
  :hints (("Goal" :use (fn2-run-page-window-advance)
           :expand ((fn2-run-read-bytes (- bound next) slot gen next pk ps pg pool))
           :in-theory (e/d (fn2-run-page-window)
                        (fn2-layout-range-code fn2-pool-base fn2-run-read-bytes fn2-pool-read)))))

(local
 (defthm fn2-run-read-bytes-length
  (equal (len (fn2-run-read-bytes n src sg at pk ps pg pool)) (nfix n))
  :hints (("Goal" :induct (fn2-run-read-bytes n src sg at pk ps pg pool)
           :in-theory (disable fn2-pool-read)))))

(defthm fn2-run-page-window-length
 (implies (and (natp next) (natp bound) (<= next bound))
          (equal (len (fn2-run-page-window next bound slot gen pk ps pg pool)) (- bound next)))
 :hints (("Goal" :use ((:instance fn2-run-read-bytes-length
             (n (- bound next)) (src slot) (sg gen) (at next)))
          :in-theory (enable fn2-run-page-window))))

(defthm fn2-run-empty-page-window
 (implies (equal next bound) (equal (fn2-run-page-window next bound slot gen pk ps pg pool) nil))
 :hints (("Goal" :in-theory (enable fn2-run-page-window fn2-run-read-bytes))))

(defthm fn2-run-successful-field-has-a-byte
 (implies (and (natp next) (natp bound) (<= next bound) (consp layout)
               (not (equal (cadar layout) '(:zero 0)))
               (eq (car (fn2-run-parser-span layout (fn2-run-page-window next bound slot gen pk ps pg pool)
                                             pos v hi size phase)) :ok))
          (< next bound))
 :rule-classes ((:forward-chaining :trigger-terms ((fn2-run-parser-span layout (fn2-run-page-window next bound slot gen pk ps pg pool) pos v hi size phase))))
 :hints (("Goal" :cases ((equal next bound))
          :in-theory (disable fn2-run-parser-span fn2-run-parser-span-at-start fn2-run-page-window))))

(defthm fn2-run-checked-parser-step
 (let* ((xs (fn2-run-page-window next bound slot gen pk ps pg pool))
        (rest (fn2-run-page-window (1+ next) bound slot gen pk ps pg pool))
        (span (fn2-run-parser-span layout xs pos v hi size phase))
        (read (fn2-pool-read slot gen next pk ps pg pool))
        (step (fn2-layout-byte (cadar layout) pos v hi size phase (mv-nth 1 read)))
        (code (car step)))
  (implies (and (consp layout) (not (equal (cadar layout) '(:zero 0)))
                (natp next) (natp bound) (<= next bound) (natp (fn2-pool-base slot pool))
                (eq (fn2-layout-range-code slot gen next bound nil pk ps pg pool) :ok)
                (eq (car span) :ok))
           (and (< next bound) (eq (car read) :ok)
                (eq (fn2-layout-range-code slot gen (1+ next) bound nil pk ps pg pool) :ok)
                (member-eq code '(:done :part :payload))
                (equal (if (eq code :done)
                           (fn2-run-parser-span (cdr layout) rest 0 0 0 0 0)
                         (fn2-run-parser-span layout rest (if (eq code :payload) 0 (1+ (nfix pos)))
                            (mv-nth 1 step) (mv-nth 2 step) (mv-nth 3 step) (mv-nth 4 step)))
                       span))))
 :rule-classes nil
 :hints (("Goal" :cases ((equal next bound))
          :use (fn2-run-page-window-cons fn2-run-page-window-advance
                (:instance fn2-run-parser-span-step (byte (mv-nth 1 (fn2-pool-read slot gen next pk ps pg pool)))
                 (xs (fn2-run-page-window (+ 1 next) bound slot gen pk ps pg pool))))
          :in-theory (disable fn2-run-parser-span fn2-run-parser-span-at-start fn2-run-page-window
                              fn2-layout-range-code fn2-pool-base fn2-layout-byte fn2-pool-read))))
