; The final overview field stores a reference to the original payload bytes.
(in-package "ACL2")
(include-book "runs-page-window-proof")

(local
 (defun fn2-run-line-payload-induct (pos next fuel size)
   (declare (xargs :measure (nfix fuel)))
   (if (or (zp fuel) (>= (+ 1 pos) size)) (list pos next fuel)
     (fn2-run-line-payload-induct (1+ pos) (1+ next) (1- fuel) size))))

(local
 (defthm fn2-run-line-payload-byte
   (equal (fn2-layout-byte '(:octets 1024) pos 0 0 size 1 b)
          (list (if (>= (1+ pos) size) :done :part) 0 0 size 1))
   :hints (("Goal" :in-theory (enable fn2-layout-byte)))))

(defthmd fn2-run-scan-line-payload
  (let* ((next (+ off pos)) (bound (+ off size))
         (scan (fn2-layout-scan '((line (:octets 1024))) fuel i pos 0 0 size off 1
                                next slot gen end pk ps pg f pool)))
    (implies (and (natp i) (< i (fn2-fields-rows f)) (natp off) (natp pos) (natp size) (< pos size)
                  (natp fuel) (<= (- size pos) fuel) (<= bound end)
                  (natp (fn2-pool-base slot pool))
                  (eq (fn2-layout-range-code slot gen next bound nil pk ps pg pool) :ok))
             (and (equal (car scan) :ok) (equal (mv-nth 8 scan) bound)
                  (equal (mv-nth 9 scan) (fn2-layout-store i 0 slot gen off size 0 f)))))
  :hints (("Goal" :induct (fn2-run-line-payload-induct pos next fuel size)
           :do-not '(preprocess generalize fertilize eliminate-destructors)
           :expand ((:free (nx) (fn2-layout-scan '((line (:octets 1024))) fuel i pos 0 0 size off 1
                                                 nx slot gen end pk ps pg f pool))
                    (:free (i fuel next f) (fn2-layout-scan nil fuel i 0 0 0 0 0 0 next slot gen end pk ps pg f pool)))
           :in-theory (e/d (fn2-run-reader-nfix)
                           (fn2-pool-read fn2-layout-byte fn2-layout-store fn2-fields-rows fn2-fields-value
                            fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                            fn2-fields-status fn2-layout-range-code fn2-pool-base mod nfix)))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use ((:instance fn2-run-page-window-advance (next (+ off pos)) (bound (+ off size))))))))

(local
 (defthm fn2-run-line-header-bytes
   (implies (and (natp n) (<= n 1024))
            (equal (fn2-layout-varoctets n)
                   (if (< n 128) (list n)
                     (list (+ 128 (mod n 128)) (floor n 128)))))
   :hints (("Goal" :expand ((fn2-layout-varoctets n) (fn2-layout-varoctets (floor n 128)))))))

(local
 (defthm fn2-run-line-header-transitions
   (implies (and (natp n) (<= n 1024))
            (if (< n 128)
                (equal (fn2-layout-byte '(:octets 1024) 0 0 0 0 0 n)
                       (list (if (zp n) :done :payload) 0 0 n 1))
              (and (equal (fn2-layout-byte '(:octets 1024) 0 0 0 0 0 (+ 128 (mod n 128)))
                          (list :part (mod n 128) 0 0 0))
                   (equal (fn2-layout-byte '(:octets 1024) 1 (mod n 128) 0 0 0 (floor n 128))
                          (list :payload 0 0 n 1)))))
   :hints (("Goal" :in-theory (enable fn2-layout-byte ash)))))

(local
 (defthm fn2-run-line-header-read
   (implies (and (posp n) (natp off) (equal (car (fn2-pool-read slot gen off pk ps pg pool)) :ok)
                 (equal (fn2-run-read-bytes n slot gen off pk ps pg pool) (cons b rest)))
            (and (equal (mv-nth 1 (fn2-pool-read slot gen off pk ps pg pool)) b)
                 (equal (fn2-run-read-bytes (1- n) slot gen (1+ off) pk ps pg pool) rest)))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-run-read-bytes n slot gen off pk ps pg pool))
            :in-theory (disable fn2-pool-read)))))

(local
 (defthmd fn2-run-scan-line-after-length
   (let* ((off (+ 1 at)) (bound (+ off size))
          (byte (mv-nth 1 (fn2-pool-read slot gen at pk ps pg pool)))
          (scan (fn2-layout-scan '((line (:octets 1024))) fuel i pos acc 0 0 0 0
                                 at slot gen end pk ps pg f pool)))
     (implies (and (natp size) (natp i) (< i (fn2-fields-rows f))
                   (natp at) (natp fuel) (<= (1+ size) fuel) (<= bound end)
                   (natp (fn2-pool-base slot pool))
                   (eq (fn2-layout-range-code slot gen at bound nil pk ps pg pool) :ok)
                   (unsigned-byte-p 8 byte)
                   (equal (fn2-layout-byte '(:octets 1024) pos acc 0 0 0 byte)
                          (list (if (zp size) :done :payload) 0 0 size 1)))
              (and (equal (car scan) :ok) (equal (mv-nth 8 scan) bound)
                   (equal (mv-nth 9 scan) (fn2-layout-store i 0 slot gen off size 0 f)))))
   :hints (("Goal" :cases ((zp size))
            :expand ((fn2-layout-scan '((line (:octets 1024))) fuel i pos acc 0 0 0 0
                                      at slot gen end pk ps pg f pool)
                     (:free (i fuel next f) (fn2-layout-scan nil fuel i 0 0 0 0 0 0 next slot gen end pk ps pg f pool)))
            :use ((:instance fn2-run-page-window-advance (next at) (bound (+ 1 at size)))
                  (:instance fn2-run-scan-line-payload (pos 0) (off (+ 1 at)) (fuel (1- fuel))))
            :in-theory (e/d (fn2-run-reader-nfix)
                           (fn2-pool-read fn2-layout-byte fn2-layout-store fn2-fields-rows fn2-fields-value
                            fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                            fn2-fields-status fn2-layout-range-code fn2-pool-base))))))

(local
 (defthmd fn2-run-scan-first-length-byte
   (let* ((b (mv-nth 1 (fn2-pool-read slot gen at pk ps pg pool)))
          (scan (fn2-layout-scan '((line (:octets 1024))) fuel i 0 0 0 0 0 0 at slot gen end pk ps pg f pool)))
     (implies (and (natp at) (< at end) (posp fuel) (natp i) (< i (fn2-fields-rows f))
                   (natp acc) (unsigned-byte-p 8 b) (equal (car (fn2-pool-read slot gen at pk ps pg pool)) :ok)
                   (equal (fn2-layout-byte '(:octets 1024) 0 0 0 0 0 b) (list :part acc 0 0 0)))
              (equal scan (fn2-layout-scan '((line (:octets 1024))) (1- fuel) i 1 acc 0 0 0 0
                                          (1+ at) slot gen end pk ps pg f pool))))
   :hints (("Goal" :expand ((fn2-layout-scan '((line (:octets 1024))) fuel i 0 0 0 0 0 0 at slot gen end pk ps pg f pool))
            :in-theory (disable fn2-layout-byte fn2-pool-read fn2-fields-rows fn2-layout-store)))))

(local
 (defthm fn2-run-line-first-checked-read
   (implies (and (natp at) (natp count) (posp count) (natp (fn2-pool-base slot pool))
                 (equal (fn2-layout-range-code slot gen at (+ at count) nil pk ps pg pool) :ok)
                 (equal (fn2-run-read-bytes count slot gen at pk ps pg pool) (cons b rest)))
            (and (equal (car (fn2-pool-read slot gen at pk ps pg pool)) :ok)
                 (equal (mv-nth 1 (fn2-pool-read slot gen at pk ps pg pool)) b)
                 (equal (fn2-layout-range-code slot gen (+ 1 at) (+ at count) nil pk ps pg pool) :ok)
                 (equal (fn2-run-read-bytes (1- count) slot gen (+ 1 at) pk ps pg pool) rest)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-line-header-read (n count) (off at))
                        (:instance fn2-run-page-window-advance (next at) (bound (+ at count))))
            :in-theory (disable fn2-pool-read fn2-pool-base fn2-run-read-bytes fn2-layout-range-code)))))

(local
 (defthm fn2-run-short-line-checked-read
   (implies (and (natp n) (< n 128) (natp at) (natp (fn2-pool-base slot pool))
                 (equal (fn2-layout-range-code slot gen at (+ at 1 n) nil pk ps pg pool) :ok)
                 (equal (fn2-run-read-bytes (+ 1 n) slot gen at pk ps pg pool) (cons n line)))
            (and (equal (mv-nth 1 (fn2-pool-read slot gen at pk ps pg pool)) n)
                 (equal (fn2-run-read-bytes n slot gen (+ 1 at) pk ps pg pool) line)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-line-first-checked-read (count (+ 1 n)) (b n) (rest line)))
            :in-theory (disable fn2-pool-read fn2-pool-base fn2-run-read-bytes fn2-layout-range-code)))))

(local
 (defthm fn2-run-long-line-checked-read
   (let ((low (+ 128 (mod n 128))) (high (floor n 128)) (bound (+ 2 at n)))
     (implies (and (natp n) (<= 128 n) (<= n 1024) (natp at) (natp (fn2-pool-base slot pool))
                   (equal (fn2-layout-range-code slot gen at bound nil pk ps pg pool) :ok)
                   (equal (fn2-run-read-bytes (+ 2 n) slot gen at pk ps pg pool) (cons low (cons high line))))
              (and (equal (car (fn2-pool-read slot gen at pk ps pg pool)) :ok)
                   (equal (mv-nth 1 (fn2-pool-read slot gen at pk ps pg pool)) low)
                   (equal (mv-nth 1 (fn2-pool-read slot gen (1+ at) pk ps pg pool)) high)
                   (equal (fn2-layout-range-code slot gen (+ 1 at) bound nil pk ps pg pool) :ok)
                   (equal (fn2-run-read-bytes n slot gen (+ 2 at) pk ps pg pool) line))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-line-first-checked-read (count (+ 2 n)) (b (+ 128 (mod n 128))) (rest (cons (floor n 128) line)))
                  (:instance fn2-run-line-first-checked-read (at (+ 1 at)) (count (+ 1 n)) (b (floor n 128)) (rest line)))
            :in-theory (disable fn2-pool-read fn2-pool-base fn2-run-read-bytes fn2-layout-range-code)))))
(local
 (defthm fn2-run-scan-long-header
   (let* ((scan (fn2-layout-scan '((line (:octets 1024))) fuel i 0 0 0 0 0 0 at slot gen end pk ps pg f pool))
          (low (+ 128 (mod n 128))) (high (floor n 128)) (bound (+ 2 at n)))
     (implies (and (natp n) (<= 128 n) (<= n 1024) (natp i) (< i (fn2-fields-rows f)) (natp at)
                   (natp fuel) (<= (+ 2 n) fuel) (<= bound end) (natp (fn2-pool-base slot pool))
                   (equal (car (fn2-pool-read slot gen at pk ps pg pool)) :ok)
                   (equal (mv-nth 1 (fn2-pool-read slot gen at pk ps pg pool)) low)
                   (equal (mv-nth 1 (fn2-pool-read slot gen (+ 1 at) pk ps pg pool)) high)
                   (equal (fn2-layout-range-code slot gen (+ 1 at) bound nil pk ps pg pool) :ok))
              (and (equal (car scan) :ok) (equal (mv-nth 8 scan) bound)
                   (equal (mv-nth 9 scan) (fn2-layout-store i 0 slot gen (+ 2 at) n 0 f)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-scan-line-after-length (at (+ 1 at)) (pos 1) (acc (mod n 128))
                             (fuel (1- fuel)) (size n))
                  (:instance fn2-run-line-header-transitions)
                  (:instance fn2-run-scan-first-length-byte (acc (mod n 128))))
            :in-theory (disable fn2-run-line-header-transitions fn2-fields-rows fn2-layout-store fn2-pool-base
                                fn2-layout-byte fn2-layout-range-code fn2-pool-read)))))

(local
 (defthm fn2-run-scan-short-header
   (let* ((scan (fn2-layout-scan '((line (:octets 1024))) fuel i 0 0 0 0 0 0 at slot gen end pk ps pg f pool))
          (bound (+ 1 at n)))
     (implies (and (natp n) (< n 128) (natp i) (< i (fn2-fields-rows f)) (natp at)
                   (natp fuel) (<= (+ 1 n) fuel) (<= bound end) (natp (fn2-pool-base slot pool))
                   (equal (mv-nth 1 (fn2-pool-read slot gen at pk ps pg pool)) n)
                   (equal (fn2-layout-range-code slot gen at bound nil pk ps pg pool) :ok))
              (and (equal (car scan) :ok) (equal (mv-nth 8 scan) bound)
                   (equal (mv-nth 9 scan) (fn2-layout-store i 0 slot gen (+ 1 at) n 0 f)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-scan-line-after-length (pos 0) (acc 0) (size n))
                  (:instance fn2-run-line-header-transitions))
            :in-theory (disable fn2-run-line-header-transitions fn2-fields-rows fn2-layout-store fn2-pool-base
                                fn2-layout-byte fn2-layout-range-code fn2-pool-read)))))
(defthm fn2-run-scan-stored-line
  (let* ((n (len line)) (header (fn2-layout-varoctets n)) (off (+ at (len header)))
         (bound (+ off n))
         (scan (fn2-layout-scan '((line (:octets 1024))) fuel i 0 0 0 0 0 0 at slot gen end pk ps pg f pool)))
    (implies (and (natp i) (< i (fn2-fields-rows f)) (natp at) (natp fuel)
                  (<= n 1024) (<= (+ (len header) n) fuel) (<= bound end)
                  (natp (fn2-pool-base slot pool))
                  (eq (fn2-layout-range-code slot gen at bound nil pk ps pg pool) :ok)
                  (equal (fn2-run-read-bytes (+ (len header) n) slot gen at pk ps pg pool)
                         (append header line)))
             (and (equal (car scan) :ok) (equal (mv-nth 8 scan) bound)
                  (equal (mv-nth 9 scan) (fn2-layout-store i 0 slot gen off n 0 f))
                  (equal (fn2-run-read-bytes n slot gen off pk ps pg pool) line))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :cases ((< (len line) 128))
           :in-theory (disable fn2-run-read-bytes fn2-pool-read fn2-layout-byte fn2-layout-store
                       fn2-fields-rows fn2-layout-range-code fn2-pool-base fn2-layout-varoctets
                       fn2-run-line-header-transitions fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen
                       fn2-fields-ref-off fn2-fields-ref-len fn2-fields-status))
          ("Subgoal 2" :use ((:instance fn2-run-long-line-checked-read (n (len line)))
                             (:instance fn2-run-scan-long-header (n (len line)))))
          ("Subgoal 1" :use ((:instance fn2-run-short-line-checked-read (n (len line)))
                             (:instance fn2-run-scan-short-header (n (len line)))))))
