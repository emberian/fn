(in-package "ACL2")
(include-book "merkle")
(include-book "crash-model")
(include-book "owed-discharge")
(local (deftheory mc-initial-rules (current-theory :here)))

(local (defun mc-two-offsets (i j x)
  (if (and (posp i) (posp j) (consp x))
      (mc-two-offsets (1- i) (1- j) (cdr x))
    (list i j x))))

;; Use the total tuple readers even when reasoning about a partial update.
(local (defthm mc-at-put
  (implies (and (natp i) (natp j))
           (equal (fn2-cm-at i (fn2-cm-put j v x))
                  (if (and (equal i j) (< j (len x))) v (fn2-cm-at i x))))
  :hints (("Goal" :expand (fn2-cm-put j v x) :induct (mc-two-offsets i j x)))))

(local (defthm mc-len-put
  (equal (len (fn2-cm-put j v x)) (len x))))

;; All three image operations consume at most the rest of this tear unit.
(local (defthm mc-len-take
  (equal (len (fn2-cm-take n x)) (min (nfix n) (len x)))))
(local (defthm mc-len-drop
  (equal (len (fn2-cm-drop n x)) (nfix (- (len x) (nfix n))))))
(local (defthm mc-true-take
  (true-listp (fn2-cm-take n x))))
(local (defthm mc-take-before-append
  (implies (<= (nfix n) (len x))
           (equal (fn2-cm-take n (append x y)) (fn2-cm-take n x)))
  :hints (("Goal" :induct (fn2-cm-take n x)))))
(local (defthm mc-drop-append
  (implies (and (natp n) (<= (len x) n))
           (equal (fn2-cm-drop n (append x y))
                  (fn2-cm-drop (- n (len x)) y)))
  :hints (("Goal" :induct (fn2-cm-drop n x)))))
(local (defthm mc-drop-drop
  (implies (and (natp m) (natp n))
           (equal (fn2-cm-drop m (fn2-cm-drop n x))
                  (fn2-cm-drop (+ m n) x)))
  :hints (("Goal" :induct (fn2-cm-drop n x)))))
(local (defthm mc-read-before-splice
  (implies (and (natp a) (natp n) (natp b) (<= (+ a n) b)
                (<= b (len x)))
           (equal (fn2-cm-take n (fn2-cm-drop a (fn2-cm-splice-unit x b bytes)))
                  (fn2-cm-take n (fn2-cm-drop a x))))
  :hints (("Goal" :induct (mc-two-offsets a b x)))))
(local (defthm mc-read-after-splice
  (implies (and (natp a) (natp b) (<= b (len x))
                (<= (+ b (len bytes)) a))
           (equal (fn2-cm-drop a (fn2-cm-splice-unit x b bytes))
                  (fn2-cm-drop a x)))))

(local (defthm mc-len-append
  (equal (len (append x y)) (+ (len x) (len y)))))
(local (defthm mc-splice-len
  (implies (and (natp b) (<= (+ b (len bytes)) (len old)))
           (equal (len (fn2-cm-splice-unit old b bytes)) (len old)))))
(local (defthm mc-drop-empty
  (implies (and (natp n) (<= (len x) n) (true-listp x))
           (equal (fn2-cm-drop n x) nil))))
(local (defthm mc-consp-drop
  (iff (consp (fn2-cm-drop n x)) (< (nfix n) (len x)))))
(local (defun mc-range-induct (xs a n b bytes unit)
  (if (and (consp xs) (posp unit) (natp a) (natp b) (posp n) (consp bytes))
      (mc-range-induct (cdr xs)
                       (if (>= a unit) (- a unit) 0)
                       (if (>= a unit) n (- n (len (fn2-cm-take n (fn2-cm-drop a (car xs))))))
                       (if (>= b unit) (- b unit) 0)
                       (if (>= b unit) bytes (fn2-cm-drop (- unit b) bytes))
                       unit)
    (list a n b bytes))))
(local (in-theory (disable fn2-cm-splice-unit mc-drop-append mc-drop-drop)))
(local (defthm mc-part-len
  (implies (and (natp b) (<= b (len x)) (equal unit (len x)))
           (equal (len (fn2-cm-splice-unit x b (fn2-cm-take (- unit b) bytes)))
                  (len x)))
  :hints (("Goal" :use ((:instance mc-splice-len (old x)
                              (bytes (fn2-cm-take (- unit b) bytes))))))))
(local (defthm mc-disjoint-part
  (implies (and (natp a) (natp b) (natp n) (<= b unit)
                (equal (len x) unit)
                (or (<= (+ a n) b) (<= (+ b (len bytes)) a)))
           (equal (fn2-cm-take n (fn2-cm-drop a (fn2-cm-splice-unit x b (fn2-cm-take (- unit b) bytes))))
                  (fn2-cm-take n (fn2-cm-drop a x))))
  :hints (("Goal" :use ((:instance mc-read-before-splice (bytes (fn2-cm-take (- unit b) bytes)))
                         (:instance mc-read-after-splice (bytes (fn2-cm-take (- unit b) bytes))))))))
(local (defthm mc-disjoint-read-write
  (implies (and (natp a) (natp n) (natp b) (posp unit)
                (fn2-cm-imagep xs unit)
                (or (<= (+ a n) b) (<= (+ b (len bytes)) a)))
           (equal (fn2-cm-read-image (fn2-cm-write-image xs b bytes unit) a n unit)
                  (fn2-cm-read-image xs a n unit)))
  :hints (("Goal" :induct (mc-range-induct xs a n b bytes unit)
           :expand ((fn2-cm-write-image xs b bytes unit)
                    (fn2-cm-read-image xs a n unit))
           :in-theory (disable fn2-cm-take fn2-cm-drop fn2-cm-octetsp mc-read-before-splice mc-read-after-splice))
          ("Subgoal *1/1" :use ((:instance mc-disjoint-part (x (car xs)))
                                (:instance mc-part-len (x (car xs))))))))

(local (defmacro mc-rules (&rest rules)
  `(union-theories ',rules (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))))
(local (defmacro mc-reader (name i)
  `(defthm ,(packn-pos (list 'mc- name '-at) name)
     (equal (,name s) (fn2-cm-at ,i s))
     :hints (("Goal" :in-theory (enable ,name fn2-cm-at))))))
(local (mc-reader fn2-cm-geometry 0))
(local (mc-reader fn2-cm-durable 1))
(local (mc-reader fn2-cm-visible 2))
(local (mc-reader fn2-cm-dstamps 3))
(local (mc-reader fn2-cm-vstamps 4))
(local (mc-reader fn2-cm-cache 5))
(local (mc-reader fn2-cm-inflight 6))
(local (mc-reader fn2-cm-fences 7))
(local (defthm mc-state-geometry
  (implies (fn2-cm-statep s)
           (and (equal (len s) 12)
                (equal (fn2-cm-unit s) 512)
                (fn2-cm-imagep (fn2-cm-at 1 s) 512)))
  :hints (("Goal" :in-theory (mc-rules fn2-cm-statep fn2-cm-unit
                                       mc-fn2-cm-durable-at)))))
(local (defthm mc-code-ok
  (implies (equal (fn2-cm-at 0 outcome) :ok)
           (and (consp outcome) (equal (car outcome) :ok)))
  :hints (("Goal" :in-theory (enable fn2-cm-at)))))
(defthm fn2-cm-fua-alone-proved
  (fn2-cm-fua-alone$owed s op outcome profile addr count)
  :rule-classes nil
  :hints (("Goal" :in-theory
           (mc-rules fn2-cm-fua-alone$owed fn2-cm-fua-only-hyps fn2-cm-fua-only-concl
                     fn2-cm-range-p fn2-cm-complete-write mc-code-ok
                     mc-state-geometry mc-disjoint-read-write mc-len-take
                     mc-fn2-cm-durable-at mc-len-put mc-at-put min nfix)
           :use ((:instance mc-disjoint-read-write
                   (xs (fn2-cm-at 1 s)) (unit 512) (a addr) (n count)
                   (b (fn2-cm-at 1 outcome))
                   (bytes (fn2-cm-take
                           (len (fn2-cm-at 2 (fn2-cm-find op (fn2-cm-inflight s))))
                           (fn2-cm-at 2 (fn2-cm-find op (fn2-cm-inflight s))))))))))
(fn2-owed-discharge fn2-cm-fua-alone fn2-cm-fua-alone-proved)

(local (defthm mc-at-zero (equal (fn2-cm-at 0 x) (car x))))
(local (defthm mc-drop-one (equal (fn2-cm-drop 1 x) (cdr x))))
(local (defthm mc-zero-length
  (equal (equal (len xs) 0) (atom xs))
  :hints (("Goal" :expand (len xs) :in-theory (mc-rules (:type-prescription len))))))
(local (defthm mc-covered-merge
  (implies (and (equal (len old) (len new)) (true-listp new)
                (equal (len ns) (len new))
                (fn2-cm-covered-versions-p old ds new ns))
           (and (equal (fn2-cm-merge-unit old ds new ns nil) new)
                (not (fn2-cm-stamps-aheadp ns (fn2-cm-merge-unit old ds new ns t)))))
  :hints (("Goal" :induct (fn2-cm-covered-versions-p old ds new ns)
           :expand ((fn2-cm-merge-unit old ds new ns nil)
                    (fn2-cm-merge-unit old ds new ns t)
                    (:free (ds) (fn2-cm-stamps-aheadp ns ds)))
           :in-theory (mc-rules fn2-cm-covered-versions-p fn2-cm-merge-unit fn2-cm-stamps-aheadp
                       mc-at-zero mc-drop-one len true-listp car-cons cdr-cons cons-car-cdr
                       (:type-prescription nfix) (:type-prescription len) mc-zero-length)))))

(local (defthm mc-octets-true
  (implies (fn2-cm-octetsp x) (true-listp x))))
(local (defun mc-fence-induct (image old ds new ns vs i)
  (if (and (consp old) (consp new))
      (mc-fence-induct (cdr image) (cdr old) (cdr ds) (cdr new) (cdr ns)
                       (cdr vs) (+ 1 (nfix i)))
    (list image old ds new ns vs i))))
(local (defthm mc-covered-crash
  (implies
   (and (fn2-cm-imagep old unit) (fn2-cm-imagep new unit)
        (fn2-cm-stampsp ns unit serial)
        (equal (len old) (len new)) (equal (len ns) (len new))
        (fn2-cm-fence-isolatedp new ns old ds vs flights cache covered i unit radius)
        (fn2-cm-crash-units-allowedp
         image (fn2-cm-merge-image old ds new ns nil) vs
         (fn2-cm-merge-image old ds new ns t) flights cache i unit radius))
   (fn2-cm-covered-imagep image new covered i unit))
  :hints (("Goal" :induct (mc-fence-induct image old ds new ns vs i)
           :expand ((:free (durable stamps)
                     (fn2-cm-crash-units-allowedp image durable vs stamps flights cache i unit radius)))
           :in-theory (disable fn2-cm-merge-unit fn2-cm-covered-versions-p
                               fn2-cm-touches-p fn2-cm-covered-unit-p fn2-cm-at fn2-cm-drop
                               fn2-cm-octetsp fn2-cm-stamp-unitp fn2-cm-stamps-aheadp nfix)))))
(local (defthm mc-find-fence-shapes
  (let ((row (fn2-cm-find op rows)) (height (len (fn2-cm-durable s))))
    (implies (and (fn2-cm-fence-rows-p rows s) row)
             (and (fn2-cm-imagep (fn2-cm-at 1 row) (fn2-cm-unit s))
                  (equal (len (fn2-cm-at 1 row)) height)
                  (fn2-cm-stampsp (fn2-cm-at 2 row) (fn2-cm-unit s) (fn2-cm-serial s))
                  (equal (len (fn2-cm-at 2 row)) height))))
  :hints (("Goal" :induct (fn2-cm-find op rows)
           :in-theory (mc-rules fn2-cm-find fn2-cm-fence-rows-p)))))
(local (defthm mc-state-fences
  (implies (fn2-cm-statep s) (fn2-cm-fence-rows-p (fn2-cm-fences s) s))
  :hints (("Goal" :in-theory (mc-rules fn2-cm-statep)))))
(local (defthm mc-crash-only-radius
  (implies (and (fn2-cm-profilep p) (equal (fn2-cm-profile-kind p) :crash-only))
           (equal (fn2-cm-radius p) 0))
  :hints (("Goal" :in-theory (mc-rules fn2-cm-profilep)))))
(local (defthm mc-unit-at-geometry
  (equal (fn2-cm-unit (fn2-cm-put 7 v (fn2-cm-put 3 ds (fn2-cm-put 1 d s))))
         (fn2-cm-unit s))
  :hints (("Goal" :in-theory (mc-rules fn2-cm-unit mc-fn2-cm-geometry-at mc-at-put)))))
(local (defthm mc-zero-product (equal (* 0 x) 0)))
(defthm fn2-cm-honest-fence-durability-proved
  (fn2-cm-honest-fence-durability$owed s op image crash-image profile)
  :rule-classes nil
  :hints (("Goal" :use
           ((:instance mc-find-fence-shapes (rows (fn2-cm-fences s)))
            (:instance mc-covered-crash
             (image crash-image) (old (fn2-cm-durable s)) (ds (fn2-cm-dstamps s))
             (new (fn2-cm-at 1 (fn2-cm-find op (fn2-cm-fences s))))
             (ns (fn2-cm-at 2 (fn2-cm-find op (fn2-cm-fences s))))
             (vs (fn2-cm-vstamps s)) (flights (fn2-cm-inflight s)) (cache (fn2-cm-cache s))
             (covered (fn2-cm-at 3 (fn2-cm-find op (fn2-cm-fences s))))
             (i 0) (unit (fn2-cm-unit s)) (serial (fn2-cm-serial s))
             (radius (* (min (nfix (fn2-cm-radius profile))
                             (nfix (fn2-cm-at 3 (fn2-cm-geometry s))))
                        (nfix (fn2-cm-at 0 (fn2-cm-geometry s)))))))
           :in-theory
           (mc-rules fn2-cm-honest-fence-durability$owed fn2-cm-fence-durability-hyps
                     fn2-cm-fence-durability-concl fn2-cm-complete-fence fn2-cm-persist-snapshot
                     fn2-cm-crash-image-allowedp fn2-cm-fence-persists-p
                     mc-fn2-cm-geometry-at mc-fn2-cm-durable-at mc-fn2-cm-dstamps-at
                     mc-fn2-cm-vstamps-at mc-fn2-cm-inflight-at mc-fn2-cm-cache-at
                     mc-at-put mc-len-put mc-state-geometry mc-unit-at-geometry
                     mc-state-fences mc-crash-only-radius (:type-prescription nfix) mc-zero-product min nfix))))
(fn2-owed-discharge fn2-cm-honest-fence-durability fn2-cm-honest-fence-durability-proved)

;; Byte and stamp images share the same shape. Parameterizing their element
;; bound lets every image operation use one preservation proof.
(local (defun mc-vectorp (x bound)
  (if (consp x)
      (and (natp (car x)) (<= (car x) bound) (mc-vectorp (cdr x) bound))
    (null x))))
(local (defun mc-arrayp (xs unit bound)
  (if (consp xs)
      (and (equal (len (car xs)) unit) (mc-vectorp (car xs) bound)
           (mc-arrayp (cdr xs) unit bound))
    (null xs))))
(local (defthm mc-octets-vector
  (equal (fn2-cm-octetsp xs) (mc-vectorp xs 255))))
(local (defthm mc-stamp-vector
  (equal (fn2-cm-stamp-unitp xs serial)
         (mc-vectorp xs (min (nfix serial) (1- (expt 2 60)))))))
(local (defthm mc-image-array
  (equal (fn2-cm-imagep xs unit) (mc-arrayp xs unit 255))))
(local (defthm mc-stamps-array
  (equal (fn2-cm-stampsp xs unit serial)
         (mc-arrayp xs unit (min (nfix serial) (1- (expt 2 60)))))))
(local (defthm mc-vector-take
  (implies (mc-vectorp x bound) (mc-vectorp (fn2-cm-take n x) bound))))
(local (defthm mc-vector-drop
  (implies (mc-vectorp x bound) (mc-vectorp (fn2-cm-drop n x) bound))))
(local (defthm mc-vector-append
  (implies (and (mc-vectorp x bound) (mc-vectorp y bound))
           (mc-vectorp (append x y) bound))))
(local (defthm mc-vector-splice
  (implies (and (mc-vectorp old bound) (mc-vectorp bytes bound))
           (mc-vectorp (fn2-cm-splice-unit old b bytes) bound))
  :hints (("Goal" :in-theory (enable fn2-cm-splice-unit)))))
(local (defthm mc-array-write
  (implies (and (natp b) (mc-arrayp xs unit bound) (mc-vectorp bytes bound))
           (mc-arrayp (fn2-cm-write-image xs b bytes unit) unit bound))
  :hints (("Goal" :induct (fn2-cm-write-image xs b bytes unit)
           :in-theory (disable fn2-cm-drop fn2-cm-take))
          ("Subgoal *1/3" :use ((:instance mc-part-len (x (car xs))))))))
(local (defthm mc-length-write
  (equal (len (fn2-cm-write-image xs b bytes unit)) (len xs))))
(local (defthm mc-vector-repeat
  (implies (and (natp value) (<= value bound))
           (mc-vectorp (fn2-cm-repeat n value) bound))))
(local (defthm mc-vector-widen
  (implies (and (mc-vectorp x low) (<= low high))
           (mc-vectorp x high))
  :rule-classes nil))
(local (defthm mc-array-widen
  (implies (and (mc-arrayp xs unit low) (<= low high))
           (mc-arrayp xs unit high))
  :hints (("Goal" :induct (mc-arrayp xs unit low))
          ("Subgoal *1/1" :use ((:instance mc-vector-widen (x (car xs))))))
  :rule-classes nil))
(local (defthm mc-merge-length
  (and (equal (len (fn2-cm-merge-unit old ds new ns flag)) (len old))
       (equal (len (fn2-cm-merge-image old ds new ns flag)) (len old)))))
(local (defthm mc-merge-vector
  (implies (and (equal (len old) (len new)) (equal (len old) (len ns))
                (equal (len old) (len ds))
                (if flag (and (mc-vectorp ds bound) (mc-vectorp ns bound))
                  (and (mc-vectorp old bound) (mc-vectorp new bound))))
           (mc-vectorp (fn2-cm-merge-unit old ds new ns flag) bound))
  :hints (("Goal" :induct (fn2-cm-merge-unit old ds new ns flag)))))
(local (defthm mc-merge-array
  (implies (and (mc-arrayp old unit data) (mc-arrayp new unit data)
                (mc-arrayp ds unit stamps) (mc-arrayp ns unit stamps)
                (equal (len old) (len ds)) (equal (len old) (len ns))
                (equal (len old) (len new)))
           (mc-arrayp (fn2-cm-merge-image old ds new ns flag) unit (if flag stamps data)))
  :hints (("Goal" :induct (fn2-cm-merge-image old ds new ns flag)
           :in-theory (disable fn2-cm-merge-unit mc-vectorp)))))

(local (defthm mc-stamps-at-serial
  (implies (unsigned-byte-p 60 serial)
           (equal (fn2-cm-stampsp xs unit serial) (mc-arrayp xs unit serial)))))
(local (defthm mc-array-put
  (implies (and (mc-arrayp xs u bound) (mc-vectorp v bound) (equal (len v) u))
           (mc-arrayp (fn2-cm-put i v xs) u bound))))
(local (defthm mc-array-at
  (implies (and (mc-arrayp xs u bound) (natp i) (< i (len xs)))
           (and (equal (len (fn2-cm-at i xs)) u)
                (mc-vectorp (fn2-cm-at i xs) bound)))
  :hints (("Goal" :induct (fn2-cm-at i xs)))))
(local (defthm mc-corrupt-vector
  (implies (and (equal (len old) (len new)) (mc-vectorp old bound) (mc-vectorp new bound))
           (and (equal (len (fn2-cm-corrupt-visible-unit old new vs ds)) (len old))
                (mc-vectorp (fn2-cm-corrupt-visible-unit old new vs ds) bound)))
  :hints (("Goal" :induct (fn2-cm-corrupt-visible-unit old new vs ds)))))
(local (defthm mc-allowed-shape
  (implies (fn2-cm-crash-units-allowedp image durable vs ds flights cache i unit radius)
           (and (mc-arrayp image unit 255) (equal (len image) (len durable))))
  :hints (("Goal" :induct (fn2-cm-crash-units-allowedp image durable vs ds flights cache i unit radius)
           :in-theory (disable fn2-cm-touches-p fn2-cm-stamps-aheadp mc-vectorp fn2-cm-octetsp)))))

;; The row predicates observe only the capacity, the image height and the
;; completion serial of a well-formed state. Make these dependencies explicit.
(local (defun mc-range (a n size) (and (natp a) (natp n) (<= (+ a n) size))))
(local (defun mc-write-row (r done size height serial)
  (let* ((bytes (fn2-cm-at 2 r)) (n (len bytes)))
    (and (true-listp r) (equal (len r) (if done 10 8))
         (mc-vectorp bytes 255) (consp bytes)
         (mc-range (fn2-cm-at 1 r) n size) (mc-range (fn2-cm-at 6 r) n size)
         (member-eq (fn2-cm-at 3 r) '(nil t :preflush-fua :fua-after-preflush))
         (mc-arrayp (fn2-cm-at 4 r) 512 255) (equal (len (fn2-cm-at 4 r)) height)
         (mc-arrayp (fn2-cm-at 5 r) 512 serial) (equal (len (fn2-cm-at 5 r)) height)
         (or (not done)
             (and (natp (fn2-cm-at 7 r)) (<= (fn2-cm-at 7 r) n)
                  (unsigned-byte-p 60 (fn2-cm-at 8 r)) (<= (fn2-cm-at 8 r) serial)
                  (member-eq (fn2-cm-at 9 r) '(:ok :io :no-space :short))))))))
(local (defun mc-writes (rows done size height serial)
  (if (consp rows)
      (and (mc-write-row (car rows) done size height serial)
           (not (fn2-cm-find (fn2-cm-at 0 (car rows)) (cdr rows)))
           (mc-writes (cdr rows) done size height serial))
    (null rows))))
(local (defun mc-preflushes (rows size height serial)
  (if (consp rows)
      (and (mc-writes (fn2-cm-at 7 (car rows)) t size height serial)
           (mc-preflushes (cdr rows) size height serial))
    (null rows))))
(local (defun mc-fence-row (r size height serial)
  (and (true-listp r) (equal (len r) 4)
       (mc-arrayp (fn2-cm-at 1 r) 512 255) (equal (len (fn2-cm-at 1 r)) height)
       (mc-arrayp (fn2-cm-at 2 r) 512 serial) (equal (len (fn2-cm-at 2 r)) height)
       (mc-writes (fn2-cm-at 3 r) t size height serial))))
(local (defun mc-fences (rows size height serial)
  (if (consp rows)
      (and (mc-fence-row (car rows) size height serial)
           (not (fn2-cm-find (fn2-cm-at 0 (car rows)) (cdr rows)))
           (mc-fences (cdr rows) size height serial))
    (null rows))))
(local (defthm mc-range-of-state
  (equal (fn2-cm-range-p s a n) (mc-range a n (fn2-cm-size s)))))
(local (defthm mc-writes-of-state
  (implies (and (equal (fn2-cm-unit s) 512) (unsigned-byte-p 60 (fn2-cm-serial s)))
           (equal (fn2-cm-write-rows-p rows s done)
                  (mc-writes rows done (fn2-cm-size s) (len (fn2-cm-durable s)) (fn2-cm-serial s))))
  :hints (("Goal" :induct (fn2-cm-write-rows-p rows s done)
           :in-theory (mc-rules fn2-cm-write-rows-p mc-writes mc-write-row mc-octets-vector
                                mc-range-of-state mc-image-array mc-stamps-at-serial
                                nfix natp unsigned-byte-p integer-range-p)))))
(local (defthm mc-preflushes-of-state
  (implies (and (equal (fn2-cm-unit s) 512) (unsigned-byte-p 60 (fn2-cm-serial s)))
           (equal (fn2-cm-preflush-snapshotsp rows s)
                  (mc-preflushes rows (fn2-cm-size s) (len (fn2-cm-durable s)) (fn2-cm-serial s))))
  :hints (("Goal" :induct (fn2-cm-preflush-snapshotsp rows s)
           :in-theory (mc-rules fn2-cm-preflush-snapshotsp mc-preflushes mc-writes-of-state)))))
(local (defthm mc-fences-of-state
  (implies (and (equal (fn2-cm-unit s) 512) (unsigned-byte-p 60 (fn2-cm-serial s)))
           (equal (fn2-cm-fence-rows-p rows s)
                  (mc-fences rows (fn2-cm-size s) (len (fn2-cm-durable s)) (fn2-cm-serial s))))
  :hints (("Goal" :induct (fn2-cm-fence-rows-p rows s)
           :in-theory (mc-rules fn2-cm-fence-rows-p mc-fences mc-fence-row
                                mc-image-array mc-stamps-at-serial mc-writes-of-state)))))

(local (mc-reader fn2-cm-dead 8))
(local (mc-reader fn2-cm-serial 9))
(local (mc-reader fn2-cm-spent 10))
(local (mc-reader fn2-cm-failed 11))
(local (defun mc-capacity (g) (* (nfix (fn2-cm-at 0 g)) (nfix (fn2-cm-at 2 g)))))
(local (defun mc-height (g) (floor (* (fn2-cm-at 0 g) (fn2-cm-at 2 g)) 512)))
(local (defun mc-geometryp (g)
  (and (true-listp g) (equal (len g) 4) (equal (fn2-cm-at 1 g) 512)
       (posp (fn2-cm-at 0 g)) (equal (mod (fn2-cm-at 0 g) 512) 0)
       (posp (fn2-cm-at 2 g))
       (unsigned-byte-p 60 (* (fn2-cm-at 0 g) (fn2-cm-at 2 g)))
       (natp (fn2-cm-at 3 g)))))
(local (defthm mc-size
  (equal (fn2-cm-size s) (mc-capacity (fn2-cm-at 0 s)))
  :hints (("Goal" :in-theory (mc-rules fn2-cm-size mc-capacity mc-fn2-cm-geometry-at)))))
(local (defthm mc-unit-512
  (implies (mc-geometryp (fn2-cm-at 0 s)) (equal (fn2-cm-unit s) 512))
  :hints (("Goal" :in-theory (mc-rules mc-geometryp fn2-cm-unit mc-fn2-cm-geometry-at)))))
(local (defthm mc-true-put
  (equal (true-listp (fn2-cm-put i v x)) (true-listp x))))
(local (defmacro mc-readers ()
  '(mc-rules mc-fn2-cm-geometry-at mc-fn2-cm-durable-at mc-fn2-cm-visible-at
             mc-fn2-cm-dstamps-at mc-fn2-cm-vstamps-at mc-fn2-cm-cache-at
             mc-fn2-cm-inflight-at mc-fn2-cm-fences-at mc-fn2-cm-serial-at
             mc-fn2-cm-spent-at mc-fn2-cm-dead-at mc-fn2-cm-failed-at)))
(local (defthm mc-state-fields
  (equal (fn2-cm-statep s)
    (let* ((g (fn2-cm-at 0 s)) (size (mc-capacity g)) (h (mc-height g))
           (serial (fn2-cm-at 9 s)) (cache (fn2-cm-at 5 s))
           (flights (fn2-cm-at 6 s)) (fences (fn2-cm-at 7 s)))
      (and (true-listp s) (equal (len s) 12) (mc-geometryp g)
           (mc-arrayp (fn2-cm-at 1 s) 512 255) (equal (len (fn2-cm-at 1 s)) h)
           (mc-arrayp (fn2-cm-at 2 s) 512 255) (equal (len (fn2-cm-at 2 s)) h)
           (unsigned-byte-p 60 serial)
           (mc-arrayp (fn2-cm-at 3 s) 512 serial) (equal (len (fn2-cm-at 3 s)) h)
           (mc-arrayp (fn2-cm-at 4 s) 512 serial) (equal (len (fn2-cm-at 4 s)) h)
           (mc-writes cache t size h serial) (mc-writes flights nil size h serial)
           (mc-preflushes flights size h serial)
           (fn2-cm-row-ids-disjointp flights cache) (fn2-cm-row-ids-disjointp flights fences)
           (mc-fences fences size h serial) (booleanp (fn2-cm-at 8 s))
           (booleanp (fn2-cm-at 11 s)) (natp (fn2-cm-at 10 s)))))
  :hints (("Goal" :in-theory
           (union-theories (mc-readers)
             (mc-rules fn2-cm-statep fn2-cm-unit mc-geometryp mc-height mc-size
                       mc-writes-of-state mc-preflushes-of-state mc-fences-of-state
                       mc-image-array mc-stamps-at-serial))))))
(local (defthm mc-empty-rows
  (and (mc-writes nil done size h serial) (mc-fences nil size h serial)
       (mc-preflushes nil size h serial)
       (fn2-cm-row-ids-disjointp nil xs) (fn2-cm-row-ids-disjointp xs nil))))
(local (defmacro mc-state-rules (&rest rules)
  `(union-theories (mc-readers)
      (mc-rules mc-state-fields mc-at-put mc-len-put mc-true-put mc-unit-512 mc-size
                mc-range-of-state mc-octets-vector mc-empty-rows ,@rules))))
(local (defthm mc-reopen-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-reopen s revert)))
  :hints (("Goal" :in-theory (mc-state-rules fn2-cm-reopen)))))
(local (defthm mc-dead-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-kill-device s)))
  :hints (("Goal" :in-theory (mc-state-rules fn2-cm-kill-device)))))
(local (defthm mc-crash-shape
  (implies (fn2-cm-crash-image-allowedp s image profile)
           (and (mc-arrayp image (fn2-cm-unit s) 255)
                (equal (len image) (len (fn2-cm-at 1 s)))))
  :hints (("Goal" :in-theory (mc-state-rules fn2-cm-crash-image-allowedp mc-allowed-shape)))))
(local (defthm mc-crash-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-crash s image profile)))
  :hints (("Goal" :use mc-crash-shape :in-theory (mc-state-rules fn2-cm-crash)))))
(local (defthm mc-land-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-land-live s image profile)))
  :hints (("Goal" :use mc-crash-shape :in-theory (mc-state-rules fn2-cm-land-live)))))
(local (defthm mc-corrupt-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-corrupt s i bytes profile)))
  :hints (("Goal" :use ((:instance mc-array-at (xs (fn2-cm-at 2 s)) (u 512) (bound 255))
                 (:instance mc-corrupt-vector (bound 255)
                   (old (fn2-cm-at i (fn2-cm-at 2 s))) (new bytes)
                   (vs (fn2-cm-at i (fn2-cm-at 4 s))) (ds (fn2-cm-at i (fn2-cm-at 3 s)))))
           :in-theory (mc-state-rules fn2-cm-corrupt mc-array-at mc-array-put
                         mc-corrupt-vector nfix natp)))))

;; Operation identifiers survive a redirect or a preflush phase change.
;; Discharge membership and uniqueness once for all three row collections.
(local (defun mc-ids (rows)
  (if (consp rows) (cons (fn2-cm-at 0 (car rows)) (mc-ids (cdr rows))) nil)))
(local (defun mc-nonempty-rows (rows)
  (if (consp rows) (and (consp (car rows)) (mc-nonempty-rows (cdr rows))) t)))
(local (defthm mc-typed-row-consp
  (and (implies (mc-write-row r done size h serial) (consp r))
       (implies (mc-fence-row r size h serial) (consp r)))
  :hints (("Goal" :cases ((consp r)) :in-theory (mc-rules mc-write-row mc-fence-row len)))))
(local (defthm mc-row-collections-nonempty
  (and (implies (mc-writes rows done size h serial) (mc-nonempty-rows rows))
       (implies (mc-fences rows size h serial) (mc-nonempty-rows rows)))
  :hints (("Goal" :induct (mc-ids rows)
           :in-theory (mc-rules (:induction mc-ids) mc-typed-row-consp mc-nonempty-rows mc-writes mc-fences)))))
(local (defthm mc-find-id
  (implies (fn2-cm-find op rows) (equal (fn2-cm-at 0 (fn2-cm-find op rows)) op))
  :hints (("Goal" :in-theory (disable mc-at-zero fn2-cm-at)))))
(local (defthm mc-find-membership
  (implies (mc-nonempty-rows rows)
           (iff (fn2-cm-find op rows) (member-equal op (mc-ids rows))))
  :hints (("Goal" :induct (fn2-cm-find op rows) :in-theory (disable mc-at-zero fn2-cm-at)))))
(local (defthm mc-find-types
  (and (implies (and (mc-writes rows done size h serial) (fn2-cm-find op rows))
                (mc-write-row (fn2-cm-find op rows) done size h serial))
       (implies (and (mc-preflushes rows size h serial) (fn2-cm-find op rows))
                (mc-writes (fn2-cm-at 7 (fn2-cm-find op rows)) t size h serial))
       (implies (and (mc-fences rows size h serial) (fn2-cm-find op rows))
                (mc-fence-row (fn2-cm-find op rows) size h serial)))
  :hints (("Goal" :induct (fn2-cm-find op rows)
           :in-theory (disable mc-write-row mc-fence-row mc-at-zero fn2-cm-at mc-find-membership)))))
(local (defthm mc-ids-remove
  (equal (mc-ids (fn2-cm-remove op rows)) (remove1-equal op (mc-ids rows)))
  :hints (("Goal" :induct (fn2-cm-remove op rows)))))
(local (defthm mc-ids-replace
  (implies (equal (fn2-cm-at 0 r) op)
           (equal (mc-ids (fn2-cm-replace-row op r rows)) (mc-ids rows)))))
(local (defthm mc-ids-append
  (equal (mc-ids (append rows ys)) (append (mc-ids rows) (mc-ids ys)))))
(local (defthm mc-nonempty-remove
  (implies (mc-nonempty-rows rows) (mc-nonempty-rows (fn2-cm-remove op rows)))))
(local (defthm mc-nonempty-replace
  (implies (and (mc-nonempty-rows rows) (consp r))
           (mc-nonempty-rows (fn2-cm-replace-row op r rows)))))
(local (defthm mc-nonempty-append
  (equal (mc-nonempty-rows (append rows ys))
         (and (mc-nonempty-rows rows) (mc-nonempty-rows ys)))))
(local (defthm mc-disjoint-ids
  (implies (mc-nonempty-rows ys)
           (equal (fn2-cm-row-ids-disjointp xs ys) (not (intersectp-equal (mc-ids xs) (mc-ids ys)))))
  :hints (("Goal" :induct (mc-ids xs) :in-theory (disable fn2-cm-find)))))
(local (defthm mc-member-remove
  (implies (not (member-equal i xs)) (not (member-equal i (remove1-equal j xs))))))
(local (defthm mc-intersect-remove
  (implies (not (intersectp-equal xs ys))
           (and (not (intersectp-equal (remove1-equal i xs) ys))
                (not (intersectp-equal xs (remove1-equal i ys)))))))
(local (defthm mc-disjoint-cons
  (equal (intersectp-equal xs (cons id ys))
         (or (if (member-equal id xs) t nil) (intersectp-equal xs ys)))))
(local (defthm mc-member-append
  (iff (member-equal id (append xs ys)) (or (member-equal id xs) (member-equal id ys)))))
(local (defthm mc-intersect-append
  (equal (intersectp-equal xs (append ys zs))
         (or (intersectp-equal xs ys) (intersectp-equal xs zs)))))
(local (defthm mc-unique-ids
  (implies (mc-writes rows done size h serial) (no-duplicatesp-equal (mc-ids rows)))
  :hints (("Goal" :induct (mc-ids rows)
           :in-theory (mc-rules mc-writes mc-ids no-duplicatesp-equal mc-find-membership
                                mc-row-collections-nonempty car-cons cdr-cons)))))
(local (defthm mc-removed-id-absent
  (implies (no-duplicatesp-equal xs) (not (member-equal op (remove1-equal op xs))))))
(local (defthm mc-typed-remove
  (and (implies (mc-writes rows done size h serial)
                (mc-writes (fn2-cm-remove op rows) done size h serial))
       (implies (mc-fences rows size h serial)
                (mc-fences (fn2-cm-remove op rows) size h serial))
       (implies (mc-preflushes rows size h serial)
                (mc-preflushes (fn2-cm-remove op rows) size h serial)))
  :hints (("Goal" :induct (fn2-cm-remove op rows)
           :in-theory (mc-rules fn2-cm-remove mc-writes mc-fences mc-preflushes
                                mc-find-membership mc-ids-remove mc-member-remove
                                mc-row-collections-nonempty mc-nonempty-remove car-cons cdr-cons)))))
(local (defthm mc-typed-replace
  (implies (and (consp r) (equal (fn2-cm-at 0 r) op))
    (and (implies (and (mc-writes rows done size h serial)
                       (mc-write-row r done size h serial))
                  (mc-writes (fn2-cm-replace-row op r rows) done size h serial))
         (implies (and (mc-preflushes rows size h serial)
                       (mc-writes (fn2-cm-at 7 r) t size h serial))
                  (mc-preflushes (fn2-cm-replace-row op r rows) size h serial))))
  :hints (("Goal" :induct (fn2-cm-replace-row op r rows)
           :in-theory (mc-rules fn2-cm-replace-row mc-writes mc-preflushes mc-find-membership
                                mc-ids-replace mc-nonempty-replace mc-row-collections-nonempty
                                car-cons cdr-cons)))))
(local (defthm mc-typed-snoc
  (implies (and (mc-writes xs done size h serial) (mc-write-row r done size h serial)
                (not (member-equal (fn2-cm-at 0 r) (mc-ids xs))))
           (mc-writes (append xs (list r)) done size h serial))
  :hints (("Goal" :induct (mc-ids xs)
           :in-theory (mc-rules mc-writes mc-ids member-equal binary-append car-cons cdr-cons
                                mc-find-membership mc-nonempty-append mc-nonempty-rows
                                mc-ids-append mc-member-append mc-typed-row-consp
                                mc-row-collections-nonempty fn2-cm-find)))))
(local (defthm mc-row-widen
  (implies (and (mc-write-row r done size h low) (<= low high))
           (mc-write-row r done size h high))
  :hints (("Goal" :in-theory (mc-rules mc-write-row)
           :use ((:instance mc-array-widen (xs (fn2-cm-at 5 r)) (unit 512)))))
  :rule-classes nil))
(local (defthm mc-writes-widen
  (implies (and (mc-writes xs done size h low) (<= low high))
           (mc-writes xs done size h high))
  :hints (("Goal" :induct (mc-ids xs) :in-theory (mc-rules mc-writes (:induction mc-ids)))
          ("Subgoal *1/1" :use ((:instance mc-row-widen (r (car xs))))))
  :rule-classes nil))
(local (defthm mc-preflushes-widen
  (implies (and (mc-preflushes xs size h low) (<= low high))
           (mc-preflushes xs size h high))
  :hints (("Goal" :induct (mc-ids xs) :in-theory (mc-rules mc-preflushes (:induction mc-ids)))
          ("Subgoal *1/1" :use ((:instance mc-writes-widen (xs (fn2-cm-at 7 (car xs))) (done t)))))
  :rule-classes nil))
(local (defthm mc-fence-widen
  (implies (and (mc-fence-row r size h low) (<= low high))
           (mc-fence-row r size h high))
  :hints (("Goal" :in-theory (mc-rules mc-fence-row)
           :use ((:instance mc-writes-widen (xs (fn2-cm-at 3 r)) (done t))
                 (:instance mc-array-widen (xs (fn2-cm-at 2 r)) (unit 512)))))
  :rule-classes nil))
(local (defthm mc-fences-widen
  (implies (and (mc-fences xs size h low) (<= low high))
           (mc-fences xs size h high))
  :hints (("Goal" :induct (mc-ids xs) :in-theory (mc-rules mc-fences (:induction mc-ids)))
          ("Subgoal *1/1" :use ((:instance mc-fence-widen (r (car xs))))))
  :rule-classes nil))

(local (defthm mc-at-cons
  (equal (fn2-cm-at n (cons a x)) (if (posp n) (fn2-cm-at (1- n) x) a))))
(local (defthm mc-list-cons
  (and (equal (true-listp (cons a x)) (true-listp x))
       (equal (len (cons a x)) (1+ (len x)))
       (equal (mc-ids (cons r xs)) (cons (fn2-cm-at 0 r) (mc-ids xs)))
       (equal (mc-nonempty-rows (cons r xs)) (and (consp r) (mc-nonempty-rows xs))))
  :hints (("Goal" :in-theory (mc-rules true-listp len mc-ids mc-nonempty-rows car-cons cdr-cons)))))
(local (defthm mc-typed-cons
  (and (equal (mc-writes (cons r xs) done size h serial)
              (and (mc-write-row r done size h serial)
                   (not (fn2-cm-find (fn2-cm-at 0 r) xs))
                   (mc-writes xs done size h serial)))
       (equal (mc-fences (cons r xs) size h serial)
              (and (mc-fence-row r size h serial)
                   (not (fn2-cm-find (fn2-cm-at 0 r) xs))
                   (mc-fences xs size h serial)))
       (equal (mc-preflushes (cons r xs) size h serial)
              (and (mc-writes (fn2-cm-at 7 r) t size h serial)
                   (mc-preflushes xs size h serial))))
  :hints (("Goal" :in-theory (mc-rules mc-writes mc-fences mc-preflushes car-cons cdr-cons)))))
(local (defthm mc-intersect-cons-left
  (equal (intersectp-equal (cons id xs) ys)
         (if (member-equal id ys) t (intersectp-equal xs ys)))
  :hints (("Goal" :in-theory (mc-rules intersectp-equal endp car-cons cdr-cons)))))
(local (defmacro mc-row-rules (&rest rules)
  `(mc-state-rules mc-at-cons mc-list-cons mc-typed-cons mc-disjoint-ids
                   mc-disjoint-cons mc-intersect-cons-left mc-find-membership
                   mc-row-collections-nonempty car-cons cdr-cons ,@rules)))
(local (defthm mc-submit-write-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-submit-write s op a bytes fua)))
  :hints (("Goal" :in-theory (mc-row-rules fn2-cm-submit-write mc-write-row member-equal)))))
(local (defthm mc-submit-fence-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-submit-fence s op)))
  :hints (("Goal" :in-theory (mc-row-rules fn2-cm-submit-fence mc-fence-row)))))
(local (defthm mc-consp-put
  (equal (consp (fn2-cm-put i v x)) (consp x))))
(local (defthm mc-positive-length-consp
  (implies (< 0 (len x)) (consp x))
  :hints (("Goal" :cases ((consp x))))))
(local (defthm mc-redirect-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-redirect-write s op physical profile)))
  :hints (("Goal" :use
           ((:instance mc-find-types (rows (fn2-cm-at 6 s)) (done nil)
             (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s)))
             (serial (fn2-cm-at 9 s))))
           :in-theory (mc-row-rules fn2-cm-redirect-write mc-typed-replace mc-ids-replace
                      mc-write-row mc-find-id mc-consp-put mc-typed-row-consp mc-positive-length-consp mc-nonempty-replace)))))

;; A successful merge and a permitted uncertain image have the same geometry.
(local (defthm mc-merge-shapes
  (implies (and (mc-arrayp old 512 255) (mc-arrayp new 512 255)
                (mc-arrayp ds 512 serial) (mc-arrayp ns 512 serial)
                (equal (len ds) (len old)) (equal (len ns) (len old))
                (equal (len new) (len old)))
           (and (mc-arrayp (fn2-cm-merge-image old ds new ns nil) 512 255)
                (mc-arrayp (fn2-cm-merge-image old ds new ns t) 512 serial)))
  :hints (("Goal" :in-theory (mc-rules)
           :use ((:instance mc-merge-array (unit 512) (data 255) (stamps serial) (flag nil))
                 (:instance mc-merge-array (unit 512) (data 255) (stamps serial) (flag t)))))))
(local (defthm mc-fence-permission
  (implies (fn2-cm-fence-allowedp s op outcome image profile)
           (and (fn2-cm-find op (fn2-cm-fences s))
                (or (fn2-cm-fence-persists-p outcome profile)
                    (and (mc-arrayp image (fn2-cm-unit s) 255)
                         (equal (len image) (len (fn2-cm-durable s)))))))
  :hints (("Goal" :in-theory (mc-rules fn2-cm-fence-allowedp mc-allowed-shape)))
  :rule-classes nil))
(local (defmacro mc-completion-rules (&rest rules)
  `(mc-row-rules mc-merge-shapes mc-merge-length fn2-cm-persist-snapshot
                 mc-typed-remove mc-ids-remove mc-nonempty-remove mc-intersect-remove
                 mc-typed-replace mc-ids-replace mc-nonempty-replace
                 mc-consp-put mc-find-id ,@rules)))
(local (defthm mc-complete-fence-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-complete-fence s op outcome image profile)))
  :hints (("Goal" :use (mc-fence-permission
                        (:instance mc-find-types (rows (fn2-cm-at 7 s)) (done nil)
                         (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s)))
                         (serial (fn2-cm-at 9 s))))
           :in-theory (mc-completion-rules fn2-cm-complete-fence mc-fence-row)))))

(local (defthm mc-find-cons
  (equal (fn2-cm-find op (cons r rows))
         (if (equal op (fn2-cm-at 0 r)) r (fn2-cm-find op rows)))
  :hints (("Goal" :expand (fn2-cm-find op (cons r rows))
           :in-theory (mc-rules car-cons cdr-cons)))))
(local (defthm mc-selected-flight
  (let* ((r (fn2-cm-find op (fn2-cm-at 6 s))) (g (fn2-cm-at 0 s))
         (h (mc-height g)) (size (mc-capacity g)) (serial (fn2-cm-at 9 s)))
    (implies (and (fn2-cm-statep s) r)
             (and (mc-write-row r nil size h serial)
                  (mc-writes (fn2-cm-at 7 r) t size h serial))))
  :hints (("Goal" :in-theory (mc-state-rules mc-find-types)))
  :rule-classes nil))
(local (defthm mc-unit-put-seven
  (equal (fn2-cm-unit (fn2-cm-put 7 v s)) (fn2-cm-unit s))
  :hints (("Goal" :in-theory (mc-state-rules fn2-cm-unit)))))
(local (defthm mc-preflush-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-complete-preflush s op outcome image profile)))
  :hints (("Goal" :use (mc-selected-flight
            (:instance mc-fence-permission
              (s (let ((r (fn2-cm-find op (fn2-cm-inflight s))))
                   (fn2-cm-put 7 (cons (list op (fn2-cm-at 4 r) (fn2-cm-at 5 r) (fn2-cm-at 7 r))
                                       (fn2-cm-fences s)) s)))))
           :in-theory (mc-completion-rules fn2-cm-complete-preflush fn2-cm-complete-fence
                         mc-find-cons mc-write-row mc-positive-length-consp mc-unit-put-seven)))))


(local (defthm mc-raise-serial
  (implies (and (fn2-cm-statep s) (unsigned-byte-p 60 high)
                (<= (fn2-cm-at 9 s) high))
           (fn2-cm-statep (fn2-cm-put 9 high s)))
  :hints (("Goal" :in-theory (mc-state-rules)
           :use ((:instance mc-array-widen (xs (fn2-cm-at 3 s)) (unit 512)
                                            (low (fn2-cm-at 9 s)))
                 (:instance mc-array-widen (xs (fn2-cm-at 4 s)) (unit 512)
                                            (low (fn2-cm-at 9 s)))
                 (:instance mc-writes-widen (xs (fn2-cm-at 5 s)) (done t)
                          (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s)))
                          (low (fn2-cm-at 9 s)))
                 (:instance mc-writes-widen (xs (fn2-cm-at 6 s)) (done nil)
                          (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s)))
                          (low (fn2-cm-at 9 s)))
                 (:instance mc-preflushes-widen (xs (fn2-cm-at 6 s))
                          (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s)))
                          (low (fn2-cm-at 9 s)))
                 (:instance mc-fences-widen (xs (fn2-cm-at 7 s))
                          (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s)))
                          (low (fn2-cm-at 9 s)))))) :rule-classes nil))
(local (defthm mc-disjoint-member
  (implies (and (not (intersectp-equal xs ys)) (member-equal op xs))
           (not (member-equal op ys)))
  :hints (("Goal" :induct (member-equal op xs)
           :in-theory (mc-rules member-equal intersectp-equal endp)))))
(local (defthm mc-at-append
  (implies (natp i)
           (equal (fn2-cm-at i (append xs ys))
                  (if (< i (len xs)) (fn2-cm-at i xs) (fn2-cm-at (- i (len xs)) ys))))
  :hints (("Goal" :induct (fn2-cm-at i xs)
           :expand ((append xs ys) (len xs)) :in-theory (mc-rules fn2-cm-at binary-append car-cons cdr-cons len natp posp mc-at-cons commutativity-of-+ associativity-of-+ commutativity-2-of-+ fold-consts-in-+ unicity-of-0 fix (:type-prescription len) distributivity-of-minus-over-+)))))
(local (defthm mc-at-take
  (implies (and (natp i) (natp n) (< i n))
           (equal (fn2-cm-at i (fn2-cm-take n xs)) (fn2-cm-at i xs)))
  :hints (("Goal" :induct (mc-two-offsets i n xs)
           :expand ((fn2-cm-at i xs) (fn2-cm-take n xs))
           :in-theory (mc-rules fn2-cm-at fn2-cm-take mc-two-offsets car-cons cdr-cons posp natp mc-at-cons)))))
(local (defthm mc-true-append
  (equal (true-listp (append xs ys)) (true-listp ys))
  :hints (("Goal" :induct (append xs ys) :in-theory (mc-rules binary-append true-listp mc-list-cons)))))
(local (defthm mc-completed-row
  (let ((done (append (fn2-cm-take 6 (if change (fn2-cm-put 3 :fua-after-preflush r) r))
                      (list addr n stamp code))))
    (implies (and (mc-write-row r nil size h stamp)
                  (mc-range addr (len (fn2-cm-at 2 r)) size)
                  (natp n) (<= n (len (fn2-cm-at 2 r)))
                  (unsigned-byte-p 60 stamp) (member-eq code '(:ok :io :no-space :short)))
             (and (mc-write-row done t size h stamp)
                  (equal (fn2-cm-at 0 done) (fn2-cm-at 0 r)))))
  :hints (("Goal" :in-theory (mc-rules mc-write-row mc-at-append mc-at-take mc-len-take
                           mc-at-put mc-len-put mc-len-append mc-true-append mc-at-cons
                           mc-list-cons mc-true-take min nfix)))))

(local (defun mc-done (r change addr n stamp code)
  (append (fn2-cm-take 6 (if change (fn2-cm-put 3 :fua-after-preflush r) r))
          (list addr n stamp code))))
(local (defthm mc-done-type
  (implies (and (mc-write-row r nil size h stamp)
                (mc-range addr (len (fn2-cm-at 2 r)) size)
                (natp n) (<= n (len (fn2-cm-at 2 r)))
                (unsigned-byte-p 60 stamp) (member-eq code '(:ok :io :no-space :short)))
           (and (mc-write-row (mc-done r change addr n stamp code) t size h stamp)
                (equal (fn2-cm-at 0 (mc-done r change addr n stamp code)) (fn2-cm-at 0 r))))
  :hints (("Goal" :use mc-completed-row :in-theory (mc-rules mc-done)))))
(local (defun mc-install-write (s op r addr n stamp code change fua unit)
  (let* ((bytes (fn2-cm-take n (fn2-cm-at 2 r)))
         (stamps (fn2-cm-repeat n stamp))
         (s (fn2-cm-put 2 (fn2-cm-write-image (fn2-cm-visible s) addr bytes unit) s))
         (s (fn2-cm-put 4 (fn2-cm-write-image (fn2-cm-vstamps s) addr stamps unit) s))
         (s (if fua
                (fn2-cm-put 3 (fn2-cm-write-image (fn2-cm-dstamps s) addr stamps unit)
                  (fn2-cm-put 1 (fn2-cm-write-image (fn2-cm-durable s) addr bytes unit) s))
              s))
         (s (fn2-cm-put 5 (append (fn2-cm-cache s) (list (mc-done r change addr n stamp code))) s))
         (s (fn2-cm-put 6 (fn2-cm-remove op (fn2-cm-inflight s)) s)))
    (fn2-cm-put 9 stamp s))))
(local (defthm mc-write-inputs
  (implies (mc-write-row r nil size h stamp)
           (mc-vectorp (fn2-cm-at 2 r) 255))
  :hints (("Goal" :in-theory (mc-rules mc-write-row)))))
(local (defthm mc-nat-address
  (implies (mc-range addr count size) (natp addr))
  :hints (("Goal" :in-theory (mc-rules mc-range)))))
(local (defthm mc-no-intersect-nil
  (not (intersectp-equal xs nil))
  :hints (("Goal" :induct (intersectp-equal xs nil) :expand (:free (a) (member-equal a nil)) :in-theory (mc-rules member-equal intersectp-equal endp)))))

(local (defthm mc-move-disjoint
  (implies (and (mc-nonempty-rows cache) (consp r) (equal (fn2-cm-at 0 r) op)
                (no-duplicatesp-equal (mc-ids flights))
                (not (intersectp-equal (mc-ids flights) (mc-ids cache))))
           (fn2-cm-row-ids-disjointp (fn2-cm-remove op flights) (append cache (list r))))
  :hints (("Goal" :use ((:instance mc-disjoint-ids
                          (xs (fn2-cm-remove op flights)) (ys (append cache (list r)))))
           :in-theory (mc-rules mc-ids-remove mc-ids-append mc-intersect-append
             mc-removed-id-absent mc-intersect-remove mc-disjoint-cons mc-no-intersect-nil
             mc-nonempty-append mc-list-cons)))))

(local (defthm mc-install-write-preserves
  (let* ((g (fn2-cm-at 0 s)) (size (mc-capacity g)) (h (mc-height g))
         (rows (fn2-cm-at 6 s)))
    (implies (and (equal (len s) 12) (fn2-cm-statep (fn2-cm-put 9 stamp s))
                  (member-equal op (mc-ids rows)) (equal (fn2-cm-at 0 r) op)
                  (mc-write-row r nil size h stamp)
                  (mc-range addr (len (fn2-cm-at 2 r)) size)
                  (natp n) (<= n (len (fn2-cm-at 2 r)))
                  (member-eq code '(:ok :io :no-space :short)))
             (fn2-cm-statep (mc-install-write s op r addr n stamp code change fua 512))))
  :hints (("Goal" :use ((:instance mc-move-disjoint (flights (fn2-cm-at 6 s)) (cache (fn2-cm-at 5 s))
                           (r (mc-done r change addr n stamp code)))
                        (:instance mc-unique-ids (rows (fn2-cm-at 6 s)) (done nil)
                           (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s))) (serial stamp))
                        (:instance mc-done-type (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s))))
                        (:instance mc-typed-row-consp (r (mc-done r change addr n stamp code))
                          (done t) (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s))) (serial stamp)))
           :in-theory (mc-completion-rules mc-install-write
            mc-array-write mc-vector-take mc-vector-repeat mc-write-inputs mc-nat-address
            mc-length-write mc-typed-snoc mc-ids-append mc-intersect-append
            mc-removed-id-absent mc-disjoint-member mc-no-intersect-nil mc-nonempty-append
            natp unsigned-byte-p integer-range-p)))))

(local (defthm mc-persist-flight
  (implies (and (fn2-cm-statep s)
                (mc-write-row r nil (mc-capacity (fn2-cm-at 0 s))
                              (mc-height (fn2-cm-at 0 s)) (fn2-cm-at 9 s)))
           (fn2-cm-statep (fn2-cm-persist-snapshot s (fn2-cm-at 4 r) (fn2-cm-at 5 r))))
  :hints (("Goal" :in-theory (mc-completion-rules mc-write-row)))))
(local (defthm mc-snapshot-frame
  (and (equal (len (fn2-cm-persist-snapshot s img ds)) (len s))
       (implies (and (natp i) (not (equal i 1)) (not (equal i 3)))
                (equal (fn2-cm-at i (fn2-cm-persist-snapshot s img ds)) (fn2-cm-at i s))))
  :hints (("Goal" :in-theory (mc-state-rules fn2-cm-persist-snapshot)))))
(local (defthm mc-state-flight-membership
  (implies (and (fn2-cm-statep s) (fn2-cm-find op (fn2-cm-at 6 s)))
           (member-equal op (mc-ids (fn2-cm-at 6 s))))
  :hints (("Goal" :in-theory (mc-row-rules)))))
(local (defun mc-finish (s op r addr n stamp code change fua flush unit)
  (let ((base (if flush (fn2-cm-persist-snapshot s (fn2-cm-at 4 r) (fn2-cm-at 5 r)) s)))
    (mc-install-write base op r addr n stamp code change fua unit))))
(local (defthm mc-finish-preserves
  (let ((r (fn2-cm-find op (fn2-cm-at 6 s))))
    (implies (and (fn2-cm-statep s) r
                  (unsigned-byte-p 60 stamp) (<= (fn2-cm-at 9 s) stamp)
                  (mc-range addr (len (fn2-cm-at 2 r)) (mc-capacity (fn2-cm-at 0 s)))
                  (natp n) (<= n (len (fn2-cm-at 2 r))) (member-eq code '(:ok :io :no-space :short)))
             (fn2-cm-statep (mc-finish s op r addr n stamp code change fua flush 512))))
  :hints (("Goal" :use (mc-selected-flight
                        (:instance mc-row-widen (r (fn2-cm-find op (fn2-cm-at 6 s)))
                          (done nil) (low (fn2-cm-at 9 s)) (high stamp)
                          (size (mc-capacity (fn2-cm-at 0 s))) (h (mc-height (fn2-cm-at 0 s))))
                        (:instance mc-raise-serial (high stamp))
                        (:instance mc-raise-serial (high stamp)
                          (s (let ((r (fn2-cm-find op (fn2-cm-at 6 s))))
                               (fn2-cm-persist-snapshot s (fn2-cm-at 4 r) (fn2-cm-at 5 r))))))
           :in-theory (mc-rules mc-finish mc-install-write-preserves mc-persist-flight
                        mc-snapshot-frame mc-state-geometry mc-find-id mc-state-flight-membership)))))

(local (defthm mc-complete-write-unfolds
  (equal (fn2-cm-complete-write s op outcome profile)
    (let* ((r (fn2-cm-find op (fn2-cm-inflight s)))
           (code (if (consp outcome) (car outcome) outcome))
           (addr (if (eq code :short) (fn2-cm-at 2 outcome)
                   (if (consp outcome) (fn2-cm-at 1 outcome) (fn2-cm-at 6 r))))
           (n (if (eq code :ok) (len (fn2-cm-at 2 r))
                (if (eq code :short) (nfix (fn2-cm-at 1 outcome)) 0)))
           (stamp (+ 1 (nfix (fn2-cm-serial s))))
           (change (and (eq (fn2-cm-at 3 r) :preflush-fua) (eq code :ok))))
      (if (and (fn2-cm-write-outcome-p s r outcome profile) (unsigned-byte-p 60 stamp))
          (mc-finish s op r addr n stamp code change
                     (and (fn2-cm-at 3 r) (not (eq (fn2-cm-at 2 outcome) :lose-fua)))
                     (and change (fn2-cm-persistence-fence profile)) (fn2-cm-unit s))
        s)))
  :hints (("Goal" :in-theory (mc-rules fn2-cm-complete-write mc-finish mc-install-write mc-done)))))
(local (defthm mc-state-serial-natp
  (implies (fn2-cm-statep s) (natp (fn2-cm-at 9 s)))
  :hints (("Goal" :in-theory (mc-state-rules natp unsigned-byte-p integer-range-p)))))
(local (defthm mc-complete-write-preserves
  (implies (fn2-cm-statep s) (fn2-cm-statep (fn2-cm-complete-write s op outcome profile)))
  :hints (("Goal" :use mc-state-serial-natp :in-theory
           (union-theories (mc-readers)
             (mc-rules mc-complete-write-unfolds mc-finish-preserves fn2-cm-write-outcome-p
                       mc-state-geometry mc-range-of-state mc-size nfix
                       natp (:type-prescription len)))))))
(defthm fn2-cm-well-formedness-proved
  (fn2-cm-well-formedness$owed s event profile)
  :rule-classes nil
  :hints (("Goal" :in-theory
           (mc-rules fn2-cm-well-formedness$owed fn2-cm-step mc-submit-write-preserves
                     mc-redirect-preserves mc-preflush-preserves mc-complete-write-preserves
                     mc-submit-fence-preserves mc-complete-fence-preserves mc-crash-preserves
                     mc-land-preserves mc-reopen-preserves mc-dead-preserves mc-corrupt-preserves))))
(fn2-owed-discharge fn2-cm-well-formedness fn2-cm-well-formedness-proved)

;; Merkle root base cases use the actual initialized digest and frontier rows.
(local (in-theory (theory 'mc-initial-rules)))

(local (defthm mc-nth-store
  (equal (nth i (update-nth j v xs))
         (if (equal (nfix i) (nfix j)) v (nth i xs)))
  :hints (("Goal" :in-theory (enable nth-update-nth)))))
(local (defmacro mc-word-rules (&rest more)
  `(mc-rules fn2-digest-list fn2-digests-w0 fn2-digests-w1 fn2-digests-w2 fn2-digests-w3
             fn2-digests-w4 fn2-digests-w5 fn2-digests-w6 fn2-digests-w7
             fn2-digests-w0$ai fn2-digests-w1$ai fn2-digests-w2$ai fn2-digests-w3$ai
             fn2-digests-w4$ai fn2-digests-w5$ai fn2-digests-w6$ai fn2-digests-w7$ai
             fn2-digests-set-w0-nth fn2-digests-set-w1-nth fn2-digests-set-w2-nth fn2-digests-set-w3-nth
             fn2-digests-set-w4-nth fn2-digests-set-w5-nth fn2-digests-set-w6-nth fn2-digests-set-w7-nth
             mc-nth-store ,@more)))
(local (defthm mc-copy-list
  (equal (fn2-digest-list i (fn2-digest-copy dst src d))
         (fn2-digest-list (if (equal (nfix i) (nfix dst)) src i) d))
  :hints (("Goal" :cases ((equal (nfix i) (nfix dst)))
           :in-theory (mc-word-rules fn2-digest-copy)))))
(local (defthm mc-empty-list
  (equal (fn2-digest-list i (fn2-digest-empty dst d))
         (if (equal (nfix i) (nfix dst)) *fn2-b3-empty-root* (fn2-digest-list i d)))
  :hints (("Goal" :in-theory (mc-word-rules fn2-digest-empty)))))
(local (defthm mc-take-step
  (implies (and (syntaxp (quotep i)) (posp i))
           (equal (take i x) (cons (car x) (take (1- i) (cdr x)))))
  :hints (("Goal" :expand (take i x) :in-theory (mc-rules posp zp)))))
(local (defthm mc-nth-step
  (implies (and (syntaxp (quotep i)) (posp i))
           (equal (nth i x) (nth (1- i) (cdr x))))
  :hints (("Goal" :expand (nth i x) :in-theory (mc-rules posp zp nth)))))
(local (defthm mc-nth-base
  (and (equal (nth 0 x) (car x)) (equal (take 0 x) nil))))
(local (defthm mc-eight-nths
  (equal (list (nth 0 ws) (nth 1 ws) (nth 2 ws) (nth 3 ws) (nth 4 ws) (nth 5 ws) (nth 6 ws) (nth 7 ws)) (take 8 ws))
  :hints (("Goal" :in-theory (mc-rules mc-nth-base mc-nth-step mc-take-step)))))
(local (defthm mc-load-list
  (equal (fn2-digest-list dst (fn2-digest-load dst ws d)) (take 8 ws))
  :hints (("Goal" :in-theory (mc-word-rules fn2-digest-load mc-eight-nths)))))
(local (defthm mc-take-length
  (implies (and (true-listp x) (equal i (len x))) (equal (take i x) x))
  :hints (("Goal" :induct (take i x) :in-theory (enable take len true-listp)))))
(local (defthm mc-run-single-hash
  (implies (and (equal (len ws) 8) (true-listp ws))
           (equal (fn2-mk-run (list ws)) ws))
  :hints (("Goal" :expand ((:free (d m) (fn2-mk-fold 136 0 0 1 nil d m))
                           (:free (d m) (fn2-mk-fold 136 0 1 0 t d m)))
           :in-theory (mc-rules fn2-mk-run fn2-mk-run-hashes fn2-mk-append
                         fn2-mk-root fn2-mk-fold fn2-mk-carry mc-copy-list mc-empty-list
                         mc-load-list mc-take-length fn2-mk-size fn2-mk-size$ai fn2-mk-table-init-nth fn2-mk-set-size-nth mc-nth-store mv-nth car-cons cdr-cons)))))
(defthm fn2-mk-root-is-mth-empty-or-singleton
  (implies (and (fn2-mk-root-hyps records hashes) (not (consp (cdr records))))
           (fn2-mk-root-result records hashes))
  :hints (("Goal" :cases ((consp records))
           :in-theory (mc-rules fn2-mk-root-hyps fn2-mk-root-result fn2-mk-leaves
                                fn2-mk-mth fn2-mk-model len true-list-listp fn-b3-words-shape
                                mc-run-single-hash mv-nth car-cons cdr-cons cons-car-cdr)))
  :rule-classes nil)

(local (defthm mc-compare-digests
  (equal (fn2-digest-equal i j d) (equal (fn2-digest-list i d) (fn2-digest-list j d)))
  :hints (("Goal" :in-theory (enable fn2-digest-list fn2-digest-equal)))))
(local (defthm mc-load-other
  (implies (not (equal (nfix i) (nfix dst)))
           (equal (fn2-digest-list i (fn2-digest-load dst ws d)) (fn2-digest-list i d)))
  :hints (("Goal" :in-theory (mc-word-rules fn2-digest-load)))))
(local (defthm mc-equal-size-run
  (implies (and (posp n) (equal (fn2-mk-phase 0 m) 0))
           (equal (car (fn2-mk-consistency-run 64 n n count d m))
                  (cond ((not (equal count 0)) :proof-length)
                        ((fn2-digest-equal 136 137 d) :ok)
                        (t :root-mismatch))))
  :hints (("Goal" :expand (fn2-mk-consistency-run 64 n n count d m)
            :in-theory (mc-rules fn2-mk-verify-consistency mv-nth car-cons cdr-cons posp)))))
(local (defthm fn2-mk-consistency-equal-size-roots
  (implies (and (posp (len old)) (equal (len old) (len new))
                (eq (car (fn2-mk-consistency-observation old new proof)) :ok))
           (equal (fn-b3-words 8 (fn2-mk-mth old)) (fn-b3-words 8 (fn2-mk-mth new))))
  :hints (("Goal" :cases ((consp proof))
           :expand ((len proof) (:free (d) (fn2-mk-load-proof proof 138 d)))
           :in-theory (mc-rules fn2-mk-consistency-observation mc-equal-size-run fn2-mk-load-proof
                         fn2-mk-phase fn2-mk-phase$ai fn2-mk-table-init-nth mc-compare-digests
                         mc-load-other mc-load-list mc-take-length fn-b3-words-shape
                         (:type-prescription len) car-cons cdr-cons mv-nth)))
  :rule-classes nil))

;; The integrity premise makes hashes injective on the finite set of tree
;; and verifier inputs that this observation actually opened.
(local (defthm mc-against-member
  (implies (and (fn2-mk-integrity-against x ys) (member-equal y ys)
                (equal (fn-blake3 x) (fn-blake3 y)))
           (equal x y))
  :hints (("Goal" :induct (member-equal y ys)
           :in-theory (mc-rules fn2-mk-integrity-against member-equal))
          ("Subgoal *1/2" :use ((:instance fn2-a-integrity-evidence-sound
                                 (expected x) (observed (car ys))))))
  :rule-classes nil))
(local (defthm mc-openings-bind
  (implies (and (fn2-mk-integrity-openings openings)
                (member-equal x openings) (member-equal y openings)
                (equal (fn-blake3 x) (fn-blake3 y)))
           (equal x y))
  :hints (("Goal" :induct (fn2-mk-integrity-openings openings)
           :in-theory (mc-rules fn2-mk-integrity-openings member-equal))
          ("Subgoal *1/2" :use
           ((:instance mc-against-member (x (car openings)) (ys (cdr openings)))
            (:instance mc-against-member (x (car openings)) (y x) (ys (cdr openings))))))
  :rule-classes nil))

(local (defthm mc-pack-two
  (implies (and (integerp a) (integerp b) (integerp x) (integerp y)
                (<= 0 a) (< a 256) (<= 0 b) (< b 256))
           (equal (equal (+ a (* 256 x)) (+ b (* 256 y)))
                  (and (equal a b) (equal x y))))
  :hints (("Goal" :cases ((<= (+ 1 x) y) (<= (+ 1 y) x))))))
(local (defthm mc-pack-four
  (implies (and (unsigned-byte-p 8 a) (unsigned-byte-p 8 b)
                (unsigned-byte-p 8 c) (unsigned-byte-p 8 d)
                (unsigned-byte-p 8 e) (unsigned-byte-p 8 f)
                (unsigned-byte-p 8 g) (unsigned-byte-p 8 h))
           (equal (equal (fn-b3-le-word a b c d) (fn-b3-le-word e f g h))
                  (and (equal a e) (equal b f) (equal c g) (equal d h))))
  :hints (("Goal" :use ((:instance mc-pack-two (b e) (x (+ b (* 256 c) (* 65536 d))) (y (+ f (* 256 g) (* 65536 h))))
                 (:instance mc-pack-two (a b) (b f) (x (+ c (* 256 d))) (y (+ g (* 256 h))))
                 (:instance mc-pack-two (a c) (b g) (x d) (y h)))
           :in-theory (enable fn-b3-le-word fn-b3-octet unsigned-byte-p)))))
(local (defun mc-words-induct (n x y)
  (if (zp n) (list x y)
    (mc-words-induct (1- n) (cddddr x) (cddddr y)))))
(local (defthm mc-pack-prefix
  (implies (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x)))
           (equal (fn-b3-words n x)
                  (if (zp n) nil
                    (cons (fn-b3-le-word (car x) (cadr x) (caddr x) (cadddr x))
                          (fn-b3-words (1- n) (cddddr x))))))
  :hints (("Goal" :expand (fn-b3-words n x)
           :in-theory (mc-rules nfix zp fn-b3-nthcdrx fn-b3-nthx)))))
(local (defthm mc-four-octets
  (implies (and (fn-b3-octet-listp x) (<= 4 (len x)))
           (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x))
                (unsigned-byte-p 8 (car x)) (unsigned-byte-p 8 (cadr x))
                (unsigned-byte-p 8 (caddr x)) (unsigned-byte-p 8 (cadddr x))
                (fn-b3-octet-listp (cddddr x)) (equal (len (cddddr x)) (- (len x) 4))))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
                        (fn-b3-octet-listp x) (fn-b3-octet-listp (cdr x))
                        (fn-b3-octet-listp (cddr x)) (fn-b3-octet-listp (cdddr x)))))))
(local (defthm mc-four-extensional
  (implies (and (consp x) (consp y) (consp (cdr x)) (consp (cdr y))
                (consp (cddr x)) (consp (cddr y)) (consp (cdddr x)) (consp (cdddr y))
                (equal (car x) (car y)) (equal (cadr x) (cadr y))
                (equal (caddr x) (caddr y)) (equal (cadddr x) (cadddr y))
                (equal (cddddr x) (cddddr y)))
           (equal x y))
  :hints (("Goal" :use ((:instance cons-car-cdr) (:instance cons-car-cdr (x y))
                 (:instance cons-car-cdr (x (cdr x))) (:instance cons-car-cdr (x (cdr y)))
                 (:instance cons-car-cdr (x (cddr x))) (:instance cons-car-cdr (x (cddr y)))
                 (:instance cons-car-cdr (x (cdddr x))) (:instance cons-car-cdr (x (cdddr y))))
           :in-theory (mc-rules))) :rule-classes nil))
(local (defthm mc-zero-octets
  (implies (and (fn-b3-octet-listp x) (equal (len x) 0)) (equal x nil))
  :hints (("Goal" :cases ((consp x)) :expand ((len x) (fn-b3-octet-listp x))))
  :rule-classes nil))
(local (defthm mc-words-injective
  (implies (and (natp n) (equal (len x) (* 4 n)) (equal (len y) (* 4 n))
                (fn-b3-octet-listp x) (fn-b3-octet-listp y)
                (equal (fn-b3-words n x) (fn-b3-words n y)))
           (equal x y))
  :hints (("Goal" :induct (mc-words-induct n x y)
           :in-theory (mc-rules mc-words-induct natp zp mc-pack-four mc-four-octets
                       cons-equal cons-car-cdr car-cons cdr-cons))
          ("Subgoal *1/1" :use (mc-zero-octets (:instance mc-zero-octets (x y))))
          ("Subgoal *1/2" :use (mc-four-extensional (:instance mc-pack-prefix) (:instance mc-pack-prefix (x y))
                                (:instance mc-four-octets) (:instance mc-four-octets (x y)))))
  :rule-classes nil))

(local (defthm mc-model-root-opening
  (let* ((m (fn2-mk-model records fuel)) (openings (mv-nth 1 m)))
    (and (consp openings) (equal (car m) (fn-blake3 (car openings)))))
  :hints (("Goal" :expand (fn2-mk-model records fuel)
           :in-theory (mc-rules car-cons cdr-cons mv-nth)))))
(local (defthm mc-first-opening-in-appended
  (implies (consp xs) (member-equal (car xs) (append xs ys)))
  :hints (("Goal" :expand (append xs ys) :in-theory (mc-rules member-equal binary-append car-cons)))))
(local (defthm mc-member-in-tail
  (implies (member-equal x ys) (member-equal x (append xs ys)))
  :hints (("Goal" :induct (append xs ys) :in-theory (mc-rules binary-append member-equal car-cons cdr-cons)))))
(defthm fn2-mk-equal-size-opening-binding
  (let* ((a (fn2-mk-model old (len old))) (b (fn2-mk-model new (len new))))
    (implies (and (posp (len old)) (equal (len old) (len new))
                  (fn2-mk-consistency-premise old new proof)
                  (eq (car (fn2-mk-consistency-observation old new proof)) :ok))
             (equal (car (mv-nth 1 a)) (car (mv-nth 1 b)))))
  :hints (("Goal" :use
           (fn2-mk-consistency-equal-size-roots
            (:instance mc-words-injective (n 8) (x (fn2-mk-mth old)) (y (fn2-mk-mth new)))
            (:instance mc-openings-bind
              (x (car (mv-nth 1 (fn2-mk-model old (len old)))))
              (y (car (mv-nth 1 (fn2-mk-model new (len new)))))
              (openings (append (mv-nth 1 (fn2-mk-model old (len old)))
                                (mv-nth 1 (fn2-mk-model new (len new)))
                                (cadr (fn2-mk-consistency-observation old new proof))))))
           :in-theory (mc-rules fn2-mk-mth fn2-mk-consistency-premise mc-model-root-opening
                          mc-first-opening-in-appended mc-member-in-tail fn-blake3-shape)))
  :rule-classes nil)
(local (defthm mc-singleton-shape
  (implies (equal (len xs) 1)
           (and (consp xs) (not (consp (cdr xs)))
                (implies (true-list-listp xs) (equal (cdr xs) nil))))
  :hints (("Goal" :cases ((consp xs) (consp (cdr xs)))
           :expand ((len xs) (len (cdr xs)) (true-list-listp xs) (true-list-listp (cdr xs)))))))
(local (defthm mc-singleton-opening
  (implies (equal (len xs) 1)
           (equal (car (mv-nth 1 (fn2-mk-model xs 1))) (cons 0 (car xs))))
  :hints (("Goal" :expand (fn2-mk-model xs 1) :in-theory (mc-rules mc-singleton-shape mv-nth car-cons cdr-cons)))))
(defthm fn2-mk-consistency-singleton-prefix
  (implies (and (true-list-listp old) (equal (len old) 1) (equal (len new) 1)
                (fn2-mk-consistency-premise old new proof)
                (eq (car (fn2-mk-consistency-observation old new proof)) :ok))
           (equal old (take (len old) new)))
  :hints (("Goal" :use (fn2-mk-equal-size-opening-binding (:instance cons-car-cdr (x old))
                        (:instance mc-singleton-shape (xs old)))
           :in-theory (mc-rules mc-singleton-opening mc-take-step mc-nth-base
                                car-cons cdr-cons cons-equal)))
  :rule-classes nil)

