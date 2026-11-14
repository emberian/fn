; Initializer geometry and free-chain evidence for the existing pool loops.
(in-package "ACL2")
(include-book "pool")
(local
 (defun fn2-pool-init-column-runes (cols)
   (declare (xargs :verify-guards nil))
   (if (atom cols) nil
     (let* ((read (fn2-columns-col-name 'fn2-pool (caar cols)))
            (write (fn2-columns-col-name 'fn2-pool (fn2-columns-pre "SET-" (caar cols))))
            (raw (fn2-columns-sym read "$AI")))
       (list* read write raw (fn2-columns-pre "UPDATE-" raw)
              (fn2-pool-init-column-runes (cdr cols)))))))
(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-pool) (w state)))))
  (value
   `(defthm fn2-pool-initial-row-write-snapshot
      (implies (and (natp r) (natp slot))
       (and (equal (fn2-pool-rows (let ((fn2-pool p)) (fn2-pool-put slot (gen gen) (base base) (cap cap) (state *fn2-pool-state-free*)
             (owner-kind 0) (owner-slot 0) (owner-gen 0)
             (lease-op-slot 0) (lease-op-gen 0) (lease-off 0) (lease-len 0)
             (out-count 0) (fill 0) (hand-to-kind 0) (hand-to-slot 0) (hand-to-gen 0)
             (next-free next) (class class)))) (fn2-pool-rows p))
            (equal (fn2-pool-row-snapshot r (let ((fn2-pool p)) (fn2-pool-put slot (gen gen) (base base) (cap cap) (state *fn2-pool-state-free*)
             (owner-kind 0) (owner-slot 0) (owner-gen 0)
             (lease-op-slot 0) (lease-op-gen 0) (lease-off 0) (lease-len 0)
             (out-count 0) (fill 0) (hand-to-kind 0) (hand-to-slot 0) (hand-to-gen 0)
             (next-free next) (class class))))
                   (if (equal r slot)
                       (list gen base cap *fn2-pool-state-free* 0 0 0 0 0 0 0 0 0 0 0 0 next class)
                     (fn2-pool-row-snapshot r p)))))
      :hints (("Goal" :cases ((equal r slot))
               :in-theory (e/d (fn2-pool-row-snapshot fn2-pool-rows
                                ,@(fn2-pool-init-column-runes cols) nth-update-nth)
                               (nth update-nth))))))))

(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-pool) (w state)))))
   (value
    `(defthm fn2-pool-carve-slots-snapshot
       (implies (and (natp left) (natp slot) (natp r) (natp base) (posp cap)
                     (<= (+ slot left) (fn2-pool-rows p))
                     (<= (+ base (* left cap)) 1152921504606846976))
                (equal (fn2-pool-row-snapshot r (fn2-pool-carve-slots left slot base cap class gen p))
                       (if (and (<= slot r) (< r (+ slot left)))
                           (list gen (+ base (* (- r slot) cap)) cap *fn2-pool-state-free*
                                 0 0 0 0 0 0 0 0 0 0 0 0
                                 (if (< (+ 1 r) (+ slot left)) (+ 1 r) *fn2-none*) class)
                         (fn2-pool-row-snapshot r p))))
       :hints (("Goal" :induct (fn2-pool-carve-slots left slot base cap class gen p)
                :nonlinearp t
                :in-theory (e/d (fn2-pool-carve-slots fn2-pool-initial-row-write-snapshot)
                                (fn2-pool-row-snapshot fn2-pool-rows
                                 ,@(fn2-pool-init-column-runes cols) nth update-nth))))))))

(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-pool) (w state)))))
  (value
   `(defthm fn2-pool-class-metadata-row-frame
      (and (equal (fn2-pool-row-snapshot r (update-fn2-pool-class-headsi i v p)) (fn2-pool-row-snapshot r p))
           (equal (fn2-pool-row-snapshot r (update-fn2-pool-class-countsi i v p)) (fn2-pool-row-snapshot r p))
           (equal (fn2-pool-row-snapshot r (update-fn2-pool-class-sizesi i v p)) (fn2-pool-row-snapshot r p))
           (equal (fn2-pool-rows (update-fn2-pool-class-headsi i v p)) (fn2-pool-rows p))
           (equal (fn2-pool-rows (update-fn2-pool-class-countsi i v p)) (fn2-pool-rows p))
           (equal (fn2-pool-rows (update-fn2-pool-class-sizesi i v p)) (fn2-pool-rows p)))
      :hints (("Goal" :in-theory (e/d
       (fn2-pool-row-snapshot fn2-pool-rows update-fn2-pool-class-headsi
        update-fn2-pool-class-countsi update-fn2-pool-class-sizesi
        ,@(fn2-pool-init-column-runes cols) nth-update-nth)
       (nth update-nth))))))))
(defthm fn2-pool-profile-total-natp
  (implies (fn2-profile-classes-p classes)
           (and (natp (fn2-profile-pool-slots classes)) (natp (fn2-profile-pool-bytes classes))))
  :hints (("Goal" :induct (fn2-profile-classes-p classes)
           :in-theory (enable fn2-profile-classes-p fn2-profile-pool-slots fn2-profile-pool-bytes))))
; A row's class interval determines its initial geometry and free successor.
(defun fn2-pool-initial-row-model (classes class slot base gen r)
  (declare (xargs :verify-guards nil))
  (if (or (atom classes) (< r slot)) nil
    (let ((count (caar classes)) (cap (cdar classes)))
      (if (< r (+ slot count))
          (list gen (+ base (* (- r slot) cap)) cap *fn2-pool-state-free*
                0 0 0 0 0 0 0 0 0 0 0 0
                (if (< (+ 1 r) (+ slot count)) (+ 1 r) *fn2-none*) class)
        (fn2-pool-initial-row-model (cdr classes) (+ 1 class) (+ slot count)
                                   (+ base (* count cap)) gen r)))))
(defthm fn2-pool-initial-row-model-before
  (implies (< r slot) (equal (fn2-pool-initial-row-model classes class slot base gen r) nil))
  :hints (("Goal" :in-theory (enable fn2-pool-initial-row-model))))
(defthm fn2-pool-profile-totals-forward
  (implies (fn2-profile-classes-p classes)
           (and (natp (fn2-profile-pool-slots classes)) (natp (fn2-profile-pool-bytes classes))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory nil :use fn2-pool-profile-total-natp)))
(defthm fn2-pool-initial-row-model-empty
  (implies (equal (len classes) 0)
           (equal (fn2-pool-initial-row-model classes class slot base gen r) nil))
  :hints (("Goal" :cases ((consp classes))
           :in-theory (enable fn2-pool-initial-row-model len))))
(defthm fn2-pool-carve-classes-snapshot
  (implies (and (fn2-profile-classes-p classes) (natp class) (natp slot) (natp base) (natp r)
                (<= (+ class (len classes)) 16)
                (<= (+ slot (fn2-profile-pool-slots classes)) (fn2-pool-rows p))
                (<= (+ base (fn2-profile-pool-bytes classes)) 1152921504606846976))
           (equal (fn2-pool-row-snapshot r (fn2-pool-carve-classes classes class slot base gen p))
                  (or (fn2-pool-initial-row-model classes class slot base gen r)
                      (fn2-pool-row-snapshot r p))))
  :hints (("Goal" :induct (fn2-pool-carve-classes classes class slot base gen p)
           :nonlinearp nil
           :in-theory (e/d (fn2-pool-carve-classes fn2-pool-initial-row-model
                            fn2-profile-classes-p fn2-profile-pool-slots fn2-profile-pool-bytes
                            fn2-pool-carve-slots-snapshot fn2-pool-class-metadata-row-frame)
                           (fn2-pool-carve-slots fn2-pool-row-snapshot fn2-pool-rows
                            update-fn2-pool-class-headsi update-fn2-pool-class-countsi update-fn2-pool-class-sizesi
                            nth update-nth)))))

(defthm fn2-pool-initial-row-model-covered
  (implies (and (fn2-profile-classes-p classes) (natp r) (natp slot)
                (<= slot r) (< r (+ slot (fn2-profile-pool-slots classes))))
           (consp (fn2-pool-initial-row-model classes class slot base gen r)))
  :hints (("Goal" :induct (fn2-pool-initial-row-model classes class slot base gen r)
           :in-theory (enable fn2-pool-initial-row-model fn2-profile-classes-p fn2-profile-pool-slots))))
(defthm fn2-pool-init-row-snapshot
  (implies (and (fn2-pool-profilep classes) (natp r) (< r (fn2-profile-pool-slots classes)))
           (equal (fn2-pool-row-snapshot r (fn2-pool-init classes gen-start gen-limit p))
                  (fn2-pool-initial-row-model classes 0 0 0 gen-start r)))
  :hints (("Goal" :in-theory (e/d
           (fn2-pool-init fn2-pool-profilep fn2-pool-carve-classes-snapshot
            fn2-pool-rows resize-fn2-pool-data update-fn2-pool-nclasses
            update-fn2-pool-gen-limit update-fn2-pool-retired-count nth-update-nth)
           (fn2-pool-carve-classes fn2-pool-initial-row-model fn2-pool-row-snapshot
            nth update-nth fn2-pool-columns-init))
           :use ((:instance fn2-pool-initial-row-model-covered (class 0) (slot 0) (base 0) (gen gen-start))))))

(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-pool) (w state)))))
  (value
   `(defthm fn2-pool-carve-slots-nth-metadata
      (implies (and (natp k) (<= ,(len cols) k))
               (equal (nth k (fn2-pool-carve-slots left slot base cap class gen p)) (nth k p)))
      :hints (("Goal" :induct (fn2-pool-carve-slots left slot base cap class gen p)
               :in-theory (e/d (fn2-pool-carve-slots)
                               (fn2-pool-rows ,@(fn2-pool-init-column-runes cols) nth update-nth))))))))
(defun fn2-pool-initial-class-model (classes class slot j)
  (declare (xargs :verify-guards nil))
  (if (or (atom classes) (< j class)) nil
    (if (equal j class)
        (list (if (posp (caar classes)) slot *fn2-none*) (caar classes) (cdar classes))
      (fn2-pool-initial-class-model (cdr classes) (+ 1 class) (+ slot (caar classes)) j))))
(defun fn2-pool-class-snapshot (j fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (list (fn2-pool-class-headsi j fn2-pool) (fn2-pool-class-countsi j fn2-pool)
        (fn2-pool-class-sizesi j fn2-pool)))
(defthm fn2-pool-carve-slots-class-snapshot
  (equal (fn2-pool-class-snapshot j (fn2-pool-carve-slots left slot base cap class gen p))
         (fn2-pool-class-snapshot j p))
  :hints (("Goal" :in-theory (e/d (fn2-pool-class-snapshot fn2-pool-class-headsi
                                  fn2-pool-class-countsi fn2-pool-class-sizesi)
                                 (fn2-pool-carve-slots nth update-nth)))))
(defthm fn2-pool-class-write-snapshot
  (implies (and (natp j) (natp class))
           (equal (fn2-pool-class-snapshot j
                     (update-fn2-pool-class-sizesi class cap
                       (update-fn2-pool-class-countsi class count
                         (update-fn2-pool-class-headsi class head p))))
                  (if (equal j class) (list head count cap) (fn2-pool-class-snapshot j p))))
  :hints (("Goal" :cases ((equal j class))
           :in-theory (e/d (fn2-pool-class-snapshot fn2-pool-class-headsi fn2-pool-class-countsi
                            fn2-pool-class-sizesi update-fn2-pool-class-headsi
                            update-fn2-pool-class-countsi update-fn2-pool-class-sizesi nth-update-nth)
                           (nth update-nth)))))
(defthm fn2-pool-initial-class-model-before
  (implies (< j class) (equal (fn2-pool-initial-class-model classes class slot j) nil))
  :hints (("Goal" :in-theory (enable fn2-pool-initial-class-model))))
(defthm fn2-pool-initial-class-model-empty
  (implies (equal (len classes) 0) (equal (fn2-pool-initial-class-model classes class slot j) nil))
  :hints (("Goal" :cases ((consp classes)) :in-theory (enable fn2-pool-initial-class-model len))))
(defthm fn2-pool-carve-classes-class-snapshot
  (implies (and (fn2-profile-classes-p classes) (natp class) (natp slot) (natp j)
                (<= (+ class (len classes)) 16)
                (<= (+ slot (fn2-profile-pool-slots classes)) (fn2-pool-rows p)))
           (equal (fn2-pool-class-snapshot j (fn2-pool-carve-classes classes class slot base gen p))
                  (or (fn2-pool-initial-class-model classes class slot j) (fn2-pool-class-snapshot j p))))
  :hints (("Goal" :induct (fn2-pool-carve-classes classes class slot base gen p)
           :in-theory (e/d (fn2-pool-carve-classes fn2-pool-initial-class-model
                            fn2-profile-classes-p fn2-profile-pool-slots)
                           (fn2-pool-carve-slots fn2-pool-class-snapshot fn2-pool-rows
                            update-fn2-pool-class-headsi update-fn2-pool-class-countsi update-fn2-pool-class-sizesi
                            nth update-nth)))))

(defthm fn2-pool-initial-class-model-covered
  (implies (and (fn2-profile-classes-p classes) (natp j) (natp class)
                (<= class j) (< j (+ class (len classes))))
           (consp (fn2-pool-initial-class-model classes class slot j)))
  :hints (("Goal" :induct (fn2-pool-initial-class-model classes class slot j)
           :in-theory (enable fn2-pool-initial-class-model fn2-profile-classes-p len))))
(defthm fn2-pool-init-class-snapshot
  (implies (and (fn2-pool-profilep classes) (natp j) (< j (len classes)))
           (equal (fn2-pool-class-snapshot j (fn2-pool-init classes gen-start gen-limit p))
                  (fn2-pool-initial-class-model classes 0 0 j)))
  :hints (("Goal" :in-theory (e/d
           (fn2-pool-init fn2-pool-profilep fn2-pool-carve-classes-class-snapshot
            fn2-pool-rows resize-fn2-pool-data update-fn2-pool-nclasses
            update-fn2-pool-gen-limit update-fn2-pool-retired-count nth-update-nth)
           (fn2-pool-carve-classes fn2-pool-initial-class-model fn2-pool-class-snapshot
            nth update-nth fn2-pool-columns-init))
           :use ((:instance fn2-pool-initial-class-model-covered (class 0) (slot 0))))))

(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-pool) (w state)))))
  (value
   `(defthm fn2-pool-carve-classes-nth-metadata
      (implies (and (natp k) (<= ,(len cols) k)
                    (not (member-equal k (list *fn2-pool-class-headsi* *fn2-pool-class-countsi* *fn2-pool-class-sizesi*))))
               (equal (nth k (fn2-pool-carve-classes classes class slot base gen p)) (nth k p)))
      :hints (("Goal" :induct (fn2-pool-carve-classes classes class slot base gen p)
               :in-theory (e/d (fn2-pool-carve-classes member-equal
                                update-fn2-pool-class-headsi update-fn2-pool-class-countsi
                                update-fn2-pool-class-sizesi nth-update-nth)
                               (fn2-pool-carve-slots nth update-nth))))))))
(defthm fn2-pool-init-scalars
  (implies (fn2-pool-profilep classes)
    (let ((after (fn2-pool-init classes gen-start gen-limit p)))
      (and (equal (fn2-pool-nslots after) (fn2-profile-pool-slots classes))
           (equal (fn2-pool-nclasses after) (len classes))
           (equal (fn2-pool-gen-limit after) gen-limit)
           (equal (fn2-pool-retired-count after) 0)
           (equal (fn2-pool-capacity-bytes after) (fn2-profile-pool-bytes classes)))))
  :hints (("Goal" :in-theory (e/d
           (fn2-pool-init fn2-pool-profilep fn2-pool-nslots fn2-pool-capacity-bytes
            fn2-pool-rows fn2-pool-nclasses fn2-pool-gen-limit fn2-pool-retired-count fn2-pool-data-length
            resize-fn2-pool-data update-fn2-pool-nclasses update-fn2-pool-gen-limit
            update-fn2-pool-retired-count nth-update-nth)
           (fn2-pool-carve-classes fn2-pool-columns-init nth update-nth)))))

(local
 (defun fn2-pool-init-reader-equations (cols r p record)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
   (cons `(equal (,(fn2-columns-col-name 'fn2-pool (caar cols)) ,r ,p)
                 (,(fn2-columns-col-name 'fn2-pool-record (caar cols)) ,record))
         (fn2-pool-init-reader-equations (cdr cols) r p record)))))
(local
 (defun fn2-pool-init-record-runes (cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
   (cons (fn2-columns-col-name 'fn2-pool-record (caar cols))
         (fn2-pool-init-record-runes (cdr cols))))))
(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-pool) (w state)))))
  (value
   `(defthm fn2-pool-row-readers-projection
      (and ,@(fn2-pool-init-reader-equations cols 'r 'p '(fn2-pool-row-snapshot r p)))
      :rule-classes nil
      :hints (("Goal" :in-theory (enable fn2-pool-row-snapshot true-list-fix
                                         ,@(fn2-pool-init-record-runes cols))))))))
(make-event
 (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-pool) (w state)))))
  (value
   `(defthm fn2-pool-init-row-readers
      (implies (and (fn2-pool-profilep classes) (natp r) (< r (fn2-profile-pool-slots classes)))
       (and ,@(fn2-pool-init-reader-equations cols 'r '(fn2-pool-init classes gen-start gen-limit p)
                                              '(fn2-pool-initial-row-model classes 0 0 0 gen-start r))))
      :hints (("Goal" :in-theory nil
               :use ((:instance fn2-pool-row-readers-projection (p (fn2-pool-init classes gen-start gen-limit p)))
                     fn2-pool-init-row-snapshot)))))))
(defthm fn2-pool-initial-row-model-constant-fields
  (implies (consp (fn2-pool-initial-row-model classes class slot base gen r))
    (let ((row (fn2-pool-initial-row-model classes class slot base gen r)))
     (and (equal (fn2-pool-record-gen row) gen)
          (equal (fn2-pool-record-state row) *fn2-pool-state-free*)
          (equal (fn2-pool-record-out-count row) 0)
          (equal (fn2-pool-record-fill row) 0)
          (equal (fn2-pool-record-lease-off row) 0)
          (equal (fn2-pool-record-lease-len row) 0))))
  :hints (("Goal" :induct (fn2-pool-initial-row-model classes class slot base gen r)
           :in-theory (enable fn2-pool-initial-row-model fn2-pool-record-gen fn2-pool-record-state
                              fn2-pool-record-out-count fn2-pool-record-fill fn2-pool-record-lease-off
                              fn2-pool-record-lease-len))))
(defthm fn2-pool-init-retired-slots
  (implies (and (fn2-pool-profilep classes) (natp n) (<= n (fn2-profile-pool-slots classes)))
           (equal (fn2-pool-retired-slots n (fn2-pool-init classes gen-start gen-limit p)) 0))
  :hints (("Goal" :induct (fn2-pool-retired-slots n (fn2-pool-init classes gen-start gen-limit p))
           :in-theory (e/d (fn2-pool-retired-slots fn2-pool-profilep)
                            (fn2-pool-init fn2-pool-state fn2-pool-record-state fn2-pool-initial-row-model)))))

(local (include-book "arithmetic-3/top" :dir :system))
(defthm fn2-pool-initial-row-model-class-bounds
  (implies (and (fn2-profile-classes-p classes) (natp r) (natp slot) (natp class)
                (<= slot r) (< r (+ slot (fn2-profile-pool-slots classes))))
    (let ((row-class (fn2-pool-record-class (fn2-pool-initial-row-model classes class slot base gen r))))
      (and (<= class row-class) (< row-class (+ class (len classes))))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn2-pool-initial-row-model classes class slot base gen r)
           :in-theory (enable fn2-pool-initial-row-model fn2-pool-record-class
                              fn2-profile-classes-p fn2-profile-pool-slots))))
(defthm fn2-pool-offset-in-class-bounds
  (implies (and (natp r) (natp slot) (natp count) (natp base) (posp cap) (natp tail)
                (<= slot r) (< r (+ slot count)))
           (and (<= base (+ base (* (- r slot) cap)))
                (<= (+ base (* (- r slot) cap) cap) (+ base (* count cap) tail))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))
(defthm fn2-pool-initial-row-model-geometry-bounds
  (implies (and (fn2-profile-classes-p classes) (natp r) (natp slot) (natp base)
                (<= slot r) (< r (+ slot (fn2-profile-pool-slots classes))))
    (let ((row (fn2-pool-initial-row-model classes class slot base gen r)))
      (and (<= base (fn2-pool-record-base row))
           (<= (+ (fn2-pool-record-base row) (fn2-pool-record-cap row))
               (+ base (fn2-profile-pool-bytes classes))))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn2-pool-initial-row-model classes class slot base gen r)
           :nonlinearp nil
           :expand ((fn2-profile-classes-p classes) (fn2-profile-pool-slots classes) (fn2-profile-pool-bytes classes))
           :in-theory (enable fn2-pool-initial-row-model fn2-pool-record-base fn2-pool-record-cap
                              fn2-profile-classes-p fn2-profile-pool-slots fn2-profile-pool-bytes))
          ("Subgoal *1/2" :use ((:instance fn2-pool-offset-in-class-bounds
            (count (caar classes)) (cap (cdar classes)) (tail (fn2-profile-pool-bytes (cdr classes))))))))
(defthm fn2-pool-initial-row-model-class-cap
  (implies (and (fn2-profile-classes-p classes) (natp r) (natp slot) (natp class)
                (<= slot r) (< r (+ slot (fn2-profile-pool-slots classes))))
    (let* ((row (fn2-pool-initial-row-model classes class slot base gen r))
           (info (fn2-pool-initial-class-model classes class slot (fn2-pool-record-class row))))
      (equal (nth 2 info) (fn2-pool-record-cap row))))
  :hints (("Goal" :induct (fn2-pool-initial-row-model classes class slot base gen r)
           :in-theory (enable fn2-pool-initial-row-model fn2-pool-initial-class-model
                              fn2-pool-record-class fn2-pool-record-cap
                              fn2-profile-classes-p fn2-profile-pool-slots))
          ("Subgoal *1/3" :use ((:instance fn2-pool-initial-row-model-class-bounds
             (classes (cdr classes)) (class (+ 1 class)) (slot (+ slot (caar classes)))
             (base (+ base (* (caar classes) (cdar classes)))))))))

; Initialized row geometry covers each allocated byte exactly once.
(defthm fn2-pool-profile-zero-slots-zero-bytes
 (implies (and (fn2-profile-classes-p classes) (equal (fn2-profile-pool-slots classes) 0))
          (equal (fn2-profile-pool-bytes classes) 0))
 :hints (("Goal" :induct (fn2-profile-classes-p classes)
          :in-theory (enable fn2-profile-classes-p fn2-profile-pool-slots fn2-profile-pool-bytes))))
(defthm fn2-pool-initial-row-model-first-base
 (implies (and (fn2-profile-classes-p classes) (natp slot) (natp base)
               (< 0 (fn2-profile-pool-slots classes)))
          (equal (fn2-pool-record-base (fn2-pool-initial-row-model classes class slot base gen slot)) base))
 :hints (("Goal" :induct (fn2-pool-initial-row-model classes class slot base gen slot)
          :in-theory (enable fn2-pool-initial-row-model fn2-pool-record-base fn2-profile-classes-p fn2-profile-pool-slots))))
(defthm fn2-pool-initial-row-model-last-end
 (implies (and (fn2-profile-classes-p classes) (natp slot) (natp base)
               (< 0 (fn2-profile-pool-slots classes)))
  (let ((row (fn2-pool-initial-row-model classes class slot base gen
               (+ slot (fn2-profile-pool-slots classes) -1))))
   (equal (+ (fn2-pool-record-base row) (fn2-pool-record-cap row))
          (+ base (fn2-profile-pool-bytes classes)))))
 :hints (("Goal" :induct (fn2-pool-initial-row-model classes class slot base gen
                            (+ slot (fn2-profile-pool-slots classes) -1))
          :in-theory (enable fn2-pool-initial-row-model fn2-pool-record-base fn2-pool-record-cap
                             fn2-profile-classes-p fn2-profile-pool-slots fn2-profile-pool-bytes))))
(defthm fn2-pool-initial-row-model-adjacent
 (implies (and (fn2-profile-classes-p classes) (natp slot) (natp base) (natp r)
               (< slot r) (< r (+ slot (fn2-profile-pool-slots classes))))
  (equal (fn2-pool-record-base (fn2-pool-initial-row-model classes class slot base gen r))
         (+ (fn2-pool-record-base (fn2-pool-initial-row-model classes class slot base gen (- r 1)))
            (fn2-pool-record-cap (fn2-pool-initial-row-model classes class slot base gen (- r 1))))))
 :hints (("Goal" :induct (fn2-pool-initial-row-model classes class slot base gen r)
          :in-theory (enable fn2-pool-initial-row-model fn2-pool-record-base fn2-pool-record-cap
                             fn2-profile-classes-p fn2-profile-pool-slots))
          ("Subgoal *1/3" :use ((:instance fn2-pool-initial-row-model-first-base
              (classes (cdr classes)) (class (+ 1 class)) (slot (+ slot (caar classes)))
              (base (+ base (* (caar classes) (cdar classes)))))))))

(defthm fn2-pool-initial-row-model-types
 (implies (and (fn2-profile-classes-p classes) (natp slot) (natp class) (natp base) (natp r)
               (<= slot r) (< r (+ slot (fn2-profile-pool-slots classes))))
  (let ((row (fn2-pool-initial-row-model classes class slot base gen r)))
   (and (natp (fn2-pool-record-class row)) (natp (fn2-pool-record-base row))
        (posp (fn2-pool-record-cap row)))))
 :hints (("Goal" :induct (fn2-pool-initial-row-model classes class slot base gen r)
          :nonlinearp t
          :in-theory (enable fn2-pool-initial-row-model fn2-pool-record-class fn2-pool-record-base fn2-pool-record-cap
                             fn2-profile-classes-p fn2-profile-pool-slots))))
(defthm fn2-pool-init-class-size
 (implies (and (fn2-pool-profilep classes) (natp j) (< j (len classes)))
  (equal (fn2-pool-class-sizesi j (fn2-pool-init classes gen-start gen-limit p))
         (nth 2 (fn2-pool-initial-class-model classes 0 0 j))))
 :hints (("Goal" :use fn2-pool-init-class-snapshot
          :in-theory (e/d (fn2-pool-class-snapshot)
                          (fn2-pool-init-class-snapshot fn2-pool-init fn2-pool-initial-class-model fn2-pool-class-sizesi
                           fn2-pool-class-headsi fn2-pool-class-countsi)))))
(defthm fn2-pool-initial-row-model-cap-positive
 (implies (and (fn2-profile-classes-p classes) (natp slot) (natp class) (natp base) (natp r)
               (<= slot r) (< r (+ slot (fn2-profile-pool-slots classes))))
  (< 0 (fn2-pool-record-cap (fn2-pool-initial-row-model classes class slot base gen r))))
 :rule-classes :linear
 :hints (("Goal" :use fn2-pool-initial-row-model-types
          :in-theory (e/d (posp) (fn2-pool-initial-row-model-types fn2-pool-record-cap fn2-pool-initial-row-model)))))
(defthm fn2-pool-init-row-invariant
 (implies (and (fn2-pool-profilep classes) (natp n) (<= n (fn2-profile-pool-slots classes))
               (natp gen-start) (natp gen-limit) (<= gen-start gen-limit))
          (fn2-pool-row-invariantp n (fn2-pool-init classes gen-start gen-limit p)))
 :hints (("Goal" :induct (fn2-pool-row-invariantp n (fn2-pool-init classes gen-start gen-limit p))
          :in-theory (e/d (fn2-pool-row-invariantp fn2-pool-profilep)
                          (fn2-pool-init fn2-pool-initial-row-model fn2-pool-initial-class-model
                           fn2-pool-state fn2-pool-base fn2-pool-cap fn2-pool-class fn2-pool-fill fn2-pool-gen
                           fn2-pool-out-count fn2-pool-lease-off fn2-pool-lease-len fn2-pool-class-sizesi
                           fn2-pool-nclasses fn2-pool-gen-limit fn2-pool-capacity-bytes
                           fn2-pool-record-state fn2-pool-record-base fn2-pool-record-cap fn2-pool-record-class
                           fn2-pool-record-fill fn2-pool-record-gen fn2-pool-record-out-count
                           fn2-pool-record-lease-off fn2-pool-record-lease-len)))))
(defthm fn2-pool-init-byte-account
 (implies (fn2-pool-profilep classes)
  (let ((after (fn2-pool-init classes gen-start gen-limit p)))
   (equal (fn2-pool-capacity-bytes after)
          (if (zp (fn2-pool-nslots after)) 0
            (+ (fn2-pool-base (- (fn2-pool-nslots after) 1) after)
               (fn2-pool-cap (- (fn2-pool-nslots after) 1) after))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-pool-initial-row-model-last-end (class 0) (slot 0) (base 0) (gen gen-start)))
          :in-theory (e/d (fn2-pool-profilep)
            (fn2-pool-init fn2-pool-capacity-bytes fn2-pool-nslots fn2-pool-base fn2-pool-cap
             fn2-pool-initial-row-model fn2-pool-record-base fn2-pool-record-cap
             fn2-pool-initial-row-model-adjacent)))))
