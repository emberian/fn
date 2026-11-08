(in-package "ACL2")
(include-book "columns")
(include-book "owed")
(include-book "profile")

; A range is slot-relative u32/u32.  Bases are u60 so the shared region is
; not artificially limited to 4 GiB.  All resident arithmetic stays fixnum.
; #xffffffff is the free-list terminator, never a slot (rows < 2^32).
(defcolumns fn2-pool
  ((gen :u60) (base :u60) (cap :u32)
   (state (:enum fn2-pool-state (:free :workspace :leased-in :leased-out :handed :retired)))
   (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
   (lease-op-slot :link) (lease-op-gen :u60) (lease-off :u32) (lease-len :u32)
   (out-count :u32) (fill :u32)
   (hand-to-kind :u8) (hand-to-slot :link) (hand-to-gen :u60)
   (next-free :link) (class :u8))
  :rows-bound 4294967296
  :init-name fn2-pool-columns-init
  :extra-fields
  ((fn2-pool-data :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t :why "Byte backing store, addressed by each slot base and capacity.")
   (fn2-pool-class-heads :type (array (unsigned-byte 32) (16)) :initially *fn2-none* :why "One free-chain head per size class, not per slot.")
   (fn2-pool-class-counts :type (array (unsigned-byte 32) (16)) :initially 0 :why "Free capacity is counted by size class.")
   (fn2-pool-class-sizes :type (array (unsigned-byte 32) (16)) :initially 0 :why "Class geometry has a different cardinality from slots.")
   (fn2-pool-nclasses :type (integer 0 16) :initially 0 :why "Number of configured size classes governs class-array access.")
   (fn2-pool-gen-limit :type (unsigned-byte 60) :initially 0 :why "A single retirement limit applies to all pool slots.")
   (fn2-pool-retired-count :type (unsigned-byte 32) :initially 0 :why "Aggregate retired capacity survives slot reuse.")))

; Expansion only: runtime is a straight let* of scalar column writes.

(defun fn2-pool-mrefp (kind slot gen)
  (declare (xargs :guard t))
  (and (unsigned-byte-p 8 kind) (unsigned-byte-p 32 slot)
       (unsigned-byte-p 60 gen)))

(defun fn2-pool-handle-code (slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (cond ((not (and (natp slot) (< slot (fn2-pool-rows fn2-pool)))) :bounds)
        ((not (equal gen (fn2-pool-gen slot fn2-pool))) :stale)
        (t :ok)))

(defun fn2-pool-ownerp (slot okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp slot)
                              (< slot (fn2-pool-rows fn2-pool)))))
  (and (equal okind (fn2-pool-owner-kind slot fn2-pool))
       (equal oslot (fn2-pool-owner-slot slot fn2-pool))
       (equal ogen (fn2-pool-owner-gen slot fn2-pool))))

(defun fn2-pool-workspace-code (slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-handle-code slot gen fn2-pool)))
    (cond ((not (eq code :ok)) code)
          ((not (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-workspace*)) :state)
          ((not (fn2-pool-ownerp slot okind oslot ogen fn2-pool)) :owner)
          ((not (= (fn2-pool-out-count slot fn2-pool) 0)) :state)
          (t :ok))))

; Init-only traversals.  Profile widths are admission limits on resident
; execution state, not ceilings on stored data.  Invalid init profiles violate
; init's guard; all handle-bearing exports below validate handles at runtime.

(defun fn2-pool-profilep (classes)
  (declare (xargs :guard t))
  (and (fn2-profile-classes-p classes)
       (<= (len classes) 16)
       (unsigned-byte-p 32 (fn2-profile-pool-slots classes))
       (unsigned-byte-p 60 (fn2-profile-pool-bytes classes))))

(defun fn2-pool-carve-slots (left slot base cap class gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp slot)
                              (natp base) (unsigned-byte-p 32 cap)
                              (unsigned-byte-p 8 class) (unsigned-byte-p 60 gen))))
  (if (or (zp left) (>= slot (fn2-pool-rows fn2-pool))
          (not (unsigned-byte-p 60 base)))
      fn2-pool
    (let* ((fn2-pool
             (fn2-pool-put slot (gen gen) (base base) (cap cap)
                           (state *fn2-pool-state-free*)
                           (owner-kind 0) (owner-slot 0) (owner-gen 0)
                           (lease-op-slot 0) (lease-op-gen 0) (lease-off 0) (lease-len 0)
                           (out-count 0) (fill 0)
                           (hand-to-kind 0) (hand-to-slot 0) (hand-to-gen 0)
                           (next-free (if (and (< 1 left) (< (+ 1 slot) (fn2-pool-rows fn2-pool)))
                                          (+ 1 slot) *fn2-none*))
                           (class class))))
      (fn2-pool-carve-slots (- left 1) (+ slot 1) (+ base cap) cap class gen fn2-pool))))

(defthm fn2-pool-carve-slots-wfp
  (implies (and (fn2-pool-wfp fn2-pool) (natp slot))
           (fn2-pool-wfp (fn2-pool-carve-slots left slot base cap class gen fn2-pool))))
(defthm fn2-pool-carve-slots-rows
  (equal (fn2-pool-rows (fn2-pool-carve-slots left slot base cap class gen fn2-pool))
         (fn2-pool-rows fn2-pool)))
(defthm fn2-pool-carve-slots-type
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                (natp left) (natp slot) (natp base)
                (unsigned-byte-p 32 cap) (unsigned-byte-p 8 class)
                (unsigned-byte-p 60 gen))
           (fn2-poolp (fn2-pool-carve-slots left slot base cap class gen fn2-pool))))
(in-theory (disable fn2-pool-carve-slots))

(defun fn2-pool-carve-classes (classes class slot base gen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool)
                              (fn2-profile-classes-p classes)
                              (natp class) (natp slot) (natp base)
                              (unsigned-byte-p 60 gen))))
  (if (or (atom classes) (>= class 16))
      fn2-pool
    (let* ((count (caar classes)) (bytes (cdar classes))
           (nslots (fn2-pool-rows fn2-pool))
           (fn2-pool (fn2-pool-carve-slots count slot base bytes class gen fn2-pool))
           (fn2-pool (update-fn2-pool-class-headsi
                       class (if (and (< 0 count) (< slot nslots))
                                 slot *fn2-none*) fn2-pool))
           (fn2-pool (update-fn2-pool-class-countsi class count fn2-pool))
           (fn2-pool (update-fn2-pool-class-sizesi class bytes fn2-pool)))
      (fn2-pool-carve-classes (cdr classes) (+ 1 class) (+ slot count)
                              (+ base (* count bytes)) gen fn2-pool))))

(defthm fn2-pool-carve-classes-wfp
  (implies (and (fn2-pool-wfp fn2-pool) (natp class) (natp slot)
                (fn2-profile-classes-p classes))
           (fn2-pool-wfp (fn2-pool-carve-classes classes class slot base gen fn2-pool))))
(defthm fn2-pool-carve-classes-type
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                (fn2-profile-classes-p classes)
                (natp class) (natp slot) (natp base) (unsigned-byte-p 60 gen))
           (fn2-poolp (fn2-pool-carve-classes classes class slot base gen fn2-pool))))
(in-theory (disable fn2-pool-carve-classes))

(defun fn2-pool-init (classes gen-start gen-limit fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-profilep classes)
                              (unsigned-byte-p 60 gen-start)
                              (unsigned-byte-p 60 gen-limit) (<= gen-start gen-limit))))
  (let* ((fn2-pool (fn2-pool-columns-init (fn2-profile-pool-slots classes) fn2-pool))
         (fn2-pool (resize-fn2-pool-data (fn2-profile-pool-bytes classes) fn2-pool))
         (fn2-pool (update-fn2-pool-nclasses (len classes) fn2-pool))
         (fn2-pool (update-fn2-pool-gen-limit gen-limit fn2-pool))
         (fn2-pool (update-fn2-pool-retired-count 0 fn2-pool)))
    (fn2-pool-carve-classes classes 0 0 0 gen-start fn2-pool)))

; A fixed 16-visit selection, independent of the number of slots or bytes.
; Unsorted classes are allowed; ties select the earliest declaration.
(defun fn2-pool-class-scan (i len best size fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix (- 16 (nfix i)))
                  :guard (and (natp i) (natp len) (natp size))))
  (if (or (not (natp i)) (>= i 16) (>= i (fn2-pool-nclasses fn2-pool)))
      best
    (let ((cap (fn2-pool-class-sizesi i fn2-pool)))
      (if (and (<= len cap) (or (null best) (< cap size)))
          (fn2-pool-class-scan (+ i 1) len i cap fn2-pool)
        (fn2-pool-class-scan (+ i 1) len best size fn2-pool)))))
(defun fn2-pool-class-for (len fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (natp len)))
  (fn2-pool-class-scan 0 len nil 0 fn2-pool))

(defun fn2-pool-reserve (class okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (not (and (natp class) (< class (fn2-pool-nclasses fn2-pool))
                (fn2-pool-mrefp okind oslot ogen)))
      (mv :bounds 0 0 fn2-pool)
    (let ((slot (fn2-pool-class-headsi class fn2-pool))
          (count (fn2-pool-class-countsi class fn2-pool)))
      (cond ((or (= count 0) (= slot *fn2-none*)) (mv :exhausted 0 0 fn2-pool))
            ((>= slot (fn2-pool-rows fn2-pool)) (mv :bounds 0 0 fn2-pool))
            ((not (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-free*))
             (mv :state 0 0 fn2-pool))
            ((not (= (fn2-pool-class slot fn2-pool) class)) (mv :state 0 0 fn2-pool))
            ((not (= (fn2-pool-out-count slot fn2-pool) 0)) (mv :state 0 0 fn2-pool))
            (t (let* ((gen (fn2-pool-gen slot fn2-pool))
                      (next (fn2-pool-next-free slot fn2-pool))
                      (fn2-pool (update-fn2-pool-class-headsi class next fn2-pool))
                      (fn2-pool (update-fn2-pool-class-countsi class (- count 1) fn2-pool))
                      (fn2-pool (fn2-pool-put slot (state *fn2-pool-state-workspace*)
                                            (owner-kind okind) (owner-slot oslot) (owner-gen ogen)
                                            (out-count 0) (fill 0))))
                 (mv :ok slot gen fn2-pool)))))))

 ; The count premise is local and constant-work. Semantic accounting owes
; that releasing a live row satisfies it; no whole-pool traversal is served.
(defun fn2-pool-release-countp (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (or (not (and (natp slot) (< slot (fn2-pool-rows fn2-pool))
                (= (fn2-pool-state slot fn2-pool) *fn2-pool-state-workspace*)))
      (and (< (fn2-pool-rows fn2-pool) 4294967296)
           (< (fn2-pool-retired-count fn2-pool) (fn2-pool-rows fn2-pool))
           (let ((class (fn2-pool-class slot fn2-pool)))
             (or (not (< class (fn2-pool-nclasses fn2-pool)))
                 (< (fn2-pool-class-countsi class fn2-pool) (fn2-pool-rows fn2-pool)))))))
(defthm fn2-pool-release-count-bound
  (implies (and (natp count) (natp rows) (< count rows) (< rows 4294967296))
           (unsigned-byte-p 32 (+ 1 count))))

(defun fn2-pool-release (slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool)
                              (fn2-pool-release-countp slot fn2-pool))))
  (if (not (mbt (fn2-pool-release-countp slot fn2-pool))) (mv :ok fn2-pool)
    (let ((code (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool)))
      (cond ((not (eq code :ok)) (mv code fn2-pool))
            ((not (= (fn2-pool-out-count slot fn2-pool) 0)) (mv :state fn2-pool))
            ((>= (fn2-pool-gen slot fn2-pool) (fn2-pool-gen-limit fn2-pool))
             (let* ((count (fn2-pool-retired-count fn2-pool))
                    (fn2-pool (fn2-pool-put slot (state *fn2-pool-state-retired*)))
                    (fn2-pool (update-fn2-pool-retired-count (+ count 1) fn2-pool)))
               (mv :retired fn2-pool)))
            (t (let ((class (fn2-pool-class slot fn2-pool)))
                 (if (not (< class (fn2-pool-nclasses fn2-pool)))
                     (mv :bounds fn2-pool)
                   (let* ((count (fn2-pool-class-countsi class fn2-pool))
                          (next (fn2-pool-class-headsi class fn2-pool))
                          (new-gen (+ 1 (fn2-pool-gen slot fn2-pool)))
                          (fn2-pool (fn2-pool-put slot (gen new-gen) (state *fn2-pool-state-free*)
                                                (next-free next) (fill 0)))
                          (fn2-pool (update-fn2-pool-class-headsi class slot fn2-pool))
                          (fn2-pool (update-fn2-pool-class-countsi class (+ 1 count) fn2-pool)))
                     (mv :ok fn2-pool)))))))))

(defun fn2-pool-lease-in (slot gen len opslot opgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code 0 fn2-pool))
          ((not (and (unsigned-byte-p 32 len) (unsigned-byte-p 32 opslot)
                     (unsigned-byte-p 60 opgen)
                     (<= (+ (fn2-pool-fill slot fn2-pool) len) (fn2-pool-cap slot fn2-pool))))
           (mv :bounds 0 fn2-pool))
          (t (let* ((off (fn2-pool-fill slot fn2-pool))
                    (fn2-pool (fn2-pool-put slot (state *fn2-pool-state-leased-in*)
                                          (lease-op-slot opslot) (lease-op-gen opgen)
                                          (lease-off off) (lease-len len))))
               (mv :ok off fn2-pool))))))

(defun fn2-pool-input-code (slot gen opslot opgen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-handle-code slot gen fn2-pool)))
    (cond ((not (eq code :ok)) code)
          ((not (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-in*)) :state)
          ((not (and (equal opslot (fn2-pool-lease-op-slot slot fn2-pool))
                     (equal opgen (fn2-pool-lease-op-gen slot fn2-pool)))) :owner)
          (t :ok))))

(defun fn2-pool-adapter-write (slot gen opslot opgen idx byte fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-input-code slot gen opslot opgen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code fn2-pool))
          ((not (and (natp idx) (unsigned-byte-p 8 byte)
                     (<= (fn2-pool-lease-off slot fn2-pool) idx)
                     (< idx (+ (fn2-pool-lease-off slot fn2-pool) (fn2-pool-lease-len slot fn2-pool)))
                     (< idx (fn2-pool-cap slot fn2-pool))
                     (< (+ (fn2-pool-base slot fn2-pool) idx) (fn2-pool-data-length fn2-pool))))
           (mv :bounds fn2-pool))
          (t (let ((fn2-pool (update-fn2-pool-datai (+ (fn2-pool-base slot fn2-pool) idx) byte fn2-pool)))
               (mv :ok fn2-pool))))))

; The adapter's completion contract says the first N loan bytes were written.
; No per-byte bitmap: the owed theorem carries that environmental premise.
(defun fn2-pool-complete-in (slot gen opslot opgen n fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-input-code slot gen opslot opgen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code fn2-pool))
          ((not (and (natp n) (<= n (fn2-pool-lease-len slot fn2-pool))
                     (<= (+ (fn2-pool-lease-off slot fn2-pool) n) (fn2-pool-cap slot fn2-pool))))
           (mv :bounds fn2-pool))
          (t (let* ((new-fill (+ (fn2-pool-lease-off slot fn2-pool) n))
                    (fn2-pool (fn2-pool-put slot (state *fn2-pool-state-workspace*) (fill new-fill))))
               (mv :ok fn2-pool))))))

(defun fn2-pool-readable-code (slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-handle-code slot gen fn2-pool)))
    (cond ((not (eq code :ok)) code)
          ((not (or (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-workspace*)
                    (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-out*))) :state)
          ((not (fn2-pool-ownerp slot okind oslot ogen fn2-pool)) :owner)
          (t :ok))))

(defun fn2-pool-lease-out (slot gen off len okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code fn2-pool))
          ((not (and (unsigned-byte-p 32 off) (unsigned-byte-p 32 len) (<= (+ off len) (fn2-pool-fill slot fn2-pool))))
           (mv :bounds fn2-pool))
          ((= (fn2-pool-out-count slot fn2-pool) *fn2-none*) (mv :exhausted fn2-pool))
          (t (let* ((count (+ 1 (fn2-pool-out-count slot fn2-pool)))
                    (fn2-pool (fn2-pool-put slot (state *fn2-pool-state-leased-out*) (out-count count))))
               (mv :ok fn2-pool))))))

; Caller has matched the terminal OpRef in the outstanding table (quest A2).
; This ABI intentionally has no owner/op arguments: the pool checks the
; generation and borrow state; A2 proves one release per matched borrow.
(defun fn2-pool-release-out (slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-handle-code slot gen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code fn2-pool))
          ((or (not (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-out*))
               (= (fn2-pool-out-count slot fn2-pool) 0)) (mv :state fn2-pool))
          (t (let* ((count (- (fn2-pool-out-count slot fn2-pool) 1))
                    (fn2-pool (fn2-pool-put slot
                               (state (if (= count 0) *fn2-pool-state-workspace* *fn2-pool-state-leased-out*))
                               (out-count count))))
               (mv :ok fn2-pool))))))

(defun fn2-pool-hand (slot gen okind oslot ogen tkind tslot tgen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code fn2-pool))
          ((not (fn2-pool-mrefp tkind tslot tgen)) (mv :bounds fn2-pool))
          (t (let ((fn2-pool (fn2-pool-put slot (state *fn2-pool-state-handed*)
                                         (hand-to-kind tkind) (hand-to-slot tslot) (hand-to-gen tgen))))
               (mv :ok fn2-pool))))))

(defun fn2-pool-accept-hand (slot gen tkind tslot tgen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-handle-code slot gen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code fn2-pool))
          ((not (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-handed*)) (mv :state fn2-pool))
          ((not (and (equal tkind (fn2-pool-hand-to-kind slot fn2-pool))
                     (equal tslot (fn2-pool-hand-to-slot slot fn2-pool))
                     (equal tgen (fn2-pool-hand-to-gen slot fn2-pool)))) (mv :owner fn2-pool))
          (t (let ((fn2-pool (fn2-pool-put slot (state *fn2-pool-state-workspace*)
                                         (owner-kind (fn2-pool-hand-to-kind slot fn2-pool))
                                         (owner-slot (fn2-pool-hand-to-slot slot fn2-pool))
                                         (owner-gen (fn2-pool-hand-to-gen slot fn2-pool)))))
               (mv :ok fn2-pool))))))

(defun fn2-pool-read (slot gen idx okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code 0))
          ((not (and (natp idx) (< idx (fn2-pool-fill slot fn2-pool))
                     (< (+ (fn2-pool-base slot fn2-pool) idx) (fn2-pool-data-length fn2-pool))))
           (mv :bounds 0))
          (t (mv :ok (fn2-pool-datai (+ (fn2-pool-base slot fn2-pool) idx) fn2-pool))))))

(defun fn2-pool-write (slot gen idx byte okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code fn2-pool))
          ((not (and (natp idx) (unsigned-byte-p 8 byte)
                     (< idx (fn2-pool-cap slot fn2-pool))
                     (<= idx (fn2-pool-fill slot fn2-pool))
                     (< (+ (fn2-pool-base slot fn2-pool) idx) (fn2-pool-data-length fn2-pool))))
           (mv :bounds fn2-pool))
          (t (let* ((base (fn2-pool-base slot fn2-pool))
                    (new-fill (max (fn2-pool-fill slot fn2-pool) (+ idx 1)))
                    (fn2-pool (update-fn2-pool-datai (+ base idx) byte fn2-pool))
                    (fn2-pool (fn2-pool-set-fill slot new-fill fn2-pool)))
               (mv :ok fn2-pool))))))

(defun fn2-pool-reset (slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool)))
    (if (not (eq code :ok)) (mv code fn2-pool)
      (let ((fn2-pool (fn2-pool-set-fill slot 0 fn2-pool)))
        (mv :ok fn2-pool)))))

(defun fn2-pool-slot-state (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp slot)
                              (< slot (fn2-pool-rows fn2-pool)))))
  (fn2-pool-state-code->keyword (fn2-pool-state slot fn2-pool)))

(defun fn2-pool-slot-gen (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp slot)
                              (< slot (fn2-pool-rows fn2-pool)))))
  (fn2-pool-gen slot fn2-pool))

(defun fn2-pool-slot-fill (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp slot)
                              (< slot (fn2-pool-rows fn2-pool)))))
  (fn2-pool-fill slot fn2-pool))

(defun fn2-pool-slot-base (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp slot)
                              (< slot (fn2-pool-rows fn2-pool)))))
  (fn2-pool-base slot fn2-pool))

(defun fn2-pool-slot-cap (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp slot)
                              (< slot (fn2-pool-rows fn2-pool)))))
  (fn2-pool-cap slot fn2-pool))

(defun fn2-pool-slot-out-count (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp slot)
                              (< slot (fn2-pool-rows fn2-pool)))))
  (fn2-pool-out-count slot fn2-pool))

(defun fn2-pool-lease-range (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp slot)
                              (< slot (fn2-pool-rows fn2-pool)))))
  (mv (fn2-pool-lease-off slot fn2-pool) (fn2-pool-lease-len slot fn2-pool)))
(defun fn2-pool-free-count (class fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (natp class) (< class (fn2-pool-nclasses fn2-pool)))))
  (fn2-pool-class-countsi class fn2-pool))
(defun fn2-pool-nslots (fn2-pool)
  (declare (xargs :stobjs fn2-pool))
  (fn2-pool-rows fn2-pool))
(defun fn2-pool-capacity-bytes (fn2-pool)
  (declare (xargs :stobjs fn2-pool))
  (fn2-pool-data-length fn2-pool))

(defun-nx fn2-pool-slot-view (slot fn2-pool)
  (fn2-pool-row-view slot fn2-pool))
(defun-nx fn2-pool-byte-slice (base n fn2-pool)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (cons (fn2-pool-datai (nfix base) fn2-pool)
          (fn2-pool-byte-slice (+ 1 (nfix base)) (- n 1) fn2-pool))))
(defun-nx fn2-pool-bytes-view (slot fn2-pool)
  (fn2-pool-byte-slice (fn2-pool-base slot fn2-pool)
                       (fn2-pool-fill slot fn2-pool) fn2-pool))

; Shape-only support for composed callers; the semantic keystones below remain owed.

(defthm fn2-pool-init-wfp
  (implies (fn2-pool-profilep classes)
           (fn2-pool-wfp (fn2-pool-init classes gen-start gen-limit fn2-pool))))

(defthm fn2-pool-init-type
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-profilep classes)
                (unsigned-byte-p 60 gen-start) (unsigned-byte-p 60 gen-limit)
                (<= gen-start gen-limit))
           (fn2-poolp (fn2-pool-init classes gen-start gen-limit fn2-pool))))

(fn2-pool-preserves fn2-pool-reserve (class okind oslot ogen fn2-pool) :position 3 :disable nil)
(fn2-pool-preserves fn2-pool-release (slot gen okind oslot ogen fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-pool-lease-in (slot gen len opslot opgen okind oslot ogen fn2-pool) :position 2 :disable nil)
(fn2-pool-preserves fn2-pool-adapter-write (slot gen opslot opgen idx byte fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-pool-complete-in (slot gen opslot opgen n fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-pool-lease-out (slot gen off len okind oslot ogen fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-pool-release-out (slot gen fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-pool-hand (slot gen okind oslot ogen tkind tslot tgen fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-pool-accept-hand (slot gen tkind tslot tgen fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-pool-write (slot gen idx byte okind oslot ogen fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-pool-reset (slot gen okind oslot ogen fn2-pool) :position 1 :disable nil)

; Guard class, queried from ACL2's world, is an executable-path acceptance gate.
(assert-event
 (fn2-assert-compliant-p
  '(fn2-pool-init fn2-pool-class-for fn2-pool-reserve
    fn2-pool-release fn2-pool-lease-in fn2-pool-adapter-write
    fn2-pool-complete-in fn2-pool-lease-out fn2-pool-release-out
    fn2-pool-hand fn2-pool-accept-hand fn2-pool-read
    fn2-pool-write fn2-pool-reset fn2-pool-slot-state
    fn2-pool-slot-gen fn2-pool-slot-fill fn2-pool-slot-base
    fn2-pool-slot-cap fn2-pool-slot-out-count fn2-pool-lease-range
    fn2-pool-free-count fn2-pool-nslots fn2-pool-capacity-bytes)
  (w state)))

; Logical obligations and executable evidence predicates.  These traversals
; are never on a served path or guards of runtime operations.  Pure scalar
; result predicates share the exact conclusion with evaluated test witnesses.
; The nx wrappers and dispatcher are logical only; no nx function is executed.
(defconst *fn2-pool-handle-operations*
  '(:release :lease-in :adapter-write :complete-in :lease-out :release-out
    :hand :accept-hand :read :write :reset))
(defconst *fn2-pool-operations*
  '(:reserve :release :lease-in :adapter-write :complete-in :lease-out
    :release-out :hand :accept-hand :read :write :reset))

; The arguments are exactly the scalar API arguments, in the API's order.
; The two-element result deliberately retains the complete logical pool.
(defun-nx fn2-pool-operation (op a p)
  (case op
    (:reserve (mv-let (code slot gen after)
                (fn2-pool-reserve (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) p)
                (declare (ignore slot gen)) (list code after)))
    (:release (mv-let (code after)
                (fn2-pool-release (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) p)
                (list code after)))
    (:lease-in (mv-let (code off after)
                 (fn2-pool-lease-in (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                                    (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a) p)
                 (declare (ignore off)) (list code after)))
    (:adapter-write (mv-let (code after)
                      (fn2-pool-adapter-write (nth 0 a) (nth 1 a) (nth 2 a)
                                             (nth 3 a) (nth 4 a) (nth 5 a) p)
                      (list code after)))
    (:complete-in (mv-let (code after)
                    (fn2-pool-complete-in (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) p)
                    (list code after)))
    (:lease-out (mv-let (code after)
                  (fn2-pool-lease-out (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                                     (nth 4 a) (nth 5 a) (nth 6 a) p)
                  (list code after)))
    (:release-out (mv-let (code after)
                    (fn2-pool-release-out (nth 0 a) (nth 1 a) p)
                    (list code after)))
    (:hand (mv-let (code after)
             (fn2-pool-hand (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                            (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a) p)
             (list code after)))
    (:accept-hand (mv-let (code after)
                    (fn2-pool-accept-hand (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) p)
                    (list code after)))
    (:read (mv-let (code byte)
             (fn2-pool-read (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) (nth 5 a) p)
             (declare (ignore byte)) (list code p)))
    (:write (mv-let (code after)
              (fn2-pool-write (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                              (nth 4 a) (nth 5 a) (nth 6 a) p)
              (list code after)))
    (:reset (mv-let (code after)
              (fn2-pool-reset (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a) p)
              (list code after)))
    (otherwise (list :unknown p))))

(defun fn2-pool-logical-slotp (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (and (natp slot) (< slot (fn2-pool-nslots fn2-pool))))

(defun fn2-pool-free-slots (n class fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (let ((i (- n 1)))
      (if (and (equal (fn2-pool-state i fn2-pool) *fn2-pool-state-free*)
               (equal (fn2-pool-class i fn2-pool) class))
          (cons i (fn2-pool-free-slots i class fn2-pool))
        (fn2-pool-free-slots i class fn2-pool)))))

(defun fn2-pool-free-chain (fuel slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (declare (xargs :measure (nfix fuel)))
  (cond ((equal slot *fn2-none*) nil)
        ((or (zp fuel) (not (fn2-pool-logical-slotp slot fn2-pool))) (list :bad-chain))
        (t (cons slot (fn2-pool-free-chain (- fuel 1) (fn2-pool-next-free slot fn2-pool) fn2-pool)))))

(defun fn2-pool-class-accountsp (n fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (declare (xargs :measure (nfix n)))
  (if (zp n) t
    (let* ((class (- n 1))
           (free (fn2-pool-free-slots (fn2-pool-nslots fn2-pool) class fn2-pool))
           (chain (fn2-pool-free-chain (fn2-pool-nslots fn2-pool)
                                      (fn2-pool-class-headsi class fn2-pool) fn2-pool)))
      (and (not (member-equal :bad-chain chain))
           (no-duplicatesp-equal chain)
           (equal (len chain) (fn2-pool-class-countsi class fn2-pool))
           (subsetp-equal chain free) (subsetp-equal free chain)
           (fn2-pool-class-accountsp class fn2-pool)))))

(defun fn2-pool-retired-slots (n fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (declare (xargs :measure (nfix n)))
  (if (zp n) 0
    (+ (if (equal (fn2-pool-state (- n 1) fn2-pool) *fn2-pool-state-retired*) 1 0)
       (fn2-pool-retired-slots (- n 1) fn2-pool))))

(defun fn2-pool-row-invariantp (n fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (declare (xargs :measure (nfix n)))
  (if (zp n) t
    (let* ((i (- n 1)) (phase (fn2-pool-state i fn2-pool))
           (base (fn2-pool-base i fn2-pool)) (cap (fn2-pool-cap i fn2-pool))
           (class (fn2-pool-class i fn2-pool)) (prefix-count (fn2-pool-fill i fn2-pool)))
      (and (member-equal phase
                        (list *fn2-pool-state-free* *fn2-pool-state-workspace*
                              *fn2-pool-state-leased-in* *fn2-pool-state-leased-out*
                              *fn2-pool-state-handed* *fn2-pool-state-retired*))
           (< class (fn2-pool-nclasses fn2-pool))
           (equal cap (fn2-pool-class-sizesi class fn2-pool))
           (equal base (if (zp i) 0
                         (+ (fn2-pool-base (- i 1) fn2-pool) (fn2-pool-cap (- i 1) fn2-pool))))
           (<= (+ base cap) (fn2-pool-capacity-bytes fn2-pool))
           (<= (fn2-pool-gen i fn2-pool) (fn2-pool-gen-limit fn2-pool))
           (<= prefix-count cap)
           (iff (< 0 (fn2-pool-out-count i fn2-pool))
                (equal phase *fn2-pool-state-leased-out*))
           (implies (equal phase *fn2-pool-state-leased-in*)
                    (and (equal prefix-count (fn2-pool-lease-off i fn2-pool))
                         (<= (+ prefix-count (fn2-pool-lease-len i fn2-pool)) cap)))
           (fn2-pool-row-invariantp i fn2-pool)))))

(defun fn2-pool-semanticp (fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
       (fn2-pool-row-invariantp (fn2-pool-nslots fn2-pool) fn2-pool)
       (fn2-pool-class-accountsp (fn2-pool-nclasses fn2-pool) fn2-pool)
       (equal (fn2-pool-retired-count fn2-pool)
              (fn2-pool-retired-slots (fn2-pool-nslots fn2-pool) fn2-pool))
       (equal (fn2-pool-capacity-bytes fn2-pool)
              (if (zp (fn2-pool-nslots fn2-pool)) 0
                (+ (fn2-pool-base (- (fn2-pool-nslots fn2-pool) 1) fn2-pool)
                   (fn2-pool-cap (- (fn2-pool-nslots fn2-pool) 1) fn2-pool))))))

; Evidence interval copier. Runtime pool exports never call this checker.
(defun fn2-pool-logical-octets (n base fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (cons (fn2-pool-datai base fn2-pool)
          (fn2-pool-logical-octets (- n 1) (+ 1 base) fn2-pool))))

(defun fn2-pool-stale-hyps (op a fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (and (fn2-pool-wfp fn2-pool) (member-eq op *fn2-pool-handle-operations*)
       (fn2-pool-logical-slotp (nth 0 a) fn2-pool)
       (not (equal (nth 1 a) (fn2-pool-gen (nth 0 a) fn2-pool)))))
(defun fn2-pool-stale-resultp (code before after)
  (and (eq code :stale) (equal before after)))
(defun-nx fn2-pool-stale-conclusion (op a p)
  (let ((r (fn2-pool-operation op a p)))
    (fn2-pool-stale-resultp (car r) p (cadr r))))

(defthm-owed fn2-pool-stale (op a p)
  (implies (fn2-pool-stale-hyps op a p)
           (fn2-pool-stale-conclusion op a p))
  :schema :invariant :from (:columns fn2-pool)
  :teeth (fn2-pool-stale-teeth)
  :doc "Every handle-taking export refuses a mismatched generation before other decisions and preserves the identical logical pool.")

(defun fn2-pool-byte-fill-hyps (op a fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (let ((slot (nth 0 a)))
    (and (fn2-pool-semanticp fn2-pool)
         (member-eq op '(:complete-in :adapter-write))
         (fn2-pool-logical-slotp slot fn2-pool)
         (equal (nth 1 a) (fn2-pool-gen slot fn2-pool))
         (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-in*)
         (equal (nth 2 a) (fn2-pool-lease-op-slot slot fn2-pool))
         (equal (nth 3 a) (fn2-pool-lease-op-gen slot fn2-pool))
         (if (eq op :complete-in)
             (and (natp (nth 4 a)) (<= (nth 4 a) (fn2-pool-lease-len slot fn2-pool)))
           (not (and (natp (nth 4 a))
                     (<= (fn2-pool-lease-off slot fn2-pool) (nth 4 a))
                     (< (nth 4 a) (+ (fn2-pool-lease-off slot fn2-pool)
                                    (fn2-pool-lease-len slot fn2-pool)))))))))
(defun fn2-pool-byte-fill-resultp
  (op code unchanged after-phase after-fill off n old-prefix new-prefix loan-prefix)
  (if (eq op :complete-in)
      (and (eq code :ok) (equal after-phase *fn2-pool-state-workspace*)
           (equal after-fill (+ off n))
           (equal new-prefix (append old-prefix loan-prefix)))
    (and (eq code :bounds) unchanged)))
(defun-nx fn2-pool-byte-fill-conclusion (op a p)
  (let* ((r (fn2-pool-operation op a p)) (q (cadr r)) (slot (nth 0 a))
         (off (fn2-pool-lease-off slot p)) (n (nth 4 a))
         (base (fn2-pool-base slot p)))
    (fn2-pool-byte-fill-resultp
     op (car r) (equal q p) (fn2-pool-state slot q) (fn2-pool-fill slot q) off n
     (fn2-pool-logical-octets (fn2-pool-fill slot p) base p)
     (fn2-pool-logical-octets (fn2-pool-fill slot q) base q)
     (fn2-pool-logical-octets n (+ base off) p))))

(defthm-owed fn2-pool-byte-fill (op a p)
  (implies (fn2-pool-byte-fill-hyps op a p)
           (fn2-pool-byte-fill-conclusion op a p))
  :schema :invariant :from (:columns fn2-pool)
  :teeth (fn2-pool-byte-teeth)
  :doc "Completion exposes exactly the reported loan prefix after the existing readable prefix; an adapter write outside its loan cannot succeed.")

(defun fn2-pool-no-reuse-hyps (slot op a fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (declare (ignore a))
  (and (fn2-pool-semanticp fn2-pool) (member-eq op *fn2-pool-operations*)
       (fn2-pool-logical-slotp slot fn2-pool) (< 0 (fn2-pool-out-count slot fn2-pool))))
(defun fn2-pool-no-reuse-resultp (old-gen new-gen new-state old-bytes new-bytes)
  (and (equal new-gen old-gen)
       (not (member-equal new-state (list *fn2-pool-state-free* *fn2-pool-state-retired*)))
       (equal old-bytes new-bytes)))
(defun-nx fn2-pool-no-reuse-conclusion (slot op a p)
  (let ((q (cadr (fn2-pool-operation op a p))))
    (fn2-pool-no-reuse-resultp
     (fn2-pool-gen slot p) (fn2-pool-gen slot q) (fn2-pool-state slot q)
     (fn2-pool-logical-octets (fn2-pool-cap slot p) (fn2-pool-base slot p) p)
     (fn2-pool-logical-octets (fn2-pool-cap slot p) (fn2-pool-base slot p) q))))

(defthm-owed fn2-pool-no-reuse (slot op a p)
  (implies (fn2-pool-no-reuse-hyps slot op a p)
           (fn2-pool-no-reuse-conclusion slot op a p))
  :schema :invariant :from (:columns fn2-pool)
  :teeth (fn2-pool-borrow-teeth)
  :doc "Across every pool operation, a borrowed slot cannot become free or retired, change generation, or have any backing byte changed.")

(defun fn2-pool-conservation-hyps (op a fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (declare (ignore a))
  (and (member-eq op *fn2-pool-operations*) (fn2-pool-semanticp fn2-pool)))
(defun-nx fn2-pool-conservation-conclusion (op a p)
  (fn2-pool-semanticp (cadr (fn2-pool-operation op a p))))

(defthm-owed fn2-pool-conservation (op a p)
  (implies (fn2-pool-conservation-hyps op a p)
           (fn2-pool-conservation-conclusion op a p))
  :schema :invariant :from (:columns fn2-pool)
  :teeth (fn2-pool-conservation-teeth)
  :doc "Preserve exactly one of six slot states, disjoint carved extents, loan/borrow consistency, exact acyclic class free lists/counts, and retired count.")

;; An owed row becomes proved by naming the admitted theorem of its exact
;; statement; the fn2-squares table guard refuses a theorem whose formula is
;; not the row's translated statement or its statement function on its vars.
;; (Generic: it belongs in owed.lisp, whose change recertifies every book.)
(defmacro fn2-owed-discharge (name thm)
  `(make-event
    (let ((row (fn2-decl-row '(:square ,name) (w state))))
      (if (not (and row (equal (fn2-decl-get :proof row) '(:owed))))
          (er soft 'fn2-owed-discharge "~x0 is not an owed obligation." ',name)
        (value (list 'table 'fn2-squares '',name
                     (list 'quote (fn2-decl-set :proof '(:proved ,thm) row))))))))

;; ---------------------------------------------------------------------------
;; FN2-POOL-CONSERVATION, proved. The invariant splits into one clause per row
;; (fn2-pool-row-okp, read through its key so frames never open it), one per
;; size class (fn2-pool-class-okp), the retired count and the extent of the
;; last row. Every writer of a row S leaves the other rows' clauses, the free
;; sets, the chains and the counts as frame rules state; each operation then
;; owes its own row's clause and, for :reserve and :release, the one class
;; whose chain and free set move together.
(encapsulate ()
(local
 (progn
  (defconst *fn2-pool-frame-readers*
    '((fn2-pool-gen . fn2-pool-set-gen) (fn2-pool-base) (fn2-pool-cap)
      (fn2-pool-state . fn2-pool-set-state) (fn2-pool-fill . fn2-pool-set-fill)
      (fn2-pool-out-count . fn2-pool-set-out-count) (fn2-pool-lease-off . fn2-pool-set-lease-off)
      (fn2-pool-lease-len . fn2-pool-set-lease-len) (fn2-pool-next-free . fn2-pool-set-next-free)
      (fn2-pool-class)
      (fn2-pool-class-headsi . update-fn2-pool-class-headsi)
      (fn2-pool-class-countsi . update-fn2-pool-class-countsi)
      (fn2-pool-class-sizesi) (fn2-pool-datai . update-fn2-pool-datai)))
  (defconst *fn2-pool-frame-scalars*
    '((fn2-pool-rows) (fn2-pool-nclasses) (fn2-pool-gen-limit)
      (fn2-pool-retired-count . update-fn2-pool-retired-count) (fn2-pool-data-length)))
  (defconst *fn2-pool-frame-writers*
    '(fn2-pool-set-gen fn2-pool-set-state fn2-pool-set-fill fn2-pool-set-out-count
      fn2-pool-set-lease-off fn2-pool-set-lease-len fn2-pool-set-next-free
      fn2-pool-set-owner-kind fn2-pool-set-owner-slot fn2-pool-set-owner-gen
      fn2-pool-set-lease-op-slot fn2-pool-set-lease-op-gen
      fn2-pool-set-hand-to-kind fn2-pool-set-hand-to-slot fn2-pool-set-hand-to-gen
      update-fn2-pool-class-headsi update-fn2-pool-class-countsi update-fn2-pool-datai))
  (deftheory fn2-pool-frame-raw-theory '(fn2-pool-gen$ai update-fn2-pool-gen$ai fn2-pool-base$ai update-fn2-pool-base$ai fn2-pool-cap$ai update-fn2-pool-cap$ai fn2-pool-state$ai update-fn2-pool-state$ai fn2-pool-owner-kind$ai update-fn2-pool-owner-kind$ai fn2-pool-owner-slot$ai update-fn2-pool-owner-slot$ai fn2-pool-owner-gen$ai update-fn2-pool-owner-gen$ai fn2-pool-lease-op-slot$ai update-fn2-pool-lease-op-slot$ai fn2-pool-lease-op-gen$ai update-fn2-pool-lease-op-gen$ai fn2-pool-lease-off$ai update-fn2-pool-lease-off$ai fn2-pool-lease-len$ai update-fn2-pool-lease-len$ai fn2-pool-out-count$ai update-fn2-pool-out-count$ai fn2-pool-fill$ai update-fn2-pool-fill$ai fn2-pool-hand-to-kind$ai update-fn2-pool-hand-to-kind$ai fn2-pool-hand-to-slot$ai update-fn2-pool-hand-to-slot$ai fn2-pool-hand-to-gen$ai update-fn2-pool-hand-to-gen$ai fn2-pool-next-free$ai update-fn2-pool-next-free$ai fn2-pool-class$ai update-fn2-pool-class$ai fn2-pool-class-headsi update-fn2-pool-class-headsi fn2-pool-class-countsi update-fn2-pool-class-countsi fn2-pool-class-sizesi fn2-pool-datai update-fn2-pool-datai fn2-pool-data-length fn2-pool-rows fn2-pool-nclasses fn2-pool-gen-limit fn2-pool-retired-count update-fn2-pool-retired-count))
  (defun fn2-pool-frame-name (r w)
    (declare (xargs :guard (and (symbolp r) (symbolp w))))
    (intern-in-package-of-symbol
     (concatenate 'string (symbol-name r) "-OF-" (symbol-name w)) 'fn2-pool))
  (defun fn2-pool-frame-row-events (r same writers)
    (declare (xargs :guard (and (symbolp r) (symbol-listp writers))))
    (if (atom writers) nil
      (let ((w (car writers)))
        (cons `(defthm ,(fn2-pool-frame-name r w)
                 ,(if (eq w same)
                      `(implies (and (natp i) (natp j))
                                (equal (,r i (,w j v fn2-pool))
                                       (if (equal i j) v (,r i fn2-pool))))
                    `(equal (,r i (,w j v fn2-pool)) (,r i fn2-pool)))
                 :hints (("Goal" :in-theory (union-theories (theory (quote fn2-pool-frame-raw-theory)) (union-theories (quote (,r ,w nth-update-nth len-update-nth update-nth-array nfix natp max (:type-prescription len) (:e nfix) (:e natp) (:e equal) (:e <))) (theory (quote minimal-theory)))))))
              (fn2-pool-frame-row-events r same (cdr writers))))))
  (defun fn2-pool-frame-scalar-events (r writers)
    (declare (xargs :guard (and (symbolp r) (symbol-listp writers))))
    (if (atom writers) nil
      (let ((w (car writers)))
        (cons `(defthm ,(fn2-pool-frame-name r w)
                 ,(if (and (eq r 'fn2-pool-data-length) (eq w 'update-fn2-pool-datai))
                      `(implies (and (natp j) (< j (fn2-pool-data-length fn2-pool)))
                                (equal (,r (,w j v fn2-pool)) (,r fn2-pool)))
                    `(equal (,r (,w j v fn2-pool)) (,r fn2-pool)))
                 :hints (("Goal" :in-theory (union-theories (theory (quote fn2-pool-frame-raw-theory)) (union-theories (quote (,r ,w nth-update-nth len-update-nth update-nth-array nfix natp max (:type-prescription len) (:e nfix) (:e natp) (:e equal) (:e <))) (theory (quote minimal-theory)))))))
              (fn2-pool-frame-scalar-events r (cdr writers))))))
  (defun fn2-pool-frame-rows-events (readers writers)
    (declare (xargs :guard (and (symbol-alistp readers) (symbol-listp writers))))
    (if (atom readers) nil
      (append (fn2-pool-frame-row-events (caar readers) (cdar readers) writers)
              (fn2-pool-frame-rows-events (cdr readers) writers))))
  (defun fn2-pool-frame-scalars-events (scalars writers)
    (declare (xargs :guard (and (symbol-alistp scalars) (symbol-listp writers))))
    (if (atom scalars) nil
      (append (fn2-pool-frame-scalar-events (caar scalars) writers)
              (fn2-pool-frame-scalars-events (cdr scalars) writers))))
  (defun fn2-pool-frame-events (readers scalars writers)
    (declare (xargs :guard (and (symbol-alistp readers) (symbol-alistp scalars) (symbol-listp writers))))
    (append (fn2-pool-frame-rows-events readers writers)
            (fn2-pool-frame-scalars-events scalars writers)))
  (make-event (cons 'progn (fn2-pool-frame-events *fn2-pool-frame-readers* *fn2-pool-frame-scalars*
                                                  *fn2-pool-frame-writers*)))
  (defthm fn2-pool-retired-count-of-update-fn2-pool-retired-count
    (equal (fn2-pool-retired-count (update-fn2-pool-retired-count v fn2-pool)) v))
  ;; the scalar writer
  (defun fn2-pool-frame-retired-events (readers rowp)
    (declare (xargs :guard (symbol-alistp readers)))
    (if (atom readers) nil
      (let ((r (caar readers)) (w 'update-fn2-pool-retired-count))
        (if (eq r 'fn2-pool-retired-count)
            (fn2-pool-frame-retired-events (cdr readers) rowp)
          (cons `(defthm ,(fn2-pool-frame-name r w)
                   ,(if rowp `(equal (,r i (,w v fn2-pool)) (,r i fn2-pool))
                      `(equal (,r (,w v fn2-pool)) (,r fn2-pool)))
                   :hints (("Goal" :in-theory (union-theories (theory (quote fn2-pool-frame-raw-theory)) (union-theories (quote (,r ,w nth-update-nth len-update-nth update-nth-array nfix natp max (:type-prescription len) (:e nfix) (:e natp) (:e equal) (:e <))) (theory (quote minimal-theory)))))))
                (fn2-pool-frame-retired-events (cdr readers) rowp))))))
  (make-event (cons 'progn (append (fn2-pool-frame-retired-events *fn2-pool-frame-readers* t)
                                   (fn2-pool-frame-retired-events *fn2-pool-frame-scalars* nil))))

  (in-theory (disable fn2-pool-gen fn2-pool-base fn2-pool-cap fn2-pool-state fn2-pool-fill
                      fn2-pool-out-count fn2-pool-lease-off fn2-pool-lease-len fn2-pool-next-free
                      fn2-pool-class fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen
                      fn2-pool-lease-op-slot fn2-pool-lease-op-gen fn2-pool-hand-to-kind
                      fn2-pool-hand-to-slot fn2-pool-hand-to-gen))
  (in-theory (set-difference-theories (current-theory :here) (theory 'fn2-pool-frame-raw-theory)))

  ;; Row invariant: one row's clause, and all rows but one.
  (defun fn2-pool-row-okp (i fn2-pool)
    (declare (xargs :stobjs fn2-pool :verify-guards nil))
    (let* ((phase (fn2-pool-state i fn2-pool))
           (base (fn2-pool-base i fn2-pool)) (cap (fn2-pool-cap i fn2-pool))
           (class (fn2-pool-class i fn2-pool)) (prefix-count (fn2-pool-fill i fn2-pool)))
      (and (member-equal phase
                         (list *fn2-pool-state-free* *fn2-pool-state-workspace*
                               *fn2-pool-state-leased-in* *fn2-pool-state-leased-out*
                               *fn2-pool-state-handed* *fn2-pool-state-retired*))
           (< class (fn2-pool-nclasses fn2-pool))
           (equal cap (fn2-pool-class-sizesi class fn2-pool))
           (equal base (if (zp i) 0
                         (+ (fn2-pool-base (- i 1) fn2-pool) (fn2-pool-cap (- i 1) fn2-pool))))
           (<= (+ base cap) (fn2-pool-capacity-bytes fn2-pool))
           (<= (fn2-pool-gen i fn2-pool) (fn2-pool-gen-limit fn2-pool))
           (<= prefix-count cap)
           (iff (< 0 (fn2-pool-out-count i fn2-pool))
                (equal phase *fn2-pool-state-leased-out*))
           (implies (equal phase *fn2-pool-state-leased-in*)
                    (and (equal prefix-count (fn2-pool-lease-off i fn2-pool))
                         (<= (+ prefix-count (fn2-pool-lease-len i fn2-pool)) cap))))))
  (defthm fn2-pool-row-invariantp-step
    (equal (fn2-pool-row-invariantp n fn2-pool)
           (if (zp n) t
             (and (fn2-pool-row-okp (- n 1) fn2-pool)
                  (fn2-pool-row-invariantp (- n 1) fn2-pool))))
    :rule-classes ((:definition :controller-alist ((fn2-pool-row-invariantp t nil))))
    :hints (("Goal" :in-theory (enable fn2-pool-row-invariantp fn2-pool-row-okp))))
  (in-theory (disable fn2-pool-row-invariantp fn2-pool-row-okp fn2-pool-row-invariantp-step))

  (defun fn2-pool-rows-ok-except (n s fn2-pool)
    (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix n)))
    (if (zp n) t
      (and (or (equal (- n 1) s) (fn2-pool-row-okp (- n 1) fn2-pool))
           (fn2-pool-rows-ok-except (- n 1) s fn2-pool))))
  (defthm fn2-pool-rows-ok-except-of-invariant
    (implies (fn2-pool-row-invariantp n fn2-pool)
             (fn2-pool-rows-ok-except n s fn2-pool))
    :hints (("Goal" :induct (fn2-pool-rows-ok-except n s fn2-pool) :in-theory (enable fn2-pool-row-invariantp-step))))
  (defthm fn2-pool-invariant-of-rows-ok-except
    (implies (and (fn2-pool-rows-ok-except n s fn2-pool)
                  (implies (and (natp s) (< s n)) (fn2-pool-row-okp s fn2-pool)))
             (fn2-pool-row-invariantp n fn2-pool))
    :hints (("Goal" :induct (fn2-pool-rows-ok-except n s fn2-pool) :in-theory (enable fn2-pool-row-invariantp-step))))
  (defthm fn2-pool-row-okp-of-invariant
    (implies (and (fn2-pool-row-invariantp n fn2-pool) (natp n) (natp i) (< i n))
             (fn2-pool-row-okp i fn2-pool))
    :hints (("Goal" :induct (fn2-pool-rows-ok-except n i fn2-pool) :in-theory (enable fn2-pool-row-invariantp-step))))


  ;; A row's clause reads only its key: the frame lemmas never open the clause.
  (defun fn2-pool-row-key (i fn2-pool)
    (declare (xargs :stobjs fn2-pool :verify-guards nil))
    (list (fn2-pool-state i fn2-pool) (fn2-pool-base i fn2-pool) (fn2-pool-cap i fn2-pool)
          (fn2-pool-class i fn2-pool) (fn2-pool-fill i fn2-pool) (fn2-pool-gen i fn2-pool)
          (fn2-pool-out-count i fn2-pool) (fn2-pool-lease-off i fn2-pool) (fn2-pool-lease-len i fn2-pool)
          (zp i) (fn2-pool-base (- i 1) fn2-pool) (fn2-pool-cap (- i 1) fn2-pool)
          (fn2-pool-nclasses fn2-pool) (fn2-pool-class-sizesi (fn2-pool-class i fn2-pool) fn2-pool)
          (fn2-pool-data-length fn2-pool) (fn2-pool-gen-limit fn2-pool)))
  (defun fn2-pool-row-key-okp (k)
    (declare (xargs :verify-guards nil))
    (let ((phase (nth 0 k)) (base (nth 1 k)) (cap (nth 2 k)) (class (nth 3 k))
          (prefix-count (nth 4 k)))
      (and (member-equal phase (list *fn2-pool-state-free* *fn2-pool-state-workspace*
                                     *fn2-pool-state-leased-in* *fn2-pool-state-leased-out*
                                     *fn2-pool-state-handed* *fn2-pool-state-retired*))
           (< class (nth 12 k)) (equal cap (nth 13 k))
           (equal base (if (nth 9 k) 0 (+ (nth 10 k) (nth 11 k))))
           (<= (+ base cap) (nth 14 k)) (<= (nth 5 k) (nth 15 k)) (<= prefix-count cap)
           (iff (< 0 (nth 6 k)) (equal phase *fn2-pool-state-leased-out*))
           (implies (equal phase *fn2-pool-state-leased-in*)
                    (and (equal prefix-count (nth 7 k)) (<= (+ prefix-count (nth 8 k)) cap))))))
  (defthm fn2-pool-row-okp-by-key
    (equal (fn2-pool-row-okp i fn2-pool) (fn2-pool-row-key-okp (fn2-pool-row-key i fn2-pool)))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable fn2-pool-row-okp))))
  (in-theory (disable fn2-pool-row-key-okp))
  (defun fn2-pool-key-frame-events (writers)
    (declare (xargs :guard (symbol-listp writers)))
    (if (atom writers) nil
      (let ((w (car writers)))
        (cons `(defthm ,(fn2-pool-frame-name 'fn2-pool-row-okp w)
                 ,(cond ((eq w 'update-fn2-pool-datai)
                         `(implies (and (natp j) (< j (fn2-pool-data-length fn2-pool)))
                                   (equal (fn2-pool-row-okp i (,w j v fn2-pool))
                                          (fn2-pool-row-okp i fn2-pool))))
                        ((member-eq w '(update-fn2-pool-class-headsi update-fn2-pool-class-countsi))
                         `(equal (fn2-pool-row-okp i (,w j v fn2-pool)) (fn2-pool-row-okp i fn2-pool)))
                        (t `(implies (and (natp i) (natp j) (not (equal i j)))
                                     (equal (fn2-pool-row-okp i (,w j v fn2-pool))
                                            (fn2-pool-row-okp i fn2-pool)))))
                 :hints (("Goal" :in-theory (disable fn2-pool-row-okp)
                          :use ((:instance fn2-pool-row-okp-by-key)
                                (:instance fn2-pool-row-okp-by-key (fn2-pool (,w j v fn2-pool)))))))
              (fn2-pool-key-frame-events (cdr writers))))))
  (make-event (cons 'progn (fn2-pool-key-frame-events *fn2-pool-frame-writers*)))
  (defthm fn2-pool-row-okp-of-update-fn2-pool-retired-count
    (equal (fn2-pool-row-okp i (update-fn2-pool-retired-count v fn2-pool)) (fn2-pool-row-okp i fn2-pool))
    :hints (("Goal" :use ((:instance fn2-pool-row-okp-by-key)
                          (:instance fn2-pool-row-okp-by-key (fn2-pool (update-fn2-pool-retired-count v fn2-pool)))))))
  ;; Every writer at row S leaves the other rows' clauses alone.
  (defun fn2-pool-except-frame-events (writers)
    (declare (xargs :guard (symbol-listp writers)))
    (if (atom writers) nil
      (let ((w (car writers)))
        (cons `(defthm ,(fn2-pool-frame-name 'fn2-pool-rows-ok-except w)
                 ,(if (eq w 'update-fn2-pool-datai)
                      `(implies (and (natp j) (< j (fn2-pool-data-length fn2-pool)))
                                (equal (fn2-pool-rows-ok-except n s (,w j v fn2-pool))
                                       (fn2-pool-rows-ok-except n s fn2-pool)))
                    (if (member-eq w '(update-fn2-pool-class-headsi update-fn2-pool-class-countsi))
                        `(equal (fn2-pool-rows-ok-except n s (,w j v fn2-pool))
                                (fn2-pool-rows-ok-except n s fn2-pool))
                      `(implies (natp s)
                                (equal (fn2-pool-rows-ok-except n s (,w s v fn2-pool))
                                       (fn2-pool-rows-ok-except n s fn2-pool)))))
                 :hints (("Goal" :induct (fn2-pool-rows-ok-except n s fn2-pool))))
              (fn2-pool-except-frame-events (cdr writers))))))
  (make-event (cons 'progn (fn2-pool-except-frame-events *fn2-pool-frame-writers*)))
  (defthm fn2-pool-rows-ok-except-of-update-fn2-pool-retired-count
    (equal (fn2-pool-rows-ok-except n s (update-fn2-pool-retired-count v fn2-pool))
           (fn2-pool-rows-ok-except n s fn2-pool))
    :hints (("Goal" :induct (fn2-pool-rows-ok-except n s fn2-pool))))

  ;; Lists.
  (defthm fn2-pool-subsetp-trans
    (implies (and (subsetp-equal x y) (subsetp-equal y z)) (subsetp-equal x z)))
  (defthm fn2-pool-subsetp-cons-right
    (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))
  (defthm fn2-pool-subsetp-refl (subsetp-equal x x))
  (defthm fn2-pool-subsetp-remove
    (implies (and (subsetp-equal x y) (not (member-equal a x)))
             (subsetp-equal x (remove-equal a y))))
  (defthm fn2-pool-remove-subsetp
    (implies (subsetp-equal y (cons a x)) (subsetp-equal (remove-equal a y) x)))
  (defthm fn2-pool-not-member-of-subsetp
    (implies (and (subsetp-equal x y) (not (member-equal a y))) (not (member-equal a x))))
  (defthm fn2-pool-remove-equal-non-member
    (implies (and (true-listp l) (not (member-equal a l))) (equal (remove-equal a l) l)))

  ;; Free slots of a class: membership, and the writers.
  (defthm fn2-pool-member-free-slots
    (iff (member-equal x (fn2-pool-free-slots n c fn2-pool))
         (and (natp x) (< x (nfix n)) (equal (fn2-pool-state x fn2-pool) *fn2-pool-state-free*)
              (equal (fn2-pool-class x fn2-pool) c))))
  (defun fn2-pool-free-slots-frame-events (writers)
    (declare (xargs :guard (symbol-listp writers)))
    (if (atom writers) nil
      (let ((w (car writers)))
        (if (eq w 'fn2-pool-set-state) (fn2-pool-free-slots-frame-events (cdr writers))
          (cons `(defthm ,(fn2-pool-frame-name 'fn2-pool-free-slots w)
                   (equal (fn2-pool-free-slots n c (,w j v fn2-pool)) (fn2-pool-free-slots n c fn2-pool)))
                (fn2-pool-free-slots-frame-events (cdr writers)))))))
  (make-event (cons 'progn (fn2-pool-free-slots-frame-events *fn2-pool-frame-writers*)))
  (defthm fn2-pool-free-slots-of-update-fn2-pool-retired-count
    (equal (fn2-pool-free-slots n c (update-fn2-pool-retired-count v fn2-pool))
           (fn2-pool-free-slots n c fn2-pool)))
  (defthm fn2-pool-free-slots-of-set-state-busy
    (implies (and (natp s) (not (equal v *fn2-pool-state-free*)))
             (equal (fn2-pool-free-slots n c (fn2-pool-set-state s v fn2-pool))
                    (remove-equal s (fn2-pool-free-slots n c fn2-pool)))))
  (defthm fn2-pool-free-slots-of-set-state-free-subset
    (implies (natp s)
             (subsetp-equal (fn2-pool-free-slots n c (fn2-pool-set-state s v fn2-pool))
                            (cons s (fn2-pool-free-slots n c fn2-pool)))))
  (defthm fn2-pool-subsetp-free-slots-of-set-state-free
    (implies (and (subsetp-equal x (fn2-pool-free-slots n c fn2-pool)) (natp s))
             (subsetp-equal x (fn2-pool-free-slots n c (fn2-pool-set-state s *fn2-pool-state-free* fn2-pool))))
    :hints (("Goal" :induct (len x))))

  ;; Retired count.
  (defun fn2-pool-retired-frame-events (writers)
    (declare (xargs :guard (symbol-listp writers)))
    (if (atom writers) nil
      (let ((w (car writers)))
        (if (eq w 'fn2-pool-set-state) (fn2-pool-retired-frame-events (cdr writers))
          (cons `(defthm ,(fn2-pool-frame-name 'fn2-pool-retired-slots w)
                   (equal (fn2-pool-retired-slots n (,w j v fn2-pool)) (fn2-pool-retired-slots n fn2-pool)))
                (fn2-pool-retired-frame-events (cdr writers)))))))
  (make-event (cons 'progn (fn2-pool-retired-frame-events *fn2-pool-frame-writers*)))
  (defthm fn2-pool-retired-slots-of-update-fn2-pool-retired-count
    (equal (fn2-pool-retired-slots n (update-fn2-pool-retired-count v fn2-pool))
           (fn2-pool-retired-slots n fn2-pool)))
  (defthm fn2-pool-retired-slots-of-set-state
    (implies (natp s)
             (equal (fn2-pool-retired-slots n (fn2-pool-set-state s v fn2-pool))
                    (if (< s (nfix n))
                        (+ (fn2-pool-retired-slots n fn2-pool)
                           (if (equal v *fn2-pool-state-retired*) 1 0)
                           (- (if (equal (fn2-pool-state s fn2-pool) *fn2-pool-state-retired*) 1 0)))
                      (fn2-pool-retired-slots n fn2-pool)))))

  ;; Free chains.
  (defun fn2-pool-chain-frame-events (writers)
    (declare (xargs :guard (symbol-listp writers)))
    (if (atom writers) nil
      (let ((w (car writers)))
        (if (eq w 'fn2-pool-set-next-free) (fn2-pool-chain-frame-events (cdr writers))
          (cons `(defthm ,(fn2-pool-frame-name 'fn2-pool-free-chain w)
                   (equal (fn2-pool-free-chain f x (,w j v fn2-pool)) (fn2-pool-free-chain f x fn2-pool)))
                (fn2-pool-chain-frame-events (cdr writers)))))))
  (make-event (cons 'progn (fn2-pool-chain-frame-events *fn2-pool-frame-writers*)))
  (defthm fn2-pool-free-chain-of-update-fn2-pool-retired-count
    (equal (fn2-pool-free-chain f x (update-fn2-pool-retired-count v fn2-pool))
           (fn2-pool-free-chain f x fn2-pool)))
  (defthm fn2-pool-free-chain-of-set-next-free
    (implies (and (natp s) (not (member-equal s (fn2-pool-free-chain f x fn2-pool))))
             (equal (fn2-pool-free-chain f x (fn2-pool-set-next-free s v fn2-pool))
                    (fn2-pool-free-chain f x fn2-pool))))
  (defthm fn2-pool-free-chain-consp
    (implies (not (equal x *fn2-none*)) (consp (fn2-pool-free-chain f x fn2-pool))))
  (defthm fn2-pool-free-chain-len-pos
    (implies (not (equal x *fn2-none*)) (< 0 (len (fn2-pool-free-chain f x fn2-pool))))
    :rule-classes :linear)
  (defun fn2-pool-chain-fuel-ind (f g x fn2-pool)
    (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix f)))
    (cond ((equal x *fn2-none*) nil)
          ((or (zp f) (zp g) (not (fn2-pool-logical-slotp x fn2-pool))) nil)
          (t (fn2-pool-chain-fuel-ind (- f 1) (- g 1) (fn2-pool-next-free x fn2-pool) fn2-pool))))
  (defthm fn2-pool-free-chain-fuel
    (implies (and (not (member-equal :bad-chain (fn2-pool-free-chain f x fn2-pool)))
                  (natp g) (<= (len (fn2-pool-free-chain f x fn2-pool)) g))
             (equal (fn2-pool-free-chain g x fn2-pool) (fn2-pool-free-chain f x fn2-pool)))
    :rule-classes nil
    :hints (("Goal" :induct (fn2-pool-chain-fuel-ind f g x fn2-pool))))
  (defthm fn2-pool-free-chain-open
    (implies (and (fn2-pool-logical-slotp x fn2-pool) (not (zp f)) (not (equal x *fn2-none*)))
             (equal (fn2-pool-free-chain f x fn2-pool)
                    (cons x (fn2-pool-free-chain (- f 1) (fn2-pool-next-free x fn2-pool) fn2-pool))))
    :rule-classes nil)

  ;; Class accounts: one class's clause.
  (defun fn2-pool-class-okp (class fn2-pool)
    (declare (xargs :stobjs fn2-pool :verify-guards nil))
    (let* ((free (fn2-pool-free-slots (fn2-pool-nslots fn2-pool) class fn2-pool))
           (chain (fn2-pool-free-chain (fn2-pool-nslots fn2-pool)
                                      (fn2-pool-class-headsi class fn2-pool) fn2-pool)))
      (and (not (member-equal :bad-chain chain))
           (no-duplicatesp-equal chain)
           (equal (len chain) (fn2-pool-class-countsi class fn2-pool))
           (subsetp-equal chain free) (subsetp-equal free chain))))
  (defthm fn2-pool-class-accountsp-step
    (equal (fn2-pool-class-accountsp n fn2-pool)
           (if (zp n) t
             (and (fn2-pool-class-okp (- n 1) fn2-pool)
                  (fn2-pool-class-accountsp (- n 1) fn2-pool))))
    :rule-classes ((:definition :controller-alist ((fn2-pool-class-accountsp t nil))))
    :hints (("Goal" :in-theory (enable fn2-pool-class-accountsp fn2-pool-class-okp))))
  (in-theory (disable (:definition fn2-pool-class-accountsp) fn2-pool-class-accountsp-step))
  (defthm fn2-pool-class-okp-of-accounts
    (implies (and (fn2-pool-class-accountsp n fn2-pool) (natp n) (natp c) (< c n))
             (fn2-pool-class-okp c fn2-pool))
    :hints (("Goal" :induct (fn2-pool-class-accountsp n fn2-pool) :in-theory (enable fn2-pool-class-accountsp-step))))
  (defun fn2-pool-accounts-frame-events (writers)
    (declare (xargs :guard (symbol-listp writers)))
    (if (atom writers) nil
      (let ((w (car writers)))
        (if (member-eq w '(fn2-pool-set-state fn2-pool-set-next-free
                           update-fn2-pool-class-headsi update-fn2-pool-class-countsi))
            (fn2-pool-accounts-frame-events (cdr writers))
          (cons `(defthm ,(fn2-pool-frame-name 'fn2-pool-class-accountsp w)
                   (equal (fn2-pool-class-accountsp n (,w j v fn2-pool)) (fn2-pool-class-accountsp n fn2-pool))
                   :hints (("Goal" :induct (fn2-pool-class-accountsp n fn2-pool)
                            :in-theory (enable fn2-pool-class-okp fn2-pool-class-accountsp-step))))
                (fn2-pool-accounts-frame-events (cdr writers)))))))
  (make-event (cons 'progn (fn2-pool-accounts-frame-events *fn2-pool-frame-writers*)))
  (defthm fn2-pool-class-accountsp-of-update-fn2-pool-retired-count
    (equal (fn2-pool-class-accountsp n (update-fn2-pool-retired-count v fn2-pool))
           (fn2-pool-class-accountsp n fn2-pool))
    :hints (("Goal" :induct (fn2-pool-class-accountsp n fn2-pool)
             :in-theory (enable fn2-pool-class-okp fn2-pool-class-accountsp-step))))
  ; A busy row stays busy: no class's free slots move.
  (defthm fn2-pool-class-accountsp-of-set-state-busy
    (implies (and (natp s) (not (equal v *fn2-pool-state-free*))
                  (not (equal (fn2-pool-state s fn2-pool) *fn2-pool-state-free*)))
             (equal (fn2-pool-class-accountsp n (fn2-pool-set-state s v fn2-pool))
                    (fn2-pool-class-accountsp n fn2-pool)))
    :hints (("Goal" :induct (fn2-pool-class-accountsp n fn2-pool)
             :in-theory (enable fn2-pool-class-okp fn2-pool-class-accountsp-step))))

  (defthm fn2-pool-semanticp-intro
    (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                  (fn2-pool-rows-ok-except (fn2-pool-rows fn2-pool) s fn2-pool)
                  (implies (and (natp s) (< s (fn2-pool-rows fn2-pool))) (fn2-pool-row-okp s fn2-pool))
                  (fn2-pool-class-accountsp (fn2-pool-nclasses fn2-pool) fn2-pool)
                  (equal (fn2-pool-retired-count fn2-pool)
                         (fn2-pool-retired-slots (fn2-pool-rows fn2-pool) fn2-pool))
                  (equal (fn2-pool-data-length fn2-pool)
                         (if (zp (fn2-pool-rows fn2-pool)) 0
                           (+ (fn2-pool-base (- (fn2-pool-rows fn2-pool) 1) fn2-pool)
                              (fn2-pool-cap (- (fn2-pool-rows fn2-pool) 1) fn2-pool)))))
             (fn2-pool-semanticp fn2-pool))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable fn2-pool-semanticp)
             :use ((:instance fn2-pool-invariant-of-rows-ok-except (n (fn2-pool-rows fn2-pool)))))))
  (defthm fn2-pool-slot-types
    (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (natp i) (< i (fn2-pool-rows fn2-pool)))
             (and (natp (fn2-pool-cap i fn2-pool)) (natp (fn2-pool-fill i fn2-pool))
                  (natp (fn2-pool-base i fn2-pool)) (natp (fn2-pool-out-count i fn2-pool))
                  (natp (fn2-pool-lease-off i fn2-pool)) (natp (fn2-pool-lease-len i fn2-pool))
                  (natp (fn2-pool-gen i fn2-pool)) (natp (fn2-pool-state i fn2-pool))
                  (natp (fn2-pool-class i fn2-pool)) (natp (fn2-pool-next-free i fn2-pool))
                  (< (fn2-pool-out-count i fn2-pool) 4294967296)
                  (< (fn2-pool-gen i fn2-pool) 1152921504606846976)))
    :rule-classes nil)
  (defthm fn2-pool-semanticp-elim
    (implies (fn2-pool-semanticp fn2-pool)
             (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                  (fn2-pool-row-invariantp (fn2-pool-rows fn2-pool) fn2-pool)
                  (fn2-pool-class-accountsp (fn2-pool-nclasses fn2-pool) fn2-pool)
                  (equal (fn2-pool-retired-count fn2-pool)
                         (fn2-pool-retired-slots (fn2-pool-rows fn2-pool) fn2-pool))
                  (equal (fn2-pool-data-length fn2-pool)
                         (if (zp (fn2-pool-rows fn2-pool)) 0
                           (+ (fn2-pool-base (- (fn2-pool-rows fn2-pool) 1) fn2-pool)
                              (fn2-pool-cap (- (fn2-pool-rows fn2-pool) 1) fn2-pool))))))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable fn2-pool-semanticp))))
  (in-theory (disable fn2-pool-semanticp))


  (defthm fn2-pool-nclasses-type
    (implies (fn2-poolp fn2-pool) (natp (fn2-pool-nclasses fn2-pool)))
    :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fn2-pool-nclasses))))
  (defthm fn2-pool-nclasses-at-most-16
    (implies (fn2-poolp fn2-pool) (<= (fn2-pool-nclasses fn2-pool) 16))
    :rule-classes :linear :hints (("Goal" :in-theory (enable fn2-pool-nclasses))))
  (defthm fn2-pool-class-headsi-type
    (implies (and (fn2-poolp fn2-pool) (natp c) (< c 16)) (natp (fn2-pool-class-headsi c fn2-pool)))
    :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fn2-pool-class-headsi))))
  (defthm fn2-pool-class-countsi-type
    (implies (and (fn2-poolp fn2-pool) (natp c) (< c 16)) (natp (fn2-pool-class-countsi c fn2-pool)))
    :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fn2-pool-class-countsi))))
  (defthm fn2-pool-free-slots-of-set-state-other-class
    (implies (and (natp s) (not (equal (fn2-pool-class s fn2-pool) c)))
             (equal (fn2-pool-free-slots n c (fn2-pool-set-state s v fn2-pool))
                    (fn2-pool-free-slots n c fn2-pool))))
  (defthm fn2-pool-true-listp-free-slots (true-listp (fn2-pool-free-slots n c fn2-pool))
    :rule-classes :type-prescription)
  (in-theory (disable fn2-pool-free-slots fn2-pool-free-chain fn2-pool-retired-slots))
  ;; Chain shapes at a head.
  (defthm fn2-pool-free-chain-car
    (implies (and (not (equal x *fn2-none*))
                  (not (member-equal :bad-chain (fn2-pool-free-chain f x fn2-pool))))
             (equal (car (fn2-pool-free-chain f x fn2-pool)) x))
    :hints (("Goal" :in-theory (enable fn2-pool-free-chain))))
  (defthm fn2-pool-free-chain-len-bound
    (implies (and (natp f) (not (member-equal :bad-chain (fn2-pool-free-chain f x fn2-pool))))
             (<= (len (fn2-pool-free-chain f x fn2-pool)) f))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable fn2-pool-free-chain))))
  (defthm fn2-pool-free-chain-tail
    (implies (and (natp n) (not (equal s *fn2-none*))
                  (not (member-equal :bad-chain (fn2-pool-free-chain n s fn2-pool))))
             (equal (fn2-pool-free-chain n (fn2-pool-next-free s fn2-pool) fn2-pool)
                    (cdr (fn2-pool-free-chain n s fn2-pool))))
    :hints (("Goal" :expand ((fn2-pool-free-chain n s fn2-pool))
             :use ((:instance fn2-pool-free-chain-len-bound (f (- n 1)) (x (fn2-pool-next-free s fn2-pool)))
                   (:instance fn2-pool-free-chain-fuel (f (- n 1)) (g n) (x (fn2-pool-next-free s fn2-pool)))))))
  (defthm fn2-pool-free-chain-fuel-down
    (implies (and (natp n) (not (member-equal :bad-chain (fn2-pool-free-chain n x fn2-pool)))
                  (< (len (fn2-pool-free-chain n x fn2-pool)) n))
             (equal (fn2-pool-free-chain (+ -1 n) x fn2-pool) (fn2-pool-free-chain n x fn2-pool)))
    :hints (("Goal" :use ((:instance fn2-pool-free-chain-fuel (f n) (g (- n 1)))))))
  (defthm fn2-pool-free-chain-push
    (implies (and (natp s) (fn2-pool-logical-slotp s fn2-pool) (not (zp n)) (not (equal s *fn2-none*))
                  (not (member-equal s (fn2-pool-free-chain (+ -1 n) h fn2-pool))))
             (equal (fn2-pool-free-chain n s (fn2-pool-set-next-free s h fn2-pool))
                    (cons s (fn2-pool-free-chain (+ -1 n) h fn2-pool))))
    :hints (("Goal" :use ((:instance fn2-pool-free-chain-open (x s) (f n)
                                     (fn2-pool (fn2-pool-set-next-free s h fn2-pool))))
             :in-theory (enable fn2-pool-logical-slotp))))
  (defthm fn2-pool-no-dup-cdr
    (implies (no-duplicatesp-equal l) (no-duplicatesp-equal (cdr l))))
  (defthm fn2-pool-not-member-cdr
    (implies (not (member-equal a l)) (not (member-equal a (cdr l)))))
  (defthm fn2-pool-len-cdr
    (implies (consp l) (equal (len (cdr l)) (- (len l) 1))))
  (defthm fn2-pool-subsetp-cdr-remove
    (implies (and (consp l) (subsetp-equal l f) (no-duplicatesp-equal l))
             (subsetp-equal (cdr l) (remove-equal (car l) f))))
  (defthm fn2-pool-remove-subsetp-cdr
    (implies (and (consp l) (subsetp-equal f l))
             (subsetp-equal (remove-equal (car l) f) (cdr l)))
    :hints (("Goal" :use ((:instance fn2-pool-remove-subsetp (y f) (a (car l)) (x (cdr l)))))))
  ; RESERVE: the head leaves its class's chain and free set together.
  (defthm fn2-pool-reserve-class-okp
    (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                  (fn2-pool-class-accountsp (fn2-pool-nclasses fn2-pool) fn2-pool)
                  (natp c2) (< c2 (fn2-pool-nclasses fn2-pool)))
             (fn2-pool-class-okp c2 (mv-nth 3 (fn2-pool-reserve class okind oslot ogen fn2-pool))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
             :in-theory (e/d (fn2-pool-class-okp) (fn2-pool-class-okp-of-accounts))
             :use (                 (:instance fn2-pool-class-okp-of-accounts (n (fn2-pool-nclasses fn2-pool)) (c c2))
                   (:instance fn2-pool-class-okp-of-accounts (n (fn2-pool-nclasses fn2-pool)) (c class))
                   (:instance fn2-pool-free-chain-open (f (fn2-pool-rows fn2-pool))
                              (x (fn2-pool-class-headsi class fn2-pool)))
                   (:instance fn2-pool-free-chain-fuel (f (- (fn2-pool-rows fn2-pool) 1))
                              (g (fn2-pool-rows fn2-pool))
                              (x (fn2-pool-next-free (fn2-pool-class-headsi class fn2-pool) fn2-pool)))))))

  (defthm fn2-pool-reserve-class-accounts
    (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                  (fn2-pool-class-accountsp (fn2-pool-nclasses fn2-pool) fn2-pool)
                  (natp k) (<= k (fn2-pool-nclasses fn2-pool)))
             (fn2-pool-class-accountsp k (mv-nth 3 (fn2-pool-reserve class okind oslot ogen fn2-pool))))
    :hints (("Goal" :induct (fn2-pool-retired-slots k fn2-pool)
             :in-theory (e/d (fn2-pool-class-accountsp-step fn2-pool-retired-slots) (fn2-pool-reserve)))))
  (defthm fn2-pool-reserve-row-okp
    (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                  (fn2-pool-row-invariantp (fn2-pool-rows fn2-pool) fn2-pool)
                  (natp (fn2-pool-class-headsi class fn2-pool))
                  (< (fn2-pool-class-headsi class fn2-pool) (fn2-pool-rows fn2-pool)))
             (fn2-pool-row-okp (fn2-pool-class-headsi class fn2-pool)
                               (mv-nth 3 (fn2-pool-reserve class okind oslot ogen fn2-pool))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
             :in-theory (e/d (fn2-pool-row-okp) (fn2-pool-row-okp-of-invariant))
             :use ((:instance fn2-pool-slot-types (i (fn2-pool-class-headsi class fn2-pool)))
                   (:instance fn2-pool-row-okp-of-invariant (n (fn2-pool-rows fn2-pool))
                              (i (fn2-pool-class-headsi class fn2-pool)))))))
  (defthm fn2-pool-subsetp-cons-cons
    (implies (subsetp-equal x y) (subsetp-equal (cons a x) (cons a y))))
  (defthm fn2-pool-free-slots-of-set-state-into
    (implies (and (natp s) (subsetp-equal (fn2-pool-free-slots n c fn2-pool) l))
             (subsetp-equal (fn2-pool-free-slots n c (fn2-pool-set-state s v fn2-pool)) (cons s l)))
    :hints (("Goal" :in-theory (disable fn2-pool-subsetp-trans)
             :use ((:instance fn2-pool-subsetp-trans
                              (x (fn2-pool-free-slots n c (fn2-pool-set-state s v fn2-pool)))
                              (y (cons s (fn2-pool-free-slots n c fn2-pool))) (z (cons s l)))))))
  ; RELEASE: the row goes to the head of its class's chain and into its free set.
  (defthm fn2-pool-release-class-okp
    (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                  (fn2-pool-class-accountsp (fn2-pool-nclasses fn2-pool) fn2-pool)
                  (natp c2) (< c2 (fn2-pool-nclasses fn2-pool)))
             (fn2-pool-class-okp c2 (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen fn2-pool))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
             :in-theory (e/d (fn2-pool-class-okp) (fn2-pool-class-okp-of-accounts))
             :use ((:instance fn2-pool-class-okp-of-accounts (n (fn2-pool-nclasses fn2-pool)) (c c2))
                   (:instance fn2-pool-class-okp-of-accounts (n (fn2-pool-nclasses fn2-pool))
                              (c (fn2-pool-class slot fn2-pool)))))))
  (defthm fn2-pool-release-class-accounts
    (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                  (fn2-pool-class-accountsp (fn2-pool-nclasses fn2-pool) fn2-pool)
                  (natp k) (<= k (fn2-pool-nclasses fn2-pool)))
             (fn2-pool-class-accountsp k (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen fn2-pool))))
    :hints (("Goal" :induct (fn2-pool-retired-slots k fn2-pool)
             :in-theory (e/d (fn2-pool-class-accountsp-step fn2-pool-retired-slots) (fn2-pool-release)))))
  (defthm fn2-pool-release-row-okp
    (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                  (fn2-pool-row-invariantp (fn2-pool-rows fn2-pool) fn2-pool)
                  (natp slot) (< slot (fn2-pool-rows fn2-pool)))
             (fn2-pool-row-okp slot (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen fn2-pool))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
             :in-theory (e/d (fn2-pool-row-okp) (fn2-pool-row-okp-of-invariant))
             :use ((:instance fn2-pool-slot-types (i slot))
                   (:instance fn2-pool-row-okp-of-invariant (n (fn2-pool-rows fn2-pool)) (i slot))))))))

(defun fn2-pool-op-sym (op suffix)
  (declare (xargs :guard (and (symbolp op) (stringp suffix))))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name op) suffix) op))
; Per operation: its row's clause after the step, then the whole invariant.
(defun fn2-pool-op-conservation-events (op formals position slot)
  (declare (xargs :guard (and (symbolp op) (symbol-listp formals) (natp position))))
  (let* ((call `(,op ,@formals)) (q `(mv-nth ,position ,call)))
    `((local (defthm ,(fn2-pool-op-sym op "-ROW-OKP")
        (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                      (fn2-pool-row-invariantp (fn2-pool-rows fn2-pool) fn2-pool)
                      (natp ,slot) (< ,slot (fn2-pool-rows fn2-pool)))
                 (fn2-pool-row-okp ,slot ,q))
        :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
                 :in-theory (e/d (fn2-pool-row-okp) (fn2-pool-row-okp-of-invariant))
                 :use ((:instance fn2-pool-slot-types (i ,slot))
                       (:instance fn2-pool-row-okp-of-invariant
                                  (n (fn2-pool-rows fn2-pool)) (i ,slot)))))))
      (defthm ,(fn2-pool-op-sym op "-CONSERVATION")
        (implies (fn2-pool-semanticp fn2-pool) (fn2-pool-semanticp ,q))
        :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
                 :use (fn2-pool-semanticp-elim ,(fn2-pool-op-sym op "-ROW-OKP") ,(fn2-pool-op-sym op "-PRESERVES-TYPE")
                       ,(fn2-pool-op-sym op "-PRESERVES-WFP")
                       (:instance fn2-pool-semanticp-intro (s ,slot) (fn2-pool ,q)))))))))
(defmacro fn2-pool-op-conservation (op formals position &optional (slot 'slot))
  (cons 'progn (fn2-pool-op-conservation-events op formals position slot)))
(fn2-pool-op-conservation fn2-pool-write (slot gen idx byte okind oslot ogen fn2-pool) 1)
(fn2-pool-op-conservation fn2-pool-reset (slot gen okind oslot ogen fn2-pool) 1)
(fn2-pool-op-conservation fn2-pool-lease-in (slot gen len opslot opgen okind oslot ogen fn2-pool) 2)
(fn2-pool-op-conservation fn2-pool-adapter-write (slot gen opslot opgen idx byte fn2-pool) 1)
(fn2-pool-op-conservation fn2-pool-complete-in (slot gen opslot opgen n fn2-pool) 1)
(fn2-pool-op-conservation fn2-pool-lease-out (slot gen off len okind oslot ogen fn2-pool) 1)
(fn2-pool-op-conservation fn2-pool-release-out (slot gen fn2-pool) 1)
(fn2-pool-op-conservation fn2-pool-hand (slot gen okind oslot ogen tkind tslot tgen fn2-pool) 1)
(fn2-pool-op-conservation fn2-pool-accept-hand (slot gen tkind tslot tgen fn2-pool) 1)

(defthm fn2-pool-reserve-conservation
  (implies (fn2-pool-semanticp fn2-pool)
           (fn2-pool-semanticp (mv-nth 3 (fn2-pool-reserve class okind oslot ogen fn2-pool))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
           :use (fn2-pool-semanticp-elim fn2-pool-reserve-row-okp
                 fn2-pool-reserve-preserves-type fn2-pool-reserve-preserves-wfp
                 (:instance fn2-pool-reserve-class-accounts (k (fn2-pool-nclasses fn2-pool)))
                 (:instance fn2-pool-semanticp-intro (s (fn2-pool-class-headsi class fn2-pool))
                            (fn2-pool (mv-nth 3 (fn2-pool-reserve class okind oslot ogen fn2-pool))))))))

(defthm fn2-pool-release-conservation
  (implies (fn2-pool-semanticp fn2-pool)
           (fn2-pool-semanticp (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen fn2-pool))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
           :use (fn2-pool-semanticp-elim fn2-pool-release-row-okp
                 fn2-pool-release-preserves-type fn2-pool-release-preserves-wfp
                 (:instance fn2-pool-release-class-accounts (k (fn2-pool-nclasses fn2-pool)))
                 (:instance fn2-pool-semanticp-intro (s slot)
                            (fn2-pool (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen fn2-pool))))))))

;; Carved extents are disjoint: row J starts at or after row I's end.
(local
 (defthm fn2-pool-row-nonneg
   (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (natp i) (< i (fn2-pool-rows fn2-pool)))
            (and (<= 0 (fn2-pool-cap i fn2-pool)) (<= 0 (fn2-pool-base i fn2-pool))
                 (<= 0 (fn2-pool-fill i fn2-pool))))
   :rule-classes :linear
   :hints (("Goal" :use fn2-pool-slot-types))))
(local
 (defthm fn2-pool-extent-below
   (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                 (fn2-pool-row-invariantp (fn2-pool-rows fn2-pool) fn2-pool)
                 (natp i) (natp j) (< i j) (< j (fn2-pool-rows fn2-pool)))
            (<= (+ (fn2-pool-base i fn2-pool) (fn2-pool-cap i fn2-pool)) (fn2-pool-base j fn2-pool)))
   :hints (("Goal" :induct (fn2-pool-retired-slots j fn2-pool)
            :in-theory (e/d (fn2-pool-retired-slots fn2-pool-row-okp) (fn2-pool-row-okp-of-invariant)))
           ("Subgoal *1/2" :use ((:instance fn2-pool-row-okp-of-invariant (n (fn2-pool-rows fn2-pool)) (i j)))))))
(defthm fn2-pool-extents-disjoint
  (implies (and (fn2-pool-semanticp fn2-pool) (natp i) (natp j) (< i j) (< j (fn2-pool-rows fn2-pool)))
           (<= (+ (fn2-pool-base i fn2-pool) (fn2-pool-cap i fn2-pool)) (fn2-pool-base j fn2-pool)))
  :rule-classes nil
  :hints (("Goal" :use (fn2-pool-semanticp-elim fn2-pool-extent-below))))
(defthm fn2-pool-extents-apart
  (implies (and (fn2-pool-semanticp fn2-pool) (natp i) (natp j) (not (equal i j))
                (< i (fn2-pool-rows fn2-pool)) (< j (fn2-pool-rows fn2-pool)))
           (or (<= (+ (fn2-pool-base i fn2-pool) (fn2-pool-cap i fn2-pool)) (fn2-pool-base j fn2-pool))
               (<= (+ (fn2-pool-base j fn2-pool) (fn2-pool-cap j fn2-pool)) (fn2-pool-base i fn2-pool))))
  :rule-classes nil
  :hints (("Goal" :cases ((< i j) (< j i)))
          ("Subgoal 2" :use ((:instance fn2-pool-extents-disjoint (i j) (j i))))
          ("Subgoal 1" :use ((:instance fn2-pool-extents-disjoint)))))
(defthm fn2-pool-semanticp-row-bounds
  (implies (and (fn2-pool-semanticp fn2-pool) (natp i) (< i (fn2-pool-rows fn2-pool)))
           (and (natp (fn2-pool-base i fn2-pool)) (natp (fn2-pool-cap i fn2-pool))
                (natp (fn2-pool-fill i fn2-pool))
                (<= (fn2-pool-fill i fn2-pool) (fn2-pool-cap i fn2-pool))
                (<= (+ (fn2-pool-base i fn2-pool) (fn2-pool-cap i fn2-pool))
                    (fn2-pool-data-length fn2-pool))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-pool-row-okp) (fn2-pool-row-okp-of-invariant))
           :use (fn2-pool-semanticp-elim (:instance fn2-pool-slot-types)
                 (:instance fn2-pool-row-okp-of-invariant (n (fn2-pool-rows fn2-pool)))))))
;; Octets of an interval: a byte written outside it, and a fill change, leave them.
(defthm fn2-pool-logical-octets-of-update-datai
  (implies (and (natp k) (natp b) (or (< k b) (<= (+ b (nfix n)) k)))
           (equal (fn2-pool-logical-octets n b (update-fn2-pool-datai k v fn2-pool))
                  (fn2-pool-logical-octets n b fn2-pool)))
  :hints (("Goal" :induct (fn2-pool-logical-octets n b fn2-pool))))
(defthm fn2-pool-logical-octets-of-set-fill
  (equal (fn2-pool-logical-octets n b (fn2-pool-set-fill j v fn2-pool))
         (fn2-pool-logical-octets n b fn2-pool)))
;; A write through one row never changes another row's extent.
(defthm fn2-pool-write-other-extent
  (implies (and (fn2-pool-semanticp fn2-pool) (natp other) (< other (fn2-pool-rows fn2-pool))
                (not (equal other slot)))
           (equal (fn2-pool-logical-octets
                   (fn2-pool-cap other fn2-pool) (fn2-pool-base other fn2-pool)
                   (mv-nth 1 (fn2-pool-write slot gen idx byte okind oslot ogen fn2-pool)))
                  (fn2-pool-logical-octets (fn2-pool-cap other fn2-pool) (fn2-pool-base other fn2-pool)
                                           fn2-pool)))
  :hints (("Goal" :use ((:instance fn2-pool-semanticp-row-bounds (i slot))
                        (:instance fn2-pool-semanticp-row-bounds (i other))
                        (:instance fn2-pool-extents-apart (i slot) (j other))))))
(defthm fn2-pool-adapter-write-other-extent
  (implies (and (fn2-pool-semanticp fn2-pool) (natp other) (< other (fn2-pool-rows fn2-pool))
                (not (equal other slot)))
           (equal (fn2-pool-logical-octets
                   (fn2-pool-cap other fn2-pool) (fn2-pool-base other fn2-pool)
                   (mv-nth 1 (fn2-pool-adapter-write slot gen opslot opgen idx byte fn2-pool)))
                  (fn2-pool-logical-octets (fn2-pool-cap other fn2-pool) (fn2-pool-base other fn2-pool)
                                           fn2-pool)))
  :hints (("Goal" :use ((:instance fn2-pool-semanticp-row-bounds (i slot))
                        (:instance fn2-pool-semanticp-row-bounds (i other))
                        (:instance fn2-pool-extents-apart (i slot) (j other))))))
;; Neither write moves a row's extent.
(defthm fn2-pool-write-keeps-extents
  (let ((q (mv-nth 1 (fn2-pool-write slot gen idx byte okind oslot ogen fn2-pool))))
    (and (equal (fn2-pool-rows q) (fn2-pool-rows fn2-pool))
         (equal (fn2-pool-base i q) (fn2-pool-base i fn2-pool))
         (equal (fn2-pool-cap i q) (fn2-pool-cap i fn2-pool)))))
(defthm fn2-pool-adapter-write-keeps-extents
  (let ((q (mv-nth 1 (fn2-pool-adapter-write slot gen opslot opgen idx byte fn2-pool))))
    (and (equal (fn2-pool-rows q) (fn2-pool-rows fn2-pool))
         (equal (fn2-pool-base i q) (fn2-pool-base i fn2-pool))
         (equal (fn2-pool-cap i q) (fn2-pool-cap i fn2-pool)))))
(defthm fn2-pool-conservation-proved
  (implies (fn2-pool-conservation-hyps op a p)
           (fn2-pool-conservation-conclusion op a p))
  :hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-lease-in
                                      fn2-pool-adapter-write fn2-pool-complete-in fn2-pool-lease-out
                                      fn2-pool-release-out fn2-pool-hand fn2-pool-accept-hand
                                      fn2-pool-read fn2-pool-write fn2-pool-reset))))
(defthm fn2-pool-conservation-statement
  (fn2-pool-conservation$owed op a p)
  :hints (("Goal" :in-theory '(fn2-pool-conservation$owed) :use fn2-pool-conservation-proved))))
(fn2-owed-discharge fn2-pool-conservation fn2-pool-conservation-statement)


(defun fn2-pool-generation-hyps (slot op a fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (declare (ignore a))
  (and (member-eq op *fn2-pool-operations*) (fn2-pool-semanticp fn2-pool)
       (fn2-pool-logical-slotp slot fn2-pool)))
(defun fn2-pool-generation-resultp
  (op selectedp code old-gen new-gen old-state new-state limit)
  (and (<= old-gen new-gen)
       (implies (equal old-state *fn2-pool-state-retired*)
                (and (equal new-state *fn2-pool-state-retired*) (equal new-gen old-gen)))
       (implies (and (eq op :release) selectedp (eq code :ok))
                (equal new-gen (+ 1 old-gen)))
       (implies (and (eq op :release) selectedp (eq code :retired))
                (and (equal old-gen limit) (equal new-state *fn2-pool-state-retired*)
                     (equal new-gen old-gen)))))
(defun-nx fn2-pool-generation-conclusion (slot op a p)
  (let* ((r (fn2-pool-operation op a p)) (q (cadr r)))
    (fn2-pool-generation-resultp
     op (equal slot (nth 0 a)) (car r)
     (fn2-pool-gen slot p) (fn2-pool-gen slot q)
     (fn2-pool-state slot p) (fn2-pool-state slot q) (fn2-pool-gen-limit p))))

(defthm-owed fn2-pool-generation (slot op a p)
  (implies (fn2-pool-generation-hyps slot op a p)
           (fn2-pool-generation-conclusion slot op a p))
  :schema :invariant :from (:columns fn2-pool)
  :teeth (fn2-pool-generation-teeth)
  :doc "Every operation preserves monotone generations and retirement; successful release increments, and terminal retirement occurs exactly at the configured limit.")
