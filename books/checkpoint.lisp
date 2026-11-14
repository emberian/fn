; Concrete checkpoint candidates. Preparation never grants allocator coverage.
(in-package "ACL2")
(include-book "format-check")
(include-book "alloc")
(fn2-book-layer :b)

; Six references per candidate: descriptor, metadata, allocation state, proof
; directory, event frontier and recovery arena. Hash bytes live in a disjoint
; concrete table, not in the reusable checker scratch rows.
(defcolumns fn2-checkpoints
 ((state (:enum fn2-checkpoint-state (:free :preparing :checked :installed :promoting :promoted :uncertain)))
  (checkpoint :u60) (cut-commit :u60) (cut-event :u60)
  (history :u60) (incarnation :u60) (installation-commit :u60)
  (previous :u60) (bank :u8) (anchor-mask :u8)))
(defcolumns fn2-checkpoint-refs
 ((storage-domain :u60) (physical-unit :u60) (writer-epoch :u60)
  (allocation :u60) (page-kind :u60) (encoded-length :u60)
  (edge :u32) (retained :bool)))
(defcolumns fn2-checkpoint-bytes ((value :u8)))

(defun fn2-checkpoint-slotp (c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes) :guard t))
 (and (fn2-checkpoints-wfp fn2-checkpoints)
      (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
      (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
      (natp c) (< c (fn2-checkpoints-rows fn2-checkpoints))
      (<= (* 6 (+ 1 c)) (fn2-checkpoint-refs-rows fn2-checkpoint-refs))
      (<= (* 192 (+ 1 c)) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes))))

; One exact holder's protection per step. Refusing halfway leaves the prior
; edges held. The coordinator must resume or discharge each one by its tuple.
(defun fn2-checkpoint-retain (c role edge fn2-checkpoints fn2-checkpoint-refs
                            fn2-checkpoint-bytes fn2-extents fn2-alloc-edges)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-extents fn2-alloc-edges)
  :guard (and (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
              (fn2-checkpoints-wfp fn2-checkpoints)
              (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 (if (not (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
               (natp role) (< role 6) (unsigned-byte-p 32 edge)
               (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-checked*)))
     (mv :state fn2-checkpoint-refs fn2-extents fn2-alloc-edges)
  (let* ((r (+ (* 6 c) role))
         (unit (fn2-checkpoint-refs-physical-unit r fn2-checkpoint-refs))
         (epoch (fn2-checkpoint-refs-writer-epoch r fn2-checkpoint-refs))
         (allocation (fn2-checkpoint-refs-allocation r fn2-checkpoint-refs))
         (holder (fn2-checkpoints-checkpoint c fn2-checkpoints)))
   (if (equal (fn2-checkpoint-refs-retained r fn2-checkpoint-refs) 1)
       (mv (if (and (equal edge (fn2-checkpoint-refs-edge r fn2-checkpoint-refs))
                     (fn2-alloc-edge-slotp edge fn2-alloc-edges)
                     (fn2-alloc-edge-matchesp edge holder (floor unit 3) epoch allocation
                                             :selectable-checkpoint fn2-alloc-edges)) :ok :edge-holder)
           fn2-checkpoint-refs fn2-extents fn2-alloc-edges)
    ; This physical profile stores three units per allocator extent.
    ; Descriptor unit addresses must therefore identify their containing extent.
    (mv-let (code fn2-extents fn2-alloc-edges)
     (fn2-alloc-edge-add edge holder (floor unit 3) epoch allocation
                         :selectable-checkpoint fn2-extents fn2-alloc-edges)
     (let* ((fn2-checkpoint-refs (if (eq code :ok)
              (fn2-checkpoint-refs-set-edge r edge fn2-checkpoint-refs) fn2-checkpoint-refs))
            (fn2-checkpoint-refs (if (eq code :ok)
              (fn2-checkpoint-refs-set-retained r 1 fn2-checkpoint-refs) fn2-checkpoint-refs)))
      (mv code fn2-checkpoint-refs fn2-extents fn2-alloc-edges)))))))

; Check six owned edges, not the extent table. Cached flags alone never grant
; permission; the named concrete edges must still match at publication.
(defun fn2-checkpoint-retainedp (role c fn2-checkpoints fn2-checkpoint-refs fn2-alloc-edges)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-alloc-edges)
  :measure (nfix (- 6 (nfix role)))
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints)
              (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-alloc-edges-wfp fn2-alloc-edges)
              (natp role) (<= role 6) (natp c) (< c (fn2-checkpoints-rows fn2-checkpoints))
              (<= (* 6 (+ 1 c)) (fn2-checkpoint-refs-rows fn2-checkpoint-refs)))))
 (if (or (not (natp role)) (>= role 6)) t
  (let ((r (+ (* 6 c) role)))
   (and (equal (fn2-checkpoint-refs-retained r fn2-checkpoint-refs) 1)
        (fn2-alloc-edge-slotp (fn2-checkpoint-refs-edge r fn2-checkpoint-refs) fn2-alloc-edges)
        (fn2-alloc-edge-matchesp (fn2-checkpoint-refs-edge r fn2-checkpoint-refs)
          (fn2-checkpoints-checkpoint c fn2-checkpoints)
          (floor (fn2-checkpoint-refs-physical-unit r fn2-checkpoint-refs) 3)
          (fn2-checkpoint-refs-writer-epoch r fn2-checkpoint-refs)
          (fn2-checkpoint-refs-allocation r fn2-checkpoint-refs)
          :selectable-checkpoint fn2-alloc-edges)
        (fn2-checkpoint-retainedp (+ 1 role) c fn2-checkpoints fn2-checkpoint-refs fn2-alloc-edges)))))

; A historical location is not a new allocation claim. The checkpoint map
; and ordered suffix transitions determine which identity currently owns it.
; :historical means do not adopt; :current requires exact allocation identity;
; :conflict is recovery uncertainty, never an instruction to overwrite it.
(defun fn2-checkpoint-location-code (cut record-commit extent epoch allocation fn2-extents)
 (declare (xargs :stobjs fn2-extents :guard (fn2-extents-wfp fn2-extents)))
 (cond ((not (and (natp cut) (posp record-commit) (unsigned-byte-p 60 record-commit))) :bounds)
       ((<= record-commit cut) :historical)
       ((not (fn2-alloc-slotp extent fn2-extents)) :bounds)
       ((not (eq (fn2-alloc-handle-code extent epoch allocation fn2-extents) :ok)) :conflict)
       ((member-equal (fn2-extents-state extent fn2-extents)
                      (list *fn2-extent-state-allocated* *fn2-extent-state-retire-pending*))) :current)
       (t :conflict)))

(defthm fn2-checkpoint-historical-location-by-definition
 (implies (and (natp cut) (posp record-commit) (unsigned-byte-p 60 record-commit)
               (<= record-commit cut))
          (equal (fn2-checkpoint-location-code cut record-commit extent epoch allocation fn2-extents)
                 :historical)))

; Copies a digest out of the checked pool into checkpoint-owned bytes. The
; directory is not marked checked if any read fails, even after a prefix copy.
(defun fn2-checkpoint-copy-hash (left dst src slot gen okind oslot ogen
                                fn2-pool fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-pool fn2-checkpoint-bytes) :measure (nfix left)
  :guard (and (fn2-pool-wfp fn2-pool) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
              (natp left) (<= left 32) (natp dst) (natp src)
              (<= (+ dst left) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes)))))
 (if (zp left) (mv :ok fn2-checkpoint-bytes)
  (mv-let (code byte) (fn2-pool-read slot gen src okind oslot ogen fn2-pool)
   (if (not (eq code :ok)) (mv code fn2-checkpoint-bytes)
    (let ((fn2-checkpoint-bytes (fn2-checkpoint-bytes-set-value dst byte fn2-checkpoint-bytes)))
     (fn2-checkpoint-copy-hash (- left 1) (+ 1 dst) (+ 1 src) slot gen okind oslot ogen
                               fn2-pool fn2-checkpoint-bytes))))))

; Descriptor root fields are an existing format declaration, in groups of
; seven. This helper consumes one root per call; callers resume at ROLE+1.
(defun fn2-checkpoint-capture-root (c role base slot gen okind oslot ogen
                                  fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 (if (not (and (natp c) (natp role) (< role 5) (natp base)
               (<= (+ base *fn2-format-checkpoint-descriptor-num-fields*) (fn2-fields-rows fn2-fields))
               (< (+ (* 6 c) role 1) (fn2-checkpoint-refs-rows fn2-checkpoint-refs))
               (<= (* 32 (+ (* 6 c) role 2)) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes))))
     (mv :bounds fn2-checkpoint-refs fn2-checkpoint-bytes)
  (let* ((f (+ base 3 (* 7 role))) (r (+ (* 6 c) 1 role))
         (hash (+ f 6))
         (src (fn2-fields-ref-off hash fn2-fields)))
   (if (not (equal (fn2-fields-value hash fn2-fields) 1))
       (mv :hash fn2-checkpoint-refs fn2-checkpoint-bytes)
    (mv-let (code fn2-checkpoint-bytes)
     (fn2-checkpoint-copy-hash 32 (* 32 r) src slot gen okind oslot ogen fn2-pool fn2-checkpoint-bytes)
     (if (not (eq code :ok)) (mv code fn2-checkpoint-refs fn2-checkpoint-bytes)
      (let* ((fn2-checkpoint-refs (fn2-checkpoint-refs-set-storage-domain r (fn2-fields-value f fn2-fields) fn2-checkpoint-refs))
             (fn2-checkpoint-refs (fn2-checkpoint-refs-set-physical-unit r (fn2-fields-value (+ f 1) fn2-fields) fn2-checkpoint-refs))
             (fn2-checkpoint-refs (fn2-checkpoint-refs-set-writer-epoch r (fn2-fields-value (+ f 2) fn2-fields) fn2-checkpoint-refs))
             (fn2-checkpoint-refs (fn2-checkpoint-refs-set-allocation r (fn2-fields-value (+ f 3) fn2-fields) fn2-checkpoint-refs))
             (fn2-checkpoint-refs (fn2-checkpoint-refs-set-page-kind r (fn2-fields-value (+ f 4) fn2-fields) fn2-checkpoint-refs))
             (fn2-checkpoint-refs (fn2-checkpoint-refs-set-encoded-length r (fn2-fields-value (+ f 5) fn2-fields) fn2-checkpoint-refs)))
       (mv :ok fn2-checkpoint-refs fn2-checkpoint-bytes))))))))

; Called immediately after the descriptor's physical page checker succeeds,
; before another decode can replace header fields. It decodes only its payload
; and rejects trailing bytes. This is a decode operation, NOT authentication;
; the composing checker must call it in the :ok arm of fn2-format-run :page.
(defun fn2-checkpoint-decode (base slot gen off len okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (if (not (and (natp base)
               (<= (+ base *fn2-format-checkpoint-descriptor-num-fields*) (fn2-fields-rows fn2-fields))
               (natp off) (unsigned-byte-p 32 len) (unsigned-byte-p 32 (+ off len))))
     (mv :bounds fn2-fields)
  (let* ((header (fn2-fields-value (+ base *fn2-format-page-header-field-header-length*) fn2-fields))
         (payload (fn2-fields-value (+ base *fn2-format-page-header-field-payload-length*) fn2-fields)))
   (if (not (and (natp header) (natp payload) (<= (+ header payload) len)
                 (equal (fn2-fields-value (+ base *fn2-format-page-header-field-page-kind*) fn2-fields)
                        *page-kind-checkpoint-descriptor*)))
       (mv :descriptor fn2-fields)
    (mv-let (code next fn2-fields)
     (fn2-format-checkpoint-descriptor-decode base slot gen (+ off header) (+ off header payload)
                                             okind oslot ogen fn2-fields fn2-pool)
     (mv (if (and (eq code :ok) (not (equal next (+ off header payload)))) :length code) fn2-fields))))))

(defun fn2-checkpoint-copy-expected (i dst hash fn2-digests fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-digests fn2-checkpoint-bytes)
  :measure (nfix (- 32 (nfix i)))
  :guard (and (natp i) (<= i 32) (natp dst)
              (fn2-digest-rowp hash fn2-digests) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
              (<= (+ dst 32) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes)))))
 (if (or (not (natp i)) (>= i 32)) fn2-checkpoint-bytes
  (let* ((byte (fn2-fc-word-byte (fn2-digest-word hash (floor i 4) fn2-digests) (mod i 4)))
         (fn2-checkpoint-bytes (fn2-checkpoint-bytes-set-value (+ dst i) byte fn2-checkpoint-bytes)))
   (fn2-checkpoint-copy-expected (+ 1 i) dst hash fn2-digests fn2-checkpoint-bytes))))

; A locator is only a candidate. Neither preparation nor a valid descriptor
; grants publication, retirement coverage, or permission to drop an old root.
(defun fn2-checkpoint-prepare (c checkpoint history incarnation domain unit epoch allocation kind len hash
                             fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-digests)
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-digests-wfp fn2-digests))))
 (if (not (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
               (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-free*)
               (posp checkpoint) (unsigned-byte-p 60 checkpoint)
               (unsigned-byte-p 60 history) (unsigned-byte-p 60 incarnation)
               (unsigned-byte-p 60 domain) (unsigned-byte-p 60 unit)
               (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
               (equal kind *page-kind-checkpoint-descriptor*) (posp len) (unsigned-byte-p 60 len)
               (fn2-digest-rowp hash fn2-digests)))
     (mv :bounds fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
  (let* ((r (* 6 c))
         (fn2-checkpoint-bytes (fn2-checkpoint-copy-expected 0 (* 32 r) hash fn2-digests fn2-checkpoint-bytes))
         (fn2-checkpoint-refs (fn2-checkpoint-refs-set-storage-domain r domain fn2-checkpoint-refs))
         (fn2-checkpoint-refs (fn2-checkpoint-refs-set-physical-unit r unit fn2-checkpoint-refs))
         (fn2-checkpoint-refs (fn2-checkpoint-refs-set-writer-epoch r epoch fn2-checkpoint-refs))
         (fn2-checkpoint-refs (fn2-checkpoint-refs-set-allocation r allocation fn2-checkpoint-refs))
         (fn2-checkpoint-refs (fn2-checkpoint-refs-set-page-kind r kind fn2-checkpoint-refs))
         (fn2-checkpoint-refs (fn2-checkpoint-refs-set-encoded-length r len fn2-checkpoint-refs))
         (fn2-checkpoints (fn2-checkpoints-set-checkpoint c checkpoint fn2-checkpoints))
         (fn2-checkpoints (fn2-checkpoints-set-history c history fn2-checkpoints))
         (fn2-checkpoints (fn2-checkpoints-set-incarnation c incarnation fn2-checkpoints))
         (fn2-checkpoints (fn2-checkpoints-set-state c *fn2-checkpoint-state-preparing* fn2-checkpoints)))
   (mv :ok fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes))))

(defun fn2-checkpoint-hash-matchesp (i dst hash fn2-digests fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-digests fn2-checkpoint-bytes)
  :measure (nfix (- 32 (nfix i)))
  :guard (and (natp i) (<= i 32) (natp dst)
              (fn2-digest-rowp hash fn2-digests) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
              (<= (+ dst 32) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes)))))
 (if (or (not (natp i)) (>= i 32)) t
  (and (equal (fn2-checkpoint-bytes-value (+ dst i) fn2-checkpoint-bytes)
              (fn2-fc-word-byte (fn2-digest-word hash (floor i 4) fn2-digests) (mod i 4)))
       (fn2-checkpoint-hash-matchesp (+ 1 i) dst hash fn2-digests fn2-checkpoint-bytes))))

(defun fn2-checkpoint-capture-roots (role c base slot gen okind oslot ogen
                                   fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes)
  :measure (nfix (- 5 (nfix role)))
  :guard (and (natp role) (<= role 5) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 (if (or (not (natp role)) (>= role 5)) (mv :ok fn2-checkpoint-refs fn2-checkpoint-bytes)
  (mv-let (code fn2-checkpoint-refs fn2-checkpoint-bytes)
   (fn2-checkpoint-capture-root c role base slot gen okind oslot ogen
                               fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes)
   (if (not (eq code :ok)) (mv code fn2-checkpoint-refs fn2-checkpoint-bytes)
    (fn2-checkpoint-capture-roots (+ 1 role) c base slot gen okind oslot ogen
                                 fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes)))))

; The successful page checker and descriptor decode are in ONE transition.
; A caller cannot supply a verification flag. Buffer ownership and checker
; continuation ownership must persist across :more, as for other B readers.
(defun fn2-checkpoint-check-step (c row slot gen off len base okind oslot ogen budget
                                fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
  :guard (and (fn2-fc-guard) (fn2-checkpoints-wfp fn2-checkpoints)
              (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 (b* (((unless (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-preparing*)
                     (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)))
       (mv :state fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      (r (* 6 c))
      ((unless (and (equal (fn2-fc-context-location row fn2-fc-context) (fn2-checkpoint-refs-physical-unit r fn2-checkpoint-refs))
                     (equal (fn2-fc-context-allocation row fn2-fc-context) (fn2-checkpoint-refs-allocation r fn2-checkpoint-refs))
                     (equal (fn2-fc-context-writer-epoch row fn2-fc-context) (fn2-checkpoint-refs-writer-epoch r fn2-checkpoint-refs))
                     (equal (fn2-fc-context-history row fn2-fc-context) (fn2-checkpoints-history c fn2-checkpoints))
                     (equal (fn2-fc-context-incarnation row fn2-fc-context) (fn2-checkpoints-incarnation c fn2-checkpoints))
                     (equal (fn2-fc-context-page-kind row fn2-fc-context) *page-kind-checkpoint-descriptor*)
                     (equal len (fn2-checkpoint-refs-encoded-length r fn2-checkpoint-refs))
                     (equal len (fn2-fc-context-encoded-length row fn2-fc-context))
                     (fn2-checkpoint-hash-matchesp 0 (* 32 r) (fn2-fc-context-hash row fn2-fc-context) fn2-digests fn2-checkpoint-bytes)))
       (mv :context fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget
                       fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((unless (eq code :ok))
       (mv code fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-fields) (fn2-checkpoint-decode base slot gen off len okind oslot ogen fn2-fields fn2-pool))
      ((unless (and (eq code :ok)
                     (equal (fn2-fields-value (+ base *fn2-format-checkpoint-descriptor-field-checkpoint*) fn2-fields)
                            (fn2-checkpoints-checkpoint c fn2-checkpoints))))
       (mv :descriptor fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-checkpoint-refs fn2-checkpoint-bytes)
       (fn2-checkpoint-capture-roots 0 c base slot gen okind oslot ogen
                                   fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes))
      ((unless (eq code :ok))
       (mv code fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      (fn2-checkpoints (fn2-checkpoints-set-cut-commit c (fn2-fields-value (+ base *fn2-format-checkpoint-descriptor-field-cut-commit*) fn2-fields) fn2-checkpoints))
      (fn2-checkpoints (fn2-checkpoints-set-cut-event c (fn2-fields-value (+ base *fn2-format-checkpoint-descriptor-field-cut-event*) fn2-fields) fn2-checkpoints))
      (fn2-checkpoints (fn2-checkpoints-set-state c *fn2-checkpoint-state-checked* fn2-checkpoints)))
  (mv :ok fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)))

(defun fn2-checkpoint-pool-hash-matchesp (left dst src slot gen okind oslot ogen
                                       fn2-pool fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-pool fn2-checkpoint-bytes) :measure (nfix left)
  :guard (and (fn2-pool-wfp fn2-pool) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
              (natp left) (<= left 32) (natp dst) (natp src)
              (<= (+ dst left) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes)))))
 (if (zp left) t
  (mv-let (code byte) (fn2-pool-read slot gen src okind oslot ogen fn2-pool)
   (and (eq code :ok) (equal byte (fn2-checkpoint-bytes-value dst fn2-checkpoint-bytes))
        (fn2-checkpoint-pool-hash-matchesp (- left 1) (+ dst 1) (+ src 1) slot gen okind oslot ogen
                                         fn2-pool fn2-checkpoint-bytes)))))

; INSTALL-COMMIT is supplied by the batch installer/replay's verified envelope,
; never decoded from a caller's claimed cut. The descriptor names an earlier
; installed cut; foreground commits may intervene. This operation only records
; journal installation; anchor promotion
; remains separate and no allocator cut is advanced here.
(defun fn2-checkpoint-install (c install-commit base slot gen okind oslot ogen
                              fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                              fn2-fields fn2-pool fn2-alloc-edges)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-fields fn2-pool fn2-alloc-edges)
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-fields-wfp fn2-fields)
              (fn2-pool-wfp fn2-pool) (fn2-alloc-edges-wfp fn2-alloc-edges))))
 (b* (((unless (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (posp install-commit) (unsigned-byte-p 60 install-commit)
                     (natp base) (<= (+ base *fn2-format-checkpoint-installation-num-fields*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-checkpoints))
      ((unless (member-equal (fn2-checkpoints-state c fn2-checkpoints)
                             (list *fn2-checkpoint-state-checked* *fn2-checkpoint-state-installed*)))
       (mv :state fn2-checkpoints))
      ((unless (< (fn2-checkpoints-cut-commit c fn2-checkpoints) install-commit))
       (mv :commit fn2-checkpoints))
      (r (* 6 c))
      (f (+ base 1))
      ((unless (and (equal (fn2-fields-value base fn2-fields) (fn2-checkpoints-checkpoint c fn2-checkpoints))
                     (equal (fn2-fields-value f fn2-fields) (fn2-checkpoint-refs-storage-domain r fn2-checkpoint-refs))
                     (equal (fn2-fields-value (+ f 1) fn2-fields) (fn2-checkpoint-refs-physical-unit r fn2-checkpoint-refs))
                     (equal (fn2-fields-value (+ f 2) fn2-fields) (fn2-checkpoint-refs-writer-epoch r fn2-checkpoint-refs))
                     (equal (fn2-fields-value (+ f 3) fn2-fields) (fn2-checkpoint-refs-allocation r fn2-checkpoint-refs))
                     (equal (fn2-fields-value (+ f 4) fn2-fields) (fn2-checkpoint-refs-page-kind r fn2-checkpoint-refs))
                     (equal (fn2-fields-value (+ f 5) fn2-fields) (fn2-checkpoint-refs-encoded-length r fn2-checkpoint-refs))
                     (equal (fn2-fields-value (+ f 6) fn2-fields) 1)
                     (fn2-checkpoint-pool-hash-matchesp 32 (* 32 r)
                       (fn2-fields-ref-off (+ f 6) fn2-fields) slot gen okind oslot ogen fn2-pool fn2-checkpoint-bytes)))
       (mv :descriptor fn2-checkpoints))
      ((unless (fn2-checkpoint-retainedp 0 c fn2-checkpoints fn2-checkpoint-refs fn2-alloc-edges))
       (mv :unprotected fn2-checkpoints))
      (fn2-checkpoints (fn2-checkpoints-set-installation-commit c install-commit fn2-checkpoints))
      (fn2-checkpoints (fn2-checkpoints-set-state c *fn2-checkpoint-state-installed* fn2-checkpoints)))
  (mv :ok fn2-checkpoints)))
