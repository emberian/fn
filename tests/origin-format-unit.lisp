; Actual bounded bootstrap packer, with independent literal wire expectation.
(in-package "ACL2")
(include-book "../books/boot-pack")
(defun fn2-ofu-read (left offset slot gen fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix left)))
 (if (zp left) nil
  (mv-let (code byte) (fn2-pool-read slot gen offset 1 0 1 fn2-pool)
   (if (eq code :ok)
       (cons byte (fn2-ofu-read (- left 1) (+ offset 1) slot gen fn2-pool))
     (list :read-refused code)))))
(defun fn2-ofu-pack (lineage domain incarnation history history-incarnation fn2-fields fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
 (b* ((fn2-fields (fn2-fields-init (+ 256 *fn2-boot-record-num-fields*) fn2-fields))
      (fn2-digests (fn2-digests-init (* 3 *fn2-digest-stride*) fn2-digests))
      (fn2-b3 (fn2-b3-table-init 3 fn2-b3))
      (fn2-pool (fn2-pool-init '((2 . 4096)) 1 100 fn2-pool))
      ((mv a slot gen fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool))
      ((mv b scratch sg fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool))
      ((mv code fn2-fields fn2-digests fn2-b3 fn2-pool)
       (fn2-boot-pack-pool 0 0 33554432 16 1 1 1 "" 0 0
                          lineage domain incarnation history history-incarnation
                          slot gen scratch sg 1 0 1 fn2-fields fn2-digests fn2-b3 fn2-pool)))
  (mv (list a b code (fn2-ofu-read 4096 0 slot gen fn2-pool)) fn2-fields fn2-digests fn2-b3 fn2-pool)))
(defun fn2-ofu-run (lineage domain incarnation history history-incarnation)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (answer fn2-fields)
   (with-local-stobj fn2-digests
    (mv-let (answer fn2-fields fn2-digests)
     (with-local-stobj fn2-b3
      (mv-let (answer fn2-fields fn2-digests fn2-b3)
       (with-local-stobj fn2-pool
        (mv-let (answer fn2-fields fn2-digests fn2-b3 fn2-pool)
         (fn2-ofu-pack lineage domain incarnation history history-incarnation
                       fn2-fields fn2-digests fn2-b3 fn2-pool)
         (mv answer fn2-fields fn2-digests fn2-b3)))
       (mv answer fn2-fields fn2-digests)))
     (mv answer fn2-fields))) answer)))
; Independent little-endian/varint prefix plus zero padding and BLAKE3 trailer.
; The literal trailer was computed from this literal prefix with
; tests.surface.blake3_pure, checked against its published BLAKE3 vectors.
; No encoder output supplies the expected bytes.
(defconst *fn2-ofu-expected-image*
 (append '(70 50 66 84 2 0 0 128 128 128 16 16 1 17 23 5 101 7
           1 0 0 0 1 0 0 0 0 0 0 0 0 0)
         (make-list 4032 :initial-element 0)
         '(245 150 125 77 220 189 239 131 114 213 247 106 37 209 208 125
           36 125 81 199 17 225 141 118 107 137 233 2 98 174 225 117)))
(defun fn2-ofu-distinct-names (cases canonical)
 (declare (xargs :verify-guards nil))
 (if (endp cases) t
  (let* ((names (car cases))
         (actual (fn2-ofu-run (nth 0 names) (nth 1 names) (nth 2 names)
                             (nth 3 names) (nth 4 names)))
         (image (nth 3 actual)))
   (and (equal (take 3 actual) '(:ok :ok :ok))
        (equal (len image) 4096)
        (not (equal image canonical))
        (not (equal (nthcdr 4064 image) (nthcdr 4064 canonical)))
        (fn2-ofu-distinct-names (cdr cases) canonical)))))
(assert-event
 (let ((actual (fn2-ofu-run 17 23 5 101 7)))
  (and (equal actual (list :ok :ok :ok *fn2-ofu-expected-image*))
       (fn2-ofu-distinct-names
        '((18 23 5 101 7) (17 24 5 101 7) (17 23 6 101 7)
          (17 23 5 102 7) (17 23 5 101 8))
        (nth 3 actual)))))
