; Core-independent first gate for the shared read decision. Expected bytes
; are a literal BLAKE3("abc") vector, independently checked with the pure
; Python fixture oracle (tests/surface/blake3_pure.py), not produced by the
; ACL2 hasher under test. This finite vector is not collision resistance.
(in-package "ACL2")
(include-book "../books/block-integrity")
(defconst *fn2-lcu-abc-hash*
 '(100 55 179 172 56 70 81 51 255 182 59 117 39 58 141 181
   72 197 88 70 93 121 219 3 253 53 156 108 213 189 157 133))
(defun fn2-lcu-write-slot (slot bytes off fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil))
 (if (atom bytes) (mv :ok fn2-pool)
  (mv-let (code fn2-pool) (fn2-pool-write slot 1 off (car bytes) 1 0 1 fn2-pool)
   (if (eq code :ok) (fn2-lcu-write-slot slot (cdr bytes) (+ 1 off) fn2-pool) (mv code fn2-pool)))))
(defun fn2-lcu-write (bytes off fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil))
 (fn2-lcu-write-slot 0 bytes off fn2-pool))
(defun fn2-lcu-check (fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-b3 fn2-digests fn2-pool) :verify-guards nil))
 (b* ((fn2-digests (fn2-digests-init 144 fn2-digests))
      (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
      (fn2-pool (fn2-pool-init '((2 . 128)) 1 100 fn2-pool))
      ((mv reserve & & fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool))
      ((mv reserve-h & & fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool))
      ((mv wrote fn2-pool) (fn2-lcu-write (append *fn2-lcu-abc-hash* '(97 98 99)) 0 fn2-pool))
      ((mv copied fn2-pool) (fn2-lcu-write-slot 1 *fn2-lcu-abc-hash* 0 fn2-pool))
      ((mv separate fn2-b3 fn2-digests)
       (fn2-block-read-commitment-children 3 3 0 1 32 1 1 0 1 0 1 fn2-b3 fn2-digests fn2-pool))
      ((mv good fn2-b3 fn2-digests)
       (fn2-block-read-commitment-children 3 3 0 1 32 0 1 0 1 0 1 fn2-b3 fn2-digests fn2-pool))
      ((mv short fn2-b3 fn2-digests)
       (fn2-block-read-commitment-children 2 3 0 1 32 0 1 0 1 0 1 fn2-b3 fn2-digests fn2-pool))
      ((mv changed fn2-pool) (fn2-pool-write 0 1 34 100 1 0 1 fn2-pool))
      ((mv bad fn2-b3 fn2-digests)
       (fn2-block-read-commitment-children 3 3 0 1 32 0 1 0 1 0 1 fn2-b3 fn2-digests fn2-pool)))
  (mv (equal (list reserve reserve-h wrote copied separate good short changed bad) '(:ok :ok :ok :ok :ok :ok :io :ok :hash))
      fn2-b3 fn2-digests fn2-pool)))
(defun fn2-lcu-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-b3
  (mv-let (ok fn2-b3)
   (with-local-stobj fn2-digests
    (mv-let (ok fn2-b3 fn2-digests)
     (with-local-stobj fn2-pool
      (mv-let (ok fn2-b3 fn2-digests fn2-pool)
       (fn2-lcu-check fn2-b3 fn2-digests fn2-pool)
       (mv ok fn2-b3 fn2-digests)))
     (mv ok fn2-b3))) ok)))
(assert-event (fn2-lcu-run))
