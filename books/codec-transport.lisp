; Shared concrete ownership envelope for bounded transport codecs.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :a)

(defun fn2-codec-span-p (offset count extent quantum)
 (declare (xargs :guard t))
 (and (unsigned-byte-p 32 offset) (unsigned-byte-p 32 count)
      (unsigned-byte-p 32 extent) (unsigned-byte-p 32 quantum)
      (<= count quantum) (<= (+ offset count) extent)))

(defun fn2-codec-transfer-counts-p (used made requested-input requested-output)
 (declare (xargs :guard t))
 (and (natp used) (natp made) (natp requested-input) (natp requested-output)
      (<= used requested-input) (<= made requested-output)))

; A codec supplies policy columns, never a twin ownership/observation envelope.
; The instance keeps the actual caller's stobj name and generated accessors.
(defconst *fn2-codec-transport-columns*
 '((cap :u32) (nonce :u60) (slot :u32) (generation :u60)
   (alive :bool) (cleanup-credit :bool)
   (handle-id :u64 :why "Opaque physical codec allocation identity, never protocol identity.")
   (budget :u32) (serial :u60)
   (input-length :u32) (input-offset :u32)
   (output-length :u32) (output-offset :u32)
   (terminal :u8) (pending :u8) (offset :u32) (requested :u32)
   (raw-negative :bool)
   (raw-code :u64 :why "Exact raw primitive result magnitude or opaque allocation identity.")
   (raw-count :u32) (raw-errno :u32)))

(defmacro defcodec-transport (name policy-columns &key (rows-bound '2))
 (let ((wfp (fn2-columns-sym name "-WFP"))
       (rows (fn2-columns-sym name "-ROWS"))
       (match (fn2-columns-sym name "-MATCH-P")))
  `(progn
    (defcolumns ,name ,(append *fn2-codec-transport-columns* policy-columns)
      :rows-bound ,rows-bound)
    (defun ,match (cap nonce slot generation serial ,name)
     (declare (xargs :stobjs ,name :guard (and (,wfp ,name) (= (,rows ,name) 1))))
     (and (equal cap (,(fn2-columns-sym name "-CAP") 0 ,name))
          (equal nonce (,(fn2-columns-sym name "-NONCE") 0 ,name))
          (equal slot (,(fn2-columns-sym name "-SLOT") 0 ,name))
          (equal generation (,(fn2-columns-sym name "-GENERATION") 0 ,name))
          (equal serial (,(fn2-columns-sym name "-SERIAL") 0 ,name))
          (< 0 (,(fn2-columns-sym name "-PENDING") 0 ,name)))))))
