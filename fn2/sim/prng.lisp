(in-package "ACL2")
(include-book "../books/profile")

; xoshiro128**. Four scalar words let the simulator store its state inline.
; All runtime products and left shifts are below 2^49 (SBCL fixnums).
; The 16-bit partial-product multiplier also serves seed expansion: never
; form the 64-bit product of two u32 words and discard its upper half later.
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)

; Projection facts preserve the compact public functions in callers' guards.
(defmacro fn2-word-facts (name term source &optional (hyp 't) (bound '4294967296))
  (let ((natname (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-NATP") name))
        (boundname (intern-in-package-of-symbol
                    (concatenate 'string (symbol-name name) "-BOUND") name)))
    `(progn
       (defthm ,natname (implies ,hyp (natp ,term))
         :rule-classes :type-prescription
         :hints (("Goal" :use ,source :in-theory (disable ,source))))
       (defthm ,boundname (implies ,hyp (< ,term ,bound))
         :rule-classes :linear
         :hints (("Goal" :use ,source :in-theory (disable ,source)))))))

(defun fn2-u32 (x)
  (declare (xargs :guard (integerp x)))
  (mod (ifix x) 4294967296))
(defthm fn2-u32-type
  (unsigned-byte-p 32 (fn2-u32 x)))
(defthm fn2-u32-natp
  (natp (fn2-u32 x)) :rule-classes :type-prescription)
(defthm fn2-u32-bound
  (< (fn2-u32 x) 4294967296) :rule-classes :linear)
(in-theory (disable fn2-u32))

(defun fn2-u32-mul (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))))
  (let* ((al (mod a 65536)) (ah (floor a 65536))
         (bl (mod b 65536)) (bh (floor b 65536))
         (cross (mod (+ (* al bh) (* ah bl)) 65536)))
    (fn2-u32 (+ (* al bl) (* 65536 cross)))))
(defthm fn2-u32-mul-type
  (unsigned-byte-p 32 (fn2-u32-mul a b)))
(in-theory (disable fn2-u32-mul))

(defun fn2-rotl32 (x n)
  (declare (xargs :guard (and (unsigned-byte-p 32 x) (natp n) (< n 32))))
  ; Mask before shifting, so the largest intermediate is still only u32.
  (fn2-u32 (+ (ash (mod x (expt 2 (- 32 n))) n)
              (ash x (- n 32)))))
(defthm fn2-rotl32-type
  (unsigned-byte-p 32 (fn2-rotl32 x n)))
(in-theory (disable fn2-rotl32))

(defun fn2-prng-next (s0 s1 s2 s3)
  (declare (xargs :guard (and (unsigned-byte-p 32 s0) (unsigned-byte-p 32 s1)
                              (unsigned-byte-p 32 s2) (unsigned-byte-p 32 s3))))
  (let* ((result (fn2-u32 (* 9 (fn2-rotl32 (fn2-u32 (* s1 5)) 7))))
         (tmp (fn2-u32 (ash s1 9)))
         (s2 (fn2-u32 (logxor s2 s0)))
         (s3 (fn2-u32 (logxor s3 s1)))
         (s1 (fn2-u32 (logxor s1 s2)))
         (s0 (fn2-u32 (logxor s0 s3)))
         (s2 (fn2-u32 (logxor s2 tmp)))
         (s3 (fn2-rotl32 s3 11)))
    (mv result s0 s1 s2 s3)))
(defthm fn2-prng-next-types
  (and (unsigned-byte-p 32 (mv-nth 0 (fn2-prng-next s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 1 (fn2-prng-next s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 2 (fn2-prng-next s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 3 (fn2-prng-next s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 4 (fn2-prng-next s0 s1 s2 s3))))
  :hints (("Goal" :in-theory (disable unsigned-byte-p logxor))))
(in-theory (disable fn2-prng-next))
(fn2-word-facts fn2-prng-next-0 (car (fn2-prng-next s0 s1 s2 s3)) fn2-prng-next-types)
(fn2-word-facts fn2-prng-next-1 (mv-nth 1 (fn2-prng-next s0 s1 s2 s3)) fn2-prng-next-types)
(fn2-word-facts fn2-prng-next-2 (mv-nth 2 (fn2-prng-next s0 s1 s2 s3)) fn2-prng-next-types)
(fn2-word-facts fn2-prng-next-3 (mv-nth 3 (fn2-prng-next s0 s1 s2 s3)) fn2-prng-next-types)
(fn2-word-facts fn2-prng-next-4 (mv-nth 4 (fn2-prng-next s0 s1 s2 s3)) fn2-prng-next-types)

; SplitMix-style Weyl sequence and avalanche, in the 32-bit domain. This is
; not SplitMix64's sequence: it is an explicitly versioned 32-bit expansion.
; Seed low/high u32 halves both influence all four words. Natural seeds
; are interpreted modulo 2^64 at init; no u64 runtime word is constructed.
(defun fn2-prng-mix32 (x)
  (declare (xargs :guard (unsigned-byte-p 32 x)))
  (let* ((x (fn2-u32 (logxor x (ash x -16))))
         (x (fn2-u32-mul x 2246822507))
         (x (fn2-u32 (logxor x (ash x -13))))
         (x (fn2-u32-mul x 3266489909)))
    (fn2-u32 (logxor x (ash x -16)))))
(defthm fn2-prng-mix32-type
  (unsigned-byte-p 32 (fn2-prng-mix32 x)))
(in-theory (disable fn2-prng-mix32))

(defun fn2-prng-seed (seed)
  (declare (xargs :guard (natp seed)))
  (let* ((lo (fn2-u32 seed))
         (hi (fn2-u32 (floor seed 4294967296)))
         (x (fn2-u32 (logxor lo (fn2-prng-mix32 hi))))
         (s0 (fn2-prng-mix32 (fn2-u32 (+ x 2654435769))))
         (s1 (fn2-prng-mix32 (fn2-u32 (+ x 1013904242))))
         (s2 (fn2-prng-mix32 (fn2-u32 (+ x 3668340011))))
         (s3 (fn2-prng-mix32 (fn2-u32 (+ x 2027808484)))))
    (mv (if (= (+ s0 s1 s2 s3) 0) 1 s0) s1 s2 s3)))
(defthm fn2-prng-seed-types
  (and (unsigned-byte-p 32 (mv-nth 0 (fn2-prng-seed seed)))
       (unsigned-byte-p 32 (mv-nth 1 (fn2-prng-seed seed)))
       (unsigned-byte-p 32 (mv-nth 2 (fn2-prng-seed seed)))
       (unsigned-byte-p 32 (mv-nth 3 (fn2-prng-seed seed))))
  :hints (("Goal" :in-theory (disable unsigned-byte-p logxor))))
(in-theory (disable fn2-prng-seed))
(fn2-word-facts fn2-prng-seed-0 (car (fn2-prng-seed seed)) fn2-prng-seed-types)
(fn2-word-facts fn2-prng-seed-1 (mv-nth 1 (fn2-prng-seed seed)) fn2-prng-seed-types)
(fn2-word-facts fn2-prng-seed-2 (mv-nth 2 (fn2-prng-seed seed)) fn2-prng-seed-types)
(fn2-word-facts fn2-prng-seed-3 (mv-nth 3 (fn2-prng-seed seed)) fn2-prng-seed-types)

; Fixed-work reduction has at most 1/2^32 absolute bucket bias. Rejection
; sampling would have unbounded work; simulation does not claim uniformity.
(defun fn2-prng-below (n s0 s1 s2 s3)
  (declare (xargs :guard (and (posp n) (unsigned-byte-p 32 n)
                              (unsigned-byte-p 32 s0) (unsigned-byte-p 32 s1)
                              (unsigned-byte-p 32 s2) (unsigned-byte-p 32 s3))))
  (mv-let (word s0 s1 s2 s3) (fn2-prng-next s0 s1 s2 s3)
    (mv (mod word (if (posp n) n 1)) s0 s1 s2 s3)))

(defthm fn2-prng-below-types
  (and (natp (mv-nth 0 (fn2-prng-below n s0 s1 s2 s3)))
       (implies (posp n) (< (mv-nth 0 (fn2-prng-below n s0 s1 s2 s3)) n))
       (unsigned-byte-p 32 (mv-nth 1 (fn2-prng-below n s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 2 (fn2-prng-below n s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 3 (fn2-prng-below n s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 4 (fn2-prng-below n s0 s1 s2 s3))))
  :hints (("Goal" :in-theory (disable logxor))))
(in-theory (disable fn2-prng-below))
(fn2-word-facts fn2-prng-below-1 (mv-nth 1 (fn2-prng-below n s0 s1 s2 s3)) fn2-prng-below-types)
(fn2-word-facts fn2-prng-below-2 (mv-nth 2 (fn2-prng-below n s0 s1 s2 s3)) fn2-prng-below-types)
(fn2-word-facts fn2-prng-below-3 (mv-nth 3 (fn2-prng-below n s0 s1 s2 s3)) fn2-prng-below-types)
(fn2-word-facts fn2-prng-below-4 (mv-nth 4 (fn2-prng-below n s0 s1 s2 s3)) fn2-prng-below-types)

(defun fn2-prng-chance (num den s0 s1 s2 s3)
  (declare (xargs :guard (and (natp num) (posp den) (<= num den)
                              (unsigned-byte-p 32 den)
                              (unsigned-byte-p 32 s0) (unsigned-byte-p 32 s1)
                              (unsigned-byte-p 32 s2) (unsigned-byte-p 32 s3))))
  (mv-let (word s0 s1 s2 s3) (fn2-prng-below den s0 s1 s2 s3)
    (mv (< word num) s0 s1 s2 s3)))

(defthm fn2-prng-chance-types
  (and (booleanp (mv-nth 0 (fn2-prng-chance num den s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 1 (fn2-prng-chance num den s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 2 (fn2-prng-chance num den s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 3 (fn2-prng-chance num den s0 s1 s2 s3)))
       (unsigned-byte-p 32 (mv-nth 4 (fn2-prng-chance num den s0 s1 s2 s3))))
  :hints (("Goal" :in-theory (disable logxor))))
(in-theory (disable fn2-prng-chance))
(fn2-word-facts fn2-prng-chance-1 (mv-nth 1 (fn2-prng-chance num den s0 s1 s2 s3)) fn2-prng-chance-types)
(fn2-word-facts fn2-prng-chance-2 (mv-nth 2 (fn2-prng-chance num den s0 s1 s2 s3)) fn2-prng-chance-types)
(fn2-word-facts fn2-prng-chance-3 (mv-nth 3 (fn2-prng-chance num den s0 s1 s2 s3)) fn2-prng-chance-types)
(fn2-word-facts fn2-prng-chance-4 (mv-nth 4 (fn2-prng-chance num den s0 s1 s2 s3)) fn2-prng-chance-types)
(assert-event (not (equal (mv-list 4 (fn2-prng-seed 0))
                           (mv-list 4 (fn2-prng-seed 4294967296)))))

(assert-event (equal (mv-list 5 (fn2-prng-next 1 2 3 4))
                     '(11520 7 0 1026 12288)))
(assert-event (equal (fn2-u32-mul 4294967295 4294967295) 1))
(assert-event (fn2-profile-exports-compliant-p
  '(fn2-prng-next fn2-prng-seed fn2-prng-below fn2-prng-chance) (w state)))
