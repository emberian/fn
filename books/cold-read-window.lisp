; Selected-layout inventory for one private raw extent window.
; This is a source allocation model, not an allocator refinement or an
; activation gate. See the adjacent evidence inventory for outstanding joins.
(in-package "ACL2")
(include-book "cold-read-layout")

(defun fn-crw-nth (n x)
  (declare (xargs :guard (natp n)))
  (if (consp x) (if (zp n) (car x) (fn-crw-nth (1- n) (cdr x))) nil))

; Inspect at most seven cells even on malformed external input.
(defun fn-crw-naturals (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) (null x)
    (and (consp x) (natp (car x)) (fn-crw-naturals (1- n) (cdr x)))))

; Native pread uses signed off_t. The end includes the integrity trailer.
; This is the selected ABI's representability condition, not a data policy.
(defun fn-crw-supportedp (descriptor ticket)
  (declare (xargs :guard t))
  (and (fn-crw-naturals 7 descriptor) (natp ticket)
       (posp (fn-crw-nth 0 descriptor))
       (<= (nfix (fn-crw-nth 1 descriptor)) (nfix (fn-crw-nth 3 descriptor)))
       (<= (+ (nfix (fn-crw-nth 3 descriptor)) (nfix (fn-crw-nth 4 descriptor)))
           (+ (nfix (fn-crw-nth 1 descriptor)) (nfix (fn-crw-nth 2 descriptor))))
       (<= (nfix (fn-crw-nth 5 descriptor)) (nfix (fn-crw-nth 4 descriptor)))
       (< (nfix (fn-crw-nth 6 descriptor)) (expt 2 257))
       (<= (+ (nfix (fn-crw-nth 1 descriptor)) (nfix (fn-crw-nth 2 descriptor)) 32)
           (- (expt 2 63) 1))))

; Raw backing only: fixed output stobj, fresh input stobj including its
; empty pre-reserve vector, native trailer vector, digest16 + frame slots64.
(defun fn-crw-backing-octets ()
  (declare (xargs :guard t))
  (+ (fn-crl-array-octets 1 8) (fn-crl-array-octets 16384 1)
     (fn-crl-array-octets 2 8) (fn-crl-array-octets 0 1)
     (fn-crl-array-octets 64 1) (fn-crl-array-octets 32 1)
     (fn-crl-array-octets 16 8) (fn-crl-array-octets 64 8)))

; Highwater includes inactive retained frames. The caller's block16 and
; the maximum ROOT path394 are separate from the retained CV/output lists.
(defun fn-crw-digest-conses ()
  (declare (xargs :guard t))
  (+ (* 64 13) 8 5 16 394 16))

; Simultaneously fund old/new plan14, three captures12, four effects7,
; descriptor7/token9, ledger binding5, outer MV12, copy span3, publication6,
; and read trailer32/result32. Counting all paths together overestimates
; coexistence; it does not assume compiled multiple values allocate nothing.
(defun fn-crw-controller-conses ()
  (declare (xargs :guard t))
  (+ (* 2 14) (* 3 12) (* 4 7) 7 9 5 12 3 6 32 32))

(defun fn-crw-natural-ceiling (descriptor ticket)
  (declare (xargs :guard t))
  ; The ledger spends NEXT before constructing the returned lease. At a
  ; digit boundary NEXT+1 can need more retained limbs than NEXT itself.
  (max (max (+ 1 (nfix ticket)) (nfix (fn-crw-nth 0 descriptor)))
       (max (+ (nfix (fn-crw-nth 1 descriptor)) (nfix (fn-crw-nth 2 descriptor)) 32)
            (- (expt 2 257) 1))))

; Pre-normalization allocation for the selected positive primitive paths.
; A bignum input has ceil((bits+1)/64) digits. SBCL add/sub and multiply
; by a positive fixnum allocate an extra digit, even if normalization later
; reduces the header. Charge the allocated extent, not the normalized value.
(defun fn-crw-primitive-buffer-octets (magnitude)
  (declare (xargs :guard t))
  (fn-crl-align16
   (+ 8 (* 8 (+ 1 (max 1 (ceiling (+ 1 (integer-length (nfix magnitude))) 64)))))))

; Positive power-of-two CEILING can allocate a quotient and its successor;
; two extra-digit buffers dominate that path as well as one add/sub buffer
; and positive multiplication (whose result has at most twice input digits).
; This is NOT an envelope for signed multiplication/general bignum division,
; EXPT, ratios, compiler helpers or unknown runtime paths.
(defun fn-crw-positive-primitive-octets (magnitude)
  (declare (xargs :guard t))
  (* 2 (fn-crw-primitive-buffer-octets magnitude)))

; ROOT packs32 bytes with32 positive *256 and32 positive adds. Every input
; has at most256 bits. The selected runtime allocates the extra digit before
; normalization, so64 bytes/object rather than the normalized48-byte u256.
(defun fn-crw-root-primitive-octets ()
  (declare (xargs :guard t))
  (* 64 (fn-crw-primitive-buffer-octets (- (expt 2 256) 1))))

; Current staged raw/cancel/current-getter conservative call-list inventory
; is250 conses, including the retained result, against a256 reserve. Literal
; cold macros avoid an outer pool REST/APPEND layer. This is a coexistence
; source inventory, not cumulative compiled allocation. Borrowed argument payloads
; are already owned; these lists do not create another integer per cell.
(defun fn-crw-native-wrapper-conses ()
  (declare (xargs :guard t)) 256)

; Every retained payload and digest slot receives its own maximum box.
; The128 high-level scalar-operation inventory separately receives the
; reviewed positive primitive envelope. Its magnitude is overcharged at
; the full descriptor/ticket ceiling (actual digest scalars have<=67bits).
; The source-count/runtime-path join is explicitly pending, not a compiler
; theorem. See window-source and arithmetic-source evidence beside it.
(defun fn-crw-source-octets (descriptor ticket)
  (declare (xargs :guard t))
  (let* ((conses (+ (fn-crw-digest-conses) (fn-crw-controller-conses)))
         (magnitude (fn-crw-natural-ceiling descriptor ticket))
         (integer-octets (fn-crl-natural-octets magnitude)))
    (+ (fn-crw-backing-octets) (* 16 (+ conses (fn-crw-native-wrapper-conses)))
       ; Another32 native scalar boxes overestimate got/fill/effect scalar
       ; coexistence. Actual raw wrapper uses issued offset/count directly.
       (* (+ conses 16 64 32) integer-octets)
       (* 128 (fn-crw-positive-primitive-octets magnitude))
       (fn-crw-root-primitive-octets))))

; Per-job resident model has collector coexistence; shared descriptors,
; native idle workers and removal scratch remain in permanent baseline.
; The staged physical admission entry consumes this sourced demand.
; Selected-runtime adequacy and funded startup/default activation remain owed.
(defun fn-crw-job-demand (descriptor ticket)
  (declare (xargs :guard t))
  (and (fn-crw-supportedp descriptor ticket)
       (list (* 2 (fn-crw-source-octets descriptor ticket)) 0 0 1 1)))

; Compressed STORAGE ONLY, never a complete job demand. All three byte
; buffers are fresh pre-reserved fn-octets instances. The20 natural decoder
; registers are general vectors, and credited input may reach2*C.
(defun fn-crw-decoder-backing-octets (compressed expected)
  (declare (xargs :guard t))
  (+ (* 3 (+ (fn-crl-array-octets 2 8) (fn-crl-array-octets 0 1)))
     (fn-crl-array-octets 65536 1) (fn-crl-array-octets 3494 1)
     (fn-crl-array-octets 64 1) (fn-crl-array-octets 1 8)
     (fn-crl-array-octets 20 8)
     (* 20 (fn-crl-natural-octets
            (max (+ 1 (nfix expected))
                 (max (* 2 (nfix compressed)) (+ 65536 (* 256 (nfix compressed)))))))))

(defthm fn-crw-demand-requires-representable-trailer-end
  (implies (fn-crw-job-demand descriptor ticket)
           (<= (+ (nfix (fn-crw-nth 1 descriptor)) (nfix (fn-crw-nth 2 descriptor)) 32)
               (- (expt 2 63) 1)))
  :rule-classes nil)

(defthm fn-crw-demand-credits-by-definition
  (implies (fn-crw-job-demand descriptor ticket)
           (equal (cdr (fn-crw-job-demand descriptor ticket)) '(0 0 1 1)))
  :rule-classes nil)

(defthm fn-crw-natural-ceiling-covers-next-ticket-by-definition
  (<= (+ 1 (nfix ticket)) (fn-crw-natural-ceiling descriptor ticket))
  :rule-classes nil)

(in-theory (disable fn-crw-nth fn-crw-naturals fn-crw-supportedp
                    fn-crw-backing-octets fn-crw-digest-conses
                    fn-crw-controller-conses fn-crw-natural-ceiling
                    fn-crw-primitive-buffer-octets fn-crw-positive-primitive-octets
                    fn-crw-root-primitive-octets fn-crw-native-wrapper-conses
                    fn-crw-source-octets fn-crw-job-demand
                    fn-crw-decoder-backing-octets))
