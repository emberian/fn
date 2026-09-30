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
  (max (max (nfix ticket) (nfix (fn-crw-nth 0 descriptor)))
       (max (+ (nfix (fn-crw-nth 1 descriptor)) (nfix (fn-crw-nth 2 descriptor)) 32)
            (- (expt 2 257) 1))))

; Charge each potential list payload and every digest vector slot as a
; separately boxed maximum natural, even when they actually share/fixnum.
; Source digest owner bounds another128 scalar results (span/power/counter,
; checks/ceiling) per step, at most67 bits for signed64 extents. ROOT's32
; multiply +32 add arithmetic temporaries are additional u256s.
(defun fn-crw-source-octets (descriptor ticket)
  (declare (xargs :guard t))
  (let* ((conses (+ (fn-crw-digest-conses) (fn-crw-controller-conses)))
         (integer-octets (fn-crl-natural-octets (fn-crw-natural-ceiling descriptor ticket))))
    (+ (fn-crw-backing-octets) (* 16 conses)
       (* (+ conses 16 64 128) integer-octets)
       (* 64 (fn-crl-natural-octets (- (expt 2 256) 1))))))

; Per-job resident model has collector coexistence; shared descriptors,
; native idle workers and removal scratch remain in permanent baseline.
; Not yet consumed by the physical admit entry: native activation and
; arithmetic transient inventory are explicitly still owed.
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

(in-theory (disable fn-crw-nth fn-crw-naturals fn-crw-supportedp
                    fn-crw-backing-octets fn-crw-digest-conses
                    fn-crw-controller-conses fn-crw-natural-ceiling
                    fn-crw-source-octets fn-crw-job-demand
                    fn-crw-decoder-backing-octets))
