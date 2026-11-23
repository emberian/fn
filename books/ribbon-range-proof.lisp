; Proofs for the range adapter.
(in-package "ACL2")

(include-book "ribbon")
(include-book "range-window-proof")
(include-book "range-union-proof")

(local
 (defthm fn2-range-value-after-set
 (implies (and (natp i) (natp j))
          (equal (fn2-fields-value j (fn2-fields-set-value i v f))
                 (if (equal j i) v (fn2-fields-value j f))))
 :hints (("Goal" :in-theory (e/d (fn2-fields-set-value update-fn2-fields-value$ai nth-update-nth) (nth update-nth))))))
(local
 (defthm fn2-range-value-after-store
 (implies (and (natp i) (natp j) (< i (fn2-fields-rows f))
               (unsigned-byte-p 60 v) (unsigned-byte-p 32 slot)
               (unsigned-byte-p 60 gen) (unsigned-byte-p 32 off)
               (unsigned-byte-p 32 size) (unsigned-byte-p 8 status))
          (equal (fn2-fields-value j (fn2-layout-store i v slot gen off size status f))
                 (if (equal i j) v (fn2-fields-value j f))))
 :hints (("Goal" :in-theory (e/d (fn2-layout-store) (unsigned-byte-p nth update-nth fn2-fields-rows))))))
(local
 (defthm fn2-range-value-after-copy
 (implies (and (fn2-fieldsp f) (fn2-fields-wfp f)
               (natp src) (< src (fn2-fields-rows f)) (natp dst) (< dst (fn2-fields-rows f)) (natp j))
          (equal (fn2-fields-value j (fn2-run-copy-row src dst f))
                 (fn2-fields-value (if (equal j dst) src j) f)))
 :hints (("Goal" :in-theory (e/d (fn2-run-copy-row)
                                 (fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-fields-value fn2-fields-ref-slot
                                  fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len fn2-fields-status))))))
(local
 (defthm fn2-range-u60-increment-fits
 (implies (unsigned-byte-p 60 v)
          (equal (unsigned-byte-p 60 (+ 1 v))
                 (not (equal v (1- (expt 2 60))))))
 :hints (("Goal" :cases ((< v (1- (expt 2 60))))))))
(local
 (defthm fn2-range-field-u60
 (implies (and (fn2-fieldsp f) (fn2-fields-wfp f) (natp i) (< i (fn2-fields-rows f)))
          (unsigned-byte-p 60 (fn2-fields-value i f)))
 :hints (("Goal" :use ((:instance fn2-fields-value-bound (fn2-fields f)))
          :in-theory (disable fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-fields-value)))))

; The served successor computes both components and reports whole-key overflow.
(defthm fn2-overview-range-successor
 (implies (and (fn2-fieldsp f) (fn2-fields-wfp f)
               (natp eb) (natp qb)
               (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
               (<= (+ qb *fn2-run-entry-rows*) (fn2-fields-rows f))
               (or (< (+ eb 1) qb) (< (+ qb 1) eb)))
          (let* ((group (fn2-fields-value eb f))
                 (number (fn2-fields-value (+ eb 1) f))
                 (carry (equal number (1- (expt 2 60))))
                 (end (and carry (equal group (1- (expt 2 60)))))
                 (out (fn2-range-successor 3 eb qb f))
                 (after (mv-nth 1 out)))
            (and (equal (mv-nth 0 out) (if end :end :ok))
                 (equal (fn2-fields-value qb after)
                        (if end 0 (if carry (+ 1 group) group)))
                 (equal (fn2-fields-value (+ 1 qb) after)
                        (if carry 0 (+ 1 number))))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (a b f) (fn2-range-copy-rows 2 a b f))
                  (:free (a b f) (fn2-range-copy-rows 1 a b f))
                  (:free (a b f) (fn2-range-copy-rows 0 a b f))
                  (:free (b f) (fn2-range-carry 2 b f))
                  (:free (b f) (fn2-range-carry 1 b f))
                  (:free (b f) (fn2-range-carry 0 b f)))
          :in-theory
          (e/d (fn2-range-successor fn2-range-copy-rows fn2-range-carry)
               (unsigned-byte-p fn2-run-copy-row fn2-fields-set-value fn2-fields-value
                fn2-fields-rows fn2-fieldsp fn2-fields-wfp)))))

(local
 (defthm fn2-range-integer-gap
  (implies (and (integerp x) (integerp y))
           (equal (< y (+ 1 x)) (<= y x)))))

; A re-seek from the new query admits precisely the keys following the
; delivered entry. At the last pair there is no such candidate.
(defthm fn2-overview-range-resume-order
 (implies (and (fn2-fieldsp f) (fn2-fields-wfp f) (natp eb) (natp qb)
               (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
               (<= (+ qb *fn2-run-entry-rows*) (fn2-fields-rows f))
               (or (< (+ eb 1) qb) (< (+ qb 1) eb))
               (unsigned-byte-p 60 group) (unsigned-byte-p 60 number))
   (let* ((key '((group (:id group)) (number (:id group-number))))
          (candidate (list group number))
          (old (list (fn2-fields-value eb f) (fn2-fields-value (+ 1 eb) f)))
          (out (fn2-range-successor 3 eb qb f))
          (after (mv-nth 1 out))
          (resume (list (fn2-fields-value qb after) (fn2-fields-value (+ 1 qb) after))))
     (iff (eq (fn2-run-key-order-spec key old candidate) :lt)
          (and (eq (mv-nth 0 out) :ok)
               (not (eq (fn2-run-key-order-spec key candidate resume) :lt))))))
 :rule-classes nil
 :hints (("Goal" :use (fn2-overview-range-successor
                        (:instance fn2-range-field-u60 (i eb))
                        (:instance fn2-range-field-u60 (i (+ 1 eb))))
          :in-theory (disable fn2-fields-value fn2-fieldsp fn2-fields-wfp fn2-fields-rows))))

(defthm fn2-overview-seek-narrow-bounds
 (let* ((g (fn2-seeks-g k s)) (out (fn2-ranges-out g r))
        (n (nfix (fn2-fields-value (+ 1 out) f)))
        (pos (nfix (fn2-fields-value (+ 3 out) f)))
        (lower (and (eq code :entry) (<= pos (fn2-seeks-after k s))))
        (res (fn2-seek-narrow k code s r f)) (after (mv-nth 1 res)))
   (implies (and (natp k) (< k (fn2-seeks-rows s))
                 (natp g) (< g (fn2-ranges-rows r))
                 (or (eq code :end)
                     (and (eq code :entry) (equal (fn2-ranges-schema g r) 3)
                          (equal (fn2-seeks-pfield k s) 3) (natp out)
                          (< (+ out 3) (fn2-fields-rows f))
                          (unsigned-byte-p 60 (1+ n)))))
            (and (equal (mv-nth 0 res) :more)
                 (equal (fn2-seeks-phase k after) *fn2-seek-phase-probe*)
                 (equal (fn2-seeks-lo k after) (if lower (1+ n) (fn2-seeks-lo k s)))
                 (equal (fn2-seeks-hi k after) (if lower (fn2-seeks-hi k s) (fn2-seeks-mid k s))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn2-seek-narrow fn2-seeks-set-lo fn2-seeks-set-hi fn2-seeks-set-phase
                update-fn2-seeks-lo$ai update-fn2-seeks-hi$ai update-fn2-seeks-phase$ai nth-update-nth)
               (nth update-nth fn2-ranges-schema fn2-ranges-rows fn2-ranges-out
                fn2-seeks-g fn2-seeks-rows fn2-seeks-pfield fn2-seeks-after
                fn2-fields-rows fn2-fields-value unsigned-byte-p nfix)))))

; Given the first row of the specified window (or :end for an empty
; window), the concrete seek update preserves the answer and its bounds.
(defthm fn2-overview-seek-narrow-preserves-answer
 (let* ((g (fn2-seeks-g k s)) (out (fn2-ranges-out g r))
        (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
        (p (fn2-seeks-after k s)) (window (fn2-overview-probe-window es group mid hi))
        (code (if (consp window) :entry :end)) (entry (car window))
        (ans (fn2-range-seek-scan es (list group) 2 p hi 3 0))
        (res (fn2-seek-narrow k code s r f)) (after (mv-nth 1 res)))
   (implies (and (natp group) (natp k) (< k (fn2-seeks-rows s))
                 (natp g) (< g (fn2-ranges-rows r))
                 (equal (fn2-ranges-schema g r) 3) (equal (fn2-seeks-pfield k s) 3)
                 (natp out) (< (+ out 3) (fn2-fields-rows f))
                 (natp mid) (unsigned-byte-p 60 hi) (< mid hi)
                 (fn2-range-natural-keysp es)
                 (fn2-run-sorted-spec *fn2-overview-range-key* es)
                 (fn2-range-monotone-scan es (list group) 3 -1)
                 (<= (fn2-seeks-lo k s) ans)
                 (implies (consp window)
                          (and (equal (fn2-fields-value (+ 1 out) f) (cadr entry))
                               (equal (fn2-fields-value (+ 3 out) f) (nth 3 entry)))))
            (and (equal (mv-nth 0 res) :more)
                 (equal (fn2-range-seek-scan es (list group) 2 p (fn2-seeks-hi k after) 3 0) ans)
                 (<= (fn2-seeks-lo k after) ans))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-range-integer-gap
                              (x (fn2-fields-value (+ 1 (fn2-ranges-out (fn2-seeks-g k s) r)) f))
                              (y (fn2-range-seek-scan es (list group) 2 (fn2-seeks-after k s) (fn2-seeks-hi k s) 3 0)))
                       (:instance fn2-range-seek-scan-natp (prefix (list group)) (nk 2)
                                  (p (fn2-seeks-after k s)) (hi (fn2-seeks-hi k s)) (pidx 3) (acc 0))
                       (:instance fn2-overview-probe-first-key (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s)))
                       (:instance fn2-range-seek-upper-probe (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
                                  (p (fn2-seeks-after k s)) (last -1) (acc 0))
                       (:instance fn2-range-seek-lower-probe (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
                                  (p (fn2-seeks-after k s)) (acc 0))
                       (:instance fn2-overview-seek-narrow-bounds
                                  (code (if (consp (fn2-overview-probe-window es group (fn2-seeks-mid k s)
                                                                            (fn2-seeks-hi k s))) :entry :end))))
          :cases ((consp (fn2-overview-probe-window es group (fn2-seeks-mid k s) (fn2-seeks-hi k s))))
          :in-theory (union-theories (theory 'minimal-theory)
                        '(natp nfix unsigned-byte-p integer-range-p not eq mv-nth
                          fn2-range-integer-gap (:type-prescription fn2-range-seek-scan-natp)
                          (:executable-counterpart expt) (:executable-counterpart binary-+)
                          (:executable-counterpart unary--) (:executable-counterpart <)
                          (:executable-counterpart equal))))))

; FN2-RIBBON-NO-FALSE-NEGATIVE is not discharged here and has no known
; counterexample. Evaluated, it holds for one empty key; 256 distinct keys
; of 250 octets, each probed; 256 copies of one key; and 2,000 generated key
; sets of 1 to 256 keys with 256 queries each. Its proof follows the build,
; B's checker on the sealed page and every probe through the pool, both
; header codecs, the page writer and sealer and the incremental BLAKE3, and
; this book's closure holds only typing, well-formedness and frame lemmas
; for those. The facts it needs are the ones about this adapter's pages, not
; the general owed squares (FN2-POOL-BYTE-FILL, FN2-LAYOUT-ROUNDTRIP,
; FN2-FORMAT-PAGE-HEADER-ROUNDTRIP, FN2-RIBBON-HEADER-ROUNDTRIP,
; FN2-B3-INCREMENTAL-IS-BLAKE3). The ribbon-false-neg book chain, ending in
; books/ribbon-false-neg-discharge-proof.lisp, proves those page facts and
; discharges this square. A square takes one discharge, so this book does
; not repeat it.

; FN2-RIBBON-MUTATION-REFUSED stays owed and cannot be proved as stated. The
; check after the mutation is B's checker, which compares the page's BLAKE3
; digest with the parent-held words. Evaluated at KEYS = ((1 2 3)) (65 slots,
; so the payload ends at offset 209) and X = 1 for every OFF below 65536,
; the refusal is structural at offsets 0-3 (:BAD-MAGIC), 4 (:VERSION),
; 5 (:WRONG-KIND), 6 (:WRONG-HISTORY), 7 (:WRONG-INCARNATION),
; 8 (:WRONG-LOCATION), 9-10 (:WRONG-ALLOCATION), 12 and 209-65535
; (:NONZERO-PADDING). At 11 and at 13-208 the only refusal is :BAD-HASH.
; Those offsets are the rest of B's header, the filter header at
; *fn2-run-header-area* (96), the bytes up to *fn2-ribbon-base* (144) and
; the solution bytes. At those offsets the statement says that no filter
; page of up to 256 keys collides under BLAKE3 with a one-byte change of
; itself, and it carries no collision-freedom premise (compare
; FN2-FC-COLLISION-FREE-PAIRP in FN2-FORMAT-FRAME-BINDS-LOCATION). A
; counterexample is a BLAKE3 collision; a proof is a collision-resistance
; theorem about the hash.
