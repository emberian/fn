; Six-word metadata entries streamed from a charged digest spool.
(in-package "ACL2")
(include-book "pagestore-exec")
(include-book "history-page-buffer")

(defun fn-hpm-word (component address digest)
  (declare (xargs :guard (and (natp component) (< component 6)
                              (unsigned-byte-p 64 address)
                              (unsigned-byte-p 256 digest))))
  (cond ((equal component 0) address)
        ((equal component 1) 1)
        ((equal component 2) (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi digest)))))
        ((equal component 3) (pgs-dlo (pgs-dhi (pgs-dhi digest))))
        ((equal component 4) (pgs-dlo (pgs-dhi digest)))
        (t (pgs-dlo digest))))

(defthm fn-hpm-word-refines-current-entry
  (implies (and (natp component) (< component 6)
                (unsigned-byte-p 64 address))
           (equal (fn-hpm-word component address digest)
                  (nth component (pgs-entry-words (list address 1 digest)))))
  :hints (("Goal" :in-theory (enable pgs-entry-words nth))))

(defthm fn-hpm-word-is-u64
  (implies (unsigned-byte-p 64 address)
           (unsigned-byte-p 64 (fn-hpm-word component address digest)))
  :hints (("Goal" :in-theory (disable pgs-dhi))))

; The source authority must bind supplied DIGEST to this ordinal. Store the
; returned u256 scalar for its six components; never collect all digests.
(defun fn-hpm-request (ordinal component entries base)
  (declare (xargs :guard (and (unsigned-byte-p 64 ordinal)
                              (natp component) (< component 6)
                              (unsigned-byte-p 64 entries)
                              (unsigned-byte-p 64 base))))
  (cond ((<= entries ordinal) (list :padding 0))
        ((<= 18446744073709551616 (+ base ordinal)) (list :refused :address))
        (t (list :entry ordinal component (+ base ordinal)))))

(defun fn-hpm-put (component address digest fn-hpb)
  (declare (xargs :stobjs fn-hpb
                  :guard (and (natp component) (< component 6)
                              (unsigned-byte-p 64 address)
                              (unsigned-byte-p 256 digest))
                  :guard-hints (("Goal" :in-theory (disable fn-hpm-word-refines-current-entry)))))
  (fn-hpb-put (fn-hpm-word component address digest) fn-hpb))

(defthm fn-hpm-put-refines-current-entry-effect
  (implies (and (natp component) (< component 6)
                (unsigned-byte-p 64 address)
                (natp (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048))
           (and (equal (mv-nth 0 (fn-hpm-put component address digest fn-hpb)) :stored)
                (equal (fn-hpb-prefix (mv-nth 1 (fn-hpm-put component address digest fn-hpb)))
                       (append (fn-hpb-prefix fn-hpb)
                               (list (nth component (pgs-entry-words (list address 1 digest))))))))
  :hints (("Goal" :in-theory (disable fn-hpm-word pgs-entry-words fn-hpb-used))))

(defthm fn-hpm-put-keeps-concrete
  (implies (and (fn-hpbp fn-hpb) (unsigned-byte-p 64 address))
           (fn-hpbp (mv-nth 1 (fn-hpm-put component address digest fn-hpb))))
  :hints (("Goal" :in-theory (disable fn-hpbp fn-hpm-word-refines-current-entry))))

(defthm fn-hpm-put-keeps-identities
  (and (equal (fn-hpb-epoch (mv-nth 1 (fn-hpm-put component address digest fn-hpb)))
              (fn-hpb-epoch fn-hpb))
       (equal (fn-hpb-lease (mv-nth 1 (fn-hpm-put component address digest fn-hpb)))
              (fn-hpb-lease fn-hpb)))
  :hints (("Goal" :in-theory (disable fn-hpb-epoch fn-hpb-lease))))

(in-theory (disable fn-hpm-word fn-hpm-request fn-hpm-put))

; Proof-only image model. Execution borrows a single spool digest at a time.
(defun fn-hpm-model-entries (digests base)
  (declare (xargs :guard (and (true-listp digests) (natp base))))
  (if (atom digests) nil
    (cons (list base 1 (car digests))
          (fn-hpm-model-entries (cdr digests) (+ 1 base)))))

(local
 (defthm fn-hpm-entry-length
   (equal (len (pgs-entry-words e)) 6)
   :hints (("Goal" :in-theory (enable pgs-entry-words)))))
(local
 (defthm fn-hpm-nth-append
   (implies (and (natp i) (<= (len a) i))
            (equal (nth i (append a b)) (nth (- i (len a)) b)))
   :hints (("Goal" :in-theory (enable nth) :induct (nth i a)))))
(local
 (defthm fn-hpm-nth-prefix
   (implies (and (natp i) (< i (len a)))
            (equal (nth i (append a b)) (nth i a)))
   :hints (("Goal" :in-theory (enable nth) :induct (nth i a)))))
(local
 (defun fn-hpm-index-ind (k ds base)
   (if (zp k) (list ds base)
     (fn-hpm-index-ind (1- k) (cdr ds) (+ 1 base)))))

(defthm fn-hpm-entry-at-stream-position
  (implies (and (natp base) (natp k) (< k (len digests))
                (natp component) (< component 6))
           (equal (nth (+ (* 6 k) component)
                       (pgs-entries-words (fn-hpm-model-entries digests base)))
                  (nth component (pgs-entry-words (list (+ base k) 1 (nth k digests))))))
  :hints (("Goal" :induct (fn-hpm-index-ind k digests base)
           :expand ((fn-hpm-model-entries digests base))
           :in-theory (e/d (pgs-entries-words nth)
                            (pgs-entry-words)))))

(local
 (defthm fn-hpm-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-hpm-entries-word-count
   (equal (len (pgs-entries-words (fn-hpm-model-entries digests base)))
          (* 6 (len digests)))
   :hints (("Goal" :induct (fn-hpm-model-entries digests base)
            :in-theory (enable pgs-entries-words)))))
(local
 (defthm fn-hpm-model-count
   (equal (len (fn-hpm-model-entries digests base)) (len digests))))

(defthm fn-hpm-word-refines-directory-run
  (implies (and (natp base) (natp k) (< k (len digests))
                (natp component) (< component 6)
                (unsigned-byte-p 64 (+ base k)))
           (equal (fn-hpm-word component (+ base k) (nth k digests))
                  (nth (+ (* 6 k) component)
                       (pgs-encode-run (fn-hpm-model-entries digests base) m))))
  :hints (("Goal" :use ((:instance fn-hpm-entry-at-stream-position))
           :in-theory (e/d (pgs-encode-run)
                            (fn-hpm-word pgs-entry-words
                             fn-hpm-entry-at-stream-position
                             pgs-entries-words fn-hpm-model-entries))))
  :rule-classes nil)

(local
 (defun fn-hpm-zero-ind (i n)
   (if (zp i) n (fn-hpm-zero-ind (1- i) (1- n)))))
(local
 (defthm fn-hpm-nth-zero
   (implies (and (natp i) (natp n) (< i n))
            (equal (nth i (pgs-zeros n)) 0))
   :hints (("Goal" :induct (fn-hpm-zero-ind i n)
            :in-theory (enable nth pgs-zeros)))))

(defthm fn-hpm-directory-padding-is-zero
  (implies (and (natp i) (natp m)
                (<= (* 6 (len digests)) i) (< i (* 2048 m)))
           (equal (nth i (pgs-encode-run (fn-hpm-model-entries digests base) m)) 0))
  :hints (("Goal" :in-theory (e/d (pgs-encode-run)
                                    (pgs-zeros pgs-entries-words fn-hpm-model-entries)))))

(defthm fn-hpm-table-is-single-page-run
  (equal (pgs-encode-table (fn-hpm-model-entries digests base))
         (pgs-encode-run (fn-hpm-model-entries digests base) 1))
  :hints (("Goal" :in-theory (enable pgs-encode-table pgs-encode-run))))

; A directory run can cross page boundaries in the middle of an entry.
; Ordinal/component survives scratch reset. REMAINING is the admitted run's
; total remaining word count, not a work quantum. A full page yields unchanged.
(defun fn-hpm-tick (ordinal component remaining entries base digest fn-hpb)
  (declare (xargs :stobjs fn-hpb
                  :guard (and (unsigned-byte-p 64 ordinal)
                              (natp component) (< component 6)
                              (unsigned-byte-p 64 remaining)
                              (unsigned-byte-p 64 entries)
                              (unsigned-byte-p 64 base)
                              (unsigned-byte-p 256 digest))
                  :guard-hints (("Goal" :use ((:instance fn-hpm-word-is-u64 (address (+ base ordinal))))
                                :in-theory (disable fn-hpm-word-refines-current-entry fn-hpm-word-is-u64)))))
  (cond ((zp remaining) (mv :done ordinal component remaining fn-hpb))
        ((<= 2048 (fn-hpb-used fn-hpb)) (mv :page-full ordinal component remaining fn-hpb))
        ((and (< ordinal entries) (<= 18446744073709551616 (+ base ordinal)))
         (mv :refused ordinal component remaining fn-hpb))
        ((and (equal component 5) (equal ordinal 18446744073709551615))
         (mv :refused ordinal component remaining fn-hpb))
        (t
         (mv-let (v fn-hpb)
           (fn-hpb-put (if (< ordinal entries)
                          (fn-hpm-word component (+ base ordinal) digest) 0) fn-hpb)
           (declare (ignore v))
           (mv :stored (if (equal component 5) (+ 1 ordinal) ordinal)
               (if (equal component 5) 0 (+ 1 component))
               (1- remaining) fn-hpb)))))

(defthm fn-hpm-tick-progress
  (implies (equal (mv-nth 0 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb))
                  :stored)
           (and (equal (mv-nth 3 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb))
                       (1- remaining))
                (equal (+ (* 6 (mv-nth 1 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))
                          (mv-nth 2 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))
                       (+ 1 (* 6 ordinal) component))))
  :hints (("Goal" :in-theory (disable fn-hpb-put fn-hpb-ready fn-hpm-word))))

(defthm fn-hpm-tick-refines-emission-effect
  (implies (and (natp (fn-hpb-used fn-hpb))
                (equal (mv-nth 0 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb))
                        :stored))
           (equal (fn-hpb-prefix
                   (mv-nth 4 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))
                  (append (fn-hpb-prefix fn-hpb)
                          (list (if (< ordinal entries)
                                    (fn-hpm-word component (+ base ordinal) digest) 0)))))
  :hints (("Goal" :in-theory (e/d (fn-hpb-ready)
                                  (fn-hpb-put fn-hpb-used fn-hpm-word)))))

(in-theory (disable fn-hpm-tick))

(defthm fn-hpm-tick-keeps-identities
  (and (equal (fn-hpb-epoch (mv-nth 4 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))
              (fn-hpb-epoch fn-hpb))
       (equal (fn-hpb-lease (mv-nth 4 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))
              (fn-hpb-lease fn-hpb)))
  :hints (("Goal" :in-theory (e/d (fn-hpm-tick)
                                  (fn-hpb-epoch fn-hpb-lease fn-hpb-put fn-hpm-word)))))

(defthm fn-hpm-tick-keeps-concrete
  (implies (and (fn-hpbp fn-hpb) (natp base) (natp ordinal))
           (fn-hpbp (mv-nth 4 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb))))
  :hints (("Goal" :use ((:instance fn-hpm-word-is-u64 (address (+ base ordinal))))
           :in-theory (e/d (fn-hpm-tick)
                            (fn-hpbp fn-hpb-put fn-hpm-word fn-hpm-word-is-u64
                             fn-hpm-word-refines-current-entry)))))

(defthm fn-hpm-tick-refines-directory-effect
  (implies (and (natp base) (natp ordinal) (< ordinal (len digests))
                (natp component) (< component 6)
                (unsigned-byte-p 64 (+ base ordinal))
                (equal entries (len digests))
                (equal digest (nth ordinal digests))
                (natp (fn-hpb-used fn-hpb))
                (equal (mv-nth 0 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) :stored))
           (equal (fn-hpb-prefix
                   (mv-nth 4 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))
                  (append (fn-hpb-prefix fn-hpb)
                          (list (nth (+ (* 6 ordinal) component)
                                     (pgs-encode-run (fn-hpm-model-entries digests base) m))))))
  :hints (("Goal" :use ((:instance fn-hpm-word-refines-directory-run (k ordinal)))
           :in-theory (disable fn-hpb-prefix fn-hpb-used fn-hpm-word
                               pgs-entry-words pgs-encode-run fn-hpm-model-entries)))
  :rule-classes nil)

(defthm fn-hpm-tick-preserves-scalar-domain
  (implies (and (unsigned-byte-p 64 ordinal)
                (natp component) (< component 6)
                (unsigned-byte-p 64 remaining))
           (and (unsigned-byte-p 64
                 (mv-nth 1 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))
                (natp (mv-nth 2 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))
                (< (mv-nth 2 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) 6)
                (unsigned-byte-p 64
                 (mv-nth 3 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)))))
  :hints (("Goal" :in-theory (e/d (fn-hpm-tick)
                                  (fn-hpb-put fn-hpb-used fn-hpm-word)))))

(defthm fn-hpm-tick-nonstored-unchanged
  (implies (not (equal (mv-nth 0 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) :stored))
           (and (equal (mv-nth 1 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) ordinal)
                (equal (mv-nth 2 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) component)
                (equal (mv-nth 3 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) remaining)
                (equal (mv-nth 4 (fn-hpm-tick ordinal component remaining entries base digest fn-hpb)) fn-hpb)))
  :hints (("Goal" :in-theory (e/d (fn-hpm-tick)
                                  (fn-hpb-put fn-hpb-used fn-hpm-word)))))
