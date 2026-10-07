(in-package "ACL2")
(include-book "paged-checkpoint-image")
(include-book "paged-checkpoint-exec")
(include-book "statement-recover-stream")
(include-book "consumer-event-index")
(local (include-book "arithmetic/top" :dir :system))

(defconst *pcko-stub* t)

; -----------------------------------------------------------------------------
; The exec.  Every word of the image is read by `pcko-w' at the call site that
; also counts it (the READS threaded through), so the returned count is the
; number of words the open read.

(defun pcko-w (i pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (and (natp i) (< i (pgs-x-len 0 pgs-mem)))))
  (pgs-x-word 0 i pgs-mem))

(defun pcko-copy (pos n reads pgs-mem fn-octets)
  ; The N octets of the payload words from POS on into the buffer, eight to a
  ; word, the last word's low octets (`adt-tp-unpack').
  (declare (xargs :stobjs (pgs-mem fn-octets)
                  :measure (nfix n)
                  :guard (and (natp pos) (natp n) (natp reads)
                              (<= (+ pos (floor (+ n 7) 8)) (pgs-x-len 0 pgs-mem))
                              (fn-octets-p fn-octets))
                  :verify-guards nil))
  (if (and (natp n) (< 0 n))
      (let ((fn-octets (fn-octets-append-word (pcko-w pos pgs-mem) (min n 8) fn-octets)))
        (pcko-copy (1+ pos) (nfix (- n 8)) (1+ reads) pgs-mem fn-octets))
    (mv reads fn-octets)))

(defun pcko-tree (fn-octets)
  ; The tree the buffer's program decodes to, or :refused.
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let ((d (fn-scc-decode-tree (fn-octets-list fn-octets))))
    (if (and (consp d) (eq (car d) :ok) (consp (cdr d))) (list :ok (cadr d)) :refused)))

(defun pcko-tape (pos lim seq acc index reads pgs-mem fn-arena fn-octets)
  ; The events tape from word POS to LIM: tag, octet count, packed octets, one
  ; record at a time, until a word that is not the tag.
  ; (mv verdict acc index reads fn-arena fn-octets).
  (declare (xargs :stobjs (pgs-mem fn-arena fn-octets)
                  :measure (nfix (- (nfix lim) (nfix pos)))
                  :verify-guards nil))
  (if (and (natp pos) (natp lim) (< pos lim))
      (if (eql (pcko-w pos pgs-mem) 1)
          (if (< (+ pos 1) lim)
              (let* ((n (nfix (pcko-w (+ pos 1) pgs-mem)))
                     (nw (floor (+ n 7) 8))
                     (npos (+ pos 2 nw)))
                (if (<= npos lim)
                    (let ((fn-octets (fn-octets-clear fn-octets)))
                      (mv-let (reads fn-octets)
                        (pcko-copy (+ pos 2) n (+ reads 2) pgs-mem fn-octets)
                        (let ((d (pcko-tree fn-octets)))
                          (if (eq d :refused)
                              (mv :record acc index reads fn-arena fn-octets)
                            (mv-let (acc2 fn-arena)
                              (fn-ssr-intern-step acc (list (cadr d)) nil nil :resident nil fn-arena)
                              (if (eq acc2 :bad)
                                  (mv :intern acc2 index reads fn-arena fn-octets)
                                (pcko-tape npos lim (1+ seq) acc2
                                           (fn-cei-put seq (cadr d) index) reads
                                           pgs-mem fn-arena fn-octets)))))))
                  (mv :truncated acc index (+ reads 2) fn-arena fn-octets)))
            (mv :truncated acc index (+ reads 1) fn-arena fn-octets))
        (mv :ok acc index (+ reads 1) fn-arena fn-octets))
    (mv :ok acc index reads fn-arena fn-octets)))

(defun fn-pck-x-open (npg pgs-mem fn-arena fn-octets)
  ; The open of the NPG-page image in PGS-MEM: the root row from words 0 ..
  ; 8*2048, then the events tape from word 8*2048 to NPG*2048, record by record.
  ; (mv VERDICT ROWS ROOTS INDEX READS fn-arena fn-octets): VERDICT :ok or a
  ; refusal by name; ROWS the arena rows, ROOTS the four fold roots, INDEX the
  ; event index, READS the words read.
  (declare (xargs :stobjs (pgs-mem fn-arena fn-octets) :verify-guards nil))
  (if (and (natp npg) (<= 8 npg) (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
           (eql (pcko-w 0 pgs-mem) 1))
      (let* ((n (nfix (pcko-w 1 pgs-mem)))
             (nw (floor (+ n 7) 8)))
        (if (<= (+ 2 nw) 16384)
            (let ((fn-octets (fn-octets-clear fn-octets)))
              (mv-let (reads fn-octets)
                (pcko-copy 2 n 2 pgs-mem fn-octets)
                (let ((d (pcko-tree fn-octets)))
                  (if (eq d :refused)
                      (mv :root nil nil nil reads fn-arena fn-octets)
                    (let ((root (cadr d)))
                      (mv-let (verdict acc index reads fn-arena fn-octets)
                        (pcko-tape 16384 (* 2048 npg) 0 (fn-ssr-seed (nth 1 root)) nil reads
                                   pgs-mem fn-arena fn-octets)
                        (mv verdict (fn-ssr-rows acc)
                            (list (nth 0 root) (nth 1 root) (nth 2 root) (nth 3 root))
                            index reads fn-arena fn-octets)))))))
          (mv :root nil nil nil 2 fn-arena fn-octets)))
    (mv :root nil nil nil (if (and (natp npg) (<= 8 npg) (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))) 1 0)
        fn-arena fn-octets)))

; -----------------------------------------------------------------------------
; The image as a list, and the copy.

(defun pcko-img (w pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard t :verify-guards nil))
  (equal (pgs-x-words 0 0 (len w) pgs-mem) w))

(defun pcko-ind (a k i)
  (if (zp i) (list a k) (pcko-ind (1+ a) (1- k) (1- i))))

(defthm pcko-nth-of-words
  (implies (and (natp a) (natp k) (natp i) (< i k))
           (equal (nth i (pgs-x-words 0 a k pgs-mem))
                  (pgs-x-word 0 (+ a i) pgs-mem)))
  :hints (("Goal" :induct (pcko-ind a k i)
           :expand ((pgs-x-words 0 a k pgs-mem)))))

(defthm pcko-w-is-nth
  (implies (and (pcko-img w pgs-mem) (natp i) (< i (len w)))
           (equal (pcko-w i pgs-mem) (nth i w)))
  :hints (("Goal" :use ((:instance pcko-nth-of-words (a 0) (k (len w))))
           :in-theory (e/d (pcko-img pcko-w) (pcko-nth-of-words))))
  :rule-classes ((:rewrite :match-free :all)))

(in-theory (disable pcko-w pcko-img))

(defthm pcko-unw-is-word-octets
  (equal (adt-tp-unw k w) (fn-oct-word-octets w k))
  :hints (("Goal" :in-theory (enable adt-tp-unw fn-oct-word-octets))))

(defthm pcko-npk-natp (natp (adt-tp-npk n))
  :hints (("Goal" :in-theory (enable adt-tp-npk)))
  :rule-classes (:rewrite :type-prescription))

(defthm pcko-unpack-step
  (implies (posp n)
           (equal (adt-tp-unpack n ws)
                  (append (adt-tp-unw (min n 8) (car ws))
                          (adt-tp-unpack (nfix (- n 8)) (cdr ws)))))
  :hints (("Goal" :expand ((adt-tp-unpack n ws)))))

(defthm pcko-npk-step
  (implies (posp n) (equal (adt-tp-npk n) (+ 1 (adt-tp-npk (nfix (- n 8))))))
  :hints (("Goal" :expand ((adt-tp-npk n)))))

(defthm pcko-car-nthcdr (equal (car (nthcdr i w)) (nth i w)))

(defthm pcko-unpack-zero (equal (adt-tp-unpack 0 ws) nil)
  :hints (("Goal" :expand ((adt-tp-unpack 0 ws)))))
(defthm pcko-npk-zero (equal (adt-tp-npk 0) 0)
  :hints (("Goal" :expand ((adt-tp-npk 0)))))

(defthm pcko-copy-is-unpack
  (implies (and (pcko-img w pgs-mem) (natp pos) (natp n) (natp reads) (true-listp buf)
                (<= (+ pos (adt-tp-npk n)) (len w)))
           (and (equal (mv-nth 0 (pcko-copy pos n reads pgs-mem buf))
                       (+ reads (adt-tp-npk n)))
                (equal (mv-nth 1 (pcko-copy pos n reads pgs-mem buf))
                       (append buf (adt-tp-unpack n (nthcdr pos w))))))
  :hints (("Goal" :induct (pcko-copy pos n reads pgs-mem buf)
           :in-theory (e/d (pcko-unpack-step pcko-npk-step) (nth nthcdr adt-tp-unpack adt-tp-npk)))))
