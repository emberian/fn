; fn: the page store's executable layer (lane arena-store, 2026-09-27).  Prefix pgs-x-.
;
; The model's decisions (books/pagestore.lisp) over the stobj
; `pgs-mem' of books/pagestore-words.lisp, with the refinement
; theorems that make the stobj's words the model's lists.  The table stays
; in words (no abstract stobj): the word SHA-256 digests the table pages in
; place (`pgs-x-words-digest', proved SHA-256 in pagestore-words-sha).
;
; Representation (SEL 2 = pgs-t, SEL 1 = pgs-m):
;   flat table entry I   pgs-t words 2048 T + 6 K, I = 341 T + K: PHYS,
;                        TXID, then the 256-bit digest as four words, most
;                        significant first (`pgs-x-eaddr', `pgs-x-get-entry')
;   directory entry J    pgs-m words *pgs-x-dir-base* + 6 J (the run
;                        contiguous, `pgs-ptab-run-pages' pages)
;   records              pgs-m slots 0 and 512, 20 words (section 9)
;   flags                pgs-d dirty; pgs-v / pgs-tv per logical / table
;                        page: 0 not resident, 1 resident unverified,
;                        2 verified
; The representation invariant (`pgs-x-inv', section 5): pgs-t is exactly
; (pgs-ntables N) table pages and every word of a table page past its
; entries is zero; pgs-m reaches the directory run's end and every word
; after the directory's entries is zero.  Established by
; `pgs-x-reset-table' and the open's checks (`pgs-x-dir-verdict',
; `pgs-x-tpage-canon' per loaded page), preserved by every write.
;
; Keystones (the host calls the subject):
;   pgs-x-set-entry-is-update-nth, pgs-x-set-entry-at-end-is-append
;   pgs-x-plan-entries-refines (+ -len, -inv): the O(dirty) plan is
;     `pgs-plan-ptab' on the decoded view (pgs-x-plan-tab-refines,
;     pgs-x-plan-dir-refines)
;   pgs-x-commit-refines: `pgs-x-commit' is `pgs-plan-commit''s sequence
;   pgs-decode-encode-table, pgs-x-table-page-words, pgs-x-dir-run-words,
;     pgs-x-decode-table-page, pgs-x-decode-dir-run: words = encodings
;   pgs-x-dir-verdict-is-model, pgs-x-table-verdict-is-model: the open's
;     verdicts are the model's over the decoded words
;   pgs-x-reset-table-establishes-inv, pgs-x-fill-table-page-keeps-inv,
;     pgs-x-dir-verdict-establishes-inv
; Ground witnesses at the end (section 13).
(in-package "ACL2")
(include-book "pagestore")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition pgs-entry-p)
                          (:definition pgs-ptab-p))))

(local (in-theory (disable floor mod)))

; =============================================================================
; 1. Arithmetic: a table page holds 341 entries; entry I is entry
;    (pgs-tr I) of table page (pgs-tq I).

(local
 (defthmd pgs-floor-mod-unique
   (implies (and (natp q) (natp r) (posp d) (< r d))
            (and (equal (floor (+ r (* d q)) d) q)
                 (equal (mod (+ r (* d q)) d) r)))))

(local
 (defthm pgs-floor-mod-facts
   (implies (and (natp x) (posp d))
            (and (natp (floor x d))
                 (natp (mod x d))
                 (< (mod x d) d)
                 (equal (+ (mod x d) (* d (floor x d))) x)))
   :rule-classes nil))

(defun pgs-tq (i)
  (declare (xargs :guard t))
  (floor (nfix i) 341))

(defun pgs-tr (i)
  (declare (xargs :guard t))
  (mod (nfix i) 341))

(defthm pgs-tq-tr-facts
  (and (natp (pgs-tq i)) (natp (pgs-tr i)) (< (pgs-tr i) 341)
       (equal (+ (pgs-tr i) (* 341 (pgs-tq i))) (nfix i)))
  :hints (("Goal" :use ((:instance pgs-floor-mod-facts (x (nfix i)) (d 341)))))
  :rule-classes ((:type-prescription :corollary (natp (pgs-tq i)))
                 (:type-prescription :corollary (natp (pgs-tr i)))
                 (:linear :corollary (< (pgs-tr i) 341))
                 (:linear :corollary (equal (+ (pgs-tr i) (* 341 (pgs-tq i))) (nfix i)))))

(defthmd pgs-tq-tr-unique
  (implies (and (natp q) (natp r) (< r 341))
           (and (equal (pgs-tq (+ r (* 341 q))) q)
                (equal (pgs-tr (+ r (* 341 q))) r)))
  :hints (("Goal" :use ((:instance pgs-floor-mod-unique (d 341))))))

(in-theory (disable pgs-tq pgs-tr))

(defthm pgs-tq-monotone
  (implies (and (natp i) (natp j) (<= i j))
           (<= (pgs-tq i) (pgs-tq j)))
  :hints (("Goal" :use ((:instance pgs-tq-tr-facts (i i))
                        (:instance pgs-tq-tr-facts (i j)))
                  :in-theory (disable pgs-tq-tr-facts)))
  :rule-classes :linear)

(defthm pgs-tq-tr-plus-341
  (implies (natp i)
           (and (equal (pgs-tq (+ 341 i)) (+ 1 (pgs-tq i)))
                (equal (pgs-tr (+ 341 i)) (pgs-tr i))))
  :hints (("Goal" :use ((:instance pgs-tq-tr-unique (q (+ 1 (pgs-tq i))) (r (pgs-tr i)))
                        (:instance pgs-tq-tr-facts))
                  :in-theory (disable pgs-tq-tr-facts))))

(defthm pgs-tq-tr-small
  (implies (and (natp i) (< i 341))
           (and (equal (pgs-tq i) 0) (equal (pgs-tr i) i)))
  :hints (("Goal" :use ((:instance pgs-tq-tr-unique (q 0) (r i))))))

(defthm pgs-ntables-as-tq
  (implies (natp n)
           (equal (pgs-ntables n)
                  (if (zp n) 0 (+ 1 (pgs-tq (- n 1))))))
  :hints (("Goal" :induct (pgs-ntables n))
          ("Subgoal *1/2" :cases ((< n 342)))
          ("Subgoal *1/2.2" :use ((:instance pgs-tq-tr-plus-341 (i (- n 342)))))))

; =============================================================================
; 2. Words: a generic put and resize over the metadata (SEL 1) and the table
;    pages (SEL 2), and their read-over-write facts.

(defun pgs-x-sel-p (sel)
  (declare (xargs :guard t))
  (or (equal sel 1) (equal sel 2)))

(defun-inline pgs-x-put (sel i v pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (pgs-x-sel-p sel) (natp i) (< i (pgs-x-len sel pgs-mem))
                              (unsigned-byte-p 64 v))))
  (if (equal sel 1) (update-pgs-mi i v pgs-mem) (update-pgs-ti i v pgs-mem)))

(defun pgs-x-resize (sel n pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (and (pgs-x-sel-p sel) (natp n))))
  (if (equal sel 1) (resize-pgs-m n pgs-mem) (resize-pgs-t n pgs-mem)))

(local
 (defthm pgs-len-resize-list
   (equal (len (resize-list l n d)) (nfix n))))

(local
 (defun pgs-resize-ind (j l n)
   (if (zp n) (list j l)
     (pgs-resize-ind (1- j) (if (consp l) (cdr l) l) (1- n)))))

(local
 (defthm pgs-nth-resize-list
   (implies (natp j)
            (equal (nth j (resize-list l n d))
                   (if (< j (nfix n)) (if (< j (len l)) (nth j l) d) nil)))
   :hints (("Goal" :in-theory (enable nth) :induct (pgs-resize-ind j l n)))))

(local
 (defthm pgs-u64p-of-resize-list
   (and (implies (pgs-mp l) (pgs-mp (resize-list l n 0)))
        (implies (pgs-tp l) (pgs-tp (resize-list l n 0))))))

(local
 (defthm pgs-mp-tp-of-update-nth
   (implies (and (natp i) (< i (len l)) (unsigned-byte-p 64 v))
            (and (implies (pgs-mp l) (pgs-mp (update-nth i v l)))
                 (implies (pgs-tp l) (pgs-tp (update-nth i v l)))))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm pgs-len-update-nth-in-range
   (implies (and (natp i) (< i (len l)))
            (equal (len (update-nth i v l)) (len l)))))

(defthm pgs-x-word-of-put
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp i) (natp j))
           (equal (pgs-x-word s j (pgs-x-put s2 i v pgs-mem))
                  (if (and (equal s s2) (equal j i)) v (pgs-x-word s j pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-word$inline pgs-mi pgs-ti update-pgs-mi update-pgs-ti))))

(defthm pgs-x-fields-of-put
  (implies (and (pgs-x-sel-p s2) (natp i) (< i (pgs-x-len s2 pgs-mem)))
           (and (equal (pgs-x-len s (pgs-x-put s2 i v pgs-mem)) (pgs-x-len s pgs-mem))
                (equal (pgs-w-length (pgs-x-put s2 i v pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (pgs-x-put s2 i v pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (pgs-x-put s2 i v pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-d-length (pgs-x-put s2 i v pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (pgs-x-put s2 i v pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (pgs-x-put s2 i v pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (pgs-wi j (pgs-x-put s2 i v pgs-mem)) (pgs-wi j pgs-mem))
                (equal (pgs-di j (pgs-x-put s2 i v pgs-mem)) (pgs-di j pgs-mem))
                (equal (pgs-vi j (pgs-x-put s2 i v pgs-mem)) (pgs-vi j pgs-mem))
                (equal (pgs-tvi j (pgs-x-put s2 i v pgs-mem)) (pgs-tvi j pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-len$inline pgs-wi pgs-di pgs-vi pgs-tvi
                                     update-pgs-mi update-pgs-ti
                                     pgs-w-length pgs-m-length pgs-t-length pgs-d-length
                                     pgs-v-length pgs-tv-length))))

(defthm pgs-memp-of-x-put
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p s) (natp i) (< i (pgs-x-len s pgs-mem))
                (unsigned-byte-p 64 v))
           (pgs-memp (pgs-x-put s i v pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-len$inline pgs-memp update-pgs-mi update-pgs-ti
                                     pgs-m-length pgs-t-length))))

(defthm pgs-x-word-of-resize
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp j))
           (equal (pgs-x-word s j (pgs-x-resize s2 n pgs-mem))
                  (if (equal s s2)
                      (if (< j (nfix n))
                          (if (< j (pgs-x-len s pgs-mem)) (pgs-x-word s j pgs-mem) 0)
                        nil)
                    (pgs-x-word s j pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-word$inline pgs-x-len$inline pgs-mi pgs-ti
                                     pgs-m-length pgs-t-length))))

(defthm pgs-x-fields-of-resize
  (implies (pgs-x-sel-p s2)
           (and (equal (pgs-x-len s (pgs-x-resize s2 n pgs-mem))
                       (if (or (equal s s2) (and (equal s2 2) (equal s 2))) (nfix n) (pgs-x-len s pgs-mem)))
                (equal (pgs-w-length (pgs-x-resize s2 n pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (pgs-x-resize s2 n pgs-mem))
                       (if (equal s2 1) (nfix n) (pgs-m-length pgs-mem)))
                (equal (pgs-t-length (pgs-x-resize s2 n pgs-mem))
                       (if (equal s2 2) (nfix n) (pgs-t-length pgs-mem)))
                (equal (pgs-d-length (pgs-x-resize s2 n pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (pgs-x-resize s2 n pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (pgs-x-resize s2 n pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (pgs-wi j (pgs-x-resize s2 n pgs-mem)) (pgs-wi j pgs-mem))
                (equal (pgs-di j (pgs-x-resize s2 n pgs-mem)) (pgs-di j pgs-mem))
                (equal (pgs-vi j (pgs-x-resize s2 n pgs-mem)) (pgs-vi j pgs-mem))
                (equal (pgs-tvi j (pgs-x-resize s2 n pgs-mem)) (pgs-tvi j pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-len$inline pgs-wi pgs-di pgs-vi pgs-tvi
                                     pgs-w-length pgs-m-length pgs-t-length pgs-d-length
                                     pgs-v-length pgs-tv-length))))

(defthm pgs-memp-of-x-resize
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p s))
           (pgs-memp (pgs-x-resize s n pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-memp))))

(in-theory (disable pgs-x-put$inline pgs-x-resize))

; =============================================================================
; 3. Entries.  An entry (PHYS TXID DIGEST) is six words: PHYS, TXID, then the
;    256-bit DIGEST as four words, most significant first.  Entry I of the
;    flat table (SEL 2) is word 6K of table page T, I = 341T + K (words
;    2046-2047 of each table page are padding); entry I of the directory
;    (SEL 1) is word BASE + 6I, the run contiguous (`pgs-ptab-run-pages').

(defconst *pgs-x-dir-base* 1024)       ; the directory run in pgs-m; slots at 0 and 512

(defun pgs-x-eaddr (sel base i)
  (declare (xargs :guard t))
  (if (equal sel 2)
      (+ (* 2048 (pgs-tq i)) (* 6 (pgs-tr i)))
    (+ (nfix base) (* 6 (nfix i)))))

(defthm pgs-x-eaddr-natp
  (natp (pgs-x-eaddr sel base i))
  :rule-classes :type-prescription)

(defthm pgs-x-eaddr-monotone
  (implies (and (natp i) (natp j) (< i j))
           (<= (+ 6 (pgs-x-eaddr sel base i)) (pgs-x-eaddr sel base j)))
  :hints (("Goal" :cases ((< (pgs-tq i) (pgs-tq j)) (equal (pgs-tq i) (pgs-tq j)))
                  :use ((:instance pgs-tq-tr-facts (i i)) (:instance pgs-tq-tr-facts (i j)))
                  :in-theory (disable pgs-tq-tr-facts)))
  :rule-classes :linear)

(defthm pgs-x-eaddr-2-in-page
  (and (<= (* 2048 (pgs-tq i)) (pgs-x-eaddr 2 base i))
       (<= (+ 6 (pgs-x-eaddr 2 base i)) (+ 2046 (* 2048 (pgs-tq i)))))
  :rule-classes :linear)

(defthm pgs-x-eaddr-2-of-page-entry
  (implies (and (natp tp) (natp k) (< k 341))
           (equal (pgs-x-eaddr 2 base (+ k (* 341 tp))) (+ (* 2048 tp) (* 6 k))))
  :hints (("Goal" :use ((:instance pgs-tq-tr-unique (q tp) (r k))))))

(in-theory (disable pgs-x-eaddr))

; Digests as words.
(defun pgs-dlo (d) (declare (xargs :guard t)) (mod (nfix d) 18446744073709551616))
(defun pgs-dhi (d) (declare (xargs :guard t)) (floor (nfix d) 18446744073709551616))
(defun pgs-h64 (lo hi)
  (declare (xargs :guard t))
  (+ (nfix lo) (* 18446744073709551616 (nfix hi))))

(defthm pgs-dlo-u64
  (and (unsigned-byte-p 64 (pgs-dlo d)) (natp (pgs-dlo d)) (< (pgs-dlo d) 18446744073709551616))
  :hints (("Goal" :in-theory (enable unsigned-byte-p)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (pgs-dlo d)))
                 (:linear :corollary (< (pgs-dlo d) 18446744073709551616))))

(defthm pgs-dhi-natp (natp (pgs-dhi d)) :rule-classes :type-prescription)
(defthm pgs-h64-natp (natp (pgs-h64 a b)) :rule-classes :type-prescription)

(defthm pgs-h64-of-dlo-dhi
  (equal (pgs-h64 (pgs-dlo d) (pgs-dhi d)) (nfix d))
  :hints (("Goal" :use ((:instance pgs-floor-mod-facts (x (nfix d)) (d 18446744073709551616))))))

(defthm pgs-dlo-small
  (implies (and (natp d) (< d 18446744073709551616)) (equal (pgs-dlo d) d)))

(defthm pgs-dhi-bounds
  (and (implies (< (nfix d) 115792089237316195423570985008687907853269984665640564039457584007913129639936)
                (< (pgs-dhi d) 6277101735386680763835789423207666416102355444464034512896))
       (implies (< (nfix d) 6277101735386680763835789423207666416102355444464034512896)
                (< (pgs-dhi d) 340282366920938463463374607431768211456))
       (implies (< (nfix d) 340282366920938463463374607431768211456)
                (< (pgs-dhi d) 18446744073709551616)))
  :hints (("Goal" :use ((:instance pgs-floor-mod-facts (x (nfix d)) (d 18446744073709551616)))))
  :rule-classes :linear)

(defthm pgs-dlo-dhi-of-h64
  (implies (< (nfix a) 18446744073709551616)
           (and (equal (pgs-dlo (pgs-h64 a b)) (nfix a))
                (equal (pgs-dhi (pgs-h64 a b)) (nfix b))))
  :hints (("Goal" :use ((:instance pgs-floor-mod-unique (q (nfix b)) (r (nfix a))
                                   (d 18446744073709551616))))))

(defthm pgs-h64-bounds
  (implies (< (nfix a) 18446744073709551616)
           (and (implies (< (nfix b) 18446744073709551616)
                         (< (pgs-h64 a b) 340282366920938463463374607431768211456))
                (implies (< (nfix b) 340282366920938463463374607431768211456)
                         (< (pgs-h64 a b) 6277101735386680763835789423207666416102355444464034512896))
                (implies (< (nfix b) 6277101735386680763835789423207666416102355444464034512896)
                         (< (pgs-h64 a b) 115792089237316195423570985008687907853269984665640564039457584007913129639936))))
  :rule-classes :linear)

(in-theory (disable pgs-dlo pgs-dhi pgs-h64))

(defun pgs-x-dig4 (sel a pgs-mem)
  ; The digest in words A..A+3, most significant first.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp a) (<= (+ a 4) (pgs-x-len sel pgs-mem)))))
  (pgs-h64 (pgs-x-word sel (+ 3 a) pgs-mem)
           (pgs-h64 (pgs-x-word sel (+ 2 a) pgs-mem)
                    (pgs-h64 (pgs-x-word sel (+ 1 a) pgs-mem)
                             (pgs-x-word sel a pgs-mem)))))

(defun pgs-x-entry-fits (e)
  ; An entry the words represent: PHYS and TXID u64, DIGEST below 2^256.
  (declare (xargs :guard t))
  (and (pgs-entry-p e)
       (< (first e) 18446744073709551616)
       (< (second e) 18446744073709551616)
       (< (third e) 115792089237316195423570985008687907853269984665640564039457584007913129639936)))

(defun pgs-x-get-entry (sel base i pgs-mem)
  ; Entry I, O(1); (0 0 0) when its words are past the array.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (pgs-x-sel-p sel) (natp base) (natp i))))
  (let ((a (pgs-x-eaddr sel base i)))
    (if (<= (+ a 6) (pgs-x-len sel pgs-mem))
        (list (nfix (pgs-x-word sel a pgs-mem))
              (nfix (pgs-x-word sel (+ 1 a) pgs-mem))
              (pgs-x-dig4 sel (+ 2 a) pgs-mem))
      (list 0 0 0))))

(defun pgs-x-set-entry (sel base i e pgs-mem)
  ; Entry I := E, O(1); nothing when its words are past the array (the
  ; callers keep them inside: `pgs-x-inv').
  (declare (xargs :stobjs pgs-mem
                  :guard (and (pgs-x-sel-p sel) (natp base) (natp i) (pgs-entry-p e))))
  (let ((a (pgs-x-eaddr sel base i)))
    (if (<= (+ a 6) (pgs-x-len sel pgs-mem))
        (let* ((d (third e))
               (pgs-mem (pgs-x-put sel a (pgs-dlo (first e)) pgs-mem))
               (pgs-mem (pgs-x-put sel (+ 1 a) (pgs-dlo (second e)) pgs-mem))
               (pgs-mem (pgs-x-put sel (+ 2 a) (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi d)))) pgs-mem))
               (pgs-mem (pgs-x-put sel (+ 3 a) (pgs-dlo (pgs-dhi (pgs-dhi d))) pgs-mem))
               (pgs-mem (pgs-x-put sel (+ 4 a) (pgs-dlo (pgs-dhi d)) pgs-mem)))
          (pgs-x-put sel (+ 5 a) (pgs-dlo d) pgs-mem))
      pgs-mem)))

(defthm pgs-x-fields-of-set-entry
  (implies (pgs-x-sel-p s2)
           (and (equal (pgs-x-len s (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-x-len s pgs-mem))
                (equal (pgs-w-length (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-d-length (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (pgs-wi j (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-wi j pgs-mem))
                (equal (pgs-di j (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-di j pgs-mem))
                (equal (pgs-vi j (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-vi j pgs-mem))
                (equal (pgs-tvi j (pgs-x-set-entry s2 b k e pgs-mem)) (pgs-tvi j pgs-mem)))))

(defthm pgs-memp-of-set-entry
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p s))
           (pgs-memp (pgs-x-set-entry s b k e pgs-mem))))

(defthm pgs-x-word-of-set-entry
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp p)
                (or (not (equal s s2))
                    (< p (pgs-x-eaddr s2 b k))
                    (<= (+ 6 (pgs-x-eaddr s2 b k)) p)))
           (equal (pgs-x-word s p (pgs-x-set-entry s2 b k e pgs-mem))
                  (pgs-x-word s p pgs-mem))))

(local
 (defthm pgs-list3-of-parts
   (implies (and (consp e) (consp (cdr e)) (true-listp (cddr e)) (equal (len (cddr e)) 1))
            (equal (cons (car e) (cons (cadr e) (cons (caddr e) nil))) e))
   :hints (("Goal" :expand ((len (cddr e)) (len (cdddr e)))))))

(defthm pgs-dig-roundtrip
  (implies (and (natp d)
                (< d 115792089237316195423570985008687907853269984665640564039457584007913129639936))
           (equal (pgs-h64 (pgs-dlo d)
                           (pgs-h64 (pgs-dlo (pgs-dhi d))
                                    (pgs-h64 (pgs-dlo (pgs-dhi (pgs-dhi d)))
                                             (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi d)))))))
                  d)))

(defthm pgs-x-words-of-set-entry-here
  (implies (and (pgs-x-sel-p s)
                (<= (+ 6 (pgs-x-eaddr s b k)) (pgs-x-len s pgs-mem)))
           (let ((a (pgs-x-eaddr s b k)) (m2 (pgs-x-set-entry s b k e pgs-mem)))
             (and (equal (pgs-x-word s a m2) (pgs-dlo (first e)))
                  (equal (pgs-x-word s (+ 1 a) m2) (pgs-dlo (second e)))
                  (equal (pgs-x-word s (+ 2 a) m2) (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi (third e))))))
                  (equal (pgs-x-word s (+ 3 a) m2) (pgs-dlo (pgs-dhi (pgs-dhi (third e)))))
                  (equal (pgs-x-word s (+ 4 a) m2) (pgs-dlo (pgs-dhi (third e))))
                  (equal (pgs-x-word s (+ 5 a) m2) (pgs-dlo (third e)))))))

(in-theory (disable pgs-x-set-entry))

(defthm pgs-x-get-entry-of-set-entry-same
  (implies (and (pgs-x-sel-p s) (natp k) (pgs-x-entry-fits e))
           (equal (pgs-x-get-entry s b k (pgs-x-set-entry s b k e pgs-mem))
                  (if (<= (+ 6 (pgs-x-eaddr s b k)) (pgs-x-len s pgs-mem))
                      e
                    (pgs-x-get-entry s b k pgs-mem))))
  :hints (("Goal" :in-theory (disable pgs-x-words-of-set-entry-here)
                  :use pgs-x-words-of-set-entry-here)))

(defthm pgs-x-get-entry-of-set-entry-other
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp j) (natp k)
                (not (and (equal s s2) (equal j k))))
           (equal (pgs-x-get-entry s b j (pgs-x-set-entry s2 b k e pgs-mem))
                  (pgs-x-get-entry s b j pgs-mem)))
  :hints (("Goal" :cases ((< j k) (< k j)))))

(defthm pgs-x-get-entry-of-set-entry
  ; Entry-level read over write: the set entry reads back as written (when
  ; it fits the words), every other entry is unchanged.
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp j) (natp k) (pgs-x-entry-fits e))
           (equal (pgs-x-get-entry s b j (pgs-x-set-entry s2 b k e pgs-mem))
                  (if (and (equal s s2) (equal j k)
                           (<= (+ 6 (pgs-x-eaddr s b k)) (pgs-x-len s pgs-mem)))
                      e
                    (pgs-x-get-entry s b j pgs-mem))))
  :hints (("Goal" :in-theory (disable pgs-x-get-entry)
                  :cases ((and (equal s s2) (equal j k))))))

(defthm pgs-x-word-of-put-other
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp i) (natp j)
                (not (and (equal s s2) (equal j i))))
           (equal (pgs-x-word s j (pgs-x-put s2 i v pgs-mem))
                  (pgs-x-word s j pgs-mem))))

(defthm pgs-x-get-entry-of-put
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp p) (< p (pgs-x-len s2 pgs-mem))
                (or (not (equal s s2)) (< p (pgs-x-eaddr s b j)) (<= (+ 6 (pgs-x-eaddr s b j)) p)))
           (equal (pgs-x-get-entry s b j (pgs-x-put s2 p v pgs-mem))
                  (pgs-x-get-entry s b j pgs-mem)))
  :hints (("Goal" :in-theory (disable pgs-x-word-of-put))))

(defthm pgs-x-word-of-resize-below
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp j)
                (< j (pgs-x-len s pgs-mem)) (<= (pgs-x-len s pgs-mem) (nfix n)))
           (equal (pgs-x-word s j (pgs-x-resize s2 n pgs-mem))
                  (pgs-x-word s j pgs-mem))))

(defthm pgs-x-get-entry-of-resize
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2)
                (<= (+ 6 (pgs-x-eaddr s b j)) (pgs-x-len s pgs-mem))
                (<= (pgs-x-len s pgs-mem) (nfix n)))
           (equal (pgs-x-get-entry s b j (pgs-x-resize s2 n pgs-mem))
                  (pgs-x-get-entry s b j pgs-mem)))
  :hints (("Goal" :in-theory (disable pgs-x-word-of-resize))))

(in-theory (disable pgs-x-get-entry))

; =============================================================================
; 4. The decoded views: entries I..N-1 as a list.  (pgs-x-tab N pgs-mem) is
;    the flat table, (pgs-x-dir ND pgs-mem) the directory.  Logical views,
;    O(N): the host never builds them on a served path.

(defun pgs-x-tab-from (sel base i n pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (pgs-x-sel-p sel) (natp base) (natp i) (natp n))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (mbe :logic (zp (- (nfix n) (nfix i))) :exec (<= n i))
      nil
    (cons (pgs-x-get-entry sel base i pgs-mem)
          (pgs-x-tab-from sel base (+ 1 (nfix i)) n pgs-mem))))

(defun pgs-x-tab (n pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (natp n)))
  (pgs-x-tab-from 2 0 0 n pgs-mem))

(defun pgs-x-dir (nd pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (natp nd)))
  (pgs-x-tab-from 1 *pgs-x-dir-base* 0 nd pgs-mem))

(defthm pgs-len-of-tab-from
  (equal (len (pgs-x-tab-from sel base i n pgs-mem)) (nfix (- (nfix n) (nfix i)))))

(defthm pgs-true-listp-of-tab-from
  (true-listp (pgs-x-tab-from sel base i n pgs-mem))
  :rule-classes (:rewrite :type-prescription))

(defthm pgs-x-tab-from-of-set-entry
  (implies (and (pgs-x-sel-p s) (natp i) (natp k) (pgs-x-entry-fits e)
                (<= (+ 6 (pgs-x-eaddr s b k)) (pgs-x-len s pgs-mem)))
           (equal (pgs-x-tab-from s b i n (pgs-x-set-entry s b k e pgs-mem))
                  (if (and (<= i k) (< k (nfix n)))
                      (update-nth (- k i) e (pgs-x-tab-from s b i n pgs-mem))
                    (pgs-x-tab-from s b i n pgs-mem))))
  :hints (("Goal" :induct (pgs-x-tab-from s b i n pgs-mem))))

(defthm pgs-x-tab-from-of-set-entry-other
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (not (equal s s2)) (natp i) (natp k)
                (pgs-x-entry-fits e))
           (equal (pgs-x-tab-from s b i n (pgs-x-set-entry s2 b2 k e pgs-mem))
                  (pgs-x-tab-from s b i n pgs-mem)))
  :hints (("Goal" :induct (pgs-x-tab-from s b i n pgs-mem)
                  :in-theory (enable pgs-x-get-entry))))

(defthm pgs-x-tab-from-extend
  (implies (and (natp i) (natp n) (<= i n))
           (equal (pgs-x-tab-from s b i (+ 1 n) pgs-mem)
                  (append (pgs-x-tab-from s b i n pgs-mem)
                          (list (pgs-x-get-entry s b n pgs-mem)))))
  :hints (("Goal" :induct (pgs-x-tab-from s b i n pgs-mem))))

(defthm pgs-x-tab-from-of-resize
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp i) (natp n)
                (or (<= n i) (<= (+ 6 (pgs-x-eaddr s b (+ -1 n))) (pgs-x-len s pgs-mem)))
                (<= (pgs-x-len s pgs-mem) (nfix m)))
           (equal (pgs-x-tab-from s b i n (pgs-x-resize s2 m pgs-mem))
                  (pgs-x-tab-from s b i n pgs-mem)))
  :hints (("Goal" :induct (pgs-x-tab-from s b i n pgs-mem))
          ("Subgoal *1/2" :cases ((< i (+ -1 n))))))

; -----------------------------------------------------------------------------
; Zero ranges: words LO..HI-1 of SEL are zero.

(defun pgs-x-zero-range (sel lo hi pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp lo) (natp hi) (<= hi (pgs-x-len sel pgs-mem)))
                  :measure (nfix (- (nfix hi) (nfix lo)))))
  (if (mbe :logic (zp (- (nfix hi) (nfix lo))) :exec (<= hi lo))
      t
    (and (equal (pgs-x-word sel lo pgs-mem) 0)
         (pgs-x-zero-range sel (+ 1 (nfix lo)) hi pgs-mem))))

(defthm pgs-x-zero-range-empty
  (implies (<= (nfix hi) (nfix lo))
           (pgs-x-zero-range s lo hi pgs-mem)))

(defthm pgs-x-zero-range-of-set-entry
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp lo)
                (or (not (equal s s2))
                    (<= (nfix hi) (pgs-x-eaddr s2 b k))
                    (<= (+ 6 (pgs-x-eaddr s2 b k)) lo)))
           (equal (pgs-x-zero-range s lo hi (pgs-x-set-entry s2 b k e pgs-mem))
                  (pgs-x-zero-range s lo hi pgs-mem)))
  :hints (("Goal" :induct (pgs-x-zero-range s lo hi pgs-mem))))

(defthm pgs-x-zero-range-of-put
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp lo) (natp p) (< p (pgs-x-len s2 pgs-mem))
                (or (not (equal s s2)) (<= (nfix hi) p) (< p lo)))
           (equal (pgs-x-zero-range s lo hi (pgs-x-put s2 p v pgs-mem))
                  (pgs-x-zero-range s lo hi pgs-mem)))
  :hints (("Goal" :induct (pgs-x-zero-range s lo hi pgs-mem))))

(defthm pgs-x-zero-range-sub
  (implies (and (pgs-x-zero-range s lo hi pgs-mem) (natp lo) (natp lo2) (<= lo lo2))
           (pgs-x-zero-range s lo2 hi pgs-mem))
  :hints (("Goal" :induct (pgs-x-zero-range s lo hi pgs-mem))))

(defthm pgs-x-zero-range-prefix
  (implies (and (pgs-x-zero-range s lo hi pgs-mem) (natp lo) (natp hi2) (<= hi2 (nfix hi)))
           (pgs-x-zero-range s lo hi2 pgs-mem))
  :hints (("Goal" :induct (pgs-x-zero-range s lo hi pgs-mem))))

(defthm pgs-x-zero-range-subrange
  (implies (and (pgs-x-zero-range s lo hi pgs-mem) (natp lo) (natp lo2) (<= lo lo2)
                (natp hi2) (<= hi2 (nfix hi)))
           (pgs-x-zero-range s lo2 hi2 pgs-mem))
  :hints (("Goal" :use ((:instance pgs-x-zero-range-prefix)
                        (:instance pgs-x-zero-range-sub (hi hi2)))
                  :in-theory (disable pgs-x-zero-range-prefix pgs-x-zero-range-sub))))

(defthm pgs-x-zero-range-word
  (implies (and (pgs-x-zero-range s lo hi pgs-mem) (natp lo) (natp j) (<= lo j) (< j (nfix hi)))
           (equal (pgs-x-word s j pgs-mem) 0))
  :hints (("Goal" :induct (pgs-x-zero-range s lo hi pgs-mem))))

(defthm pgs-x-zero-range-of-resize-old
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp lo) (natp hi)
                (<= hi (pgs-x-len s pgs-mem)) (<= hi (nfix n)))
           (equal (pgs-x-zero-range s lo hi (pgs-x-resize s2 n pgs-mem))
                  (pgs-x-zero-range s lo hi pgs-mem)))
  :hints (("Goal" :induct (pgs-x-zero-range s lo hi pgs-mem))))

(defthm pgs-x-zero-range-of-resize-grow
  ; A zero tail stays a zero tail when the array grows.
  (implies (and (pgs-x-sel-p s) (natp lo) (natp n) (<= (pgs-x-len s pgs-mem) n)
                (pgs-x-zero-range s lo (pgs-x-len s pgs-mem) pgs-mem))
           (pgs-x-zero-range s lo n (pgs-x-resize s n pgs-mem)))
  :hints (("Goal" :induct (pgs-x-zero-range s lo n (pgs-x-resize s n pgs-mem)))))

; =============================================================================
; 5. The representation invariant.
;
; The flat table of N entries (SEL 2): pgs-t is exactly (pgs-ntables N)
; table pages, and every word of table page T past its entries (from word
; 6 * (pgs-x-tcnt T N), which includes words 2046-2047) is zero.
; The directory of ND entries (SEL 1, from BASE): pgs-m reaches at least
; the directory run's end, BASE + 2048 * (pgs-ptab-run-pages ND), and every
; word from BASE + 6 ND to the end of pgs-m is zero.

(defun pgs-x-tcnt (tp n)
  ; The entries of table page TP in a table of N entries.
  (declare (xargs :guard t))
  (min 341 (nfix (- (nfix n) (* 341 (nfix tp))))))

(defun pgs-x-tpage-canon (tp n pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp tp) (natp n) (<= (* 2048 (+ 1 tp)) (pgs-t-length pgs-mem)))))
  (pgs-x-zero-range 2 (+ (* 2048 tp) (* 6 (pgs-x-tcnt tp n))) (+ 2048 (* 2048 tp)) pgs-mem))

(defun pgs-x-tpages-canon (k n pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp k) (natp n) (<= (* 2048 k) (pgs-t-length pgs-mem)))))
  (if (zp k)
      t
    (and (pgs-x-tpage-canon (1- k) n pgs-mem)
         (pgs-x-tpages-canon (1- k) n pgs-mem))))

(defun pgs-x-tab-inv (n pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard t))
  (and (natp n)
       (equal (pgs-t-length pgs-mem) (* 2048 (pgs-ntables n)))
       (pgs-x-tpages-canon (pgs-ntables n) n pgs-mem)))

(defun pgs-x-dir-inv (base nd pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard t))
  (and (natp base) (natp nd)
       (<= (+ base (* 2048 (pgs-ptab-run-pages nd))) (pgs-m-length pgs-mem))
       (pgs-x-zero-range 1 (+ base (* 6 nd)) (pgs-m-length pgs-mem) pgs-mem)))

(defun pgs-x-inv (sel base n pgs-mem)
  ; The representation invariant of SEL's entries, N of them (BASE the
  ; directory's first word; the table's is 0).
  (declare (xargs :stobjs pgs-mem :guard t))
  (and (natp base) (natp n)
       (if (equal sel 2) (pgs-x-tab-inv n pgs-mem) (pgs-x-dir-inv base n pgs-mem))))

(defthm pgs-x-inv-natp
  (implies (pgs-x-inv s b n pgs-mem) (and (natp b) (natp n)))
  :rule-classes :forward-chaining)

(defthm pgs-x-ptab-run-pages-posp
  (and (integerp (pgs-ptab-run-pages n)) (<= 1 (pgs-ptab-run-pages n)))
  :rule-classes ((:type-prescription :corollary (integerp (pgs-ptab-run-pages n)))
                 (:linear :corollary (<= 1 (pgs-ptab-run-pages n)))))

(defthm pgs-run-pages-covers
  (<= (* 6 (nfix n)) (* 2048 (pgs-ptab-run-pages n)))
  :rule-classes :linear)

(defthm pgs-x-tpages-canon-member
  (implies (and (pgs-x-tpages-canon k n pgs-mem) (natp tp) (< tp (nfix k)))
           (pgs-x-tpage-canon tp n pgs-mem)))

(defthm pgs-x-tpages-canon-prefix
  (implies (and (pgs-x-tpages-canon k n pgs-mem) (natp j) (<= j (nfix k)))
           (pgs-x-tpages-canon j n pgs-mem)))

(in-theory (disable pgs-x-tpage-canon))

(defthm pgs-x-inv-entry-in-range
  ; Every entry below N lies inside its array.
  (implies (and (pgs-x-inv s b n pgs-mem) (pgs-x-sel-p s) (natp i) (< i n))
           (<= (+ 6 (pgs-x-eaddr s b i)) (pgs-x-len s pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-eaddr)
                  :use ((:instance pgs-tq-monotone (i i) (j (- n 1))))))
  :rule-classes (:rewrite :linear))

; -- set-entry below N keeps the invariant.

(defthm pgs-x-tpage-canon-of-set-entry
  (implies (and (natp tp) (natp i) (natp n) (< i n))
           (equal (pgs-x-tpage-canon tp n (pgs-x-set-entry 2 b i e pgs-mem))
                  (pgs-x-tpage-canon tp n pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-tpage-canon pgs-x-eaddr)
                  :cases ((< tp (pgs-tq i)) (equal tp (pgs-tq i))))))

(defthm pgs-x-tpages-canon-of-set-entry
  (implies (and (natp i) (natp n) (< i n))
           (equal (pgs-x-tpages-canon k n (pgs-x-set-entry 2 b i e pgs-mem))
                  (pgs-x-tpages-canon k n pgs-mem))))

(defthm pgs-x-inv-of-set-entry
  (implies (and (pgs-x-inv s b n pgs-mem) (pgs-x-sel-p s) (natp i) (< i n))
           (pgs-x-inv s b n (pgs-x-set-entry s b i e pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-eaddr))))

; -- appending entry N: grow the array by whole pages when needed, then set.

(defun pgs-x-grow-need (sel base n)
  ; The array length entry N needs: whole table pages, or the directory run.
  (declare (xargs :guard (natp n)))
  (if (equal sel 2)
      (* 2048 (+ 1 (pgs-tq n)))
    (+ (nfix base) (* 2048 (pgs-ptab-run-pages (+ 1 (nfix n)))))))

(defun pgs-x-grow (sel base n pgs-mem)
  ; Resizing copies the array (O(its length)); it happens once every 341
  ; appended entries for the table and once a directory page for the run.
  (declare (xargs :stobjs pgs-mem :guard (and (pgs-x-sel-p sel) (natp base) (natp n))))
  (let ((need (pgs-x-grow-need sel base n)))
    (if (< (pgs-x-len sel pgs-mem) need) (pgs-x-resize sel need pgs-mem) pgs-mem)))

(defthm pgs-x-fields-of-grow
  (implies (pgs-x-sel-p s2)
           (and (equal (pgs-x-len s (pgs-x-grow s2 b k pgs-mem))
                       (if (equal s s2)
                           (max (pgs-x-len s pgs-mem) (pgs-x-grow-need s b k))
                         (pgs-x-len s pgs-mem)))
                (equal (pgs-w-length (pgs-x-grow s2 b k pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (pgs-x-grow s2 b k pgs-mem))
                       (if (equal s2 1) (max (pgs-m-length pgs-mem) (pgs-x-grow-need s2 b k))
                         (pgs-m-length pgs-mem)))
                (equal (pgs-t-length (pgs-x-grow s2 b k pgs-mem))
                       (if (equal s2 2) (max (pgs-t-length pgs-mem) (pgs-x-grow-need s2 b k))
                         (pgs-t-length pgs-mem)))
                (equal (pgs-d-length (pgs-x-grow s2 b k pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (pgs-x-grow s2 b k pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (pgs-x-grow s2 b k pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (pgs-wi j (pgs-x-grow s2 b k pgs-mem)) (pgs-wi j pgs-mem))
                (equal (pgs-di j (pgs-x-grow s2 b k pgs-mem)) (pgs-di j pgs-mem))
                (equal (pgs-vi j (pgs-x-grow s2 b k pgs-mem)) (pgs-vi j pgs-mem))
                (equal (pgs-tvi j (pgs-x-grow s2 b k pgs-mem)) (pgs-tvi j pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-len$inline))))

(defthm pgs-memp-of-grow
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p s))
           (pgs-memp (pgs-x-grow s b k pgs-mem))))

(defthm pgs-tq-pred
  (implies (posp n)
           (equal (pgs-tq (- n 1))
                  (if (equal (pgs-tr n) 0) (- (pgs-tq n) 1) (pgs-tq n))))
  :hints (("Goal" :cases ((equal (pgs-tr n) 0)))
          ("Subgoal 2" :use ((:instance pgs-tq-tr-unique (q (pgs-tq n)) (r (- (pgs-tr n) 1)))
                             (:instance pgs-tq-tr-facts (i n)))
                       :in-theory (disable pgs-tq-tr-facts))
          ("Subgoal 1" :use ((:instance pgs-tq-tr-unique (q (- (pgs-tq n) 1)) (r 340))
                             (:instance pgs-tq-tr-facts (i n)))
                       :in-theory (disable pgs-tq-tr-facts))))

(defthm pgs-ntables-bounds
  (implies (natp n)
           (and (<= (pgs-ntables n) (+ 1 (pgs-tq n)))
                (<= (pgs-tq n) (pgs-ntables n))
                (equal (pgs-ntables (+ 1 n)) (+ 1 (pgs-tq n)))))
  :hints (("Goal" :cases ((zp n))))
  :rule-classes ((:linear :corollary (implies (natp n) (<= (pgs-ntables n) (+ 1 (pgs-tq n)))))
                 (:linear :corollary (implies (natp n) (<= (pgs-tq n) (pgs-ntables n))))
                 (:rewrite :corollary (implies (natp n) (equal (pgs-ntables (+ 1 n)) (+ 1 (pgs-tq n)))))))

(defthm pgs-x-inv-in-range-after-grow
  (implies (and (pgs-x-sel-p s) (natp n))
           (<= (+ 6 (pgs-x-eaddr s b n)) (pgs-x-len s (pgs-x-grow s b n pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-eaddr)
                  :use ((:instance pgs-run-pages-covers (n (+ 1 n)))))))

(defthm pgs-x-tab-from-of-grow
  (implies (and (pgs-x-inv s b n pgs-mem) (pgs-x-sel-p s) (natp n) (natp i))
           (equal (pgs-x-tab-from s b i n (pgs-x-grow s b n pgs-mem))
                  (pgs-x-tab-from s b i n pgs-mem)))
  :hints (("Goal" :cases ((zp n))
                  :in-theory (disable pgs-x-inv))
          ("Subgoal 1" :use ((:instance pgs-x-inv-entry-in-range (i (- n 1)))))))

(defthm pgs-x-tab-zero-tail
  ; The words from entry N's to the end of pgs-t are zero.
  (implies (pgs-x-tab-inv n pgs-mem)
           (pgs-x-zero-range 2 (pgs-x-eaddr 2 b n) (pgs-t-length pgs-mem) pgs-mem))
  :hints (("Goal" :cases ((zp n) (equal (pgs-tr n) 0))
                  :in-theory (enable pgs-x-eaddr))
          ("Subgoal 3" :use ((:instance pgs-x-tpages-canon-member (k (pgs-ntables n)) (tp (pgs-tq n))))
                       :in-theory (e/d (pgs-x-eaddr pgs-x-tpage-canon) (pgs-x-tpages-canon-member)))))

(defthm pgs-x-tcnt-facts
  (implies (natp n)
           (and (equal (pgs-x-tcnt (pgs-tq n) (+ 1 n)) (+ 1 (pgs-tr n)))
                (equal (pgs-x-tcnt (pgs-tq n) n) (pgs-tr n))
                (implies (and (natp tp) (< tp (pgs-tq n)))
                         (and (equal (pgs-x-tcnt tp n) 341)
                              (equal (pgs-x-tcnt tp (+ 1 n)) 341)))))
  :hints (("Goal" :use ((:instance pgs-tq-tr-facts (i n)))
                  :in-theory (disable pgs-tq-tr-facts))))

(in-theory (disable pgs-x-tcnt))

(defthm pgs-x-tpage-canon-full-page
  (implies (and (natp tp) (natp n) (< tp (pgs-tq n)))
           (equal (pgs-x-tpage-canon tp (+ 1 n) pgs-mem)
                  (pgs-x-tpage-canon tp n pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-tpage-canon))))

(defthm pgs-x-tpage-canon-of-grow-below
  (implies (and (natp tp) (<= (* 2048 (+ 1 tp)) (pgs-t-length pgs-mem)))
           (equal (pgs-x-tpage-canon tp n (pgs-x-grow 2 b k pgs-mem))
                  (pgs-x-tpage-canon tp n pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-tpage-canon))))

(defthm pgs-x-tpage-canon-after-grow
  (implies (and (natp tp) (natp n) (< tp (pgs-tq n)) (pgs-x-tab-inv n pgs-mem))
           (equal (pgs-x-tpage-canon tp (+ 1 n) (pgs-x-grow 2 b n pgs-mem))
                  (pgs-x-tpage-canon tp n pgs-mem)))
  :hints (("Goal" :in-theory (disable pgs-x-grow pgs-x-tpages-canon))))

(defthm pgs-x-tpages-canon-after-grow
  (implies (and (natp n) (natp k) (<= k (pgs-tq n)) (pgs-x-tab-inv n pgs-mem))
           (equal (pgs-x-tpages-canon k (+ 1 n) (pgs-x-grow 2 b n pgs-mem))
                  (pgs-x-tpages-canon k n pgs-mem)))
  :hints (("Goal" :induct (pgs-x-tpages-canon k n pgs-mem)
                  :in-theory (disable pgs-x-tab-inv pgs-x-grow))))

(defthm pgs-x-tpage-canon-of-appended
  (implies (and (natp n) (pgs-x-tab-inv n pgs-mem))
           (pgs-x-tpage-canon (pgs-tq n) (+ 1 n) (pgs-x-grow 2 b n pgs-mem)))
  :hints (("Goal" :in-theory (e/d (pgs-x-tpage-canon pgs-x-eaddr)
                                  (pgs-x-tab-inv pgs-x-tab-zero-tail pgs-x-zero-range-sub))
                  :cases ((< (pgs-t-length pgs-mem) (pgs-x-grow-need 2 b n)))
                  :use ((:instance pgs-x-tab-zero-tail)
                        (:instance pgs-x-zero-range-sub (s 2)
                                   (lo (pgs-x-eaddr 2 b n))
                                   (lo2 (+ 6 (pgs-x-eaddr 2 b n)))
                                   (hi (+ 2048 (* 2048 (pgs-tq n))))
                                   (pgs-mem (pgs-x-grow 2 b n pgs-mem)))))))

(defthm pgs-x-dir-inv-parts
  (implies (pgs-x-dir-inv b nd pgs-mem)
           (and (natp b) (natp nd)
                (<= (+ b (* 2048 (pgs-ptab-run-pages nd))) (pgs-m-length pgs-mem))
                (pgs-x-zero-range 1 (+ b (* 6 nd)) (pgs-m-length pgs-mem) pgs-mem)))
  :rule-classes nil)

(defthm pgs-x-tab-inv-parts
  (implies (pgs-x-tab-inv n pgs-mem)
           (and (natp n)
                (equal (pgs-t-length pgs-mem) (* 2048 (pgs-ntables n)))
                (pgs-x-tpages-canon (pgs-ntables n) n pgs-mem)))
  :rule-classes nil)

(defthm pgs-x-tab-inv-after-append
  (implies (and (pgs-x-tab-inv n pgs-mem) (natp n))
           (pgs-x-tab-inv (+ 1 n) (pgs-x-set-entry 2 b n e (pgs-x-grow 2 b n pgs-mem))))
  :hints (("Goal" :in-theory (disable pgs-x-grow pgs-x-tab-inv pgs-x-tpage-canon-of-appended
                                      pgs-x-tpages-canon-after-grow pgs-x-tpages-canon-prefix
                                      pgs-x-tpage-canon-of-grow-below)
                  :expand ((pgs-x-tab-inv (+ 1 n) (pgs-x-set-entry 2 b n e (pgs-x-grow 2 b n pgs-mem)))
                           (pgs-x-tab-inv 1 (pgs-x-set-entry 2 b 0 e (pgs-x-grow 2 b 0 pgs-mem)))
                           (pgs-x-tpages-canon 1 1 (pgs-x-grow 2 b 0 pgs-mem))
                           (pgs-x-tpages-canon (+ 1 (pgs-tq n)) (+ 1 n) (pgs-x-grow 2 b n pgs-mem)))
                  :use (pgs-x-tpage-canon-of-appended
                        pgs-x-tab-inv-parts
                        (:instance pgs-x-tpages-canon-after-grow (k (pgs-tq n)))
                        (:instance pgs-x-tpages-canon-prefix (k (pgs-ntables n)) (j (pgs-tq n)))))))

(defthm pgs-x-dir-inv-after-append
  (implies (and (pgs-x-dir-inv b n pgs-mem) (natp n))
           (pgs-x-dir-inv b (+ 1 n) (pgs-x-set-entry 1 b n e (pgs-x-grow 1 b n pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-eaddr)
                  :cases ((< (pgs-m-length pgs-mem) (pgs-x-grow-need 1 b n)))
                  :use ((:instance pgs-run-pages-covers (n (+ 1 n)))
                        (:instance pgs-x-zero-range-of-resize-grow (s 1) (lo (+ b (* 6 n)))
                                   (n (pgs-x-grow-need 1 b n)))))))

(defthm pgs-x-inv-after-append
  (implies (and (pgs-x-inv s b n pgs-mem) (pgs-x-sel-p s) (natp n))
           (pgs-x-inv s b (+ 1 n) (pgs-x-set-entry s b n e (pgs-x-grow s b n pgs-mem))))
  :hints (("Goal" :in-theory (disable pgs-x-tab-inv pgs-x-dir-inv pgs-x-grow pgs-x-set-entry))))

(defthm pgs-x-tab-inv-natp
  (implies (pgs-x-tab-inv n pgs-mem) (natp n))
  :rule-classes :forward-chaining)

(defthm pgs-x-dir-inv-natp
  (implies (pgs-x-dir-inv b n pgs-mem) (and (natp n) (natp b)))
  :rule-classes :forward-chaining)

(in-theory (disable pgs-x-tab-inv pgs-x-dir-inv))

; -- The two entry-level refinement theorems.

(defthm pgs-x-set-entry-is-update-nth
  ; Setting entry I < N of the decoded view is `update-nth'.
  (implies (and (pgs-x-inv s b n pgs-mem) (pgs-x-sel-p s) (natp i) (natp n) (< i n)
                (pgs-x-entry-fits e))
           (equal (pgs-x-tab-from s b 0 n (pgs-x-set-entry s b i e pgs-mem))
                  (update-nth i e (pgs-x-tab-from s b 0 n pgs-mem))))
  :hints (("Goal" :use ((:instance pgs-x-tab-from-of-set-entry (i 0) (k i))
                        (:instance pgs-x-inv-entry-in-range))
                  :in-theory (disable pgs-x-tab-from pgs-x-tab-from-of-set-entry
                                      pgs-x-inv-entry-in-range pgs-x-inv))))

(defthm pgs-x-set-entry-at-end-is-append
  ; Setting entry N after growing the array is appending to the decoded view.
  (implies (and (pgs-x-inv s b n pgs-mem) (pgs-x-sel-p s) (natp n) (pgs-x-entry-fits e))
           (equal (pgs-x-tab-from s b 0 (+ 1 n)
                                  (pgs-x-set-entry s b n e (pgs-x-grow s b n pgs-mem)))
                  (append (pgs-x-tab-from s b 0 n pgs-mem) (list e))))
  :hints (("Goal" :use ((:instance pgs-x-tab-from-extend (i 0)
                                   (pgs-mem (pgs-x-set-entry s b n e (pgs-x-grow s b n pgs-mem))))
                        (:instance pgs-x-tab-from-of-set-entry (i 0) (k n)
                                   (pgs-mem (pgs-x-grow s b n pgs-mem)))
                        (:instance pgs-x-tab-from-of-grow (i 0))
                        (:instance pgs-x-inv-in-range-after-grow))
                  :in-theory (disable pgs-x-grow pgs-x-inv pgs-x-tab-from pgs-x-tab-from-extend
                                      pgs-x-tab-from-of-set-entry pgs-x-tab-from-of-grow
                                      pgs-x-inv-in-range-after-grow))))

(defthm pgs-dig4-bound
  (implies (and (unsigned-byte-p 64 w0) (unsigned-byte-p 64 w1)
                (unsigned-byte-p 64 w2) (unsigned-byte-p 64 w3))
           (< (pgs-h64 w3 (pgs-h64 w2 (pgs-h64 w1 w0)))
              115792089237316195423570985008687907853269984665640564039457584007913129639936))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm pgs-x-get-entry-fits
  ; Decoding an entry gives an entry the words represent.
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p s))
           (pgs-x-entry-fits (pgs-x-get-entry s b i pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-get-entry))))

; =============================================================================
; 6. The O(dirty) plan: `pgs-plan-ptab' over the stobj, entry by entry.

(defun pgs-x-plan-fits1 (lpages fresh digests)
  (declare (xargs :guard (and (true-listp fresh) (true-listp digests))))
  (if (atom lpages)
      t
    (and (< (nfix (car fresh)) 18446744073709551616)
         (< (nfix (car digests))
            115792089237316195423570985008687907853269984665640564039457584007913129639936)
         (pgs-x-plan-fits1 (cdr lpages) (cdr fresh) (cdr digests)))))

(defun pgs-x-plan-fits (lpages fresh digests txid)
  ; Every entry the plan writes fits the words: addresses and TXID u64,
  ; digests below 2^256.  O(len LPAGES).
  (declare (xargs :guard (and (true-listp fresh) (true-listp digests))))
  (and (< (nfix txid) 18446744073709551616)
       (pgs-x-plan-fits1 lpages fresh digests)))

(defun pgs-x-mk-entry (f txid d)
  ; The entry the plan writes (`pgs-plan-ptab''s).
  (declare (xargs :guard t))
  (list (nfix f) (nfix txid) (nfix d)))

(defthm pgs-x-mk-entry-facts
  (and (pgs-entry-p (pgs-x-mk-entry f txid d))
       (implies (and (< (nfix f) 18446744073709551616) (< (nfix txid) 18446744073709551616)
                     (< (nfix d) 115792089237316195423570985008687907853269984665640564039457584007913129639936))
                (pgs-x-entry-fits (pgs-x-mk-entry f txid d)))))

(defthm pgs-x-mk-entry-intro
  (equal (cons (nfix f) (cons (nfix txid) (cons (nfix d) nil)))
         (pgs-x-mk-entry f txid d)))

(in-theory (disable pgs-x-mk-entry))

(defthm pgs-x-nfix-when-natp
  (implies (natp n) (equal (nfix n) n)))

(defun pgs-x-plan-entries (sel base lpages fresh digests txid n pgs-mem)
  ; (mv N2 pgs-mem): `pgs-plan-ptab' over SEL's N entries; LPAGES, FRESH
  ; and DIGESTS parallel.  O(len LPAGES) plus a resize per new page.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (pgs-x-sel-p sel) (natp base) (nat-listp lpages)
                              (true-listp fresh) (true-listp digests) (natp n))))
  (if (atom lpages)
      (mv n pgs-mem)
    (let ((l (car lpages))
          (e (pgs-x-mk-entry (car fresh) txid (car digests))))
      (cond ((< l n)
             (let ((pgs-mem (pgs-x-set-entry sel base l e pgs-mem)))
               (pgs-x-plan-entries sel base (cdr lpages) (cdr fresh) (cdr digests) txid n pgs-mem)))
            ((= l n)
             (let* ((pgs-mem (pgs-x-grow sel base n pgs-mem))
                    (pgs-mem (pgs-x-set-entry sel base n e pgs-mem)))
               (pgs-x-plan-entries sel base (cdr lpages) (cdr fresh) (cdr digests) txid
                                   (+ 1 n) pgs-mem)))
            (t (pgs-x-plan-entries sel base (cdr lpages) (cdr fresh) (cdr digests) txid n
                                   pgs-mem))))))

(defthm pgs-update-entry-of-tab-from
  (implies (and (natp i) (natp n))
           (equal (pgs-update-entry i e (pgs-x-tab-from s b 0 n pgs-mem))
                  (cond ((< i n) (update-nth i e (pgs-x-tab-from s b 0 n pgs-mem)))
                        ((equal i n) (append (pgs-x-tab-from s b 0 n pgs-mem) (list e)))
                        (t (pgs-x-tab-from s b 0 n pgs-mem))))))

(local
 (defun-nx pgs-x-plan-ind (s b lpages fresh digests txid n lo mem)
   ; The plan's recursion, with the lower bound `pgs-lpages-ok' carries.
   (declare (xargs :verify-guards nil))
   (if (atom lpages)
       (list n lo mem)
     (let ((l (car lpages))
           (e (pgs-x-mk-entry (car fresh) txid (car digests))))
       (cond ((< l n)
              (let ((mem (pgs-x-set-entry s b l e mem)))
                (pgs-x-plan-ind s b (cdr lpages) (cdr fresh) (cdr digests) txid n (+ 1 l) mem)))
             ((= l n)
              (let* ((mem (pgs-x-grow s b n mem))
                     (mem (pgs-x-set-entry s b n e mem)))
                (pgs-x-plan-ind s b (cdr lpages) (cdr fresh) (cdr digests) txid (+ 1 n) (+ 1 l)
                                mem)))
             (t (pgs-x-plan-ind s b (cdr lpages) (cdr fresh) (cdr digests) txid n (+ 1 l)
                                mem)))))))

(defun pgs-x-plan-len (lpages n)
  (declare (xargs :guard (and (nat-listp lpages) (natp n))))
  (if (atom lpages)
      n
    (let ((l (car lpages)))
      (pgs-x-plan-len (cdr lpages) (if (= l n) (+ 1 n) n)))))

(defthm pgs-x-plan-entries-len-is
  (equal (mv-nth 0 (pgs-x-plan-entries s b lpages fresh digests txid n pgs-mem))
         (pgs-x-plan-len lpages n))
  :hints (("Goal" :induct (pgs-x-plan-entries s b lpages fresh digests txid n pgs-mem)
                  :in-theory (disable pgs-x-grow pgs-x-set-entry))))

(defthm pgs-x-plan-len-is-grown-len
  (implies (and (pgs-lpages-ok lpages n lo) (natp n))
           (equal (pgs-x-plan-len lpages n) (pgs-grown-len lpages n))))

(defthm pgs-x-plan-entries-len
  (implies (and (pgs-lpages-ok lpages n lo) (natp n))
           (equal (mv-nth 0 (pgs-x-plan-entries s b lpages fresh digests txid n pgs-mem))
                  (pgs-grown-len lpages n))))

(in-theory (disable pgs-x-plan-entries-len-is))

(defthm pgs-x-plan-entries-inv
  (implies (and (pgs-x-inv s b n pgs-mem) (pgs-x-sel-p s)
                (pgs-lpages-ok lpages n lo))
           (pgs-x-inv s b (pgs-grown-len lpages n)
                      (mv-nth 1 (pgs-x-plan-entries s b lpages fresh digests txid n pgs-mem))))
  :hints (("Goal" :induct (pgs-x-plan-ind s b lpages fresh digests txid n lo pgs-mem)
                  :in-theory (disable pgs-x-inv pgs-x-grow pgs-x-set-entry pgs-x-tab-from
                                      pgs-x-sel-p))))

(defthm pgs-x-plan-entries-refines
  ; THE PLAN REFINES THE MODEL: over the invariant and in-order dirty pages,
  ; the decoded view after the plan is `pgs-plan-ptab' of the decoded view
  ; before (and its length is `pgs-grown-len', and the invariant holds
  ; after: the two lemmas above).
  (implies (and (pgs-x-inv s b n pgs-mem) (pgs-x-sel-p s)
                (pgs-lpages-ok lpages n lo)
                (pgs-x-plan-fits lpages fresh digests txid))
           (equal (pgs-x-tab-from s b 0 (pgs-grown-len lpages n)
                                  (mv-nth 1 (pgs-x-plan-entries s b lpages fresh digests txid n pgs-mem)))
                  (pgs-plan-ptab (pgs-x-tab-from s b 0 n pgs-mem) lpages fresh digests txid)))
  :hints (("Goal" :induct (pgs-x-plan-ind s b lpages fresh digests txid n lo pgs-mem)
                  :in-theory (disable pgs-x-inv pgs-x-grow pgs-x-set-entry pgs-x-tab-from
                                      pgs-x-sel-p pgs-x-tab-from-extend pgs-x-tab-from-of-set-entry
                                      pgs-x-tab-from-of-grow nfix)
                  :expand ((pgs-lpages-ok lpages n lo)))))

(defthm pgs-x-word-of-grow-other
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (not (equal s s2)) (natp j))
           (equal (pgs-x-word s j (pgs-x-grow s2 b k pgs-mem))
                  (pgs-x-word s j pgs-mem))))

(defthm pgs-x-plan-entries-other-sel
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (not (equal s s2)) (natp j))
           (let ((m2 (mv-nth 1 (pgs-x-plan-entries s2 b lpages fresh digests txid n pgs-mem))))
             (and (equal (pgs-x-len s m2) (pgs-x-len s pgs-mem))
                  (equal (pgs-x-word s j m2) (pgs-x-word s j pgs-mem)))))
  :hints (("Goal" :induct (pgs-x-plan-entries s2 b lpages fresh digests txid n pgs-mem)
                  :in-theory (disable pgs-x-grow pgs-x-set-entry pgs-x-sel-p))))

(defthm pgs-x-plan-entries-other-arrays
  (implies (pgs-x-sel-p s2)
           (let ((m2 (mv-nth 1 (pgs-x-plan-entries s2 b lpages fresh digests txid n pgs-mem))))
             (and (equal (pgs-w-length m2) (pgs-w-length pgs-mem))
                  (equal (pgs-d-length m2) (pgs-d-length pgs-mem))
                  (equal (pgs-v-length m2) (pgs-v-length pgs-mem))
                  (equal (pgs-tv-length m2) (pgs-tv-length pgs-mem))
                  (equal (pgs-wi j m2) (pgs-wi j pgs-mem))
                  (equal (pgs-di j m2) (pgs-di j pgs-mem))
                  (equal (pgs-vi j m2) (pgs-vi j pgs-mem))
                  (equal (pgs-tvi j m2) (pgs-tvi j pgs-mem)))))
  :hints (("Goal" :induct (pgs-x-plan-entries s2 b lpages fresh digests txid n pgs-mem)
                  :in-theory (disable pgs-x-grow pgs-x-set-entry pgs-x-sel-p))))

(defthm pgs-memp-of-plan-entries
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p s))
           (pgs-memp (mv-nth 1 (pgs-x-plan-entries s b lpages fresh digests txid n pgs-mem))))
  :hints (("Goal" :induct (pgs-x-plan-entries s b lpages fresh digests txid n pgs-mem)
                  :in-theory (disable pgs-x-grow pgs-x-set-entry))))

(defun pgs-x-plan-tab (lpages fresh digests txid n pgs-mem)
  ; The flat table's plan: (mv N2 pgs-mem).
  (declare (xargs :stobjs pgs-mem
                  :guard (and (nat-listp lpages) (true-listp fresh) (true-listp digests) (natp n))))
  (pgs-x-plan-entries 2 0 lpages fresh digests txid n pgs-mem))

(defun pgs-x-plan-dir (tl tfresh tdigests txid nd pgs-mem)
  ; The directory's plan: (mv ND2 pgs-mem).
  (declare (xargs :stobjs pgs-mem
                  :guard (and (nat-listp tl) (true-listp tfresh) (true-listp tdigests) (natp nd))))
  (pgs-x-plan-entries 1 *pgs-x-dir-base* tl tfresh tdigests txid nd pgs-mem))

(defthm pgs-x-plan-tab-refines
  (implies (and (pgs-x-tab-inv n pgs-mem)
                (pgs-lpages-ok lpages n 0)
                (pgs-x-plan-fits lpages fresh digests txid))
           (let ((r (pgs-x-plan-tab lpages fresh digests txid n pgs-mem)))
             (and (equal (mv-nth 0 r) (pgs-grown-len lpages n))
                  (equal (pgs-x-tab (pgs-grown-len lpages n) (mv-nth 1 r))
                         (pgs-plan-ptab (pgs-x-tab n pgs-mem) lpages fresh digests txid))
                  (pgs-x-tab-inv (pgs-grown-len lpages n) (mv-nth 1 r)))))
  :hints (("Goal" :use ((:instance pgs-x-plan-entries-refines (s 2) (b 0) (lo 0))
                        (:instance pgs-x-plan-entries-inv (s 2) (b 0) (lo 0)))
                  :in-theory (disable pgs-x-plan-entries-refines pgs-x-plan-entries-inv))))

(defthm pgs-x-plan-dir-refines
  (implies (and (pgs-x-dir-inv *pgs-x-dir-base* nd pgs-mem)
                (pgs-lpages-ok tl nd 0)
                (pgs-x-plan-fits tl tfresh tdigests txid))
           (let ((r (pgs-x-plan-dir tl tfresh tdigests txid nd pgs-mem)))
             (and (equal (mv-nth 0 r) (pgs-grown-len tl nd))
                  (equal (pgs-x-dir (pgs-grown-len tl nd) (mv-nth 1 r))
                         (pgs-plan-ptab (pgs-x-dir nd pgs-mem) tl tfresh tdigests txid))
                  (pgs-x-dir-inv *pgs-x-dir-base* (pgs-grown-len tl nd) (mv-nth 1 r)))))
  :hints (("Goal" :use ((:instance pgs-x-plan-entries-refines (s 1) (b *pgs-x-dir-base*)
                                   (lpages tl) (fresh tfresh) (digests tdigests) (n nd) (lo 0))
                        (:instance pgs-x-plan-entries-inv (s 1) (b *pgs-x-dir-base*)
                                   (lpages tl) (fresh tfresh) (digests tdigests) (n nd) (lo 0)))
                  :in-theory (disable pgs-x-plan-entries-refines pgs-x-plan-entries-inv))))

; =============================================================================
; 7. Page encoding.  A table page is its entries' words, zero padded to
;    2048; the directory run of M pages is its entries' words, zero padded
;    to 2048 M.  List functions: the specification of the words.

(defun pgs-entry-words (e)
  (declare (xargs :guard (pgs-entry-p e)))
  (let ((d (third e)))
    (list (pgs-dlo (first e)) (pgs-dlo (second e))
          (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi d)))) (pgs-dlo (pgs-dhi (pgs-dhi d)))
          (pgs-dlo (pgs-dhi d)) (pgs-dlo d))))

(defun pgs-entries-words (c)
  (declare (xargs :guard (pgs-ptab-p c)))
  (if (atom c) nil (append (pgs-entry-words (car c)) (pgs-entries-words (cdr c)))))

(defun pgs-zeros (k)
  (declare (xargs :guard t :measure (nfix k)))
  (if (zp (nfix k)) nil (cons 0 (pgs-zeros (1- (nfix k))))))

(defun pgs-encode-table (c)
  ; Table page words: the entries, zero padded to 2048.
  (declare (xargs :guard (pgs-ptab-p c)))
  (append (pgs-entries-words c) (pgs-zeros (- 2048 (* 6 (len c))))))

(defun pgs-encode-run (c m)
  ; Directory run words (M pages): the entries, zero padded to 2048 M.
  (declare (xargs :guard (and (pgs-ptab-p c) (natp m))))
  (append (pgs-entries-words c) (pgs-zeros (- (* 2048 (nfix m)) (* 6 (len c))))))

(defun pgs-decode-entry (ws)
  (declare (xargs :guard (true-listp ws)))
  (list (nfix (nth 0 ws)) (nfix (nth 1 ws))
        (pgs-h64 (nth 5 ws) (pgs-h64 (nth 4 ws) (pgs-h64 (nth 3 ws) (nth 2 ws))))))

(defun pgs-decode-table (words k)
  ; K entries from WORDS.
  (declare (xargs :guard (and (true-listp words) (natp k))))
  (if (zp k)
      nil
    (cons (pgs-decode-entry words) (pgs-decode-table (nthcdr 6 words) (1- k)))))

(defun pgs-x-entries-fit (c)
  (declare (xargs :guard t))
  (if (atom c) t (and (pgs-x-entry-fits (car c)) (pgs-x-entries-fit (cdr c)))))

(defthm pgs-len-of-entry-words
  (equal (len (pgs-entry-words e)) 6))

(defthm pgs-decode-entry-of-entry-words
  (implies (pgs-x-entry-fits e)
           (equal (pgs-decode-entry (append (pgs-entry-words e) rest)) e)))

(defthm pgs-nthcdr-6-of-entry-words
  (equal (nthcdr 6 (append (pgs-entry-words e) rest)) rest))

(in-theory (disable pgs-entry-words pgs-decode-entry))

(defthm pgs-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm pgs-decode-entries-words
  (implies (and (pgs-ptab-p c) (pgs-x-entries-fit c))
           (equal (pgs-decode-table (append (pgs-entries-words c) rest) (len c)) c))
  :hints (("Goal" :induct (pgs-x-entries-fit c))))

(defthm pgs-decode-encode-table
  ; Decoding a table page's words gives the table page back.
  (implies (and (pgs-ptab-p c) (pgs-x-entries-fit c))
           (equal (pgs-decode-table (pgs-encode-table c) (len c)) c)))

(defthm pgs-decode-encode-run
  (implies (and (pgs-ptab-p c) (pgs-x-entries-fit c))
           (equal (pgs-decode-table (pgs-encode-run c m) (len c)) c)))

(in-theory (disable pgs-encode-table pgs-encode-run))

; -- The words in the stobj are the encodings.

(defun pgs-x-words (sel a k pgs-mem)
  ; Words A..A+K-1 of SEL, as a list (logical; the host digests in place).
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp a) (natp k) (<= (+ a k) (pgs-x-len sel pgs-mem)))
                  :measure (nfix k)))
  (if (zp k)
      nil
    (cons (pgs-x-word sel a pgs-mem) (pgs-x-words sel (+ 1 a) (1- k) pgs-mem))))

(defthm pgs-x-words-split
  (implies (and (natp a) (natp k1) (natp k2))
           (equal (pgs-x-words s a (+ k1 k2) pgs-mem)
                  (append (pgs-x-words s a k1 pgs-mem)
                          (pgs-x-words s (+ a k1) k2 pgs-mem))))
  :hints (("Goal" :induct (pgs-x-words s a k1 pgs-mem))))

(defthm pgs-x-words-of-zero-range
  (implies (and (pgs-x-zero-range s lo (+ lo k) pgs-mem) (natp lo) (natp k))
           (equal (pgs-x-words s lo k pgs-mem) (pgs-zeros k)))
  :hints (("Goal" :induct (pgs-x-words s lo k pgs-mem))))

(defthm pgs-x-words-of-entry
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p s)
                (<= (+ 6 (pgs-x-eaddr s b i)) (pgs-x-len s pgs-mem)))
           (equal (pgs-x-words s (pgs-x-eaddr s b i) 6 pgs-mem)
                  (pgs-entry-words (pgs-x-get-entry s b i pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-get-entry pgs-entry-words)
                  :expand ((:free (a k) (pgs-x-words s a k pgs-mem))))))

(defthm pgs-x-eaddr-next
  (implies (and (natp i) (or (not (equal s 2)) (< (pgs-tr i) 340)))
           (and (equal (pgs-x-eaddr s b (+ 1 i)) (+ 6 (pgs-x-eaddr s b i)))
                (equal (pgs-tr (+ 1 i)) (if (equal s 2) (+ 1 (pgs-tr i)) (pgs-tr (+ 1 i))))))
  :hints (("Goal" :in-theory (enable pgs-x-eaddr)
                  :use ((:instance pgs-tq-tr-unique (q (pgs-tq i)) (r (+ 1 (pgs-tr i))))
                        (:instance pgs-tq-tr-facts)))))

(local
 (defun pgs-run-ind (i k)
   (if (zp k) (list i k) (pgs-run-ind (+ 1 i) (1- k)))))

(defthm pgs-x-words-of-entries
  ; K consecutive entries whose words are contiguous (one table page, or
  ; the directory run) are their entries' words.
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p s) (natp i) (natp k)
                (or (not (equal s 2)) (<= (+ (pgs-tr i) k) 341))
                (or (zp k) (<= (+ 6 (pgs-x-eaddr s b (+ -1 i k))) (pgs-x-len s pgs-mem))))
           (equal (pgs-x-words s (pgs-x-eaddr s b i) (* 6 k) pgs-mem)
                  (pgs-entries-words (pgs-x-tab-from s b i (+ i k) pgs-mem))))
  :hints (("Goal" :induct (pgs-run-ind i k))
          ("Subgoal *1/2" :use ((:instance pgs-x-words-split (a (pgs-x-eaddr s b i)) (k1 6)
                                           (k2 (* 6 (- k 1))))
                                (:instance pgs-x-eaddr-monotone (i i) (j (+ -1 i k)) (sel s) (base b)))
                          :cases ((equal k 1)))))

(defthm pgs-tab-from-empty
  (implies (<= (nfix n) (nfix i))
           (equal (pgs-x-tab-from s b i n pgs-mem) nil)))

(defthm pgs-consp-of-tab-from
  (equal (consp (pgs-x-tab-from s b i n pgs-mem)) (< (nfix i) (nfix n))))

(defthm pgs-nth-of-tab-from
  (implies (and (natp i) (natp k) (< (+ i k) (nfix n)))
           (equal (nth k (pgs-x-tab-from s b i n pgs-mem))
                  (pgs-x-get-entry s b (+ i k) pgs-mem)))
  :hints (("Goal" :induct (pgs-run-ind i k))))

(defthm pgs-take-of-tab-from
  (implies (and (natp i) (natp k) (<= (+ i k) (nfix n)))
           (equal (take k (pgs-x-tab-from s b i n pgs-mem))
                  (pgs-x-tab-from s b i (+ i k) pgs-mem)))
  :hints (("Goal" :induct (pgs-run-ind i k))))

(defthm pgs-nthcdr-of-tab-from
  (implies (and (natp i) (natp k))
           (equal (nthcdr k (pgs-x-tab-from s b i n pgs-mem))
                  (pgs-x-tab-from s b (+ i k) n pgs-mem)))
  :hints (("Goal" :induct (pgs-run-ind i k))))

(local
 (defun pgs-x-chunk-ind (tp i)
   (if (zp tp) (list tp i) (pgs-x-chunk-ind (1- tp) (+ 341 i)))))

(defthm pgs-nth-chunk-of-tab-from
  ; Table page TP of the decoded view is entries 341 TP ... of it.
  (implies (and (natp i) (natp n) (natp tp) (< (+ i (* 341 tp)) n))
           (equal (nth tp (pgs-chunk (pgs-x-tab-from s b i n pgs-mem)))
                  (pgs-x-tab-from s b (+ i (* 341 tp)) (min n (+ i (* 341 tp) 341)) pgs-mem)))
  :hints (("Goal" :induct (pgs-x-chunk-ind tp i)
                  :expand ((pgs-chunk (pgs-x-tab-from s b i n pgs-mem))))))

(defthm pgs-x-eaddr-2-page-start
  (implies (natp tp)
           (and (equal (pgs-x-eaddr 2 b (* 341 tp)) (* 2048 tp))
                (equal (pgs-tr (* 341 tp)) 0)))
  :hints (("Goal" :use ((:instance pgs-tq-tr-unique (q tp) (r 0)))
                  :in-theory (enable pgs-x-eaddr))))

(defthm pgs-x-tcnt-of-page
  (implies (and (natp n) (natp tp) (< tp (pgs-ntables n)))
           (and (< (* 341 tp) n)
                (< 0 (pgs-x-tcnt tp n))
                (<= (pgs-x-tcnt tp n) 341)
                (<= (+ (* 341 tp) (pgs-x-tcnt tp n)) n)
                (equal (min n (+ 341 (* 341 tp))) (+ (* 341 tp) (pgs-x-tcnt tp n)))))
  :hints (("Goal" :in-theory (enable pgs-x-tcnt)
                  :use ((:instance pgs-tq-tr-facts (i (- n 1))))))
  :rule-classes ((:rewrite :corollary (implies (and (natp n) (natp tp) (< tp (pgs-ntables n)))
                                               (< (* 341 tp) n)))
                 (:linear :corollary (implies (and (natp n) (natp tp) (< tp (pgs-ntables n)))
                                              (< 0 (pgs-x-tcnt tp n))))
                 (:linear :corollary (implies (and (natp n) (natp tp) (< tp (pgs-ntables n)))
                                              (<= (pgs-x-tcnt tp n) 341)))
                 (:linear :corollary (implies (and (natp n) (natp tp) (< tp (pgs-ntables n)))
                                              (<= (+ (* 341 tp) (pgs-x-tcnt tp n)) n)))
                 (:rewrite :corollary (implies (and (natp n) (natp tp) (< tp (pgs-ntables n)))
                                               (equal (min n (+ 341 (* 341 tp)))
                                                      (+ (* 341 tp) (pgs-x-tcnt tp n)))))))

(defthm pgs-x-tcnt-natp
  (natp (pgs-x-tcnt tp n))
  :hints (("Goal" :in-theory (enable pgs-x-tcnt)))
  :rule-classes :type-prescription)

(defthm pgs-x-table-page-words
  ; THE TABLE PAGE'S WORDS ARE ITS ENCODING: under the invariant, the 2048
  ; words of table page TP in pgs-t are `pgs-encode-table' of table page TP
  ; of the decoded flat table.
  (implies (and (pgs-x-tab-inv n pgs-mem) (pgs-memp pgs-mem)
                (natp tp) (< tp (pgs-ntables n)))
           (equal (pgs-x-words 2 (* 2048 tp) 2048 pgs-mem)
                  (pgs-encode-table (nth tp (pgs-chunk (pgs-x-tab n pgs-mem))))))
  :hints (("Goal" :in-theory (e/d (pgs-encode-table pgs-x-tpage-canon)
                                  (pgs-x-words-split pgs-x-words-of-entries pgs-x-tpages-canon-member
                                   pgs-x-inv-entry-in-range))
                  :use ((:instance pgs-x-words-split (s 2) (a (* 2048 tp))
                                   (k1 (* 6 (pgs-x-tcnt tp n))) (k2 (- 2048 (* 6 (pgs-x-tcnt tp n)))))
                        (:instance pgs-x-words-of-entries (s 2) (b 0) (i (* 341 tp))
                                   (k (pgs-x-tcnt tp n)))
                        (:instance pgs-x-tpages-canon-member (k (pgs-ntables n)))
                        (:instance pgs-x-tab-inv-parts)
                        (:instance pgs-x-inv-entry-in-range (s 2) (b 0)
                                   (i (+ -1 (* 341 tp) (pgs-x-tcnt tp n))))))))

(defthm pgs-x-dir-run-words
  ; THE DIRECTORY RUN'S WORDS ARE ITS ENCODING.
  (implies (and (pgs-x-dir-inv b nd pgs-mem) (pgs-memp pgs-mem))
           (equal (pgs-x-words 1 b (* 2048 (pgs-ptab-run-pages nd)) pgs-mem)
                  (pgs-encode-run (pgs-x-tab-from 1 b 0 nd pgs-mem) (pgs-ptab-run-pages nd))))
  :hints (("Goal" :in-theory (e/d (pgs-encode-run pgs-x-dir-inv pgs-x-eaddr)
                                  (pgs-x-words-split pgs-x-words-of-entries pgs-x-inv-entry-in-range))
                  :use ((:instance pgs-x-words-split (s 1) (a b)
                                   (k1 (* 6 nd)) (k2 (- (* 2048 (pgs-ptab-run-pages nd)) (* 6 nd))))
                        (:instance pgs-x-words-of-entries (s 1) (i 0) (k nd))))))

(defthm pgs-entry-p-of-get-entry
  (pgs-entry-p (pgs-x-get-entry s b i pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-get-entry))))

(defthm pgs-ptab-p-of-tab-from
  (pgs-ptab-p (pgs-x-tab-from s b i n pgs-mem)))

(defthm pgs-entries-fit-of-tab-from
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p s))
           (pgs-x-entries-fit (pgs-x-tab-from s b i n pgs-mem))))

(defthm pgs-x-decode-table-page
  ; Decoding table page TP's words at its entry count gives table page TP
  ; of the decoded flat table.
  (implies (and (pgs-x-tab-inv n pgs-mem) (pgs-memp pgs-mem)
                (natp tp) (< tp (pgs-ntables n)))
           (equal (pgs-decode-table (pgs-x-words 2 (* 2048 tp) 2048 pgs-mem) (pgs-x-tcnt tp n))
                  (nth tp (pgs-chunk (pgs-x-tab n pgs-mem)))))
  :hints (("Goal" :in-theory (disable pgs-x-table-page-words pgs-decode-encode-table
                                      pgs-ntables pgs-chunk pgs-ntables-as-tq)
                  :use (pgs-x-table-page-words
                        pgs-x-tab-inv-parts
                        (:instance pgs-decode-encode-table
                                   (c (pgs-x-tab-from 2 0 (* 341 tp) (+ (* 341 tp) (pgs-x-tcnt tp n))
                                                      pgs-mem)))))))

(defthm pgs-x-decode-dir-run
  (implies (and (pgs-x-dir-inv b nd pgs-mem) (pgs-memp pgs-mem))
           (equal (pgs-decode-table (pgs-x-words 1 b (* 2048 (pgs-ptab-run-pages nd)) pgs-mem) nd)
                  (pgs-x-tab-from 1 b 0 nd pgs-mem)))
  :hints (("Goal" :in-theory (disable pgs-x-dir-run-words pgs-decode-encode-run)
                  :use (pgs-x-dir-run-words
                        (:instance pgs-decode-encode-run (c (pgs-x-tab-from 1 b 0 nd pgs-mem))
                                   (m (pgs-ptab-run-pages nd)))))))

; =============================================================================
; 8. Establishing the invariant: the reset (all zero) and the page load.
;
; `pgs-x-fill' is the logical twin of the host's fill primitive (the words
; it leaves are the file's: A-PGS-OBSERVE); a table page the host filled is
; kept only after `pgs-x-tpage-canon' checks it (`pgs-x-open-table-page').

(defun pgs-x-ntables (n)
  ; `pgs-ntables' in O(1).
  (declare (xargs :guard (natp n)))
  (mbe :logic (pgs-ntables n)
       :exec (if (zp n) 0 (+ 1 (floor (- n 1) 341)))))

(local
 (defthm pgs-tvp-of-resize-list
   (implies (pgs-tvp l) (pgs-tvp (resize-list l n 0)))))

(defthm pgs-resize-tv-facts
  (and (equal (pgs-tv-length (resize-pgs-tv k pgs-mem)) (nfix k))
       (implies (pgs-memp pgs-mem) (pgs-memp (resize-pgs-tv k pgs-mem)))
       (equal (pgs-x-len 2 (resize-pgs-tv k pgs-mem)) (pgs-x-len 2 pgs-mem))
       (equal (pgs-t-length (resize-pgs-tv k pgs-mem)) (pgs-t-length pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-tv-length pgs-memp pgs-t-length))))

(in-theory (disable resize-pgs-tv))

(defun pgs-x-reset-table (n pgs-mem)
  ; pgs-t := the zero table pages of a table of N entries; pgs-tv := zeros.
  (declare (xargs :stobjs pgs-mem :guard (natp n)
                  :guard-hints (("Goal" :in-theory (enable pgs-tq)))))
  (let* ((nt (pgs-x-ntables n))
         (pgs-mem (resize-pgs-tv 0 pgs-mem))
         (pgs-mem (resize-pgs-tv nt pgs-mem))
         (pgs-mem (pgs-x-resize 2 0 pgs-mem)))
    (pgs-x-resize 2 (* 2048 nt) pgs-mem)))

(defthm pgs-x-zero-range-of-fresh-resize
  (implies (and (pgs-x-sel-p s) (natp lo) (natp hi) (<= hi (nfix n)))
           (pgs-x-zero-range s lo hi (pgs-x-resize s n (pgs-x-resize s 0 pgs-mem))))
  :hints (("Goal" :use ((:instance pgs-x-zero-range-of-resize-grow (lo lo) (n (nfix n))
                                   (pgs-mem (pgs-x-resize s 0 pgs-mem)))
                        (:instance pgs-x-zero-range-prefix (hi (nfix n)) (hi2 hi)
                                   (pgs-mem (pgs-x-resize s n (pgs-x-resize s 0 pgs-mem)))))
                  :in-theory (disable pgs-x-zero-range-of-resize-grow pgs-x-zero-range-prefix
                                      pgs-x-zero-range-subrange))))

(defthm pgs-x-tpages-canon-of-zero
  (implies (and (natp k) (<= (* 2048 k) (nfix len)))
           (pgs-x-tpages-canon k n (pgs-x-resize 2 len (pgs-x-resize 2 0 pgs-mem))))
  :hints (("Goal" :induct (pgs-run-ind 0 k)
                  :in-theory (enable pgs-x-tpage-canon))))

(defthm pgs-x-reset-table-establishes-inv
  (implies (and (natp n) (pgs-memp pgs-mem))
           (and (pgs-x-tab-inv n (pgs-x-reset-table n pgs-mem))
                (pgs-memp (pgs-x-reset-table n pgs-mem))
                (equal (pgs-tv-length (pgs-x-reset-table n pgs-mem)) (pgs-ntables n))))
  :hints (("Goal" :in-theory (e/d (pgs-x-tab-inv) (pgs-ntables pgs-ntables-as-tq))
                  :use ((:instance pgs-x-tpages-canon-of-zero (k (pgs-ntables n))
                                   (len (* 2048 (pgs-ntables n)))
                                   (pgs-mem (resize-pgs-tv (pgs-ntables n) (resize-pgs-tv 0 pgs-mem)))))))
  :otf-flg t)

(defun pgs-x-u64-listp (ws)
  (declare (xargs :guard t))
  (if (atom ws) (null ws) (and (unsigned-byte-p 64 (car ws)) (pgs-x-u64-listp (cdr ws)))))

(defun pgs-x-fill (sel a ws pgs-mem)
  ; Words A.. of SEL := WS (the host's fill primitive, in the logic).
  (declare (xargs :stobjs pgs-mem
                  :guard (and (pgs-x-sel-p sel) (natp a) (pgs-x-u64-listp ws)
                              (<= (+ a (len ws)) (pgs-x-len sel pgs-mem)))))
  (if (atom ws)
      pgs-mem
    (let ((pgs-mem (pgs-x-put sel a (car ws) pgs-mem)))
      (pgs-x-fill sel (+ 1 a) (cdr ws) pgs-mem))))

(defthm pgs-x-fill-lengths
  (implies (and (pgs-x-sel-p s) (natp a) (<= (+ a (len ws)) (pgs-x-len s pgs-mem)))
           (and (equal (pgs-t-length (pgs-x-fill s a ws pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-m-length (pgs-x-fill s a ws pgs-mem)) (pgs-m-length pgs-mem))))
  :hints (("Goal" :induct (pgs-x-fill s a ws pgs-mem))))

(defthm pgs-memp-of-fill
  (implies (and (pgs-x-sel-p s) (natp a) (<= (+ a (len ws)) (pgs-x-len s pgs-mem))
                (pgs-memp pgs-mem) (pgs-x-u64-listp ws))
           (pgs-memp (pgs-x-fill s a ws pgs-mem)))
  :hints (("Goal" :induct (pgs-x-fill s a ws pgs-mem))))

(defthm pgs-x-zero-range-of-fill-outside
  (implies (and (pgs-x-sel-p s) (natp a) (natp lo) (natp hi)
                (<= (+ a (len ws)) (pgs-x-len s pgs-mem))
                (or (<= hi a) (<= (+ a (len ws)) lo)))
           (equal (pgs-x-zero-range s lo hi (pgs-x-fill s a ws pgs-mem))
                  (pgs-x-zero-range s lo hi pgs-mem)))
  :hints (("Goal" :induct (pgs-x-fill s a ws pgs-mem)
                  :in-theory (disable pgs-x-zero-range))))

(defthm pgs-x-tpage-canon-of-fill-other
  (implies (and (natp tp) (natp tp2) (not (equal tp tp2)) (equal (len ws) 2048)
                (<= (* 2048 (+ 1 tp)) (pgs-t-length pgs-mem)))
           (equal (pgs-x-tpage-canon tp2 n (pgs-x-fill 2 (* 2048 tp) ws pgs-mem))
                  (pgs-x-tpage-canon tp2 n pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-tpage-canon) :cases ((< tp2 tp)))))

(defthm pgs-x-tpages-canon-of-fill-page
  (implies (and (natp tp) (natp k) (equal (len ws) 2048)
                (<= (* 2048 (+ 1 tp)) (pgs-t-length pgs-mem))
                (pgs-x-tpages-canon k n pgs-mem)
                (or (<= k tp) (pgs-x-tpage-canon tp n (pgs-x-fill 2 (* 2048 tp) ws pgs-mem))))
           (pgs-x-tpages-canon k n (pgs-x-fill 2 (* 2048 tp) ws pgs-mem)))
  :hints (("Goal" :induct (pgs-run-ind 0 k)
                  :in-theory (disable pgs-x-fill))
          ("Subgoal *1/2" :cases ((equal (+ -1 k) tp)))))

(defthm pgs-x-fill-table-page-keeps-inv
  ; Loading table page TP keeps the invariant when the loaded page is
  ; canonical (the load's check).
  (implies (and (pgs-x-tab-inv n pgs-mem) (natp tp) (< tp (pgs-ntables n))
                (equal (len ws) 2048)
                (pgs-x-tpage-canon tp n (pgs-x-fill 2 (* 2048 tp) ws pgs-mem)))
           (pgs-x-tab-inv n (pgs-x-fill 2 (* 2048 tp) ws pgs-mem)))
  :hints (("Goal" :in-theory (e/d (pgs-x-tab-inv) (pgs-ntables pgs-ntables-as-tq pgs-x-fill)))))

(local (in-theory (disable fn-shs-p)))

; =============================================================================
; 9. The commit record: 20 words in pgs-m at a slot base (0 or 512):
;    0 magic  1 txid  2 dir-addr  3 npages  4 page words  5-7 zero
;    8-11 dir digest  12-15 zero  16-19 check = SHA-256 of words 0-15.
; A slot of zeros is EMPTY (nil); anything else not of this shape is :torn,
; which `pgs-slot-refusals' names.

(defun pgs-x-put-dig4 (sel a d pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (pgs-x-sel-p sel) (natp a) (<= (+ a 4) (pgs-x-len sel pgs-mem)))))
  (let* ((pgs-mem (pgs-x-put sel a (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi d)))) pgs-mem))
         (pgs-mem (pgs-x-put sel (+ 1 a) (pgs-dlo (pgs-dhi (pgs-dhi d))) pgs-mem))
         (pgs-mem (pgs-x-put sel (+ 2 a) (pgs-dlo (pgs-dhi d)) pgs-mem)))
    (pgs-x-put sel (+ 3 a) (pgs-dlo d) pgs-mem)))

(defthm pgs-x-put-dig4-facts
  (implies (and (pgs-x-sel-p s2) (natp a) (<= (+ a 4) (pgs-x-len s2 pgs-mem)))
           (and (equal (pgs-x-len s (pgs-x-put-dig4 s2 a d pgs-mem)) (pgs-x-len s pgs-mem))
                (equal (pgs-m-length (pgs-x-put-dig4 s2 a d pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (pgs-x-put-dig4 s2 a d pgs-mem)) (pgs-t-length pgs-mem))
                (implies (pgs-memp pgs-mem) (pgs-memp (pgs-x-put-dig4 s2 a d pgs-mem))))))

(in-theory (disable pgs-x-put-dig4))

(defun pgs-x-read-rec (base pgs-mem fn-shs)
  ; (mv RECORD CHECK fn-shs): the record slot BASE holds (nil when empty,
  ; :torn when malformed) and the check observed over its words 0-15.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp base) (<= (+ base *pgs-rec-words*) (pgs-m-length pgs-mem)))))
  (mv-let (check fn-shs)
    (pgs-x-words-digest 1 base 2 pgs-mem fn-shs)
    (mv (cond ((pgs-x-zero-range 1 base (+ base *pgs-rec-words*) pgs-mem) nil)
              ((and (equal (pgs-mi base pgs-mem) *pgs-magic*)
                    (equal (pgs-mi (+ 4 base) pgs-mem) *pgs-page-words*)
                    (pgs-x-zero-range 1 (+ 5 base) (+ 8 base) pgs-mem)
                    (pgs-x-zero-range 1 (+ 12 base) (+ 16 base) pgs-mem))
               (list :pgs-commit
                     (pgs-mi (+ 1 base) pgs-mem) (pgs-mi (+ 2 base) pgs-mem)
                     (pgs-mi (+ 3 base) pgs-mem) (pgs-x-dig4 1 (+ 8 base) pgs-mem)
                     (pgs-x-dig4 1 (+ 16 base) pgs-mem)))
              (t :torn))
        check
        fn-shs)))

(defun pgs-x-zero-words (sel a k pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (pgs-x-sel-p sel) (natp a) (natp k) (<= (+ a k) (pgs-x-len sel pgs-mem)))
                  :measure (nfix k)))
  (if (zp k)
      pgs-mem
    (let ((pgs-mem (pgs-x-put sel a 0 pgs-mem)))
      (pgs-x-zero-words sel (+ 1 a) (1- k) pgs-mem))))

(defthm pgs-x-zero-words-facts
  (implies (and (pgs-x-sel-p s2) (natp a) (natp k) (<= (+ a k) (pgs-x-len s2 pgs-mem)))
           (and (equal (pgs-x-len s (pgs-x-zero-words s2 a k pgs-mem)) (pgs-x-len s pgs-mem))
                (equal (pgs-m-length (pgs-x-zero-words s2 a k pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (pgs-x-zero-words s2 a k pgs-mem)) (pgs-t-length pgs-mem))
                (implies (pgs-memp pgs-mem) (pgs-memp (pgs-x-zero-words s2 a k pgs-mem)))))
  :hints (("Goal" :induct (pgs-x-zero-words s2 a k pgs-mem))))

(in-theory (disable pgs-x-zero-words))

(defun pgs-x-write-rec (base txid addr npages ddig pgs-mem fn-shs)
  ; Encode the record at slot BASE and compute its check:
  ; (mv RECORD pgs-mem fn-shs), RECORD the one the words hold.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp base) (<= (+ base *pgs-rec-words*) (pgs-m-length pgs-mem)))))
  (let* ((pgs-mem (pgs-x-zero-words 1 base *pgs-rec-words* pgs-mem))
         (pgs-mem (pgs-x-put 1 base *pgs-magic* pgs-mem))
         (pgs-mem (pgs-x-put 1 (+ 1 base) (pgs-dlo txid) pgs-mem))
         (pgs-mem (pgs-x-put 1 (+ 2 base) (pgs-dlo addr) pgs-mem))
         (pgs-mem (pgs-x-put 1 (+ 3 base) (pgs-dlo npages) pgs-mem))
         (pgs-mem (pgs-x-put 1 (+ 4 base) *pgs-page-words* pgs-mem))
         (pgs-mem (pgs-x-put-dig4 1 (+ 8 base) ddig pgs-mem)))
    (mv-let (check fn-shs)
      (pgs-x-words-digest 1 base 2 pgs-mem fn-shs)
      (let ((pgs-mem (pgs-x-put-dig4 1 (+ 16 base) check pgs-mem)))
        (mv (list :pgs-commit (pgs-dlo txid) (pgs-dlo addr) (pgs-dlo npages)
                  (pgs-x-dig4 1 (+ 8 base) pgs-mem) (pgs-x-dig4 1 (+ 16 base) pgs-mem))
            pgs-mem fn-shs)))))

(defthm pgs-x-write-rec-facts
  (implies (and (natp base) (<= (+ base 20) (pgs-m-length pgs-mem)))
           (and (equal (pgs-m-length (mv-nth 1 (pgs-x-write-rec base txid addr npages ddig pgs-mem fn-shs)))
                       (pgs-m-length pgs-mem))
                (implies (pgs-memp pgs-mem)
                         (pgs-memp (mv-nth 1 (pgs-x-write-rec base txid addr npages ddig pgs-mem fn-shs))))
                (implies (fn-shs-p fn-shs)
                         (fn-shs-p (mv-nth 2 (pgs-x-write-rec base txid addr npages ddig pgs-mem fn-shs)))))))

(in-theory (disable pgs-x-write-rec pgs-x-read-rec))

; =============================================================================
; 10. The open: the directory, then table pages and data pages on demand.
;
; The host reads both slots (`pgs-x-read-rec' 0 and 512), orders them
; (`pgs-rec-ok', `pgs-open-order', `pgs-slot-refusals'), and for a
; candidate record REC:
;   1. fills pgs-m from *pgs-x-dir-base* with the directory run
;      ((pgs-dir-run-pages npages) pages at the record's dir-addr) and calls
;      `pgs-x-open-dir';
;   2. calls `pgs-x-reset-table' (npages) and sizes pgs-w, pgs-v, pgs-d;
;   3. for each (T PHYS) of `pgs-x-open-tables', fills table page T from
;      PHYS and calls `pgs-x-open-table-page' (every one's digest first,
;      then the shapes: `pgs-try''s order, see `pgs-x-open-tables');
;   4. for each (I PHYS) of `pgs-x-open-pages' of each verified table page,
;      fills image page I and calls `pgs-x-open-page'.
; Eager mode lists every table and data page; lazy mode only those the
; record's own commit wrote (entry TXID = the record's), the rest load on
; first touch through `pgs-x-read'.  Open costs O(directory + what it
; lists); pgs-t is allocated whole (zero) at open.

(defun pgs-x-dir-verdict (rec nt observed pgs-mem)
  ; The model's directory verdict over the decoded run, then the run's
  ; zero padding (a stronger local check: the words must be canonical).
  (declare (xargs :stobjs pgs-mem :guard (natp nt)))
  (or (pgs-dir-verdict rec (pgs-x-dir nt pgs-mem) observed)
      (if (pgs-x-zero-range 1 (+ *pgs-x-dir-base* (* 6 nt)) (pgs-m-length pgs-mem) pgs-mem)
          nil
        (list :dir-malformed (pgs-rec-dir-addr rec)))))

(defun pgs-x-open-dir (rec pgs-mem fn-shs)
  ; (mv VERDICT fn-shs): nil when REC's directory run (in pgs-m from
  ; *pgs-x-dir-base*) is sound, else the refusal.
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard t))
  (let* ((nt (pgs-x-ntables (pgs-rec-npages rec)))
         (m (pgs-ptab-run-pages nt)))
    (if (not (and (<= (+ *pgs-x-dir-base* (* 2048 m)) (pgs-m-length pgs-mem))
                  (< m 4294967296)))
        (mv (list :dir-unloaded (pgs-rec-dir-addr rec)) fn-shs)
      (mv-let (observed fn-shs)
        (pgs-x-words-digest 1 *pgs-x-dir-base* (* 256 m) pgs-mem fn-shs)
        (mv (pgs-x-dir-verdict rec nt observed pgs-mem) fn-shs)))))

(defthm pgs-x-dir-verdict-establishes-inv
  ; A directory the open accepts satisfies the representation invariant.
  (implies (and (not (pgs-x-dir-verdict rec nt observed pgs-mem)) (natp nt)
                (<= (+ *pgs-x-dir-base* (* 2048 (pgs-ptab-run-pages nt))) (pgs-m-length pgs-mem)))
           (pgs-x-dir-inv *pgs-x-dir-base* nt pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-dir-inv))))

(defthm pgs-x-dir-verdict-is-model
  ; Over canonical words, the open's directory verdict IS the model's
  ; `pgs-dir-verdict' of the decoded run.
  (implies (and (pgs-x-dir-inv *pgs-x-dir-base* nt pgs-mem) (pgs-memp pgs-mem))
           (equal (pgs-x-dir-verdict rec nt observed pgs-mem)
                  (pgs-dir-verdict rec
                                   (pgs-decode-table
                                    (pgs-x-words 1 *pgs-x-dir-base* (* 2048 (pgs-ptab-run-pages nt)) pgs-mem)
                                    nt)
                                   observed)))
  :hints (("Goal" :in-theory (disable pgs-x-decode-dir-run pgs-x-dir-run-words pgs-x-tab-from
                                      pgs-dir-verdict pgs-ptab-run-pages pgs-decode-table)
                  :use ((:instance pgs-x-decode-dir-run (b *pgs-x-dir-base*) (nd nt))
                        (:instance pgs-x-dir-inv-parts (b *pgs-x-dir-base*) (nd nt))))))

(in-theory (disable pgs-x-dir-verdict))

(defun pgs-x-table-verdict (tp npages txid mode observed pgs-mem)
  ; Table page TP (filled): its digest against directory entry TP (the
  ; model's `pgs-check-pages' step, :table-damaged), its padding, and its
  ; shape (`pgs-table-ok' with REM = NPAGES - 341 TP, :table-malformed).
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp tp) (natp npages) (<= (* 2048 (+ 1 tp)) (pgs-t-length pgs-mem)))))
  (let ((d (pgs-x-get-entry 1 *pgs-x-dir-base* tp pgs-mem)))
    (cond ((eq (pgs-entry-verdict d txid mode observed) :damaged)
           (list :table-damaged tp (first d)))
          ((not (pgs-x-tpage-canon tp npages pgs-mem))
           (list :table-malformed tp))
          ((not (pgs-table-ok (pgs-x-tab-from 2 0 (* 341 tp) (+ (* 341 tp) (pgs-x-tcnt tp npages)) pgs-mem)
                              (- npages (* 341 tp)) txid))
           (list :table-malformed tp))
          (t nil))))

(defthm pgs-x-table-verdict-is-model
  ; Over the invariant, the table page's verdict is the model's two steps
  ; for page TP: `pgs-entry-verdict' against directory entry TP, then
  ; `pgs-table-ok' of the page's decoded words.
  (implies (and (pgs-x-tab-inv npages pgs-mem) (pgs-memp pgs-mem)
                (natp tp) (< tp (pgs-ntables npages)))
           (equal (pgs-x-table-verdict tp npages txid mode observed pgs-mem)
                  (let ((d (nth tp (pgs-x-dir (pgs-ntables npages) pgs-mem))))
                    (cond ((eq (pgs-entry-verdict d txid mode observed) :damaged)
                           (list :table-damaged tp (first d)))
                          ((not (pgs-table-ok (pgs-decode-table (pgs-x-words 2 (* 2048 tp) 2048 pgs-mem)
                                                                (pgs-x-tcnt tp npages))
                                              (- npages (* 341 tp)) txid))
                           (list :table-malformed tp))
                          (t nil)))))
  :hints (("Goal" :in-theory (disable pgs-table-ok pgs-entry-verdict pgs-x-decode-table-page
                                      pgs-ntables pgs-ntables-as-tq pgs-chunk pgs-x-tab-from
                                      pgs-x-tpages-canon-member pgs-x-table-page-words)
                  :use ((:instance pgs-x-decode-table-page (n npages)) (:instance pgs-x-tab-inv-parts (n npages))
                        (:instance pgs-x-tpages-canon-member (k (pgs-ntables npages)) (n npages))))))

(defun pgs-x-open-table-page (tp rec mode pgs-mem fn-shs)
  ; (mv VERDICT pgs-mem fn-shs) after the host filled table page TP of
  ; pgs-t from the address directory entry TP names: nil (and table page TP
  ; marked verified) or the refusal.  MODE :eager at a first touch.
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (natp tp)))
  (let* ((npages (pgs-rec-npages rec)))
    (if (not (and (< tp (pgs-x-ntables npages))
                  (<= (* 2048 (+ 1 tp)) (pgs-t-length pgs-mem))
                  (< tp (pgs-tv-length pgs-mem))))
        (mv (list :table-unloaded tp) pgs-mem fn-shs)
      (mv-let (observed fn-shs)
        (pgs-x-words-digest 2 (* 2048 tp) 256 pgs-mem fn-shs)
        (let ((v (pgs-x-table-verdict tp npages (pgs-rec-txid rec) mode observed pgs-mem)))
          (if v
              (mv v pgs-mem fn-shs)
            (let ((pgs-mem (update-pgs-tvi tp 2 pgs-mem)))
              (mv nil pgs-mem fn-shs))))))))

(defun pgs-x-open-tables (j nt txid mode acc pgs-mem)
  ; The table pages J..NT-1 the open loads now, as (T PHYS), ascending onto
  ; the reverse of ACC: every one in :eager mode, those whose directory
  ; entry's TXID is the record's in :lazy mode.  O(NT).
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp j) (natp nt) (true-listp acc))
                  :measure (nfix (- (nfix nt) (nfix j)))))
  (if (mbe :logic (zp (- (nfix nt) (nfix j))) :exec (<= nt j))
      (reverse acc)
    (let ((d (pgs-x-get-entry 1 *pgs-x-dir-base* j pgs-mem)))
      (pgs-x-open-tables (+ 1 (nfix j)) nt txid mode
                         (if (pgs-entry-checked-p d txid mode) (cons (list j (first d)) acc) acc)
                         pgs-mem))))

(defun pgs-x-open-pages (i hi txid mode acc pgs-mem)
  ; The data pages I..HI-1 (one table page's) the open loads now, as
  ; (I PHYS).  O(HI - I).
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp hi) (true-listp acc))
                  :measure (nfix (- (nfix hi) (nfix i)))))
  (if (mbe :logic (zp (- (nfix hi) (nfix i))) :exec (<= hi i))
      (reverse acc)
    (let ((e (pgs-x-get-entry 2 0 i pgs-mem)))
      (pgs-x-open-pages (+ 1 (nfix i)) hi txid mode
                        (if (pgs-entry-checked-p e txid mode) (cons (list i (first e)) acc) acc)
                        pgs-mem))))

(defun pgs-x-table-page-range (tp npages)
  ; (LO HI): the logical pages table page TP holds.
  (declare (xargs :guard (and (natp tp) (natp npages))))
  (list (* 341 tp) (+ (* 341 tp) (pgs-x-tcnt tp npages))))

(defun pgs-x-open-page (i txid mode pgs-mem fn-shs)
  ; (mv VERDICT pgs-mem fn-shs) after the host filled image page I from
  ; the address its entry names: nil (page I marked verified when MODE
  ; checks it, resident otherwise), (:need-table T) when its table page is
  ; not verified, or (:page-damaged I PHYS) -- `pgs-check-pages''s step.
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (natp i)))
  (let ((tp (floor i 341)))
    (cond ((not (and (< i (pgs-v-length pgs-mem))
                     (<= (* 2048 (+ 1 i)) (pgs-w-length pgs-mem))
                     (< tp (pgs-tv-length pgs-mem))))
           (mv (list :page-unloaded i) pgs-mem fn-shs))
          ((not (equal (pgs-tvi tp pgs-mem) 2))
           (mv (list :need-table tp) pgs-mem fn-shs))
          (t (let ((e (pgs-x-get-entry 2 0 i pgs-mem)))
               (mv-let (observed fn-shs)
                 (pgs-x-page-digest i pgs-mem fn-shs)
                 (if (eq (pgs-entry-verdict e txid mode observed) :damaged)
                     (mv (list :page-damaged i (first e)) pgs-mem fn-shs)
                   (let ((pgs-mem (update-pgs-vi i (if (pgs-entry-checked-p e txid mode) 2 1) pgs-mem)))
                     (mv nil pgs-mem fn-shs)))))))))

(defthm pgs-x-get-entry-is-nth-tab
  ; The entry `pgs-x-open-page' and `pgs-x-read' check a data page against
  ; is entry I of the decoded table: their refusal is `pgs-check-pages''s
  ; step for entry I, over the digest observed.
  (implies (and (natp i) (natp n) (< i n))
           (equal (nth i (pgs-x-tab n pgs-mem)) (pgs-x-get-entry 2 0 i pgs-mem))))

; -----------------------------------------------------------------------------
; Reads through the store, on demand.

(defun pgs-x-read (i off pgs-mem fn-shs)
  ; Word OFF of logical page I: (mv VERDICT WORD pgs-mem fn-shs), VERDICT
  ;   :ok
  ;   (:need-table T PHYS)  fill table page T from PHYS, call
  ;                         `pgs-x-open-table-page' T with :eager, retry
  ;   (:need-page I PHYS)   fill image page I from PHYS, call
  ;                         `pgs-x-open-page' I with :eager, retry
  ;   (:page-damaged I PHYS), (:table-damaged ...) never a value
  ;   :out-of-range
  ; A resident, unverified page (lazy open) is verified here, at first touch.
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (and (natp i) (natp off))))
  (let ((tp (floor i 341)))
    (cond ((not (and (< off 2048)
                     (< i (pgs-v-length pgs-mem))
                     (<= (* 2048 (+ 1 i)) (pgs-w-length pgs-mem))
                     (< tp (pgs-tv-length pgs-mem))))
           (mv :out-of-range 0 pgs-mem fn-shs))
          ((not (equal (pgs-tvi tp pgs-mem) 2))
           (mv (list :need-table tp (first (pgs-x-get-entry 1 *pgs-x-dir-base* tp pgs-mem)))
               0 pgs-mem fn-shs))
          ((equal (pgs-vi i pgs-mem) 0)
           (mv (list :need-page i (first (pgs-x-get-entry 2 0 i pgs-mem))) 0 pgs-mem fn-shs))
          ((equal (pgs-vi i pgs-mem) 2)
           (mv :ok (pgs-wi (+ (* 2048 i) off) pgs-mem) pgs-mem fn-shs))
          (t (let ((e (pgs-x-get-entry 2 0 i pgs-mem)))
               (mv-let (observed fn-shs)
                 (pgs-x-page-digest i pgs-mem fn-shs)
                 (if (eq (pgs-entry-verdict e 0 :eager observed) :damaged)
                     (mv (list :page-damaged i (first e)) 0 pgs-mem fn-shs)
                   (let ((pgs-mem (update-pgs-vi i 2 pgs-mem)))
                     (mv :ok (pgs-wi (+ (* 2048 i) off) pgs-mem) pgs-mem fn-shs)))))))))

(defthm pgs-x-read-stobjs
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs) (natp i))
           (let ((r (pgs-x-read i off pgs-mem fn-shs)))
             (and (pgs-memp (mv-nth 2 r))
                  (fn-shs-p (mv-nth 3 r))
                  (equal (pgs-w-length (mv-nth 2 r)) (pgs-w-length pgs-mem))
                  (equal (pgs-v-length (mv-nth 2 r)) (pgs-v-length pgs-mem))
                  (equal (pgs-tv-length (mv-nth 2 r)) (pgs-tv-length pgs-mem))))))

(in-theory (disable pgs-x-read))

; =============================================================================
; 11. The commit, as the host calls it.
;
;   (pgs-x-dirty-list (pgs-d-length) nil pgs-mem) -> LPAGES, ascending
;   (pgs-x-commit LPAGES N TXID ALLOC SLOT pgs-mem fn-shs) -> a plan, or a
;     refusal before anything changed, or (:need-table T PHYS) (lazy mode:
;     load it and retry)
;   the host writes, in order: each data page LPAGES[k] (pgs-w words
;   [2048 l, 2048 l + 2048)) to FRESH[k]; each table page TL[k] (pgs-t words
;   [2048 T, 2048 T + 2048)) to TFRESH[k]; the directory run (pgs-m words
;   [*pgs-x-dir-base*, + 2048 M)) to RUN-START..RUN-START+M-1; the record
;   (pgs-m words [SLOT, SLOT + 20)) to the root's slot; one barrier;
;   then, only once the record is durable, (pgs-x-commit-durable LPAGES).
; A failure after `pgs-x-commit' answered a plan is a recovery event: the
; stobj holds the new table and directory, so the host re-opens.

(defun pgs-x-dirty-list (j acc pgs-mem)
  ; The dirty logical pages below J, ascending, onto ACC.  O(J): a scan of
  ; the dirty flags (a dirty-page list kept by the writers would make it
  ; O(dirty); not done).
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp j) (<= j (pgs-d-length pgs-mem)))
                  :measure (nfix j)))
  (if (zp j)
      acc
    (pgs-x-dirty-list (1- j)
                      (if (equal (pgs-di (1- j) pgs-mem) 1) (cons (1- j) acc) acc)
                      pgs-mem)))

(defun pgs-x-lpages-resident (lpages pgs-mem)
  ; Every dirty page is in the image.
  (declare (xargs :stobjs pgs-mem :guard (nat-listp lpages)))
  (if (atom lpages)
      t
    (and (<= (* 2048 (+ 1 (car lpages))) (pgs-w-length pgs-mem))
         (< (car lpages) (pgs-v-length pgs-mem))
         (< (car lpages) (pgs-d-length pgs-mem))
         (pgs-x-lpages-resident (cdr lpages) pgs-mem))))

(defun pgs-x-dirty-digests (lpages pgs-mem fn-shs)
  ; (mv DIGESTS fn-shs): the SHA-256 of each dirty page's words.
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (nat-listp lpages)))
  (if (atom lpages)
      (mv nil fn-shs)
    (mv-let (d fn-shs)
      (if (<= (* 2048 (+ 1 (car lpages))) (pgs-w-length pgs-mem))
          (pgs-x-page-digest (car lpages) pgs-mem fn-shs)
        (mv 0 fn-shs))
      (mv-let (ds fn-shs)
        (pgs-x-dirty-digests (cdr lpages) pgs-mem fn-shs)
        (mv (cons d ds) fn-shs)))))

(defthm pgs-x-dirty-digests-facts
  (and (true-listp (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-shs)))
       (true-listp (car (pgs-x-dirty-digests lpages pgs-mem fn-shs)))
       (implies (fn-shs-p fn-shs) (fn-shs-p (mv-nth 1 (pgs-x-dirty-digests lpages pgs-mem fn-shs))))))

(defun pgs-x-tables-ready (tl nt pgs-mem)
  ; nil when every existing table page in TL is verified, else
  ; (:need-table T PHYS) for the first that is not.
  (declare (xargs :stobjs pgs-mem :guard (and (nat-listp tl) (natp nt))))
  (cond ((atom tl) nil)
        ((and (< (car tl) nt)
              (not (and (< (car tl) (pgs-tv-length pgs-mem)) (equal (pgs-tvi (car tl) pgs-mem) 2))))
         (list :need-table (car tl) (first (pgs-x-get-entry 1 *pgs-x-dir-base* (car tl) pgs-mem))))
        (t (pgs-x-tables-ready (cdr tl) nt pgs-mem))))

(defun pgs-x-table-digests (tl pgs-mem fn-shs)
  ; (mv DIGESTS fn-shs): the SHA-256 of each table page in TL, over its
  ; 2048 words in pgs-t (taken mod 2^256, the identity on a SHA-256 value).
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (nat-listp tl)))
  (if (atom tl)
      (mv nil fn-shs)
    (mv-let (d fn-shs)
      (if (<= (* 2048 (+ 1 (car tl))) (pgs-t-length pgs-mem))
          (pgs-x-words-digest 2 (* 2048 (car tl)) 256 pgs-mem fn-shs)
        (mv 0 fn-shs))
      (mv-let (ds fn-shs)
        (pgs-x-table-digests (cdr tl) pgs-mem fn-shs)
        (mv (cons (mod (nfix d) 115792089237316195423570985008687907853269984665640564039457584007913129639936) ds)
            fn-shs)))))

(defun pgs-x-u64-bounded (xs)
  (declare (xargs :guard t))
  (if (atom xs) t (and (< (nfix (car xs)) 18446744073709551616) (pgs-x-u64-bounded (cdr xs)))))

(defthm pgs-x-table-digests-true-listp
  (and (true-listp (mv-nth 0 (pgs-x-table-digests tl pgs-mem fn-shs)))
       (true-listp (car (pgs-x-table-digests tl pgs-mem fn-shs)))))

(defthm pgs-x-table-digests-shs
  (implies (fn-shs-p fn-shs) (fn-shs-p (mv-nth 1 (pgs-x-table-digests tl pgs-mem fn-shs)))))

(defun pgs-x-mod256-listp (ds)
  (declare (xargs :guard t))
  (if (atom ds)
      t
    (and (< (nfix (car ds)) 115792089237316195423570985008687907853269984665640564039457584007913129639936)
         (pgs-x-mod256-listp (cdr ds)))))

(defthm pgs-x-table-digests-bounded
  (and (pgs-x-mod256-listp (mv-nth 0 (pgs-x-table-digests tl pgs-mem fn-shs)))
       (pgs-x-mod256-listp (car (pgs-x-table-digests tl pgs-mem fn-shs)))))

(defthm pgs-x-plan-fits1-when-bounded
  (implies (and (pgs-x-u64-bounded fresh) (pgs-x-mod256-listp ds))
           (pgs-x-plan-fits1 tl fresh ds)))

(in-theory (disable pgs-x-table-digests))

(defun pgs-x-mark-tables1 (tl pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (nat-listp tl)))
  (if (atom tl)
      pgs-mem
    (let ((pgs-mem (if (< (car tl) (pgs-tv-length pgs-mem)) (update-pgs-tvi (car tl) 2 pgs-mem) pgs-mem)))
      (pgs-x-mark-tables1 (cdr tl) pgs-mem))))

(defthm pgs-x-word-of-update-tvi
  (and (equal (pgs-x-word 1 j (update-pgs-tvi i v pgs-mem)) (pgs-x-word 1 j pgs-mem))
       (equal (pgs-x-word 2 j (update-pgs-tvi i v pgs-mem)) (pgs-x-word 2 j pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-word$inline pgs-mi pgs-ti update-pgs-tvi))))

(defthm pgs-x-mark-tables1-frame
  (let ((m2 (pgs-x-mark-tables1 tl pgs-mem)))
   (implies (nat-listp tl)
    (and (equal (pgs-m-length m2) (pgs-m-length pgs-mem))
         (equal (pgs-t-length m2) (pgs-t-length pgs-mem))
         (equal (pgs-w-length m2) (pgs-w-length pgs-mem))
         (equal (pgs-tv-length m2) (pgs-tv-length pgs-mem))
         (equal (pgs-x-word 1 j m2) (pgs-x-word 1 j pgs-mem))
         (equal (pgs-x-word 2 j m2) (pgs-x-word 2 j pgs-mem))
         (implies (pgs-memp pgs-mem) (pgs-memp m2)))))
  :hints (("Goal" :induct (pgs-x-mark-tables1 tl pgs-mem))))

(defthm pgs-x-word-of-resize-tv
  (and (equal (pgs-x-word 1 j (resize-pgs-tv k pgs-mem)) (pgs-x-word 1 j pgs-mem))
       (equal (pgs-x-word 2 j (resize-pgs-tv k pgs-mem)) (pgs-x-word 2 j pgs-mem))
       (equal (pgs-m-length (resize-pgs-tv k pgs-mem)) (pgs-m-length pgs-mem))
       (equal (pgs-w-length (resize-pgs-tv k pgs-mem)) (pgs-w-length pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-word$inline pgs-mi pgs-ti resize-pgs-tv
                                     pgs-m-length pgs-w-length))))

(defun pgs-x-mark-tables (tl nt2 pgs-mem)
  ; pgs-tv covers NT2 table pages; the rewritten ones in TL are verified.
  (declare (xargs :stobjs pgs-mem :guard (and (nat-listp tl) (natp nt2))))
  (let ((pgs-mem (if (< (pgs-tv-length pgs-mem) nt2) (resize-pgs-tv nt2 pgs-mem) pgs-mem)))
    (pgs-x-mark-tables1 tl pgs-mem)))

(defthm pgs-x-mark-tables-frame
  ; Marking touches only the table pages' flags.
  (let ((m2 (pgs-x-mark-tables tl nt2 pgs-mem)))
   (implies (nat-listp tl)
    (and (equal (pgs-x-len 1 m2) (pgs-x-len 1 pgs-mem))
         (equal (pgs-x-len 2 m2) (pgs-x-len 2 pgs-mem))
         (equal (pgs-m-length m2) (pgs-m-length pgs-mem))
         (equal (pgs-t-length m2) (pgs-t-length pgs-mem))
         (equal (pgs-x-word 1 j m2) (pgs-x-word 1 j pgs-mem))
         (equal (pgs-x-word 2 j m2) (pgs-x-word 2 j pgs-mem))
         (implies (pgs-memp pgs-mem) (pgs-memp m2)))))
  :hints (("Goal" :in-theory (disable pgs-x-mark-tables1)
                  :expand ((pgs-x-mark-tables tl nt2 pgs-mem)))))

(in-theory (disable pgs-x-mark-tables))

(defun pgs-x-ensure-m (k pgs-mem)
  ; pgs-m reaches K words (a no-op under the directory invariant).
  (declare (xargs :stobjs pgs-mem :guard (natp k)))
  (if (< (pgs-m-length pgs-mem) k) (pgs-x-resize 1 k pgs-mem) pgs-mem))

(defthm pgs-x-nat-listp-of-touched
  (nat-listp (pgs-touched lpages prev)))

(defthm pgs-x-dir-run-pages-posp
  (and (integerp (pgs-dir-run-pages n)) (<= 1 (pgs-dir-run-pages n)))
  :rule-classes ((:type-prescription :corollary (integerp (pgs-dir-run-pages n)))
                 (:linear :corollary (<= 1 (pgs-dir-run-pages n)))))

(defun pgs-x-commit-prepare (lpages n txid alloc pgs-mem fn-shs)
  ; The commit's checks and allocation, changing nothing but fn-shs:
  ; (mv VERDICT PLAN fn-shs), VERDICT nil or the refusal / (:need-table T
  ; PHYS); PLAN (TL FRESH TFRESH DIGESTS RUN-START M N2 NT2 ALLOC2).
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (nat-listp lpages) (natp n))
                  :guard-hints (("Goal" :in-theory (disable pgs-alloc pgs-grown-len pgs-touched
                                                            pgs-lpages-ok pgs-x-plan-fits
                                                            pgs-dir-run-pages pgs-x-ntables
                                                            pgs-x-dirty-digests pgs-ptab-run-pages
                                                            pgs-x-lpages-resident pgs-x-tables-ready)))))
  (let* ((nt (pgs-x-ntables n)))
    (cond
     ((not (pgs-lpages-ok lpages n 0))
      (mv (list :refused :dirty-out-of-order) nil fn-shs))
     ((not (pgs-x-lpages-resident lpages pgs-mem))
      (mv (list :refused :dirty-not-resident) nil fn-shs))
     ((not (and (equal (pgs-t-length pgs-mem) (* 2048 nt))
                (<= (+ *pgs-x-dir-base* (* 2048 (pgs-ptab-run-pages nt))) (pgs-m-length pgs-mem))
                (<= nt (pgs-tv-length pgs-mem))))
      (mv (list :refused :state-unloaded) nil fn-shs))
     (t
      (let* ((tl (pgs-touched lpages nil))
             (need (pgs-x-tables-ready tl nt pgs-mem)))
        (cond
         (need (mv need nil fn-shs))
         ((not (pgs-lpages-ok tl nt 0))
          (mv (list :refused :touched-out-of-order) nil fn-shs))
         (t
          (mv-let (digests fn-shs)
            (pgs-x-dirty-digests lpages pgs-mem fn-shs)
            (let* ((ndirty (len lpages))
                   (n2 (pgs-grown-len lpages n))
                   (nt2 (pgs-x-ntables n2))
                   (m (pgs-dir-run-pages n2))
                   (al (pgs-alloc (+ ndirty (len tl)) m alloc))
                   (rs (nfix (first al)))
                   (singles (true-list-fix (second al)))
                   (fresh (take ndirty singles))
                   (tfresh (nthcdr ndirty singles)))
              (if (not (and (pgs-x-plan-fits lpages fresh digests txid)
                            (pgs-x-u64-bounded tfresh)
                            (< rs 18446744073709551616)
                            (< n2 18446744073709551616)
                            (< m 4294967296)
                            (equal (pgs-grown-len tl nt) nt2)))
                  (mv (list :refused :out-of-range) nil fn-shs)
                (mv nil (list tl fresh tfresh digests rs m n2 nt2 (list (third al) (fourth al)))
                    fn-shs)))))))))))

(defthm pgs-x-commit-prepare-shs
  (implies (fn-shs-p fn-shs)
           (fn-shs-p (mv-nth 2 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-shs))))
  :hints (("Goal" :in-theory (disable pgs-alloc pgs-grown-len pgs-touched pgs-lpages-ok
                                      pgs-x-plan-fits pgs-dir-run-pages pgs-x-ntables
                                      pgs-x-dirty-digests pgs-ptab-run-pages
                                      pgs-x-lpages-resident pgs-x-tables-ready))))

(defun pgs-x-commit-plan-p (plan)
  ; The shape `pgs-x-commit-prepare' answers (checked at run time: O(dirty)).
  (declare (xargs :guard t))
  (and (true-listp plan) (equal (len plan) 9)
       (nat-listp (nth 0 plan)) (true-listp (nth 1 plan)) (true-listp (nth 2 plan))
       (true-listp (nth 3 plan)) (natp (nth 4 plan))
       (natp (nth 5 plan)) (< (nth 5 plan) 4294967296)
       (natp (nth 6 plan)) (natp (nth 7 plan))))

(defthm pgs-x-ensure-m-facts
  (and (<= (nfix k) (pgs-m-length (pgs-x-ensure-m k pgs-mem)))
       (implies (natp k) (<= (pgs-m-length pgs-mem) (pgs-m-length (pgs-x-ensure-m k pgs-mem))))
       (equal (pgs-t-length (pgs-x-ensure-m k pgs-mem)) (pgs-t-length pgs-mem))
       (implies (pgs-memp pgs-mem) (pgs-memp (pgs-x-ensure-m k pgs-mem))))
  :rule-classes ((:linear :corollary (<= (nfix k) (pgs-m-length (pgs-x-ensure-m k pgs-mem))))
                 (:linear :corollary (implies (natp k) (<= (pgs-m-length pgs-mem) (pgs-m-length (pgs-x-ensure-m k pgs-mem)))))
                 (:rewrite :corollary (equal (pgs-t-length (pgs-x-ensure-m k pgs-mem)) (pgs-t-length pgs-mem)))
                 (:rewrite :corollary (implies (pgs-memp pgs-mem) (pgs-memp (pgs-x-ensure-m k pgs-mem))))))

(defun pgs-x-commit-apply (lpages n txid slot plan pgs-mem fn-shs)
  ; The commit's effect, after `pgs-x-commit-prepare' answered PLAN:
  ; (mv RESULT pgs-mem fn-shs).
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (nat-listp lpages) (natp n) (natp txid)
                              (or (equal slot 0) (equal slot 512)))
                  :guard-hints (("Goal" :in-theory (disable pgs-x-plan-entries pgs-x-ensure-m
                                                            pgs-x-words-digest pgs-x-write-rec
                                                            pgs-x-ntables)
                                 :do-not '(eliminate-destructors)))))
  (if (not (pgs-x-commit-plan-p plan))   ; unreachable-in-composition: pgs-x-commit-prepare-plan-p
      (mv (list :refused :internal) pgs-mem fn-shs)
    (let ((tl (nth 0 plan)) (fresh (nth 1 plan)) (tfresh (nth 2 plan)) (digests (nth 3 plan))
          (rs (nth 4 plan)) (m (nth 5 plan)) (n2 (nth 6 plan)) (nt2 (nth 7 plan))
          (nt (pgs-x-ntables n)))
      (mv-let (n2b pgs-mem)
        (pgs-x-plan-tab lpages fresh digests txid n pgs-mem)
        (declare (ignore n2b))
        (let ((pgs-mem (pgs-x-mark-tables tl nt2 pgs-mem)))
          (mv-let (tdigests fn-shs)
            (pgs-x-table-digests tl pgs-mem fn-shs)
            (mv-let (nd2 pgs-mem)
              (pgs-x-plan-dir tl tfresh tdigests txid nt pgs-mem)
              (declare (ignore nd2))
              (let ((pgs-mem (pgs-x-ensure-m (+ *pgs-x-dir-base* (* 2048 m)) pgs-mem)))
                (mv-let (ddig fn-shs)
                  (pgs-x-words-digest 1 *pgs-x-dir-base* (* 256 m) pgs-mem fn-shs)
                  (mv-let (rec pgs-mem fn-shs)
                    (pgs-x-write-rec slot txid rs n2 ddig pgs-mem fn-shs)
                    (mv (list :plan rec fresh tl tfresh rs m (nth 8 plan) digests tdigests)
                        pgs-mem fn-shs)))))))))))

(defun pgs-x-commit (lpages n txid alloc slot pgs-mem fn-shs)
  ; The commit of the dirty pages LPAGES over the open table of N logical
  ; pages, as transaction TXID, allocating from ALLOC = (FREE HWM), the
  ; record into pgs-m slot SLOT (0 or 512): (mv RESULT pgs-mem fn-shs),
  ; RESULT one of
  ;   (:refused REASON)       nothing changed; REASON :dirty-out-of-order,
  ;                           :dirty-not-resident, :state-unloaded,
  ;                           :touched-out-of-order, :out-of-range
  ;   (:need-table T PHYS)    nothing changed; load table page T, retry
  ;   (:plan RECORD FRESH TL TFRESH RUN-START M ALLOC2 DIGESTS TDIGESTS)
  ;                           pgs-t and pgs-m hold the new table, directory
  ;                           and record; write them (above), then barrier.
  ; `pgs-plan-commit''s sequence: `pgs-lpages-ok', `pgs-touched',
  ; `pgs-alloc' of N-DIRTY + N-TOUCHED singles and the directory run,
  ; `pgs-plan-ptab' of the table (`pgs-x-plan-tab') and of the directory
  ; (`pgs-x-plan-dir') over the table pages' digests, then the record.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (nat-listp lpages) (natp n) (natp txid)
                              (or (equal slot 0) (equal slot 512)))
                  :guard-hints (("Goal" :in-theory (disable pgs-x-commit-prepare pgs-x-commit-apply)))))
  (mv-let (verdict plan fn-shs)
    (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-shs)
    (if verdict
        (mv verdict pgs-mem fn-shs)
      (pgs-x-commit-apply lpages n txid slot plan pgs-mem fn-shs))))

; -- The commit refines the model: frames for each step, then the theorem.

(defthm pgs-x-word-of-zero-words
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp j) (natp a) (natp k)
                (<= (+ a k) (pgs-x-len s2 pgs-mem))
                (or (not (equal s s2)) (< j a) (<= (+ a k) j)))
           (equal (pgs-x-word s j (pgs-x-zero-words s2 a k pgs-mem)) (pgs-x-word s j pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-zero-words) :induct (pgs-x-zero-words s2 a k pgs-mem))))

(defthm pgs-x-word-of-put-dig4
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (natp j) (natp a)
                (or (not (equal s s2)) (< j a) (<= (+ a 4) j)))
           (equal (pgs-x-word s j (pgs-x-put-dig4 s2 a d pgs-mem)) (pgs-x-word s j pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-put-dig4))))

(defthm pgs-x-write-rec-frame
  (implies (and (natp slot) (<= (+ slot 20) (pgs-m-length pgs-mem))
                (pgs-x-sel-p s) (natp j) (or (equal s 2) (<= (+ slot 20) j)))
           (let ((m2 (mv-nth 1 (pgs-x-write-rec slot txid addr npages ddig pgs-mem fn-shs))))
             (and (equal (pgs-x-word s j m2) (pgs-x-word s j pgs-mem))
                  (equal (pgs-x-len s m2) (pgs-x-len s pgs-mem)))))
  :hints (("Goal" :in-theory (enable pgs-x-write-rec))))

(defthm pgs-x-plan-entries-other-len
  (implies (and (pgs-x-sel-p s) (pgs-x-sel-p s2) (not (equal s s2)))
           (equal (pgs-x-len s (mv-nth 1 (pgs-x-plan-entries s2 b lpages fresh digests txid n pgs-mem)))
                  (pgs-x-len s pgs-mem)))
  :hints (("Goal" :use ((:instance pgs-x-plan-entries-other-sel (j 0))))))

; A step that keeps SEL's words at and above LO and its length keeps its
; entries, zero ranges and invariant there.  Stated per step (no
; quantifier over words): mark-tables, the other array's plan, write-rec.

(defmacro pgs-x-frame-lemmas (name step hyps s lo)
  ; get-entry, tab-from, zero-range and the invariants of SEL S above LO
  ; are unchanged by STEP (a term in pgs-mem) under HYPS.
  (let ((ge (intern-in-package-of-symbol (concatenate 'string "PGS-X-GET-ENTRY-OF-" (symbol-name name)) 'pgs))
        (tf (intern-in-package-of-symbol (concatenate 'string "PGS-X-TAB-FROM-OF-" (symbol-name name)) 'pgs))
        (zr (intern-in-package-of-symbol (concatenate 'string "PGS-X-ZERO-RANGE-OF-" (symbol-name name)) 'pgs))
        (tc (intern-in-package-of-symbol (concatenate 'string "PGS-X-TPAGES-CANON-OF-" (symbol-name name)) 'pgs))
        (iv (intern-in-package-of-symbol (concatenate 'string "PGS-X-INV-OF-" (symbol-name name)) 'pgs)))
    `(progn
       (defthm ,ge
         (implies (and ,@hyps (<= ,lo (pgs-x-eaddr ,s b j)))
                  (equal (pgs-x-get-entry ,s b j ,step) (pgs-x-get-entry ,s b j pgs-mem)))
         :hints (("Goal" :in-theory (enable pgs-x-get-entry))))
       (defthm ,tf
         (implies (and ,@hyps (natp i) (<= ,lo (pgs-x-eaddr ,s b i)))
                  (equal (pgs-x-tab-from ,s b i n ,step) (pgs-x-tab-from ,s b i n pgs-mem)))
         :hints (("Goal" :induct (pgs-x-tab-from ,s b i n pgs-mem))
                 ("Subgoal *1/2" :use ((:instance pgs-x-eaddr-monotone (sel ,s) (base b) (i i) (j (+ 1 i)))))))
       (defthm ,zr
         (implies (and ,@hyps (natp lo) (<= ,lo lo))
                  (equal (pgs-x-zero-range ,s lo hi ,step) (pgs-x-zero-range ,s lo hi pgs-mem)))
         :hints (("Goal" :induct (pgs-x-zero-range ,s lo hi pgs-mem))))
       ,@(and (equal s 2)
              `((defthm ,tc
                  (implies (and ,@hyps)
                           (equal (pgs-x-tpages-canon k n ,step) (pgs-x-tpages-canon k n pgs-mem)))
                  :hints (("Goal" :induct (pgs-run-ind 0 k)
                                  :in-theory (enable pgs-x-tpage-canon))))))
       (defthm ,iv
         (implies (and ,@hyps ,@(if (equal s 2) nil `((<= ,lo (+ b (* 6 n))))))
                  (equal ,(if (equal s 2) `(pgs-x-tab-inv n ,step) `(pgs-x-dir-inv b n ,step))
                         ,(if (equal s 2) `(pgs-x-tab-inv n pgs-mem) `(pgs-x-dir-inv b n pgs-mem))))
         :hints (("Goal" :in-theory (enable pgs-x-tab-inv pgs-x-dir-inv))))))) 

(pgs-x-frame-lemmas mark-tables-1 (pgs-x-mark-tables tl nt2 pgs-mem) ((nat-listp tl)) 1 0)
(pgs-x-frame-lemmas mark-tables-2 (pgs-x-mark-tables tl nt2 pgs-mem) ((nat-listp tl)) 2 0)
(defthm pgs-x-plan-entries-other-lengths
  (and (equal (pgs-m-length (mv-nth 1 (pgs-x-plan-entries 2 bb ll ff dd tt nn pgs-mem)))
              (pgs-m-length pgs-mem))
       (equal (pgs-t-length (mv-nth 1 (pgs-x-plan-entries 1 bb ll ff dd tt nn pgs-mem)))
              (pgs-t-length pgs-mem)))
  :hints (("Goal" :use ((:instance pgs-x-plan-entries-other-len (s 1) (s2 2) (b bb) (lpages ll)
                                   (fresh ff) (digests dd) (txid tt) (n nn))
                        (:instance pgs-x-plan-entries-other-len (s 2) (s2 1) (b bb) (lpages ll)
                                   (fresh ff) (digests dd) (txid tt) (n nn)))
                  :in-theory (disable pgs-x-plan-entries-other-len))))

(pgs-x-frame-lemmas plan-tab-1 (mv-nth 1 (pgs-x-plan-entries 2 bb ll ff dd tt nn pgs-mem)) () 1 0)
(pgs-x-frame-lemmas plan-dir-2 (mv-nth 1 (pgs-x-plan-entries 1 bb ll ff dd tt nn pgs-mem)) () 2 0)
(defthm pgs-x-write-rec-t-length
  (implies (and (natp slot) (<= (+ slot 20) (pgs-m-length pgs-mem)))
           (equal (pgs-t-length (mv-nth 1 (pgs-x-write-rec slot tx ad np dg pgs-mem fn-shs)))
                  (pgs-t-length pgs-mem)))
  :hints (("Goal" :use ((:instance pgs-x-write-rec-frame (s 2) (j 0) (txid tx) (addr ad)
                                   (npages np) (ddig dg)))
                  :in-theory (disable pgs-x-write-rec-frame))))

(pgs-x-frame-lemmas write-rec-2 (mv-nth 1 (pgs-x-write-rec slot tx ad np dg pgs-mem fn-shs))
                    ((natp slot) (<= (+ slot 20) (pgs-m-length pgs-mem))) 2 0)
(pgs-x-frame-lemmas write-rec-1 (mv-nth 1 (pgs-x-write-rec slot tx ad np dg pgs-mem fn-shs))
                    ((natp slot) (<= (+ slot 20) (pgs-m-length pgs-mem))) 1 (+ slot 20))

(defthm pgs-x-ensure-m-noop
  (implies (<= k (pgs-m-length pgs-mem))
           (equal (pgs-x-ensure-m k pgs-mem) pgs-mem)))

(defthm pgs-x-tab-inv-of-plan-entries
  (implies (and (pgs-x-tab-inv n pgs-mem) (pgs-lpages-ok lpages n lo))
           (pgs-x-tab-inv (pgs-grown-len lpages n)
                          (mv-nth 1 (pgs-x-plan-entries 2 0 lpages fresh digests txid n pgs-mem))))
  :hints (("Goal" :use ((:instance pgs-x-plan-entries-inv (s 2) (b 0)))
                  :in-theory (disable pgs-x-plan-entries-inv pgs-x-plan-entries))))

(defthm pgs-x-dir-inv-of-plan-entries
  (implies (and (pgs-x-dir-inv b n pgs-mem) (pgs-lpages-ok lpages n lo))
           (pgs-x-dir-inv b (pgs-grown-len lpages n)
                          (mv-nth 1 (pgs-x-plan-entries 1 b lpages fresh digests txid n pgs-mem))))
  :hints (("Goal" :use ((:instance pgs-x-plan-entries-inv (s 1)))
                  :in-theory (disable pgs-x-plan-entries-inv pgs-x-plan-entries))))

(defthm pgs-x-plan-entries-m-length-grows
  (<= (pgs-m-length pgs-mem)
      (pgs-m-length (mv-nth 1 (pgs-x-plan-entries 1 b lpages fresh digests txid n pgs-mem))))
  :hints (("Goal" :induct (pgs-x-plan-entries 1 b lpages fresh digests txid n pgs-mem)
                  :in-theory (disable pgs-x-set-entry pgs-x-grow-need)))
  :rule-classes :linear)

(defthm pgs-x-dir-inv-m-length
  (implies (pgs-x-dir-inv b nd pgs-mem)
           (<= (+ 2048 b) (pgs-m-length pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-dir-inv)))
  :rule-classes :linear)

(defthm pgs-x-ensure-m-noop-under-dir-inv
  (implies (pgs-x-dir-inv b nd pgs-mem)
           (equal (pgs-x-ensure-m (+ b (* 2048 (pgs-ptab-run-pages nd))) pgs-mem) pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-dir-inv))))

(defthm pgs-x-commit-apply-refines
  ; The commit's effect, over the invariants and the plan
  ; `pgs-x-commit-prepare' answers: the decoded table and directory after
  ; it are `pgs-plan-ptab' of those before (the directory over the touched
  ; table pages' digests it answers), and the invariants hold after.
  (implies (and (pgs-x-tab-inv n pgs-mem)
                (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n) pgs-mem)
                (pgs-lpages-ok lpages n 0)
                (pgs-x-plan-fits lpages fresh digests txid)
                (nat-listp tl)
                (pgs-lpages-ok tl (pgs-ntables n) 0)
                (pgs-x-u64-bounded tfresh)
                (equal (pgs-grown-len tl (pgs-ntables n)) (pgs-ntables (pgs-grown-len lpages n)))
                (< (pgs-ptab-run-pages (pgs-ntables (pgs-grown-len lpages n))) 4294967296)
                (natp rs)
                (true-listp fresh) (true-listp tfresh) (true-listp digests)
                (or (equal slot 0) (equal slot 512)))
           (let* ((n2 (pgs-grown-len lpages n))
                  (nt2 (pgs-ntables n2))
                  (m (pgs-ptab-run-pages nt2))
                  (r (pgs-x-commit-apply lpages n txid slot (list tl fresh tfresh digests rs m n2 nt2 a2)
                                         pgs-mem fn-shs))
                  (m2 (mv-nth 1 r)))
             (and (equal (car (mv-nth 0 r)) :plan)
                  (equal (nth 2 (mv-nth 0 r)) fresh)
                  (equal (nth 3 (mv-nth 0 r)) tl)
                  (equal (nth 4 (mv-nth 0 r)) tfresh)
                  (equal (nth 8 (mv-nth 0 r)) digests)
                  (equal (pgs-x-tab n2 m2)
                         (pgs-plan-ptab (pgs-x-tab n pgs-mem) lpages fresh digests txid))
                  (equal (pgs-x-dir nt2 m2)
                         (pgs-plan-ptab (pgs-x-dir (pgs-ntables n) pgs-mem) tl tfresh
                                        (nth 9 (mv-nth 0 r)) txid))
                  (pgs-x-tab-inv n2 m2)
                  (pgs-x-dir-inv *pgs-x-dir-base* nt2 m2))))
  :hints (("Goal" :in-theory (disable pgs-x-plan-entries pgs-x-mark-tables pgs-x-table-digests
                                      pgs-x-ensure-m pgs-x-words-digest pgs-x-write-rec
                                      pgs-plan-ptab pgs-grown-len pgs-lpages-ok pgs-ntables
                                      pgs-ntables-as-tq pgs-ptab-run-pages pgs-x-tab-from
                                      pgs-x-plan-entries-len-is pgs-x-plan-entries-refines)
                  :use ((:instance pgs-x-plan-entries-refines (s 2) (b 0) (lo 0))
                        (:instance pgs-x-plan-entries-refines
                                   (s 1) (b *pgs-x-dir-base*) (lo 0) (lpages tl) (fresh tfresh)
                                   (n (pgs-ntables n))
                                   (digests (car (pgs-x-table-digests
                                                  tl (pgs-x-mark-tables
                                                      tl (pgs-ntables (pgs-grown-len lpages n))
                                                      (mv-nth 1 (pgs-x-plan-entries 2 0 lpages fresh digests
                                                                                    txid n pgs-mem)))
                                                  fn-shs)))
                                   (pgs-mem (pgs-x-mark-tables
                                             tl (pgs-ntables (pgs-grown-len lpages n))
                                             (mv-nth 1 (pgs-x-plan-entries 2 0 lpages fresh digests
                                                                           txid n pgs-mem)))))))))

(defthm pgs-x-commit-prepare-plan
  ; What `pgs-x-commit-prepare' answers when it does not refuse: the plan
  ; `pgs-plan-commit' computes (touched pages, the allocation cut into the
  ; data pages' and the table pages' addresses, the grown lengths), and the
  ; facts the effect needs.
  (implies (and (not (mv-nth 0 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-shs)))
                (natp n) (nat-listp lpages))
           (let* ((plan (mv-nth 1 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-shs)))
                  (tl (pgs-touched lpages nil))
                  (n2 (pgs-grown-len lpages n))
                  (al (pgs-alloc (+ (len lpages) (len tl)) (pgs-dir-run-pages n2) alloc)))
             (and (equal plan
                         (list tl
                               (take (len lpages) (true-list-fix (second al)))
                               (nthcdr (len lpages) (true-list-fix (second al)))
                               (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-shs))
                               (nfix (first al))
                               (pgs-ptab-run-pages (pgs-ntables n2))
                               n2 (pgs-ntables n2)
                               (list (third al) (fourth al))))
                  (pgs-lpages-ok lpages n 0)
                  (pgs-x-plan-fits lpages (take (len lpages) (true-list-fix (second al)))
                                   (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-shs)) txid)
                  (pgs-lpages-ok tl (pgs-ntables n) 0)
                  (pgs-x-u64-bounded (nthcdr (len lpages) (true-list-fix (second al))))
                  (equal (pgs-grown-len tl (pgs-ntables n)) (pgs-ntables n2))
                  (< (pgs-ptab-run-pages (pgs-ntables n2)) 4294967296))))
  :hints (("Goal" :in-theory (disable pgs-alloc pgs-grown-len pgs-touched pgs-lpages-ok
                                      pgs-x-plan-fits pgs-ntables pgs-ntables-as-tq
                                      pgs-x-dirty-digests pgs-ptab-run-pages
                                      pgs-x-lpages-resident pgs-x-tables-ready))))

(defthm pgs-x-tables-ready-tag
  (implies (pgs-x-tables-ready tl nt pgs-mem)
           (equal (car (pgs-x-tables-ready tl nt pgs-mem)) :need-table)))

(defthm pgs-x-commit-prepare-verdict-not-plan
  (and (not (equal (car (mv-nth 0 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-shs))) :plan))
       (not (equal (car (car (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-shs))) :plan)))
  :hints (("Goal" :in-theory (disable pgs-alloc pgs-grown-len pgs-touched pgs-lpages-ok
                                      pgs-x-plan-fits pgs-ntables pgs-ntables-as-tq
                                      pgs-x-dirty-digests pgs-ptab-run-pages
                                      pgs-x-lpages-resident pgs-x-tables-ready))))

(defthm pgs-x-commit-refines
  ; THE COMMIT THE HOST CALLS REFINES THE MODEL'S: when `pgs-x-commit'
  ; answers a plan over the two invariants, its touched pages, addresses
  ; and digests are `pgs-plan-commit''s sequence (`pgs-touched', the first
  ; N-DIRTY singles of `pgs-alloc' for the data pages and the rest for the
  ; table pages), the decoded table after it is `pgs-plan-ptab' of the one
  ; before, the decoded directory is `pgs-plan-ptab' of the one before over
  ; the table pages' digests, and both invariants hold after.
  (implies (and (pgs-x-tab-inv n pgs-mem)
                (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n) pgs-mem)
                (natp n) (nat-listp lpages) (or (equal slot 0) (equal slot 512))
                (equal (car (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-shs))) :plan))
           (let* ((r (pgs-x-commit lpages n txid alloc slot pgs-mem fn-shs))
                  (res (mv-nth 0 r))
                  (m2 (mv-nth 1 r))
                  (n2 (pgs-grown-len lpages n))
                  (tl (pgs-touched lpages nil))
                  (al (pgs-alloc (+ (len lpages) (len tl)) (pgs-dir-run-pages n2) alloc)))
             (and (equal (nth 3 res) tl)
                  (equal (nth 2 res) (take (len lpages) (true-list-fix (second al))))
                  (equal (nth 4 res) (nthcdr (len lpages) (true-list-fix (second al))))
                  (equal (pgs-x-tab n2 m2)
                         (pgs-plan-ptab (pgs-x-tab n pgs-mem) lpages (nth 2 res) (nth 8 res) txid))
                  (equal (pgs-x-dir (pgs-ntables n2) m2)
                         (pgs-plan-ptab (pgs-x-dir (pgs-ntables n) pgs-mem) tl (nth 4 res) (nth 9 res) txid))
                  (pgs-x-tab-inv n2 m2)
                  (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n2) m2))))
  :hints (("Goal" :in-theory (disable pgs-x-commit-prepare pgs-x-commit-apply pgs-x-commit-apply-refines
                                      pgs-x-commit-prepare-plan pgs-alloc pgs-grown-len pgs-touched
                                      pgs-lpages-ok pgs-x-plan-fits pgs-ntables pgs-ntables-as-tq
                                      pgs-ptab-run-pages pgs-x-tab pgs-x-dir pgs-plan-ptab
                                      pgs-x-dirty-digests pgs-dir-run-pages)
                  :use (pgs-x-commit-prepare-plan
                        (:instance pgs-x-commit-apply-refines
                                   (tl (pgs-touched lpages nil))
                                   (fresh (take (len lpages)
                                                (true-list-fix
                                                 (second (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil)))
                                                                    (pgs-dir-run-pages (pgs-grown-len lpages n))
                                                                    alloc)))))
                                   (tfresh (nthcdr (len lpages)
                                                   (true-list-fix
                                                    (second (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil)))
                                                                       (pgs-dir-run-pages (pgs-grown-len lpages n))
                                                                       alloc)))))
                                   (digests (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-shs)))
                                   (rs (nfix (first (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil)))
                                                               (pgs-dir-run-pages (pgs-grown-len lpages n))
                                                               alloc))))
                                   (a2 (list (third (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil)))
                                                               (pgs-dir-run-pages (pgs-grown-len lpages n))
                                                               alloc))
                                             (fourth (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil)))
                                                                (pgs-dir-run-pages (pgs-grown-len lpages n))
                                                                alloc))))
                                   (fn-shs (mv-nth 2 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-shs))))))))

(defthm pgs-x-commit-prepare-plan-p
  ; `pgs-x-commit-apply''s :internal refusal is unreachable-in-composition:
  ; the plan `pgs-x-commit-prepare' answers always has the shape.
  (implies (and (not (mv-nth 0 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-shs)))
                (natp n) (nat-listp lpages))
           (pgs-x-commit-plan-p (mv-nth 1 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-shs))))
  :hints (("Goal" :in-theory (disable pgs-alloc pgs-grown-len pgs-touched pgs-lpages-ok
                                      pgs-x-plan-fits pgs-ntables pgs-ntables-as-tq
                                      pgs-x-dirty-digests pgs-ptab-run-pages
                                      pgs-x-lpages-resident pgs-x-tables-ready pgs-x-u64-bounded
                                      pgs-dir-run-pages))))

; -----------------------------------------------------------------------------
; Writers.

(defun pgs-x-write (lp off v pgs-mem)
  ; Word OFF of logical page LP := V (mod 2^64), and LP is dirty:
  ; (mv VERDICT pgs-mem), VERDICT :ok, (:need-page LP) when the page is not
  ; verified (lazy open: read it first), or :out-of-range.
  (declare (xargs :stobjs pgs-mem :guard (and (natp lp) (natp off))))
  (cond ((not (and (< off 2048)
                   (< lp (pgs-d-length pgs-mem)) (< lp (pgs-v-length pgs-mem))
                   (<= (* 2048 (+ 1 lp)) (pgs-w-length pgs-mem))))
         (mv :out-of-range pgs-mem))
        ((not (equal (pgs-vi lp pgs-mem) 2))
         (mv (list :need-page lp) pgs-mem))
        (t (let* ((pgs-mem (update-pgs-wi (+ (* 2048 lp) off) (pgs-dlo v) pgs-mem))
                  (pgs-mem (update-pgs-di lp 1 pgs-mem)))
             (mv :ok pgs-mem)))))

(defun pgs-x-set-flags (i k v pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp k) (unsigned-byte-p 64 v)
                              (<= k (pgs-v-length pgs-mem)))
                  :measure (nfix (- (nfix k) (nfix i)))))
  (if (mbe :logic (zp (- (nfix k) (nfix i))) :exec (<= k i))
      pgs-mem
    (let ((pgs-mem (update-pgs-vi i v pgs-mem)))
      (pgs-x-set-flags (+ 1 (nfix i)) k v pgs-mem))))

(local
 (defthm pgs-wdvp-of-resize-list
   (and (implies (pgs-wp l) (pgs-wp (resize-list l n 0)))
        (implies (pgs-dp l) (pgs-dp (resize-list l n 0)))
        (implies (pgs-vp l) (pgs-vp (resize-list l n 0))))))

(defthm pgs-resize-image-facts
  (and (equal (pgs-v-length (resize-pgs-v k pgs-mem)) (nfix k))
       (equal (pgs-v-length (resize-pgs-w k pgs-mem)) (pgs-v-length pgs-mem))
       (equal (pgs-v-length (resize-pgs-d k pgs-mem)) (pgs-v-length pgs-mem))
       (implies (pgs-memp pgs-mem)
                (and (pgs-memp (resize-pgs-v k pgs-mem))
                     (pgs-memp (resize-pgs-w k pgs-mem))
                     (pgs-memp (resize-pgs-d k pgs-mem)))))
  :hints (("Goal" :in-theory (enable pgs-v-length pgs-memp))))

(defun pgs-x-set-tflags (i k v pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp k) (unsigned-byte-p 64 v)
                              (<= k (pgs-tv-length pgs-mem)))
                  :measure (nfix (- (nfix k) (nfix i)))))
  (if (mbe :logic (zp (- (nfix k) (nfix i))) :exec (<= k i))
      pgs-mem
    (let ((pgs-mem (update-pgs-tvi i v pgs-mem)))
      (pgs-x-set-tflags (+ 1 (nfix i)) k v pgs-mem))))

(defun pgs-x-grow-image (npages2 pgs-mem)
  ; Appended logical pages N..NPAGES2-1: zero, clean, verified; and the
  ; table pages they add to (pgs-ntables NPAGES2) resident, since the
  ; commit's plan builds them in memory.  Resizing copies the image
  ; (O(image)); the host grows by as many pages as it means to append.
  (declare (xargs :stobjs pgs-mem :guard (natp npages2)))
  (let ((n (pgs-v-length pgs-mem)))
    (if (<= npages2 n)
        pgs-mem
      (let* ((pgs-mem (resize-pgs-w (* 2048 npages2) pgs-mem))
             (pgs-mem (resize-pgs-d npages2 pgs-mem))
             (pgs-mem (resize-pgs-v npages2 pgs-mem))
             (pgs-mem (pgs-x-set-flags n npages2 2 pgs-mem))
             (nt (pgs-tv-length pgs-mem))
             (nt2 (pgs-ntables npages2)))
        (if (<= nt2 nt)
            pgs-mem
          (let ((pgs-mem (resize-pgs-tv nt2 pgs-mem)))
            (pgs-x-set-tflags nt nt2 2 pgs-mem)))))))

(defun pgs-x-commit-durable (lpages pgs-mem)
  ; After the host reports the record durable: the dirty pages are clean
  ; and verified.
  (declare (xargs :stobjs pgs-mem :guard (nat-listp lpages)))
  (if (atom lpages)
      pgs-mem
    (let* ((l (car lpages))
           (pgs-mem (if (< l (pgs-d-length pgs-mem)) (update-pgs-di l 0 pgs-mem) pgs-mem))
           (pgs-mem (if (< l (pgs-v-length pgs-mem)) (update-pgs-vi l 2 pgs-mem) pgs-mem)))
      (pgs-x-commit-durable (cdr lpages) pgs-mem))))

; =============================================================================
; 12. The two first requests over the fn-hist-shaped columns, through
;     `pgs-x-read' (so a lazy store loads what they touch on demand: any
;     verdict but :ok, :need-table and :need-page included, goes back to
;     the host, which loads and retries).
;
; Layout (logical page 0, the header):
;   0 magic "FNPSCOLS"  1 N records  2 HBITS (table of 2^HBITS slots)
;   3 OFF: word index of the offsets column (N words: pool byte offsets)
;   4 TAB: word index of the Message-ID table (slot = sequence + 1, 0 empty)
;   5 POOL: word index of the byte pool   6 pool words   7 salt
; A pool entry at byte offset O (8-aligned): its first word holds the
; Message-ID length L (bits 0-15) and the row length R (bits 16-31); the
; Message-ID's octets follow from O + 8, then the row's.

(defconst *pgs-cols-magic* #x534C4F4353504E46)   ; "FNPSCOLS", little-endian

(defun pgs-x-rd (w pgs-mem fn-shs)
  ; Word W of the image: (mv VERDICT WORD pgs-mem fn-shs).
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (natp w)))
  (pgs-x-read (floor (nfix w) 2048) (mod (nfix w) 2048) pgs-mem fn-shs))

(defthm pgs-x-rd-stobjs
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
           (and (pgs-memp (mv-nth 2 (pgs-x-rd w pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 3 (pgs-x-rd w pgs-mem fn-shs))))))

(in-theory (disable pgs-x-rd))

(defun pgs-byte-of-word (w k)
  (declare (xargs :guard (and (natp w) (natp k))))
  (mod (floor (nfix w) (expt 2 (* 8 (mod (nfix k) 8)))) 256))

(defun pgs-x-pool-bytes (o n pool acc pgs-mem fn-shs)
  ; N octets from pool byte O, reversed onto ACC (the caller reverses).
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp o) (natp n) (natp pool) (true-listp acc))
                  :measure (nfix n)))
  (if (zp n)
      (mv :ok acc pgs-mem fn-shs)
    (mv-let (v w pgs-mem fn-shs)
      (pgs-x-rd (+ pool (floor o 8)) pgs-mem fn-shs)
      (if (not (eq v :ok))
          (mv v acc pgs-mem fn-shs)
        (pgs-x-pool-bytes (+ 1 o) (1- n) pool (cons (pgs-byte-of-word (nfix w) o) acc)
                          pgs-mem fn-shs)))))

(defthm pgs-x-pool-bytes-true-listp
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (pgs-x-pool-bytes o n pool acc pgs-mem fn-shs))))
  :hints (("Goal" :induct (pgs-x-pool-bytes o n pool acc pgs-mem fn-shs))))

(defthm pgs-x-pool-bytes-stobjs
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
           (and (pgs-memp (mv-nth 2 (pgs-x-pool-bytes o n pool acc pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 3 (pgs-x-pool-bytes o n pool acc pgs-mem fn-shs)))))
  :hints (("Goal" :induct (pgs-x-pool-bytes o n pool acc pgs-mem fn-shs)
                  :in-theory (disable pgs-byte-of-word))))

(in-theory (disable pgs-x-pool-bytes))

(defun pgs-x-rd2 (w1 w2 pgs-mem fn-shs)
  ; Words W1 and W2: (mv VERDICT A B pgs-mem fn-shs), VERDICT the first
  ; that is not :ok.
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (and (natp w1) (natp w2))))
  (mv-let (v a pgs-mem fn-shs)
    (pgs-x-rd w1 pgs-mem fn-shs)
    (if (not (eq v :ok))
        (mv v 0 0 pgs-mem fn-shs)
      (mv-let (v b pgs-mem fn-shs)
        (pgs-x-rd w2 pgs-mem fn-shs)
        (mv v a b pgs-mem fn-shs)))))

(defthm pgs-x-rd2-stobjs
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
           (and (pgs-memp (mv-nth 3 (pgs-x-rd2 w1 w2 pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 4 (pgs-x-rd2 w1 w2 pgs-mem fn-shs))))))

(in-theory (disable pgs-x-rd2))

(defun pgs-x-row-tail (seq off pool pgs-mem fn-shs)
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (and (natp seq) (natp off) (natp pool))))
  (mv-let (v o pgs-mem fn-shs)
    (pgs-x-rd (+ off seq) pgs-mem fn-shs)
    (if (not (eq v :ok))
        (mv v nil pgs-mem fn-shs)
      (mv-let (v h pgs-mem fn-shs)
        (pgs-x-rd (+ pool (floor (nfix o) 8)) pgs-mem fn-shs)
        (if (not (eq v :ok))
            (mv v nil pgs-mem fn-shs)
          (mv :ok (list (nfix o) (mod (nfix h) 65536) (mod (floor (nfix h) 65536) 65536) pool)
              pgs-mem fn-shs))))))

(defthm pgs-x-row-tail-stobjs
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
           (and (pgs-memp (mv-nth 2 (pgs-x-row-tail seq off pool pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 3 (pgs-x-row-tail seq off pool pgs-mem fn-shs))))))

(in-theory (disable pgs-x-row-tail))

(defun pgs-x-row (seq pgs-mem fn-shs)
  ; (mv VERDICT (O L R POOL) pgs-mem fn-shs) for record SEQ.
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (natp seq)))
  (mv-let (v magic n pgs-mem fn-shs)
    (pgs-x-rd2 0 1 pgs-mem fn-shs)
    (if (not (eq v :ok))
        (mv v nil pgs-mem fn-shs)
      (mv-let (v off pool pgs-mem fn-shs)
        (pgs-x-rd2 3 5 pgs-mem fn-shs)
        (cond ((not (eq v :ok)) (mv v nil pgs-mem fn-shs))
              ((not (equal magic *pgs-cols-magic*))
               (mv :header-malformed nil pgs-mem fn-shs))
              ((not (< seq (nfix n)))
               (mv :no-such-sequence nil pgs-mem fn-shs))
              (t (pgs-x-row-tail seq (nfix off) (nfix pool) pgs-mem fn-shs)))))))

(defthm pgs-x-row-stobjs
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
           (and (pgs-memp (mv-nth 2 (pgs-x-row seq pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 3 (pgs-x-row seq pgs-mem fn-shs))))))

(in-theory (disable pgs-x-row))

(defun pgs-x-lookup-seq (seq pgs-mem fn-shs)
  ; The first request by sequence: (mv VERDICT MSGID-OCTETS pgs-mem fn-shs).
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (natp seq)))
  (mv-let (v e pgs-mem fn-shs)
    (pgs-x-row seq pgs-mem fn-shs)
    (if (not (and (eq v :ok) (true-listp e) (= (len e) 4)))
        (mv v nil pgs-mem fn-shs)
      (mv-let (v bytes pgs-mem fn-shs)
        (pgs-x-pool-bytes (+ 8 (nfix (first e))) (nfix (second e)) (nfix (fourth e))
                          nil pgs-mem fn-shs)
        (mv v (revappend bytes nil) pgs-mem fn-shs)))))

(defthm pgs-x-lookup-seq-facts
  (and (true-listp (mv-nth 1 (pgs-x-lookup-seq seq pgs-mem fn-shs)))
       (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
                (and (pgs-memp (mv-nth 2 (pgs-x-lookup-seq seq pgs-mem fn-shs)))
                     (fn-shs-p (mv-nth 3 (pgs-x-lookup-seq seq pgs-mem fn-shs)))))))

(in-theory (disable pgs-x-lookup-seq))

(defun pgs-fnv (s i h)
  ; FNV-1a, 32 bits, over the octets of S from I.
  (declare (xargs :guard (and (stringp s) (natp i) (natp h))
                  :measure (nfix (- (length s) (nfix i)))))
  (if (and (stringp s) (natp i) (< i (length s)))
      (pgs-fnv s (1+ i) (mod (* (logxor (nfix h) (char-code (char s i))) 16777619)
                            4294967296))
    (nfix h)))

(defun pgs-x-octets-match (s i bytes)
  (declare (xargs :guard (and (stringp s) (natp i) (true-listp bytes))
                  :measure (len bytes)))
  (if (atom bytes)
      (and (natp i) (= i (length s)))
    (and (natp i) (< i (length s))
         (equal (char-code (char s i)) (car bytes))
         (pgs-x-octets-match s (+ 1 i) (cdr bytes)))))

(defun pgs-x-probe (s slot k size tab pgs-mem fn-shs)
  ; Walk the table from SLOT for at most K slots; every candidate is
  ; compared exactly.  (mv VERDICT SEQ-OR-NIL pgs-mem fn-shs).
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (stringp s) (natp slot) (natp k) (natp size) (natp tab))
                  :measure (nfix k)))
  (if (zp k)
      (mv :ok nil pgs-mem fn-shs)
    (mv-let (v x pgs-mem fn-shs)
      (pgs-x-rd (+ tab slot) pgs-mem fn-shs)
      (cond ((not (eq v :ok)) (mv v nil pgs-mem fn-shs))
            ((equal x 0) (mv :ok nil pgs-mem fn-shs))
            ((not (posp x)) (mv :table-malformed nil pgs-mem fn-shs))
            (t (mv-let (v bytes pgs-mem fn-shs)
                 (pgs-x-lookup-seq (1- x) pgs-mem fn-shs)
                 (cond ((not (eq v :ok)) (mv v nil pgs-mem fn-shs))
                       ((pgs-x-octets-match s 0 bytes) (mv :ok (1- x) pgs-mem fn-shs))
                       (t (pgs-x-probe s (if (< (+ 1 slot) size) (+ 1 slot) 0) (1- k)
                                       size tab pgs-mem fn-shs)))))))))

(defun pgs-msgid-start (s salt size)
  (declare (xargs :guard (and (stringp s) (posp size))))
  (mod (pgs-fnv s 0 (mod (logxor 2166136261 (nfix salt)) 4294967296)) size))

(defthm pgs-natp-of-msgid-start
  (implies (posp size) (natp (pgs-msgid-start s salt size)))
  :rule-classes :type-prescription)

(in-theory (disable pgs-msgid-start))

(defun pgs-x-lookup-msgid (s pgs-mem fn-shs)
  ; The first request by Message-ID: (mv VERDICT SEQ-OR-NIL pgs-mem fn-shs).
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (stringp s)))
  (mv-let (v2 hbits pgs-mem fn-shs) (pgs-x-rd 2 pgs-mem fn-shs)
    (mv-let (v4 tab pgs-mem fn-shs) (pgs-x-rd 4 pgs-mem fn-shs)
      (mv-let (v7 salt pgs-mem fn-shs) (pgs-x-rd 7 pgs-mem fn-shs)
        (cond ((not (eq v2 :ok)) (mv v2 nil pgs-mem fn-shs))
              ((not (eq v4 :ok)) (mv v4 nil pgs-mem fn-shs))
              ((not (eq v7 :ok)) (mv v7 nil pgs-mem fn-shs))
              ((not (< (nfix hbits) 40)) (mv :header-malformed nil pgs-mem fn-shs))
              (t (let ((size (expt 2 (nfix hbits))))
                   (pgs-x-probe s (pgs-msgid-start s salt size) size size (nfix tab)
                                pgs-mem fn-shs))))))))

; =============================================================================
; 13. Ground witnesses, run on the executable (with-local-stobj).

(defun pgs-x-iota (i n)
  ; I, I+1, ..., N-1.
  (declare (xargs :guard (and (natp i) (natp n)) :measure (nfix (- (nfix n) (nfix i)))))
  (if (<= (nfix n) (nfix i)) nil (cons (nfix i) (pgs-x-iota (+ 1 (nfix i)) n))))

(defun pgs-x-witness-plan ()
  ; A 3-entry table; then one update (entry 1) and one append (entry 3).
  ; (N BEFORE N2 AFTER MODEL-AFTER PAGE0-IS-ENCODING INV)
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (r pgs-mem)
      (let ((pgs-mem (pgs-x-reset-table 0 pgs-mem)))
        (mv-let (n pgs-mem)
          (pgs-x-plan-tab '(0 1 2) '(10 11 12) '(100 101 102) 1 0 pgs-mem)
          (let ((before (pgs-x-tab n pgs-mem)))
            (mv-let (n2 pgs-mem)
              (pgs-x-plan-tab '(1 3) '(20 21) '(200 201) 2 n pgs-mem)
              (mv (list n before n2 (pgs-x-tab n2 pgs-mem)
                        (pgs-plan-ptab before '(1 3) '(20 21) '(200 201) 2)
                        (equal (pgs-x-words 2 0 2048 pgs-mem)
                               (pgs-encode-table (nth 0 (pgs-chunk (pgs-x-tab n2 pgs-mem)))))
                        (pgs-x-tab-inv n2 pgs-mem))
                  pgs-mem)))))
      r)))

(defthm pgs-x-witness-plan-ok
  ; The plan's refinement on a ground state: the decoded table after the
  ; plan is `pgs-plan-ptab''s, the words of table page 0 are its encoding,
  ; and the invariant holds.
  (equal (pgs-x-witness-plan)
         (list 3 '((10 1 100) (11 1 101) (12 1 102))
               4 '((10 1 100) (20 2 200) (12 1 102) (21 2 201))
               '((10 1 100) (20 2 200) (12 1 102) (21 2 201))
               t t)))

(defun pgs-x-witness-growth ()
  ; 341 entries fill table page 0; appending entry 341 grows pgs-t by a
  ; page and a directory append grows its run: (TAB-OK DIR-OK T-LENGTH INVS)
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (r pgs-mem)
      (let* ((pgs-mem (pgs-x-reset-table 0 pgs-mem))
             (pgs-mem (resize-pgs-m 0 pgs-mem))
             (pgs-mem (resize-pgs-m (+ *pgs-x-dir-base* 2048) pgs-mem)))
        (mv-let (n pgs-mem)
          (pgs-x-plan-tab (pgs-x-iota 0 341) (pgs-x-iota 1000 1341) (pgs-x-iota 5 346) 1 0 pgs-mem)
          (let ((before (pgs-x-tab n pgs-mem)))
            (mv-let (n2 pgs-mem)
              (pgs-x-plan-tab '(340 341) '(7 8) '(9 10) 2 n pgs-mem)
              (mv-let (nd pgs-mem)
                (pgs-x-plan-dir '(0 1) '(70 71) '(90 91) 2 0 pgs-mem)
                (mv (list (equal (pgs-x-tab n2 pgs-mem)
                                 (pgs-plan-ptab before '(340 341) '(7 8) '(9 10) 2))
                          (equal (pgs-x-dir nd pgs-mem) '((70 2 90) (71 2 91)))
                          (pgs-t-length pgs-mem)
                          (and (pgs-x-tab-inv n2 pgs-mem)
                               (pgs-x-dir-inv *pgs-x-dir-base* nd pgs-mem)))
                    pgs-mem))))))
      r)))

(defthm pgs-x-witness-growth-ok
  (equal (pgs-x-witness-growth) (list t t 4096 t)))

(defun pgs-x-witness-commit ()
  ; A commit on an empty store of two dirty pages (0 and 1, both appended),
  ; then the record read back and the durable step.  Seven checks:
  ; a plan; the table's (PHYS TXID) are the fresh singles after the run;
  ; each entry's digest is its page's SHA-256; the directory's one entry
  ; names the table page at its fresh address with the page's SHA-256;
  ; the record's directory digest is the run's SHA-256 and the record reads
  ; back valid; both invariants; no dirty page left.
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (r pgs-mem)
      (with-local-stobj fn-shs
        (mv-let (r pgs-mem fn-shs)
          (let* ((pgs-mem (pgs-x-reset-table 0 pgs-mem))
                 (pgs-mem (resize-pgs-m (+ *pgs-x-dir-base* 2048) pgs-mem))
                 (pgs-mem (resize-pgs-w 4096 pgs-mem))
                 (pgs-mem (resize-pgs-d 2 pgs-mem))
                 (pgs-mem (resize-pgs-v 2 pgs-mem))
                 (pgs-mem (update-pgs-wi 0 7 pgs-mem))
                 (pgs-mem (update-pgs-wi 2048 9 pgs-mem))
                 (pgs-mem (update-pgs-di 0 1 pgs-mem))
                 (pgs-mem (update-pgs-di 1 1 pgs-mem))
                 (lpages (pgs-x-dirty-list 2 nil pgs-mem))
                 (inv0 (and (pgs-x-tab-inv 0 pgs-mem) (pgs-x-dir-inv *pgs-x-dir-base* 0 pgs-mem)))
                 (tab0 (pgs-x-tab 0 pgs-mem))
                 (dir0 (pgs-x-dir 0 pgs-mem)))
            (mv-let (res pgs-mem fn-shs)
              (pgs-x-commit lpages 0 1 '(nil 10) 0 pgs-mem fn-shs)
              (mv-let (d0 fn-shs) (pgs-x-page-digest 0 pgs-mem fn-shs)
                (mv-let (d1 fn-shs) (pgs-x-page-digest 1 pgs-mem fn-shs)
                  (mv-let (td fn-shs) (pgs-x-words-digest 2 0 256 pgs-mem fn-shs)
                    (mv-let (dd fn-shs) (pgs-x-words-digest 1 *pgs-x-dir-base* 256 pgs-mem fn-shs)
                      (mv-let (rec check fn-shs)
                        (pgs-x-read-rec 0 pgs-mem fn-shs)
                        (let* ((tab (pgs-x-tab 2 pgs-mem))
                               (dir (pgs-x-dir 1 pgs-mem))
                               (pgs-mem (pgs-x-commit-durable lpages pgs-mem)))
                          (mv (list (equal (list (first res) (third res) (fourth res) (fifth res) (sixth res) (seventh res))
                                           '(:plan (11 12) (0) (13) 10 1))
                                    (equal (list (take 2 (first tab)) (take 2 (second tab)))
                                           '((11 1) (12 1)))
                                    (equal (list (third (first tab)) (third (second tab))) (list d0 d1))
                                    (equal dir (list (list 13 1 td)))
                                    (and (equal rec (second res)) (pgs-rec-ok rec check)
                                         (equal (fifth rec) dd) (equal (fourth rec) 2))
                                    (and (pgs-x-tab-inv 2 pgs-mem)
                                         (pgs-x-dir-inv *pgs-x-dir-base* 1 pgs-mem))
                                    (null (pgs-x-dirty-list 2 nil pgs-mem))
                                    ;; pgs-x-commit-refines' antecedent and conclusion
                                    (let* ((tl (pgs-touched lpages nil))
                                           (al (pgs-alloc (+ (len lpages) (len tl))
                                                          (pgs-dir-run-pages 2) '(nil 10))))
                                      (and inv0 (equal lpages '(0 1)) (equal (car res) :plan)
                                           (equal (nth 3 res) tl)
                                           (equal (nth 2 res) (take 2 (second al)))
                                           (equal (nth 4 res) (nthcdr 2 (second al)))
                                           (equal tab (pgs-plan-ptab tab0 lpages (nth 2 res) (nth 8 res) 1))
                                           (equal dir (pgs-plan-ptab dir0 tl (nth 4 res) (nth 9 res) 1)))))
                              pgs-mem fn-shs)))))))))
          (mv r pgs-mem)))
      r)))

(defthm pgs-x-witness-commit-ok
  ; Checks 1-7 above, and 8: `pgs-x-commit-refines'' complete antecedent
  ; (both invariants over the empty store, in-order dirty pages, a plan)
  ; and its conclusion's equalities, on the executable.
  (equal (pgs-x-witness-commit) '(t t t t t t t t)))

(defun pgs-x-witness-grow ()
  ; An empty image grown to 343 logical pages (across a table-page
  ; boundary): (TV-LENGTH TABLE-FLAGS V-LENGTH LAST-PAGE-FLAG W-LENGTH READ)
  ; -- both table pages resident, the appended pages verified, and a read of
  ; the last appended page answers :ok (it answered :out-of-range when the
  ; grow left pgs-tv short).
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (r pgs-mem)
      (with-local-stobj fn-shs
        (mv-let (r pgs-mem fn-shs)
          (let* ((pgs-mem (pgs-x-reset-table 0 pgs-mem))
                 (pgs-mem (pgs-x-grow-image 343 pgs-mem)))
            (mv-let (v w pgs-mem fn-shs)
              (pgs-x-read 342 0 pgs-mem fn-shs)
              (mv (list (pgs-tv-length pgs-mem) (list (pgs-tvi 0 pgs-mem) (pgs-tvi 1 pgs-mem))
                        (pgs-v-length pgs-mem) (pgs-vi 342 pgs-mem) (pgs-w-length pgs-mem)
                        (list v w))
                  pgs-mem fn-shs)))
          (mv r pgs-mem)))
      r)))

(defthm pgs-x-witness-grow-ok
  (equal (pgs-x-witness-grow) (list 2 '(2 2) 343 2 702464 '(:ok 0))))
