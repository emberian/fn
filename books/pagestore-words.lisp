;; fn: the page store's word layer (lane arena-store, 2026-09-27).  Prefix pgs-.
;;
;; The stobj the host fills and drains with its two byte primitives
;; (host/native/proto-pagestore-io.lisp), and SHA-256 over a range of its
;; little-endian u64 words with books/sha256-stobj.lisp's compression.  Split
;; out of books/proto/pagestore.lisp so that the word digest's correspondence
;; to `fn-sha256' (A-PGS-OBSERVE's SHA part) is proved against a frozen book.
;;
;; The arrays (all (unsigned-byte 64), resizable):
;;   pgs-w   the resident image: logical page I is words [I*W, (I+1)*W),
;;           W = *pgs-page-words*.
;;   pgs-m   metadata: the root slots' records, the directory run.
;;   pgs-t   the page table as its table pages: table page J is words
;;           [J*W, (J+1)*W), entry K of it at J*W + 6K (see pagestore.lisp).
;;   pgs-d   the dirty flag of each logical page.
;;   pgs-v   the verified flag of each logical page (lazy mode).
;;   pgs-tv  the loaded/verified flag of each table page (lazy table load).
;; A word range is named by a selector SEL: 0 the image, 1 the metadata,
;; 2 the table pages (`pgs-x-len', `pgs-x-word').
(in-package "ACL2")
(include-book "../sha256-stobj")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(defconst *pgs-page-words* 2048)        ; 16 KiB pages

(defstobj pgs-mem
  (pgs-w :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (pgs-m :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (pgs-t :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (pgs-d :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (pgs-v :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (pgs-tv :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  :inline t)

;; The stobj's facts, stated over its accessors, which are then closed.
(local (defthm pgs-wp-of-update-nth
  (implies (and (pgs-wp l) (natp i) (< i (len l)) (unsigned-byte-p 64 v))
           (pgs-wp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm pgs-wp-nth-0
  (implies (and (pgs-wp l) (natp i) (< i (len l)))
           (unsigned-byte-p 64 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm pgs-mp-of-update-nth
  (implies (and (pgs-mp l) (natp i) (< i (len l)) (unsigned-byte-p 64 v))
           (pgs-mp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm pgs-mp-nth-0
  (implies (and (pgs-mp l) (natp i) (< i (len l)))
           (unsigned-byte-p 64 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm pgs-tp-of-update-nth
  (implies (and (pgs-tp l) (natp i) (< i (len l)) (unsigned-byte-p 64 v))
           (pgs-tp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm pgs-tp-nth-0
  (implies (and (pgs-tp l) (natp i) (< i (len l)))
           (unsigned-byte-p 64 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm pgs-dp-of-update-nth
  (implies (and (pgs-dp l) (natp i) (< i (len l)) (unsigned-byte-p 64 v))
           (pgs-dp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm pgs-dp-nth-0
  (implies (and (pgs-dp l) (natp i) (< i (len l)))
           (unsigned-byte-p 64 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm pgs-vp-of-update-nth
  (implies (and (pgs-vp l) (natp i) (< i (len l)) (unsigned-byte-p 64 v))
           (pgs-vp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm pgs-vp-nth-0
  (implies (and (pgs-vp l) (natp i) (< i (len l)))
           (unsigned-byte-p 64 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm pgs-tvp-of-update-nth
  (implies (and (pgs-tvp l) (natp i) (< i (len l)) (unsigned-byte-p 64 v))
           (pgs-tvp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm pgs-tvp-nth-0
  (implies (and (pgs-tvp l) (natp i) (< i (len l)))
           (unsigned-byte-p 64 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))

(defthm pgs-u64-of-wi
  (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-w-length pgs-mem)))
           (and (integerp (pgs-wi i pgs-mem)) (<= 0 (pgs-wi i pgs-mem)) (< (pgs-wi i pgs-mem) 18446744073709551616)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (pgs-wp-nth-0))
                  :use ((:instance pgs-wp-nth-0 (l (nth *pgs-wi* pgs-mem))))))
  :rule-classes ((:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-w-length pgs-mem))) (integerp (pgs-wi i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-w-length pgs-mem))) (acl2-numberp (pgs-wi i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-w-length pgs-mem))) (unsigned-byte-p 64 (pgs-wi i pgs-mem)))
                           :hints (("Goal" :in-theory (enable unsigned-byte-p))))
                 (:linear :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-w-length pgs-mem))) (and (<= 0 (pgs-wi i pgs-mem)) (< (pgs-wi i pgs-mem) 18446744073709551616))))))

(defthm pgs-u64-of-mi
  (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-m-length pgs-mem)))
           (and (integerp (pgs-mi i pgs-mem)) (<= 0 (pgs-mi i pgs-mem)) (< (pgs-mi i pgs-mem) 18446744073709551616)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (pgs-mp-nth-0))
                  :use ((:instance pgs-mp-nth-0 (l (nth *pgs-mi* pgs-mem))))))
  :rule-classes ((:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-m-length pgs-mem))) (integerp (pgs-mi i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-m-length pgs-mem))) (acl2-numberp (pgs-mi i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-m-length pgs-mem))) (unsigned-byte-p 64 (pgs-mi i pgs-mem)))
                           :hints (("Goal" :in-theory (enable unsigned-byte-p))))
                 (:linear :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-m-length pgs-mem))) (and (<= 0 (pgs-mi i pgs-mem)) (< (pgs-mi i pgs-mem) 18446744073709551616))))))

(defthm pgs-u64-of-ti
  (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-t-length pgs-mem)))
           (and (integerp (pgs-ti i pgs-mem)) (<= 0 (pgs-ti i pgs-mem)) (< (pgs-ti i pgs-mem) 18446744073709551616)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (pgs-tp-nth-0))
                  :use ((:instance pgs-tp-nth-0 (l (nth *pgs-ti* pgs-mem))))))
  :rule-classes ((:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-t-length pgs-mem))) (integerp (pgs-ti i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-t-length pgs-mem))) (acl2-numberp (pgs-ti i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-t-length pgs-mem))) (unsigned-byte-p 64 (pgs-ti i pgs-mem)))
                           :hints (("Goal" :in-theory (enable unsigned-byte-p))))
                 (:linear :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-t-length pgs-mem))) (and (<= 0 (pgs-ti i pgs-mem)) (< (pgs-ti i pgs-mem) 18446744073709551616))))))

(defthm pgs-u64-of-di
  (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-d-length pgs-mem)))
           (and (integerp (pgs-di i pgs-mem)) (<= 0 (pgs-di i pgs-mem)) (< (pgs-di i pgs-mem) 18446744073709551616)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (pgs-dp-nth-0))
                  :use ((:instance pgs-dp-nth-0 (l (nth *pgs-di* pgs-mem))))))
  :rule-classes ((:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-d-length pgs-mem))) (integerp (pgs-di i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-d-length pgs-mem))) (acl2-numberp (pgs-di i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-d-length pgs-mem))) (unsigned-byte-p 64 (pgs-di i pgs-mem)))
                           :hints (("Goal" :in-theory (enable unsigned-byte-p))))
                 (:linear :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-d-length pgs-mem))) (and (<= 0 (pgs-di i pgs-mem)) (< (pgs-di i pgs-mem) 18446744073709551616))))))

(defthm pgs-u64-of-vi
  (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-v-length pgs-mem)))
           (and (integerp (pgs-vi i pgs-mem)) (<= 0 (pgs-vi i pgs-mem)) (< (pgs-vi i pgs-mem) 18446744073709551616)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (pgs-vp-nth-0))
                  :use ((:instance pgs-vp-nth-0 (l (nth *pgs-vi* pgs-mem))))))
  :rule-classes ((:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-v-length pgs-mem))) (integerp (pgs-vi i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-v-length pgs-mem))) (acl2-numberp (pgs-vi i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-v-length pgs-mem))) (unsigned-byte-p 64 (pgs-vi i pgs-mem)))
                           :hints (("Goal" :in-theory (enable unsigned-byte-p))))
                 (:linear :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-v-length pgs-mem))) (and (<= 0 (pgs-vi i pgs-mem)) (< (pgs-vi i pgs-mem) 18446744073709551616))))))

(defthm pgs-u64-of-tvi
  (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-tv-length pgs-mem)))
           (and (integerp (pgs-tvi i pgs-mem)) (<= 0 (pgs-tvi i pgs-mem)) (< (pgs-tvi i pgs-mem) 18446744073709551616)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (pgs-tvp-nth-0))
                  :use ((:instance pgs-tvp-nth-0 (l (nth *pgs-tvi* pgs-mem))))))
  :rule-classes ((:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-tv-length pgs-mem))) (integerp (pgs-tvi i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-tv-length pgs-mem))) (acl2-numberp (pgs-tvi i pgs-mem))))
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-tv-length pgs-mem))) (unsigned-byte-p 64 (pgs-tvi i pgs-mem)))
                           :hints (("Goal" :in-theory (enable unsigned-byte-p))))
                 (:linear :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-tv-length pgs-mem))) (and (<= 0 (pgs-tvi i pgs-mem)) (< (pgs-tvi i pgs-mem) 18446744073709551616))))))

(local (defthm pgs-u64-bounds
  (implies (unsigned-byte-p 64 x)
           (and (integerp x) (<= 0 x) (< x 18446744073709551616)))
  :rule-classes ((:forward-chaining))))

(defthm pgs-memp-of-updates
  (implies (and (pgs-memp pgs-mem) (natp i) (unsigned-byte-p 64 v))
           (and (implies (< i (pgs-w-length pgs-mem)) (pgs-memp (update-pgs-wi i v pgs-mem)))
                (implies (< i (pgs-m-length pgs-mem)) (pgs-memp (update-pgs-mi i v pgs-mem)))
                (implies (< i (pgs-t-length pgs-mem)) (pgs-memp (update-pgs-ti i v pgs-mem)))
                (implies (< i (pgs-d-length pgs-mem)) (pgs-memp (update-pgs-di i v pgs-mem)))
                (implies (< i (pgs-v-length pgs-mem)) (pgs-memp (update-pgs-vi i v pgs-mem)))
                (implies (< i (pgs-tv-length pgs-mem)) (pgs-memp (update-pgs-tvi i v pgs-mem))))))

(defthm pgs-lengths-of-updates
  (implies (natp i)
           (and (equal (pgs-w-length (update-pgs-wi i v pgs-mem))
                       (if (< i (pgs-w-length pgs-mem)) (pgs-w-length pgs-mem) (+ 1 i)))
                (equal (pgs-m-length (update-pgs-wi i v pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (update-pgs-wi i v pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-d-length (update-pgs-wi i v pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (update-pgs-wi i v pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (update-pgs-wi i v pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (pgs-w-length (update-pgs-mi i v pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (update-pgs-mi i v pgs-mem))
                       (if (< i (pgs-m-length pgs-mem)) (pgs-m-length pgs-mem) (+ 1 i)))
                (equal (pgs-t-length (update-pgs-mi i v pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-d-length (update-pgs-mi i v pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (update-pgs-mi i v pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (update-pgs-mi i v pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (pgs-w-length (update-pgs-ti i v pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (update-pgs-ti i v pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (update-pgs-ti i v pgs-mem))
                       (if (< i (pgs-t-length pgs-mem)) (pgs-t-length pgs-mem) (+ 1 i)))
                (equal (pgs-d-length (update-pgs-ti i v pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (update-pgs-ti i v pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (update-pgs-ti i v pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (pgs-w-length (update-pgs-di i v pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (update-pgs-di i v pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (update-pgs-di i v pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-d-length (update-pgs-di i v pgs-mem))
                       (if (< i (pgs-d-length pgs-mem)) (pgs-d-length pgs-mem) (+ 1 i)))
                (equal (pgs-v-length (update-pgs-di i v pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (update-pgs-di i v pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (pgs-w-length (update-pgs-vi i v pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (update-pgs-vi i v pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (update-pgs-vi i v pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-d-length (update-pgs-vi i v pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (update-pgs-vi i v pgs-mem))
                       (if (< i (pgs-v-length pgs-mem)) (pgs-v-length pgs-mem) (+ 1 i)))
                (equal (pgs-tv-length (update-pgs-vi i v pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (pgs-w-length (update-pgs-tvi i v pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (update-pgs-tvi i v pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (update-pgs-tvi i v pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-d-length (update-pgs-tvi i v pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (update-pgs-tvi i v pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (update-pgs-tvi i v pgs-mem))
                       (if (< i (pgs-tv-length pgs-mem)) (pgs-tv-length pgs-mem) (+ 1 i)))))
  :hints (("Goal" :in-theory (enable update-nth))))

(in-theory (disable pgs-memp pgs-wi pgs-mi pgs-ti pgs-di pgs-vi pgs-tvi
                    update-pgs-wi update-pgs-mi update-pgs-ti update-pgs-di update-pgs-vi update-pgs-tvi
                    pgs-w-length pgs-m-length pgs-t-length pgs-d-length pgs-v-length pgs-tv-length))

(defconst *pgs-u64-modulus* 18446744073709551616)
(defconst *pgs-magic* #x31544D4353504E46)   ; "FNPSCMT1", little-endian
(defconst *pgs-rec-words* 20)             ; 16 body words, 4 check words

; -----------------------------------------------------------------------------
; The fn-shs facts this section needs (sha256-stobj keeps its own local;
; restated as books/sha256-buffer.lisp restates them).

(local (in-theory (disable floor mod truncate rem ash)))

(local
 (defthm pgs-shs-wp-of-update-nth
   (implies (and (fn-shs-wp w) (natp i) (< i (len w)) (unsigned-byte-p 32 v))
            (fn-shs-wp (update-nth i v w)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm pgs-shs-hp-of-update-nth
   (implies (and (fn-shs-hp h) (natp i) (< i (len h)) (unsigned-byte-p 32 v))
            (fn-shs-hp (update-nth i v h)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm pgs-len-of-update-nth
   (equal (len (update-nth i v l))
          (max (+ 1 (nfix i)) (len l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local (in-theory (disable nth update-nth)))

(defthm pgs-shs-p-of-update-w
   (implies (and (fn-shs-p fn-shs) (natp i) (< i 64) (unsigned-byte-p 32 v))
            (fn-shs-p (update-nth 0 (update-nth i v (nth 0 fn-shs)) fn-shs)))
   :hints (("Goal" :do-not-induct t)))

(defthm pgs-shs-p-of-update-h
   (implies (and (fn-shs-p fn-shs) (natp i) (< i 8) (unsigned-byte-p 32 v))
            (fn-shs-p (update-nth 1 (update-nth i v (nth 1 fn-shs)) fn-shs)))
   :hints (("Goal" :do-not-induct t)))

(defthm pgs-shs-p-parts
   (implies (fn-shs-p fn-shs)
            (and (fn-shs-wp (nth 0 fn-shs))
                 (equal (len (nth 0 fn-shs)) 64)
                 (fn-shs-hp (nth 1 fn-shs))
                 (equal (len (nth 1 fn-shs)) 8))))

(defthm pgs-shs-p-of-h-init
   (implies (and (fn-shs-p fn-shs) (natp i) (fn-shs-word-listp hs))
            (fn-shs-p (fn-shs-h-init i hs fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-h-init fn-shs-word-listp) (fn-shs-p)))))

(defthm pgs-shs-p-of-extend
   (implies (and (fn-shs-p fn-shs) (natp t0))
            (fn-shs-p (fn-shs-extend t0 fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-extend fn-shs-sched-word$inline) (fn-shs-p)))))

(defthm pgs-shs-p-of-h-add
   (implies (and (fn-shs-p fn-shs) (natp i))
            (fn-shs-p (fn-shs-h-add i regs fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-h-add fn-shs-add$inline) (fn-shs-p)))))

(defthm pgs-shs-p-of-compress-loaded
   (implies (fn-shs-p fn-shs)
            (fn-shs-p (fn-shs-compress-loaded fn-shs)))
   :hints (("Goal" :in-theory (e/d (fn-shs-compress-loaded) (fn-shs-p)))))

(local (in-theory (disable fn-shs-p)))

; -----------------------------------------------------------------------------
; SHA-256 over words: the octets of a word range, each word little-endian.
; The message is 8*NW octets (NW a multiple of 8, so whole 64-octet
; blocks); the padding is one more block.

(defun-inline pgs-x-len (sel pgs-mem)
  ; The length of the word array SEL names: 1 the metadata, 2 the table
  ; pages, anything else the image.
  (declare (xargs :stobjs pgs-mem :guard t))
  (case sel
    (1 (pgs-m-length pgs-mem))
    (2 (pgs-t-length pgs-mem))
    (otherwise (pgs-w-length pgs-mem))))

(defun-inline pgs-x-word (sel i pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (< i (pgs-x-len sel pgs-mem)))))
  (case sel
    (1 (pgs-mi i pgs-mem))
    (2 (pgs-ti i pgs-mem))
    (otherwise (pgs-wi i pgs-mem))))

(defun-inline pgs-sw (x)
  ; The big-endian SHA word of the four octets of X, low octet first.
  (declare (type (unsigned-byte 32) x)
           (xargs :guard-hints (("Goal" :in-theory (enable mod ash)))))
  (fn-shs-be-word (mod x 256) (mod (ash x -8) 256)
                  (mod (ash x -16) 256) (mod (ash x -24) 256)))

(defthm pgs-u32-of-be-word
  (unsigned-byte-p 32 (fn-shs-be-word a b c d))
  :hints (("Goal" :in-theory (enable fn-shs-be-word$inline fn-sha256-w32))))

(local (defthm pgs-u32-of-lo
  (implies (unsigned-byte-p 64 w)
           (unsigned-byte-p 32 (mod w 4294967296)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p mod)))))

(local (defthm pgs-u32-of-hi
  (implies (unsigned-byte-p 64 w)
           (unsigned-byte-p 32 (floor w 4294967296)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p)
                  :nonlinearp t))))

(defthm pgs-u32-of-sw
  (unsigned-byte-p 32 (pgs-sw x))
  :hints (("Goal" :in-theory (e/d (pgs-sw$inline) (fn-shs-be-word$inline unsigned-byte-p))
                  :use ((:instance pgs-u32-of-be-word
                                   (a (mod x 256)) (b (mod (ash x -8) 256))
                                   (c (mod (ash x -16) 256)) (d (mod (ash x -24) 256)))))))

(local (defthm pgs-wp-nth
  (implies (and (pgs-wp l) (natp i) (< i (len l)))
           (unsigned-byte-p 64 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))

(local (defthm pgs-mp-nth
  (implies (and (pgs-mp l) (natp i) (< i (len l)))
           (unsigned-byte-p 64 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))

(defthm pgs-u64-of-x-word
  (implies (and (pgs-memp pgs-mem) (natp i)
                (< i (pgs-x-len sel pgs-mem)))
           (unsigned-byte-p 64 (pgs-x-word sel i pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-word$inline pgs-x-len$inline)))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-x-len sel pgs-mem))) (integerp (pgs-x-word sel i pgs-mem))))
                 (:linear :corollary (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-x-len sel pgs-mem))) (and (<= 0 (pgs-x-word sel i pgs-mem)) (< (pgs-x-word sel i pgs-mem) 18446744073709551616))))))

(defun-inline pgs-lo32 (w)
  (declare (type (unsigned-byte 64) w))
  (mbe :logic (mod (ifix w) 4294967296)
       :exec (mod w 4294967296)))

(defun-inline pgs-hi32 (w)
  (declare (type (unsigned-byte 64) w)
           (xargs :guard-hints (("Goal" :in-theory (enable unsigned-byte-p) :nonlinearp t))))
  (mbe :logic (mod (floor (ifix w) 4294967296) 4294967296)
       :exec (floor w 4294967296)))

(defthm pgs-u32-of-lo32
  (unsigned-byte-p 32 (pgs-lo32 w))
  :hints (("Goal" :in-theory (enable pgs-lo32$inline mod)))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (natp (pgs-lo32 w)))
                 (:linear :corollary (< (pgs-lo32 w) 4294967296))))

(defthm pgs-u32-of-hi32
  (unsigned-byte-p 32 (pgs-hi32 w))
  :hints (("Goal" :in-theory (enable pgs-hi32$inline mod)))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (natp (pgs-hi32 w)))
                 (:linear :corollary (< (pgs-hi32 w) 4294967296))))

(defthm pgs-u32-of-sw-linear
  (and (natp (pgs-sw x)) (< (pgs-sw x) 4294967296))
  :hints (("Goal" :use pgs-u32-of-sw :in-theory (disable pgs-u32-of-sw)))
  :rule-classes ((:type-prescription :corollary (natp (pgs-sw x)))
                 (:linear :corollary (< (pgs-sw x) 4294967296))))

(in-theory (disable pgs-sw$inline pgs-x-word$inline pgs-lo32$inline pgs-hi32$inline))

(defun pgs-load-half (j x fn-shs)
  ; Schedule word J (0..15) from the 32-bit half X of a message word.
  (declare (xargs :stobjs fn-shs
                  :guard (and (natp j) (< j 16) (unsigned-byte-p 32 x))))
  (fn-shs-w-set j (pgs-sw x) fn-shs))

(defthm pgs-shs-p-of-load-half
  (implies (and (fn-shs-p fn-shs) (natp j) (< j 16))
           (fn-shs-p (pgs-load-half j x fn-shs))))

(in-theory (disable pgs-load-half))

(defun pgs-load-block (k sel base pgs-mem fn-shs)
  ; Message words BASE..BASE+7 into schedule words 0..15.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp k) (<= k 8) (natp base)
                              (<= (+ base 8)
                                  (pgs-x-len sel pgs-mem)))
                  :measure (nfix (- 8 (nfix k)))))
  (if (mbe :logic (zp (- 8 (nfix k))) :exec (= k 8))
      fn-shs
    (let* ((w (pgs-x-word sel (+ base k) pgs-mem))
           (fn-shs (pgs-load-half (* 2 k) (pgs-lo32 w) fn-shs))
           (fn-shs (pgs-load-half (+ 1 (* 2 k)) (pgs-hi32 w) fn-shs)))
      (pgs-load-block (+ 1 (nfix k)) sel base pgs-mem fn-shs))))

(defthm pgs-shs-p-of-load-block
  (implies (and (fn-shs-p fn-shs) (natp k))
           (fn-shs-p (pgs-load-block k sel base pgs-mem fn-shs))))

(in-theory (disable pgs-load-block))

(defun pgs-blocks (b nb sel base pgs-mem fn-shs)
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp b) (natp nb) (natp base) (<= b nb)
                              (<= (+ base (* 8 nb))
                                  (pgs-x-len sel pgs-mem)))
                  :measure (nfix (- (nfix nb) (nfix b)))))
  (if (mbe :logic (zp (- (nfix nb) (nfix b))) :exec (= b nb))
      fn-shs
    (let* ((fn-shs (pgs-load-block 0 sel (+ base (* 8 b)) pgs-mem fn-shs))
           (fn-shs (fn-shs-compress-loaded fn-shs)))
      (pgs-blocks (+ 1 (nfix b)) nb sel base pgs-mem fn-shs))))

(defthm pgs-shs-p-of-blocks
  (implies (fn-shs-p fn-shs)
           (fn-shs-p (pgs-blocks b nb sel base pgs-mem fn-shs))))

(in-theory (disable pgs-blocks))

(defun pgs-zero-w (j fn-shs)
  (declare (xargs :stobjs fn-shs :guard (and (natp j) (<= j 14))
                  :measure (nfix (- 14 (nfix j)))))
  (if (mbe :logic (zp (- 14 (nfix j))) :exec (= j 14))
      fn-shs
    (let ((fn-shs (fn-shs-w-set j 0 fn-shs)))
      (pgs-zero-w (+ 1 (nfix j)) fn-shs))))

(defthm pgs-shs-p-of-zero-w
  (implies (and (fn-shs-p fn-shs) (natp j)) (fn-shs-p (pgs-zero-w j fn-shs))))

(in-theory (disable pgs-zero-w))

(defun pgs-set-w (j v fn-shs)
  (declare (xargs :stobjs fn-shs
                  :guard (and (natp j) (< j 16) (unsigned-byte-p 32 v))))
  (fn-shs-w-set j v fn-shs))

(defthm pgs-shs-p-of-set-w
  (implies (and (fn-shs-p fn-shs) (natp j) (< j 16) (unsigned-byte-p 32 v))
           (fn-shs-p (pgs-set-w j v fn-shs))))

(in-theory (disable pgs-set-w))

(defun pgs-pad-block (nbits fn-shs)
  ; The final block of a message whose length is a whole number of blocks:
  ; the 1 bit, zeros, and the 64-bit big-endian bit count.
  (declare (xargs :stobjs fn-shs :guard (unsigned-byte-p 64 nbits)))
  (let* ((fn-shs (pgs-set-w 0 #x80000000 fn-shs))
         (fn-shs (pgs-zero-w 1 fn-shs))
         (fn-shs (pgs-set-w 14 (pgs-hi32 nbits) fn-shs)))
    (pgs-set-w 15 (pgs-lo32 nbits) fn-shs)))

(defthm pgs-shs-p-of-pad-block
  (implies (fn-shs-p fn-shs) (fn-shs-p (pgs-pad-block nbits fn-shs))))

(in-theory (disable pgs-pad-block))

(defthm pgs-shs-hp-nth
  (implies (and (fn-shs-hp l) (natp i) (< i (len l)))
           (and (integerp (nth i l)) (<= 0 (nth i l))))
  :hints (("Goal" :in-theory (enable nth))))

(defthm pgs-h-word-natp
  (implies (and (fn-shs-p fn-shs) (natp i) (< i 8))
           (and (integerp (nth i (nth 1 fn-shs))) (<= 0 (nth i (nth 1 fn-shs)))))
  :hints (("Goal" :in-theory (enable fn-shs-p))))

(defun pgs-h-nat (i acc fn-shs)
  (declare (xargs :stobjs fn-shs :guard (and (natp i) (<= i 8) (natp acc))
                  :measure (nfix (- 8 (nfix i)))
                  :guard-hints (("Goal" :use ((:instance pgs-h-word-natp))
                                 :in-theory (disable pgs-h-word-natp)))))
  (if (mbe :logic (zp (- 8 (nfix i))) :exec (= i 8))
      (nfix acc)
    (pgs-h-nat (+ 1 (nfix i)) (+ (* (nfix acc) 4294967296) (fn-shs-h-ref i fn-shs)) fn-shs)))

(defun pgs-x-words-digest (sel base nb pgs-mem fn-shs)
  ; SHA-256 of the 64*NB octets of words [BASE, BASE + 8*NB), as a natural.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp base) (natp nb) (< nb 1099511627776)
                              (<= (+ base (* 8 nb))
                                  (pgs-x-len sel pgs-mem)))
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p)))))
  (let* ((fn-shs (fn-shs-h-init 0 *fn-sha256-h0* fn-shs))
         (fn-shs (pgs-blocks 0 nb sel base pgs-mem fn-shs))
         (fn-shs (pgs-pad-block (* 512 nb) fn-shs))
         (fn-shs (fn-shs-compress-loaded fn-shs)))
    (mv (pgs-h-nat 0 0 fn-shs) fn-shs)))

(defthm pgs-natp-of-words-digest
  (natp (mv-nth 0 (pgs-x-words-digest sel base nb pgs-mem fn-shs)))
  :rule-classes :type-prescription)

(defthm pgs-shs-p-of-words-digest
  (implies (fn-shs-p fn-shs)
           (fn-shs-p (mv-nth 1 (pgs-x-words-digest sel base nb pgs-mem fn-shs)))))

(in-theory (disable pgs-x-words-digest))

(defun pgs-x-page-digest (i pgs-mem fn-shs)
  ; The digest of resident logical page I.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp i) (<= (* (+ 1 i) *pgs-page-words*) (pgs-w-length pgs-mem)))))
  (pgs-x-words-digest 0 (* i *pgs-page-words*) (floor *pgs-page-words* 8) pgs-mem fn-shs))

