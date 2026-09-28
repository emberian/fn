;; fn: the page store's word layer (lane arena-store, 2026-09-27).  Prefix pgs-.
;;
;; The stobj the host fills and drains with its two byte primitives
;; (host/native/proto-pagestore-io.lisp), and the page digest: BLAKE3 over
;; the little-endian octets of a range of its u64 words (lane arena-store-4,
;; 2026-09-28; SHA-256 until then).  The words are copied into the page
;; store's own octet buffer `fn-octets-pg' (congruent to fn-octets,
;; books/octets-stobj.lisp), two u32 halves at a time, and hashed in place by
;; books/blake3-stobj.lisp's `fn-blake3-of-prefixed-buffer'.  Work and
;; allocation are those of the range: a page is 16 KiB, a directory run as
;; many pages as it has, and the buffer is reused across calls (cleared, not
;; reallocated).  BLAKE3 is the digest `fn-digest' is attached to
;; (books/crypto-attach.lisp attaches `fn-blake3-stobj', proved equal to
;; `fn-blake3'); the correspondence to `fn-blake3'
;; (`pgs-x-words-digest-is-blake3') is proved in
;; books/pagestore-words-blake3.lisp against this frozen book.
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
(include-book "blake3-stobj")
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

(local (in-theory (disable floor mod truncate rem ash)))

; -----------------------------------------------------------------------------
; The digest's octet buffer: the page store's own live object, congruent to
; fn-octets (the served attempt's buffer and the log walk's are never
; touched by a page digest).

(defabsstobj fn-octets-pg
  :foundation fn-octets$c
  :recognizer (fn-octets-pg-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets-pg :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-octets-pg-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-pg-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-pg-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-pg-append-octet :logic fn-octets$a-append-octet
                                       :exec fn-octets$c-append-octet :protect t)
            (fn-octets-pg-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-pg-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                  :protect t)
            (fn-octets-pg-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-pg-from-list :logic fn-octets$a-from-list
                                    :exec fn-octets$c-from-list :protect t)
            (fn-octets-pg-append-list :logic fn-octets$a-append-list
                                      :exec fn-oct-write-list :protect t)
            (fn-octets-pg-append-back :logic fn-octets$a-append-back
                                      :exec fn-octets$c-append-back :protect t)
            (fn-octets-pg-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-octets-pg-append-word :logic fn-octets$a-append-word
                                      :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

(defthm pgs-oct-clear-is-nil
  (equal (fn-octets-pg-clear fn-octets-pg) nil)
  :hints (("Goal" :in-theory (enable fn-octets-pg-clear))))

(defthm pgs-oct-append-word-is-append
  (equal (fn-octets-pg-append-word w k fn-octets-pg)
         (append fn-octets-pg (fn-oct-word-octets w k)))
  :hints (("Goal" :in-theory (enable fn-octets-pg-append-word))))

(defthm pgs-oct-list-is-identity
  (equal (fn-octets-pg-list fn-octets-pg) fn-octets-pg)
  :hints (("Goal" :in-theory (enable fn-octets-pg-list))))

(defthm pgs-oct-p-is-octet-listp
  (equal (fn-octets-pg-p x) (fn-cbor-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-octets-pg-p))))

(in-theory (disable fn-octets-pg-p fn-octets-pg-clear fn-octets-pg-append-word fn-octets-pg-list))

; The buffer's concrete-array rules (books/octets-stobj.lisp) are about its
; foundation, never about the page store's lists, and backchaining through
; them on every `true-listp' more than doubled pagestore-keystones' prover
; steps: out of the page store's theory.
(in-theory (disable fn-oct-bufp-true-listp fn-oct-bufp-cell-is-octet fn-oct-bufp-of-update-nth
                    fn-oct-bufp-of-resize-list fn-octets$c-bufp))

; -----------------------------------------------------------------------------
; BLAKE3 over words: the octets of a word range, each word little-endian.

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

(in-theory (disable pgs-x-word$inline pgs-lo32$inline pgs-hi32$inline))

(defun pgs-octets-be-nat-acc (os acc)
  (declare (xargs :guard (natp acc)))
  (if (consp os)
      (pgs-octets-be-nat-acc (cdr os) (+ (* 256 (nfix acc)) (nfix (car os))))
    (nfix acc)))

(defun pgs-octets-be-nat (os)
  ; The natural whose big-endian octets OS are: the 256-bit digest the
  ; table entries and records hold as four words.
  (declare (xargs :guard t))
  (pgs-octets-be-nat-acc os 0))

(defun pgs-x-words-load (k n sel base pgs-mem fn-octets-pg)
  ; Append the little-endian octets of words [BASE + K, BASE + N) of the
  ; array SEL names to the buffer, each word as its low and high halves.
  (declare (xargs :stobjs (pgs-mem fn-octets-pg)
                  :guard (and (natp k) (natp n) (natp base) (<= k n)
                              (<= (+ base n) (pgs-x-len sel pgs-mem)))
                  :measure (nfix (- (nfix n) (nfix k)))))
  (if (mbe :logic (zp (- (nfix n) (nfix k))) :exec (= k n))
      fn-octets-pg
    (let* ((w (pgs-x-word sel (+ base k) pgs-mem))
           (fn-octets-pg (fn-octets-pg-append-word (pgs-lo32 w) 4 fn-octets-pg))
           (fn-octets-pg (fn-octets-pg-append-word (pgs-hi32 w) 4 fn-octets-pg)))
      (pgs-x-words-load (+ 1 (nfix k)) n sel base pgs-mem fn-octets-pg))))

(defthm pgs-oct-p-of-words-load
  (implies (fn-octets-pg-p fn-octets-pg)
           (fn-octets-pg-p (pgs-x-words-load k n sel base pgs-mem fn-octets-pg))))

(in-theory (disable pgs-x-words-load))

(defun pgs-x-words-digest (sel base nb pgs-mem fn-octets-pg)
  ; BLAKE3 of the 64*NB octets of words [BASE, BASE + 8*NB), as the
  ; big-endian natural of its 32 octets: (mv DIGEST fn-octets-pg).
  (declare (xargs :stobjs (pgs-mem fn-octets-pg)
                  :guard (and (natp base) (natp nb)
                              (<= (+ base (* 8 nb))
                                  (pgs-x-len sel pgs-mem)))))
  (let* ((fn-octets-pg (fn-octets-pg-clear fn-octets-pg))
         (fn-octets-pg (pgs-x-words-load 0 (* 8 nb) sel base pgs-mem fn-octets-pg)))
    ; The buffer twin runs; its logical value is the list definition's
    ; (`fn-blake3-of-prefixed-buffer-is-blake3', the guard proof), so
    ; ground evaluation in the logic reads the octets as a list, not by
    ; index.
    (mv (pgs-octets-be-nat (mbe :logic (fn-blake3 (fn-octets-pg-list fn-octets-pg))
                                :exec (fn-blake3-of-prefixed-buffer nil fn-octets-pg)))
        fn-octets-pg)))

(defthm pgs-natp-of-words-digest
  (natp (mv-nth 0 (pgs-x-words-digest sel base nb pgs-mem fn-octets-pg)))
  :rule-classes :type-prescription)

(defthm pgs-oct-p-of-words-digest
  (fn-octets-pg-p (mv-nth 1 (pgs-x-words-digest sel base nb pgs-mem fn-octets-pg))))

(in-theory (disable pgs-x-words-digest))

(defun pgs-x-page-digest (i pgs-mem fn-octets-pg)
  ; The digest of resident logical page I.
  (declare (xargs :stobjs (pgs-mem fn-octets-pg)
                  :guard (and (natp i) (<= (* (+ 1 i) *pgs-page-words*) (pgs-w-length pgs-mem)))))
  (pgs-x-words-digest 0 (* i *pgs-page-words*) (floor *pgs-page-words* 8) pgs-mem fn-octets-pg))

; The octet lists' recognizer from books/cbor.lisp (through the buffer's
; include) backchains on every `true-listp' the page store's books ask; the
; page store never reasons about octet lists past this point.
(in-theory (disable fn-cbor-octet-listp-implies-true-listp fn-cbor-octet-listp))
