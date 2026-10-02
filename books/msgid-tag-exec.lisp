; fn: the Message-ID's keyed tag computed consing nothing (lane served-
; incremental-3, 2026-10-02).  The executable twin of books/msgid-linear-exec
; `fn-mlh-tag', which `fn-mlh-tag' itself and `fn-mlh-tag-of' execute.
;
; THE TAG is the first eight octets of the keyed BLAKE3 of the Message-ID's
; octets, read as a little-endian natural, reduced to 60 bits and floored at
; 1 (`fn-mlh-tag').  The list model builds the Message-ID's octet list, the
; key's word list, a block's word lists, the node's output record and the 32
; output octets: about 3 KB per tag at 23 octets and the key's 32-cons list
; on top at every catalog probe (measured, hbox, 2026-10-02).  Here the key
; is eight words read from wherever it is kept (`fn-mlh-key-word' from a
; list), the message is read from the string by index
; (books/blake3-string `fn-b3s-root'), and the tag is the root's first two
; output words: 2^32 * (o1 mod 2^28) + o0, a fixnum, without forming the
; 64-bit natural (`fn-mlh-tag-x').
;
; KEYSTONE `fn-mlh-tag-x-is-tag': for a string, `fn-mlh-tag-x' of the key's
; eight words is the list model's tag, for any key object.

(in-package "ACL2")
(include-book "blake3-string")
(include-book "msgid-pages-exec")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The key's words: word J of the key read as eight words (keyed_hash reads
; its 32-octet key so, books/blake3 `fn-blake3-keyed').

(local
 (defthm fn-mte-nthx-of-cons
   (equal (fn-b3-nthx i (cons x y))
          (if (zp (nfix i)) x (fn-b3-nthx (- (nfix i) 1) y)))))

(local
 (defthm fn-mte-nthx-of-non-cons
   (implies (not (consp x)) (equal (fn-b3-nthx i x) 0))))

(local
 (defthm fn-mte-nthx-of-nthcdrx
   (equal (fn-b3-nthx j (fn-b3-nthcdrx a l))
          (fn-b3-nthx (+ (nfix a) (nfix j)) l))
   :hints (("Goal" :induct (fn-b3-nthcdrx a l)))))

(local
 (defun fn-mte-ind-words (j k x)
   (declare (xargs :measure (nfix k)))
   (if (zp (nfix k)) (list j x)
     (fn-mte-ind-words (- (nfix j) 1) (- (nfix k) 1) (fn-b3-nthcdrx 4 x)))))

(local
 (defthm fn-mte-nthx-of-words
   (implies (natp j)
            (equal (fn-b3-nthx j (fn-b3-words k x))
                   (if (< j (nfix k))
                       (fn-b3-le-word (fn-b3-nthx (* 4 j) x) (fn-b3-nthx (+ 1 (* 4 j)) x)
                                      (fn-b3-nthx (+ 2 (* 4 j)) x) (fn-b3-nthx (+ 3 (* 4 j)) x))
                     0)))
   :hints (("Goal" :induct (fn-mte-ind-words j k x)
            :expand ((fn-b3-words k x))))))

(local
 (defthm fn-mte-nthx-of-fix-octets
   (equal (fn-b3-nthx i (fn-b3-fix-octets l))
          (fn-b3-octet (fn-b3-nthx i l)))
   :hints (("Goal" :in-theory (enable fn-b3-octet fn-b3-fix-octets fn-b3-fix-octets-walk)
            :induct (fn-b3-nthx i l)))))

(local
 (defthm fn-mte-le-word-of-octets
   (equal (fn-b3-le-word (fn-b3-octet a) (fn-b3-octet b) (fn-b3-octet c) (fn-b3-octet d))
          (fn-b3-le-word a b c d))
   :hints (("Goal" :in-theory (enable fn-b3-le-word fn-b3-octet fn-b3-byte)))))

(local (in-theory (disable fn-b3-nthx fn-b3-fix-octets)))

(defun fn-mlh-key-word (j key)
  (declare (xargs :guard (and (natp j) (< j 8))
                  :guard-hints (("Goal" :in-theory (disable fn-b3-words fn-b3-le-word)))))
  (mbe :logic (fn-b3-nthx j (fn-b3-words 8 (fn-b3-fix-octets key)))
       :exec (fn-b3-le-word (fn-b3-nthx (* 4 j) key) (fn-b3-nthx (+ 1 (* 4 j)) key)
                            (fn-b3-nthx (+ 2 (* 4 j)) key) (fn-b3-nthx (+ 3 (* 4 j)) key))))

(defthm fn-mlh-key-word-is-le-word
  (implies (and (natp j) (< j 8))
           (equal (fn-mlh-key-word j key)
                  (fn-b3-le-word (fn-b3-nthx (* 4 j) key) (fn-b3-nthx (+ 1 (* 4 j)) key)
                                 (fn-b3-nthx (+ 2 (* 4 j)) key) (fn-b3-nthx (+ 3 (* 4 j)) key)))))

(in-theory (disable fn-mlh-key-word-is-le-word))

; -----------------------------------------------------------------------------
; The tag from the eight key words.

(defun fn-mlh-tag-x (msgid k0 k1 k2 k3 k4 k5 k6 k7)
  (declare (xargs :guard (stringp msgid)))
  (mv-let (o0 o1 o2 o3 o4 o5 o6 o7)
    (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 *fn-b3-keyed-hash* msgid)
    (declare (ignore o2 o3 o4 o5 o6 o7))
    (max 1 (+ (fn-b3-word o0) (* 4294967296 (mod (fn-b3-word o1) 268435456))))))

; The Message-ID's octets are the string's octets.
(local
 (defthm fn-mte-string-octets-aux-is-codes
   (equal (fn-record-string-octets-aux cs) (fn-b3s-codes cs))
   :hints (("Goal" :in-theory (enable fn-record-string-octets-aux)))))

(local
 (defthm fn-mte-string-octets-is-msg
   (implies (stringp msgid)
            (equal (fn-record-string-octets msgid) (fn-b3s-msg msgid)))
   :hints (("Goal" :in-theory (enable fn-b3s-msg fn-record-string-octets)))))

(local
 (defthm fn-mte-fix-of-string-octets
   (implies (stringp msgid)
            (equal (fn-b3-fix-octets (fn-record-string-octets msgid))
                   (fn-b3s-msg msgid)))))

; The key's word list is the list of its eight words.
(local
 (defthm fn-mte-key-words-list
   (equal (list (fn-mlh-key-word 0 key) (fn-mlh-key-word 1 key) (fn-mlh-key-word 2 key) (fn-mlh-key-word 3 key)
                (fn-mlh-key-word 4 key) (fn-mlh-key-word 5 key) (fn-mlh-key-word 6 key) (fn-mlh-key-word 7 key))
          (fn-b3-words 8 (fn-b3-fix-octets key)))
   :hints (("Goal" :in-theory (disable fn-mte-nthx-of-words fn-mte-nthx-of-fix-octets)
            :expand ((:free (x) (fn-b3-words 8 x)) (:free (x) (fn-b3-words 7 x)) (:free (x) (fn-b3-words 6 x))
                     (:free (x) (fn-b3-words 5 x)) (:free (x) (fn-b3-words 4 x)) (:free (x) (fn-b3-words 3 x))
                     (:free (x) (fn-b3-words 2 x)) (:free (x) (fn-b3-words 1 x)) (:free (x) (fn-b3-words 0 x)))))))

; The first eight octets of eight words, read little-endian.
(local
 (defthm fn-mte-mod-bounds
   (and (natp (mod (fn-b3-word w) 256))
        (< (mod (fn-b3-word w) 256) 256)
        (natp (mod (floor (fn-b3-word w) 256) 256))
        (< (mod (floor (fn-b3-word w) 256) 256) 256)
        (natp (mod (floor (fn-b3-word w) 65536) 256))
        (< (mod (floor (fn-b3-word w) 65536) 256) 256)
        (natp (mod (floor (fn-b3-word w) 16777216) 256))
        (< (mod (floor (fn-b3-word w) 16777216) 256) 256))
   :hints (("Goal" :use ((:instance fn-b3-word-type (x w)))
            :in-theory (e/d (unsigned-byte-p) (fn-b3-word-type))))))

(local
 (defthm fn-mte-word8-of-words-octets
   (implies (and (true-listp x) (equal (len x) 8))
            (equal (fn-mpxt-word 8 (fn-b3-words-octets x))
                   (+ (fn-b3-word (car x)) (* 4294967296 (fn-b3-word (cadr x))))))
   :hints (("Goal" :in-theory (e/d (fn-b3-words-octets min) (floor mod))
            :expand ((fn-b3-words-octets x) (fn-b3-words-octets (cdr x)))
            :use ((:instance fn-b3s-word-of-octets (w (fn-b3-word (car x))))
                  (:instance fn-b3s-word-of-octets (w (fn-b3-word (cadr x))))
                  (:instance fn-mte-mod-bounds (w (car x)))
                  (:instance fn-mte-mod-bounds (w (cadr x))))))))

(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-mte-mod-60
     (implies (and (natp a) (< a 4294967296) (natp b))
              (equal (mod (+ a (* 4294967296 b)) 1152921504606846976)
                     (+ a (* 4294967296 (mod b 268435456))))))))

(local
 (defthm fn-mte-mac-is-root-octets
   (implies (stringp msgid)
            (equal (fn-ns-mac key (fn-record-string-octets msgid))
                   (fn-b3-words-octets (fn-b3s-root (fn-mlh-key-word 0 key) (fn-mlh-key-word 1 key)
                                    (fn-mlh-key-word 2 key) (fn-mlh-key-word 3 key)
                                    (fn-mlh-key-word 4 key) (fn-mlh-key-word 5 key)
                                    (fn-mlh-key-word 6 key) (fn-mlh-key-word 7 key)
                                    *fn-b3-keyed-hash* msgid))))
   :hints (("Goal" :in-theory (e/d (fn-ns-mac fn-blake3-keyed)
                                   (fn-mlh-key-word fn-b3s-root-is-hash fn-b3-words-octets))
            :use ((:instance fn-b3s-root-is-hash
                             (k0 (fn-mlh-key-word 0 key)) (k1 (fn-mlh-key-word 1 key))
                             (k2 (fn-mlh-key-word 2 key)) (k3 (fn-mlh-key-word 3 key))
                             (k4 (fn-mlh-key-word 4 key)) (k5 (fn-mlh-key-word 5 key))
                             (k6 (fn-mlh-key-word 6 key)) (k7 (fn-mlh-key-word 7 key))
                             (flags *fn-b3-keyed-hash*) (s msgid)))))))

(local
 (defthm fn-mte-tag-x-is-root-word
   (implies (stringp msgid)
            (equal (fn-mlh-tag-x msgid k0 k1 k2 k3 k4 k5 k6 k7)
                   (max 1 (mod (fn-mpxt-word 8 (fn-b3-words-octets (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 *fn-b3-keyed-hash* msgid)))
                               1152921504606846976))))
   :hints (("Goal" :in-theory (e/d (unsigned-byte-p)
                                   (fn-b3-words-octets fn-mpxt-word
                                    floor mod fn-b3-word fn-b3-word-type fn-b3s-root fn-b3s-root-is-hash))
            :use ((:instance fn-b3-word-type (x (car (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 *fn-b3-keyed-hash* msgid))))
                  (:instance fn-b3-word-type (x (cadr (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 *fn-b3-keyed-hash* msgid))))
                  (:instance fn-mte-mod-60
                             (a (fn-b3-word (car (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 *fn-b3-keyed-hash* msgid))))
                             (b (fn-b3-word (cadr (fn-b3s-root k0 k1 k2 k3 k4 k5 k6 k7 *fn-b3-keyed-hash* msgid))))))))))

(defthm fn-mlh-tag-x-is-tag
  (implies (stringp msgid)
           (equal (fn-mlh-tag-x msgid (fn-mlh-key-word 0 key) (fn-mlh-key-word 1 key)
                                (fn-mlh-key-word 2 key) (fn-mlh-key-word 3 key)
                                (fn-mlh-key-word 4 key) (fn-mlh-key-word 5 key)
                                (fn-mlh-key-word 6 key) (fn-mlh-key-word 7 key))
                  (max 1 (mod (fn-mpxt-word 8 (fn-ns-mac key (fn-record-string-octets msgid)))
                              1152921504606846976))))
  :hints (("Goal" :in-theory (union-theories '(fn-mte-tag-x-is-root-word fn-mte-mac-is-root-octets)
                                             (theory 'minimal-theory)))))

(in-theory (disable fn-mlh-tag-x))
