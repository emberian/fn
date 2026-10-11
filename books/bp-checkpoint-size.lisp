; A selected checkpoint is within its file (landing 4c, item 2a).  The host
; decodes the selected file with fn-bpnr-checkpoint-decode; the value it
; gets back, measured by fn-bpck-size, is no larger than the file's octets,
; and so the held rows, handoffs and jobs it carries together number at most
; the file's octets.  The profile caps none of these counts; the file does.
(in-package "ACL2")
(include-book "bp-node-rotation")

(defun fn-bpck-size (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         (cond ((or (null x) (equal x t)) 1)
               ((symbolp x) (+ 9 (length (symbol-name x))))
               ((integerp x) 9)
               ((stringp x) (+ 9 (length x)))
               ((characterp x) 2)
               (t 0)))
        ((fn-cbor-octet-listp x) (+ 9 (len x)))
        (t (+ 1 (fn-bpck-size (car x)) (fn-bpck-size (cdr x))))))

(local
 (defthm fn-bpck-u64-shape
   (implies (natp n)
            (and (true-listp (fn-bpc-u64-bytes n))
                 (equal (len (fn-bpc-u64-bytes n)) 8)
                 (fn-cbor-octet-listp (fn-bpc-u64-bytes n))))
   :hints (("Goal" :use fn-bpc-u64-bytes-have-eight-octets
            :in-theory (disable fn-bpc-u64-bytes fn-bpc-u64-bytes-have-eight-octets)))))

(local (defthm fn-bpck-counted-len
  (implies (fn-bpnr-counted tag codes) (equal (len (fn-bpnr-counted tag codes)) (+ 9 (len codes))))
  :hints (("Goal" :in-theory (enable fn-bpnr-counted)))))
(local (defthm fn-bpck-codes-len (equal (len (fn-bpnr-codes chars)) (len chars))))
(local (defthm fn-bpck-enc-within-size
  (implies (fn-bpnr-enc x d) (<= (len (fn-bpnr-enc x d)) (fn-bpck-size x)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-bpnr-enc x d)
           :in-theory (e/d (fn-bpnr-enc fn-bpck-size) (fn-bpnr-counted fn-bpc-u64-bytes fn-bpnr-codes))))))
(local (defthm fn-bpck-file-len
  (implies (fn-bpnr-checkpoint-octets ck budget)
           (equal (len (fn-bpnr-checkpoint-octets ck budget)) (+ 46 (len (fn-bpnr-enc ck budget)))))
  :hints (("Goal" :in-theory (e/d (fn-bpnr-checkpoint-octets fn-bpnr-value-octets fn-bpnr-checkpoint-prefix)
                                  (fn-bpc-u64-bytes fn-frame-trailer))
           :use ((:instance fn-frame-trailer-is-a-digest (octets (fn-bpnr-checkpoint-prefix (fn-bpnr-enc ck budget))))
                 (:instance fn-bpc-u64-bytes-have-eight-octets (n (len (fn-bpnr-enc ck budget)))))))))

; OB-SEL, precisely: a successful decode of BYTES at budget D returns a value whose accounting
; plus the remaining bytes is at most the input.
(local (defthm fn-bpck-read-u64-len
  (implies (and (true-listp bytes) (consp (fn-bpnr-read-u64 bytes)))
           (equal (len (cdr (fn-bpnr-read-u64 bytes))) (- (len bytes) 8)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (fn-bpnr-read-u64) (fn-frame-split-suffix-len))
           :use ((:instance fn-frame-split-suffix-len (n 8) (xs bytes)))))))
(local (defthm fn-bpck-read-u64-true-listp
  (implies (and (true-listp bytes) (consp (fn-bpnr-read-u64 bytes)))
           (true-listp (cdr (fn-bpnr-read-u64 bytes))))
  :hints (("Goal" :in-theory (e/d (fn-bpnr-read-u64) (fn-frame-split-suffix-true-listp))
           :use ((:instance fn-frame-split-suffix-true-listp (n 8) (xs bytes)))))))
(local (defthm fn-bpck-read-counted-len
  (implies (and (true-listp bytes) (consp (fn-bpnr-read-counted bytes)))
           (equal (+ 8 (len (car (fn-bpnr-read-counted bytes))) (len (cdr (fn-bpnr-read-counted bytes))))
                  (len bytes)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bpnr-read-counted) (fn-bpnr-read-u64 fn-frame-split-suffix-len fn-frame-split-prefix-len))
           :use ((:instance fn-bpck-read-u64-len) (:instance fn-bpck-read-u64-true-listp)
                 (:instance fn-frame-split-prefix-len (n (nfix (car (fn-bpnr-read-u64 bytes)))) (xs (if (true-listp (cdr (fn-bpnr-read-u64 bytes))) (cdr (fn-bpnr-read-u64 bytes)) nil)))
                 (:instance fn-frame-split-suffix-len (n (nfix (car (fn-bpnr-read-u64 bytes)))) (xs (if (true-listp (cdr (fn-bpnr-read-u64 bytes))) (cdr (fn-bpnr-read-u64 bytes)) nil))))))))

(local (defthm fn-bpck-len8-conses
  (implies (equal (len l) 8)
           (and (consp l) (consp (cdr l)) (consp (cddr l)) (consp (cdddr l))
                (consp (cddddr l)) (consp (cdr (cddddr l))) (consp (cddr (cddddr l)))
                (consp (cdddr (cddddr l)))))
  :hints (("Goal" :expand ((len l) (len (cdr l)) (len (cddr l)) (len (cdddr l)) (len (cddddr l))
                           (len (cdr (cddddr l))) (len (cddr (cddddr l))) (len (cdddr (cddddr l))))))))
(local (defthm fn-bpck-read-u64-natp
  (implies (consp (fn-bpnr-read-u64 bytes)) (natp (car (fn-bpnr-read-u64 bytes))))
  :hints (("Goal" :in-theory (e/d (fn-bpnr-read-u64) (fn-bpc-u64-from fn-frame-split))
           :use ((:instance fn-bpc-u64-from-is-natural (xs (car (fn-frame-split 8 (if (true-listp bytes) bytes nil)))))
                 (:instance fn-bpck-len8-conses (l (car (fn-frame-split 8 (if (true-listp bytes) bytes nil))))))))))
(local (defthm fn-bpck-read-u64-integerp
  (implies (consp (fn-bpnr-read-u64 bytes)) (integerp (car (fn-bpnr-read-u64 bytes))))
  :hints (("Goal" :use fn-bpck-read-u64-natp :in-theory (disable fn-bpck-read-u64-natp)))))
(local (defthm fn-bpck-read-counted-size
  (implies (consp (fn-bpnr-read-counted bytes))
           (<= (fn-bpck-size (car (fn-bpnr-read-counted bytes)))
               (+ 9 (len (car (fn-bpnr-read-counted bytes))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-bpnr-read-counted fn-bpck-size) (fn-bpnr-read-u64 fn-frame-split))))))
(local (defthm fn-bpck-read-counted-true-listp
  (implies (and (true-listp bytes) (consp (fn-bpnr-read-counted bytes)))
           (true-listp (cdr (fn-bpnr-read-counted bytes))))
  :hints (("Goal" :in-theory (e/d (fn-bpnr-read-counted) (fn-bpnr-read-u64 fn-frame-split-suffix-true-listp))
           :use ((:instance fn-frame-split-suffix-true-listp (n (nfix (car (fn-bpnr-read-u64 bytes))))
                            (xs (if (true-listp (cdr (fn-bpnr-read-u64 bytes))) (cdr (fn-bpnr-read-u64 bytes)) nil))))))))
(local (defthm fn-bpck-dec-rest-true-listp
  (implies (and (true-listp bytes) (consp (fn-bpnr-dec bytes d)))
           (true-listp (cdr (fn-bpnr-dec bytes d))))
  :hints (("Goal" :induct (fn-bpnr-dec bytes d)
           :in-theory (e/d (fn-bpnr-dec) (fn-bpnr-read-u64 fn-bpnr-read-counted))))))
(local (defthm fn-bpck-size-of-integer (implies (integerp x) (equal (fn-bpck-size x) 9))
  :hints (("Goal" :in-theory (enable fn-bpck-size)))))
(local (defthm fn-bpck-chars-len (equal (len (fn-bpnr-chars codes)) (len codes))))
(local (defthm fn-bpck-length-of-coerce
  (implies (character-listp x) (equal (length (coerce x 'string)) (len x)))))
(local (defthm fn-bpck-size-of-interned
  (implies (and (stringp s) (symbolp sym) (not (equal (intern-in-package-of-symbol s sym) nil))
                (not (equal (intern-in-package-of-symbol s sym) t)))
           (equal (fn-bpck-size (intern-in-package-of-symbol s sym)) (+ 9 (length s))))
  :hints (("Goal" :in-theory (enable fn-bpck-size)))))
(local (defthm fn-bpck-dec-size
  (implies (and (true-listp bytes) (consp (fn-bpnr-dec bytes d)))
           (<= (+ (fn-bpck-size (car (fn-bpnr-dec bytes d))) (len (cdr (fn-bpnr-dec bytes d))))
               (len bytes)))
  :hints (("Goal" :induct (fn-bpnr-dec bytes d)
           :in-theory (e/d (fn-bpnr-dec fn-bpck-size) (fn-bpnr-read-u64 fn-bpnr-read-counted))))))



(local
 (defthm fn-bpck-split-within
   (implies (and (true-listp xs) (fn-frame-split n xs))
            (<= (len (car (fn-frame-split n xs))) (len xs)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-frame-split-prefix-len)
                         (:instance fn-frame-split-suffix-len))
            :in-theory (disable fn-frame-split-prefix-len fn-frame-split-suffix-len)))))

(local
 (defthm fn-bpck-body-size
   (implies (and (true-listp body) (consp (fn-bpnr-dec body d)) (null (cdr (fn-bpnr-dec body d))))
            (<= (fn-bpck-size (car (fn-bpnr-dec body d))) (len body)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :use (:instance fn-bpck-dec-size (bytes body))
            :in-theory (disable fn-bpck-dec-size fn-bpnr-dec fn-bpck-size)))))

(local
 (defthm fn-bpck-octet-listp-true-listp
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :rule-classes :forward-chaining))

(local
 (defthm fn-bpck-framed-body-size
   (implies (and (true-listp bytes)
                 (consp (fn-bpnr-read-u64 bytes))
                 (fn-frame-split (nfix (car (fn-bpnr-read-u64 bytes)))
                                 (cdr (fn-bpnr-read-u64 bytes)))
                 (consp (fn-bpnr-dec (car (fn-frame-split (nfix (car (fn-bpnr-read-u64 bytes)))
                                                          (cdr (fn-bpnr-read-u64 bytes))))
                                     d))
                 (null (cdr (fn-bpnr-dec (car (fn-frame-split (nfix (car (fn-bpnr-read-u64 bytes)))
                                                              (cdr (fn-bpnr-read-u64 bytes))))
                                         d))))
            (<= (fn-bpck-size (car (fn-bpnr-dec (car (fn-frame-split (nfix (car (fn-bpnr-read-u64 bytes)))
                                                                     (cdr (fn-bpnr-read-u64 bytes))))
                                                d)))
                (len bytes)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bpck-split-within (n (nfix (car (fn-bpnr-read-u64 bytes))))
                             (xs (cdr (fn-bpnr-read-u64 bytes))))
                  (:instance fn-bpck-body-size
                             (body (car (fn-frame-split (nfix (car (fn-bpnr-read-u64 bytes)))
                                                        (cdr (fn-bpnr-read-u64 bytes)))))
                             (d d))
                  fn-bpck-read-u64-len fn-bpck-read-u64-true-listp
                  (:instance fn-frame-split-prefix-true-listp (n (nfix (car (fn-bpnr-read-u64 bytes)))) (xs (cdr (fn-bpnr-read-u64 bytes)))))
            :in-theory (disable fn-bpck-split-within fn-bpck-read-u64-len
                                fn-bpck-read-u64-true-listp fn-bpnr-read-u64 fn-bpnr-dec
                                fn-frame-split fn-bpck-size)))))

(defthm fn-bpck-checkpoint-decode-size
  (implies (fn-bpnr-checkpoint-decode octets budget)
           (<= (fn-bpck-size (fn-bpnr-checkpoint-decode octets budget)) (len octets)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnr-checkpoint-decode)
                           (fn-bpnr-read-u64 fn-bpnr-dec fn-frame-split fn-bpnr-checkpointp
                            fn-frame-trailer fn-bpnr-checkpoint-prefix fn-bpck-size))
           :use ((:instance fn-frame-split-suffix-len (n 6) (xs octets))
                 (:instance fn-frame-split-suffix-true-listp (n 6) (xs octets))
                 (:instance fn-bpck-framed-body-size
                            (bytes (cdr (fn-frame-split 6 octets))) (d budget))))))

(local
 (defthm fn-bpck-len-within-size
   (<= (len x) (fn-bpck-size x))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-bpck-size)))))

(local
 (defthm fn-bpck-size-natp
   (natp (fn-bpck-size x))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-bpck-size)))))

(local
 (defthm fn-bpck-size-of-checkpoint-slots
   (implies (and (true-listp held) (true-listp handoffs) (true-listp jobs))
            (<= (+ (fn-bpck-size held) (fn-bpck-size handoffs) (fn-bpck-size jobs))
                (fn-bpck-size (list :bpnr-checkpoint generation held handoffs prior
                                    next-arrival covered jobs next-token))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bpck-size)))))

(local
 (defthm fn-bpck-plan-checkpoint-is-decode
   (equal (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan present octets budget))
          (if present (fn-bpnr-checkpoint-decode octets budget) nil))
   :hints (("Goal" :in-theory (e/d (fn-bpnr-selection-plan fn-bpnr-plan-checkpoint fn-cbor-ag-car fn-bpn-nth)
                                   (fn-bpnr-checkpoint-decode))))))

(local
 (defthm fn-bpck-plan-checkpoint-is-decode
   (equal (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan present octets budget))
          (if present (fn-bpnr-checkpoint-decode octets budget) nil))
   :hints (("Goal" :in-theory (e/d (fn-bpnr-selection-plan fn-bpnr-plan-checkpoint fn-cbor-ag-car fn-bpn-nth)
                                   (fn-bpnr-checkpoint-decode))))))

;; KEYSTONE: a selected checkpoint is no larger than the file it was decoded from.
(defthm fn-bpck-selected-checkpoint-within-its-file
  (implies (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan present octets budget))
           (<= (fn-bpck-size (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan present octets budget)))
               (len octets)))
  :rule-classes nil
  :hints (("Goal" :use fn-bpck-checkpoint-decode-size
           :in-theory (union-theories '(fn-bpck-plan-checkpoint-is-decode)
                                      (disable fn-bpnr-selection-plan fn-bpnr-plan-checkpoint fn-bpnr-checkpoint-decode)))))

(local
 (defthm fn-bpck-decode-is-checkpointp
   (implies (fn-bpnr-checkpoint-decode octets budget)
            (fn-bpnr-checkpointp (fn-bpnr-checkpoint-decode octets budget)))
   :hints (("Goal" :in-theory (e/d (fn-bpnr-checkpoint-decode)
                                   (fn-bpnr-read-u64 fn-bpnr-dec fn-frame-split fn-frame-trailer
                                    fn-bpnr-checkpoint-prefix fn-bpnr-checkpointp))))))

(local
 (defthm fn-bpck-checkpointp-head
   (implies (fn-bpnr-checkpointp x)
            (and (true-listp x) (equal (len x) 9) (equal (nth 0 x) :bpnr-checkpoint)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bpnr-checkpointp)))))

(local
 (defthm fn-bpck-len9-is-nine-slots
   (implies (and (true-listp ck) (equal (len ck) 9))
            (equal ck (list (nth 0 ck) (nth 1 ck) (nth 2 ck) (nth 3 ck) (nth 4 ck)
                            (nth 5 ck) (nth 6 ck) (nth 7 ck) (nth 8 ck))))
   :rule-classes nil
   :hints (("Goal" :expand ((len ck) (len (cdr ck)) (len (cddr ck)) (len (cdddr ck)) (len (cddddr ck))
                            (len (cdr (cddddr ck))) (len (cddr (cddddr ck))) (len (cdddr (cddddr ck)))
                            (len (cddddr (cddddr ck))))))))

(local
 (defthm fn-bpck-checkpoint-is-its-slots
   (implies (fn-bpnr-checkpointp ck)
            (equal ck (list :bpnr-checkpoint (nth 1 ck) (nth 2 ck) (nth 3 ck) (nth 4 ck)
                            (nth 5 ck) (nth 6 ck) (nth 7 ck) (nth 8 ck))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bpck-len9-is-nine-slots
                  (:instance fn-bpck-checkpointp-head (x ck)))
            :in-theory (disable fn-bpnr-checkpointp)))))

(local
 (defthm fn-bpck-checkpoint-slots-within-size
   (implies (fn-bpnr-checkpointp ck)
            (<= (+ (len (fn-bpnr-checkpoint-held ck))
                   (len (fn-bpnr-checkpoint-handoffs ck))
                   (len (fn-bpnr-checkpoint-jobs ck)))
                (fn-bpck-size ck)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnr-checkpointp fn-bpnr-checkpoint-held fn-bpnr-checkpoint-handoffs
                             fn-bpnr-checkpoint-jobs fn-bpn-nth fn-cbor-ag-car)
                            (fn-bpck-len-within-size))
            :use (fn-bpck-checkpoint-is-its-slots
                  (:instance fn-bpck-size-of-checkpoint-slots
                             (generation (nth 1 ck)) (held (nth 2 ck)) (handoffs (nth 3 ck))
                             (prior (nth 4 ck)) (next-arrival (nth 5 ck)) (covered (nth 6 ck))
                             (jobs (nth 7 ck)) (next-token (nth 8 ck)))
                  (:instance fn-bpck-len-within-size (x (nth 2 ck)))
                  (:instance fn-bpck-len-within-size (x (nth 3 ck)))
                  (:instance fn-bpck-len-within-size (x (nth 7 ck))))))))

;; KEYSTONE: so its held rows, handoffs and jobs together number at most the file octets
;; (the profile caps none of these counts; the file does).
(defthm fn-bpck-selected-checkpoint-counts-within-its-file
  (implies (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan present octets budget))
           (let ((ck (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan present octets budget))))
             (<= (+ (len (fn-bpnr-checkpoint-held ck))
                    (len (fn-bpnr-checkpoint-handoffs ck))
                    (len (fn-bpnr-checkpoint-jobs ck)))
                 (len octets))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bpck-selected-checkpoint-within-its-file
                 (:instance fn-bpck-checkpoint-slots-within-size
                            (ck (fn-bpnr-checkpoint-decode octets budget)))
                 fn-bpck-decode-is-checkpointp fn-bpck-plan-checkpoint-is-decode)
           :in-theory (disable fn-bpnr-selection-plan fn-bpnr-plan-checkpoint fn-bpnr-checkpoint-decode
                               fn-bpnr-checkpointp fn-bpnr-checkpoint-held fn-bpnr-checkpoint-handoffs
                               fn-bpnr-checkpoint-jobs fn-bpck-plan-checkpoint-is-decode
                               fn-bpck-decode-is-checkpointp))))
