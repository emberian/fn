; Logical source abstraction is proof-only; the served reader borrows its string.
(in-package "ACL2")
(include-book "substrate-commit-profile-codec")
(local (defthm fn-stcp-nth-of-string-octets-aux
 (implies (and (character-listp chars) (natp i) (< i (len chars)))
  (equal (nth i (fn-record-string-octets-aux chars))
         (char-code (nth i chars))))
 :hints (("Goal" :induct (nth i chars)
          :in-theory (enable fn-record-string-octets-aux nth)))))
(local (defthm fn-stcp-len-of-string-octets-aux
 (equal (len (fn-record-string-octets-aux chars)) (len chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars)))))
(local (defthm fn-stcp-car-of-nthcdr
 (equal (car (nthcdr i xs)) (nth i xs))
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr nth)))))
(local (include-book "arithmetic/top" :dir :system))
(local (defthm fn-stcp-shift-less
 (implies (and (integerp i) (integerp n))
  (equal (< (+ -1 i) n) (< i (+ 1 n))))
 :hints (("Goal" :cases ((< i (+ 1 n)))))))
(local (defthm fn-stcp-consp-nthcdr
 (implies (natp i) (equal (consp (nthcdr i xs)) (< i (len xs))))
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr len)))))
(defthm fn-stcp-borrowed-source-byte-is-logical
 (implies (and (stringp text) (natp offset) (< offset (length text)))
  (equal (fn-stcp-source-byte text offset)
         (fn-stcp-source-byte (nthcdr offset (fn-record-string-octets text)) offset)))
 :hints (("Goal" :in-theory (enable fn-stcp-source-byte fn-cbor-ag-car
                                    fn-record-string-octets char))))
(defthm fn-stcp-borrowed-source-empty-is-logical
 (implies (and (stringp text) (natp offset))
  (equal (fn-stcp-source-empty text offset)
         (fn-stcp-source-empty (nthcdr offset (fn-record-string-octets text)) offset)))
 :hints (("Goal" :in-theory (enable fn-stcp-source-empty fn-record-string-octets))))
(local (defthm fn-stcp-nthcdr-next
 (implies (natp i) (equal (nthcdr (+ 1 i) xs) (cdr (nthcdr i xs))))
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr)))))
(defthm fn-stcp-borrowed-source-advance-is-logical
 (implies (and (stringp text) (natp offset))
  (equal (nthcdr (+ 1 offset)
                (fn-record-string-octets (fn-stcp-source-next text)))
         (fn-stcp-source-next (nthcdr offset (fn-record-string-octets text)))))
 :hints (("Goal" :in-theory (enable fn-stcp-source-next fn-cbor-ag-cdr))))
(local (defthm fn-stcp-nthcdr-past-list
 (implies (and (true-listp xs) (natp i) (<= (len xs) i))
  (equal (nthcdr i xs) nil))
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr len)))))
(local (defthm fn-stcp-octets-aux-true-list
 (true-listp (fn-record-string-octets-aux chars))))
(defthm fn-stcp-borrowed-source-byte-is-logical-total
 (implies (stringp text)
  (equal (fn-stcp-source-byte text offset)
         (fn-stcp-source-byte (nthcdr (nfix offset) (fn-record-string-octets text)) offset)))
 :hints (("Goal" :cases ((< (nfix offset) (length text)))
  :in-theory (e/d (fn-stcp-source-byte fn-record-string-octets fn-cbor-ag-car)
                  (nfix fn-record-string-octets-aux)))))
(defthm fn-stcp-borrowed-source-empty-is-logical-total
 (implies (stringp text)
  (equal (fn-stcp-source-empty text offset)
         (fn-stcp-source-empty (nthcdr (nfix offset) (fn-record-string-octets text)) offset)))
 :hints (("Goal" :in-theory (e/d (fn-stcp-source-empty fn-record-string-octets)
                                     (nfix fn-record-string-octets-aux)))))
(defthm fn-stcp-borrowed-source-advance-is-logical-total
 (implies (stringp text)
  (equal (nthcdr (+ 1 (nfix offset))
                (fn-record-string-octets (fn-stcp-source-next text)))
         (fn-stcp-source-next (nthcdr (nfix offset) (fn-record-string-octets text)))))
 :hints (("Goal" :in-theory (enable fn-stcp-source-next fn-cbor-ag-cdr))))
(defun-nx fn-stcp-source-abstract (source offset)
 (if (stringp source) (nthcdr (nfix offset) (fn-record-string-octets source)) source))
(defun-nx fn-stcp-dec-abstract (c)
 (list* (fn-stcp-at 0 c) (fn-stcp-at 1 c)
        (fn-stcp-source-abstract (fn-stcp-at 2 c) (fn-stcp-at 3 c))
        (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr c)))))
(local (defthm fn-stcp-at-of-dec-abstract
 (implies (and (natp n) (< n 14))
  (equal (fn-stcp-at n (fn-stcp-dec-abstract c))
   (if (equal n 2)
    (fn-stcp-source-abstract (fn-stcp-at 2 c) (fn-stcp-at 3 c))
    (fn-stcp-at n c))))
 :hints (("Goal" :cases ((equal n 0) (equal n 1) (equal n 2) (equal n 3) (equal n 4) (equal n 5) (equal n 6) (equal n 7) (equal n 8) (equal n 9) (equal n 10) (equal n 11) (equal n 12) (equal n 13))
   :in-theory (e/d (fn-stcp-at fn-stcp-dec-abstract fn-cbor-ag-car fn-cbor-ag-cdr) (fn-stcp-source-abstract))))))
(local (defthm fn-stcp-source-next-string
 (implies (stringp text) (equal (fn-stcp-source-next text) text))
 :hints (("Goal" :in-theory (enable fn-stcp-source-next)))))
(local (defthm fn-stcp-nfix-idempotent (equal (nfix (nfix x)) (nfix x))))
(local (defthm fn-stcp-nfix-successor
 (equal (nfix (+ 1 (nfix x))) (+ 1 (nfix x)))))
(local (defthm fn-stcp-source-next-list
 (implies (true-listp xs) (equal (fn-stcp-source-next xs) (cdr xs)))
 :hints (("Goal" :in-theory (enable fn-stcp-source-next fn-cbor-ag-cdr)))))
(local (defthm fn-stcp-source-empty-list
 (implies (true-listp xs) (equal (fn-stcp-source-empty xs offset) (null xs)))
 :hints (("Goal" :in-theory (enable fn-stcp-source-empty)))))
(defthm fn-stcp-dec-tick-borrowed-refinement
 (implies (and (fn-stcp-widthp c 14) (stringp (fn-stcp-at 2 c)))
  (equal (fn-stcp-dec-abstract (fn-stcp-dec-tick p c))
         (fn-stcp-dec-tick p (fn-stcp-dec-abstract c))))
 :hints (("Goal" :in-theory (e/d (fn-stcp-dec-abstract fn-stcp-dec-tick
                       fn-stcp-dec-c fn-stcp-dec-refuse fn-stcp-dec-value
                       fn-stcp-at fn-stcp-source-abstract fn-cbor-ag-car fn-cbor-ag-cdr)
                    (fn-stcp-source-byte fn-stcp-source-empty fn-stcp-source-next
                     fn-record-string-octets fn-record-string-octets-aux
                     fn-stcp-profilep fn-stcp-profile-check fn-stcp-canonicalp nfix floor mod fn-stcp-widthp fn-stx-op-of-code fn-cbor-octetp)))))

(defthm fn-stcp-dec-tick-borrowed-refinement-total
 (implies (stringp (fn-stcp-at 2 c))
  (equal (fn-stcp-dec-abstract (fn-stcp-dec-tick p c))
         (fn-stcp-dec-tick p (fn-stcp-dec-abstract c))))
 :hints (("Goal" :in-theory (e/d (fn-stcp-dec-abstract fn-stcp-dec-tick
                       fn-stcp-dec-c fn-stcp-dec-refuse fn-stcp-dec-value
                       fn-stcp-at fn-stcp-source-abstract fn-cbor-ag-car fn-cbor-ag-cdr)
                    (fn-stcp-source-byte fn-stcp-source-empty fn-stcp-source-next
                     fn-record-string-octets fn-record-string-octets-aux
                     fn-stcp-profilep fn-stcp-profile-check fn-stcp-canonicalp nfix floor mod fn-stcp-widthp fn-stx-op-of-code fn-cbor-octetp)))))
(defthm fn-stcp-dec-tick-keeps-borrowed-source
 (implies (stringp (fn-stcp-at 2 c))
  (stringp (fn-stcp-at 2 (fn-stcp-dec-tick p c))))
 :hints (("Goal" :in-theory (e/d (fn-stcp-dec-tick fn-stcp-dec-value
                  fn-stcp-dec-refuse fn-stcp-dec-c fn-stcp-at
                  fn-cbor-ag-car fn-cbor-ag-cdr)
               (fn-stcp-source-byte fn-stcp-source-empty fn-stcp-source-next
                fn-stcp-profilep fn-stcp-profile-check fn-stcp-canonicalp
                nfix floor mod fn-stx-op-of-code fn-cbor-octetp)))))
(defthm fn-stcp-dec-terminal-abstract
 (equal (fn-stcp-terminalp (fn-stcp-dec-abstract c)) (fn-stcp-terminalp c))
 :hints (("Goal" :in-theory (e/d (fn-stcp-terminalp fn-stcp-dec-abstract
                         fn-stcp-at fn-cbor-ag-car fn-cbor-ag-cdr)
                                 (fn-stcp-source-abstract)))))
(defthm fn-stcp-dec-drive-borrowed-refinement
 (implies (stringp (fn-stcp-at 2 c))
  (and (equal (fn-stcp-dec-abstract (mv-nth 0 (fn-stcp-dec-drive p c fuel)))
              (mv-nth 0 (fn-stcp-dec-drive p (fn-stcp-dec-abstract c) fuel)))
       (equal (mv-nth 1 (fn-stcp-dec-drive p c fuel))
              (mv-nth 1 (fn-stcp-dec-drive p (fn-stcp-dec-abstract c) fuel)))))
 :hints (("Goal" :induct (fn-stcp-dec-drive p c fuel)
  :in-theory (e/d (fn-stcp-dec-drive)
                 (fn-stcp-dec-tick fn-stcp-dec-abstract fn-stcp-at
                  fn-stcp-terminalp)))))
(defthm fn-stcp-dec-result-borrowed-refinement
 (equal (fn-stcp-dec-result (fn-stcp-dec-abstract c)) (fn-stcp-dec-result c))
 :hints (("Goal" :in-theory (e/d (fn-stcp-dec-result)
                    (fn-stcp-dec-abstract fn-stcp-at fn-stcp-source-abstract)))))
(defthm fn-stcp-decode-resume-borrowed-refinement
 (implies (stringp (fn-stcp-at 2 c))
  (and (equal (fn-stcp-dec-abstract (mv-nth 0 (fn-stcp-decode-resume p c)))
              (mv-nth 0 (fn-stcp-decode-resume p (fn-stcp-dec-abstract c))))
       (equal (mv-nth 1 (fn-stcp-decode-resume p c))
              (mv-nth 1 (fn-stcp-decode-resume p (fn-stcp-dec-abstract c))))
       (equal (fn-stcp-dec-result (mv-nth 0 (fn-stcp-decode-resume p c)))
              (fn-stcp-dec-result (mv-nth 0 (fn-stcp-decode-resume p (fn-stcp-dec-abstract c)))))))
 :hints (("Goal" :in-theory (e/d (fn-stcp-decode-resume)
                  (fn-stcp-dec-drive fn-stcp-dec-abstract fn-stcp-dec-result fn-stcp-at mv-nth fn-stcp-profilep nfix)))))
