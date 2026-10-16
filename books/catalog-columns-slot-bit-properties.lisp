; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-pointer-slot-frames")
(local (include-book "ihs/logops-lemmas" :dir :system))

(local (defthm fn-lbbit-logcar-of-logior
  (implies (and (integerp x) (integerp y))
   (equal (logcar (logior x y)) (b-ior (logcar x) (logcar y))))
  :hints (("Goal" :do-not-induct t
   :use ((:instance logior* (i x) (j y)))
   :in-theory (union-theories (theory 'minimal-theory)
    '(logcar-logcons logcar-type b-ior$inline bitp (:type-prescription binary-logior)
      (:type-prescription b-ior$inline) (:executable-counterpart equal)))))))

(local (defthm fn-lbbit-logcdr-of-logior
  (implies (and (integerp x) (integerp y))
   (equal (logcdr (logior x y)) (logior (logcdr x) (logcdr y))))
  :hints (("Goal" :do-not-induct t
   :use ((:instance logior* (i x) (j y)))
   :in-theory (union-theories (theory 'minimal-theory)
    '(logcdr-logcons logcar-type logcdr-type b-ior$inline bitp ifix (:type-prescription binary-logior) (:type-prescription b-ior$inline)))))))

(local (defthm fn-lbbit-logbitp-recursion
  (implies (and (syntaxp (quotep pos)) (integerp pos) (<= 0 pos) (integerp value))
   (equal (logbitp pos value)
    (if (equal pos 0) (equal (logcar value) 1)
     (logbitp (- pos 1) (logcdr value)))))
  :hints (("Goal" :do-not-induct t
   :use ((:instance logbitp* (i value)))
   :in-theory (theory 'minimal-theory)))))

(local (defthm fn-lbbit-u64-integer
 (implies (unsigned-byte-p 64 flags) (integerp flags))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(unsigned-byte-p integer-range-p))))))

(local (defthm fn-lbbit-nfix-u64
 (implies (unsigned-byte-p 64 x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(nfix unsigned-byte-p integer-range-p))))))

(local (defthm fn-lbbit-logior-u64
 (implies (unsigned-byte-p 64 flags) (unsigned-byte-p 64 (logior flags 8)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(unsigned-byte-p-logior (:executable-counterpart unsigned-byte-p) (:executable-counterpart integerp)))))))

(local (defthm fn-lbbit-logior-eight-preserves-bit-0
 (implies (integerp flags) (equal (logbitp 0 (logior flags 8)) (logbitp 0 flags)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbbit-logbitp-recursion fn-lbbit-logcar-of-logior fn-lbbit-logcdr-of-logior logcar-type logcdr-type b-ior$inline ifix zbp bfix (:type-prescription binary-logior) (:executable-counterpart logcar$inline) (:executable-counterpart logcdr$inline)))
   '((:definition binary-logior) (:definition logbitp) (tau-system)))))))

(defthm fn-lbc-flag-word-or-eight-preserves-bit-0
 (implies (unsigned-byte-p 64 flags)
  (equal (logbitp 0 (nfix (logior flags 8))) (logbitp 0 (nfix flags))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lbbit-nfix-u64 fn-lbbit-logior-u64 fn-lbbit-logior-eight-preserves-bit-0 fn-lbbit-u64-integer)))))

(local (defthm fn-lbbit-logior-eight-preserves-bit-1
 (implies (integerp flags) (equal (logbitp 1 (logior flags 8)) (logbitp 1 flags)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbbit-logbitp-recursion fn-lbbit-logcar-of-logior fn-lbbit-logcdr-of-logior logcar-type logcdr-type b-ior$inline ifix zbp bfix (:type-prescription binary-logior) (:executable-counterpart logcar$inline) (:executable-counterpart logcdr$inline)))
   '((:definition binary-logior) (:definition logbitp) (tau-system)))))))

(defthm fn-lbc-flag-word-or-eight-preserves-bit-1
 (implies (unsigned-byte-p 64 flags)
  (equal (logbitp 1 (nfix (logior flags 8))) (logbitp 1 (nfix flags))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lbbit-nfix-u64 fn-lbbit-logior-u64 fn-lbbit-logior-eight-preserves-bit-1 fn-lbbit-u64-integer)))))

(local (defthm fn-lbbit-logior-eight-preserves-bit-2
 (implies (integerp flags) (equal (logbitp 2 (logior flags 8)) (logbitp 2 flags)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbbit-logbitp-recursion fn-lbbit-logcar-of-logior fn-lbbit-logcdr-of-logior logcar-type logcdr-type b-ior$inline ifix zbp bfix (:type-prescription binary-logior) (:executable-counterpart logcar$inline) (:executable-counterpart logcdr$inline)))
   '((:definition binary-logior) (:definition logbitp) (tau-system)))))))

(defthm fn-lbc-flag-word-or-eight-preserves-bit-2
 (implies (unsigned-byte-p 64 flags)
  (equal (logbitp 2 (nfix (logior flags 8))) (logbitp 2 (nfix flags))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lbbit-nfix-u64 fn-lbbit-logior-u64 fn-lbbit-logior-eight-preserves-bit-2 fn-lbbit-u64-integer)))))

(local (defthm fn-lbbit-logior-eight-preserves-bit-4
 (implies (integerp flags) (equal (logbitp 4 (logior flags 8)) (logbitp 4 flags)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbbit-logbitp-recursion fn-lbbit-logcar-of-logior fn-lbbit-logcdr-of-logior logcar-type logcdr-type b-ior$inline ifix zbp bfix (:type-prescription binary-logior) (:executable-counterpart logcar$inline) (:executable-counterpart logcdr$inline)))
   '((:definition binary-logior) (:definition logbitp) (tau-system)))))))

(defthm fn-lbc-flag-word-or-eight-preserves-bit-4
 (implies (unsigned-byte-p 64 flags)
  (equal (logbitp 4 (nfix (logior flags 8))) (logbitp 4 (nfix flags))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lbbit-nfix-u64 fn-lbbit-logior-u64 fn-lbbit-logior-eight-preserves-bit-4 fn-lbbit-u64-integer)))))

(local (defthm fn-lbbit-logior-eight-preserves-bit-5
 (implies (integerp flags) (equal (logbitp 5 (logior flags 8)) (logbitp 5 flags)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbbit-logbitp-recursion fn-lbbit-logcar-of-logior fn-lbbit-logcdr-of-logior logcar-type logcdr-type b-ior$inline ifix zbp bfix (:type-prescription binary-logior) (:executable-counterpart logcar$inline) (:executable-counterpart logcdr$inline)))
   '((:definition binary-logior) (:definition logbitp) (tau-system)))))))

(defthm fn-lbc-flag-word-or-eight-preserves-bit-5
 (implies (unsigned-byte-p 64 flags)
  (equal (logbitp 5 (nfix (logior flags 8))) (logbitp 5 (nfix flags))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lbbit-nfix-u64 fn-lbbit-logior-u64 fn-lbbit-logior-eight-preserves-bit-5 fn-lbbit-u64-integer)))))
