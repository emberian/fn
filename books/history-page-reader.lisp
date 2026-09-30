; PRF-1107: incremental selected-entry extraction from current directory/table
; words. First library component of the authenticated source reader.
(in-package "ACL2")
(include-book "pagestore-exec")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-hsr-field (i c)
  (declare (xargs :guard (natp i)))
  (if (consp c) (if (zp i) (car c) (fn-hsr-field (1- i) (cdr c))) nil))
(defun fn-hsr-widthp (c k)
  (declare (xargs :guard (natp k)))
  (if (zp k) (null c) (and (consp c) (fn-hsr-widthp (cdr c) (1- k)))))
(defun fn-hsr-prefixp (p k)
  (declare (xargs :guard (natp k)))
  (if (null p) t
    (and (not (zp k)) (consp p) (unsigned-byte-p 64 (car p))
         (fn-hsr-prefixp (cdr p) (1- k)))))

; Fixed nine-cell scan: index,total words,entry count,selected entry,root txid,
; selected <=6 words,malformed flag,capture,buffer/root lease identity.
(defun fn-hsr-scan-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hsr-widthp c 9)
       (unsigned-byte-p 64 (fn-hsr-field 0 c))
       (unsigned-byte-p 64 (fn-hsr-field 1 c))
       (unsigned-byte-p 64 (fn-hsr-field 2 c))
       (unsigned-byte-p 64 (fn-hsr-field 3 c))
       (unsigned-byte-p 64 (fn-hsr-field 4 c))
       (<= (fn-hsr-field 0 c) (fn-hsr-field 1 c))
       (<= (* 6 (fn-hsr-field 2 c)) (fn-hsr-field 1 c))
       (< (fn-hsr-field 3 c) (fn-hsr-field 2 c))
       (fn-hsr-prefixp (fn-hsr-field 5 c) 6)
       (booleanp (fn-hsr-field 6 c))))

(defun fn-hsr-scan-begin (total count selected txid capture lease)
  (declare (xargs :guard t))
  (list 0 total count selected txid nil nil capture lease))

(defun fn-hsr-selected-indexp (i selected)
  (declare (xargs :guard (and (natp i) (natp selected))))
  (and (<= (* 6 selected) i) (< i (+ 6 (* 6 selected)))))

(defun fn-hsr-word-okp (i count txid word)
  (declare (xargs :guard (and (natp i) (natp count) (natp txid) (natp word))))
  (if (< i (* 6 count))
      (or (not (equal (mod i 6) 1)) (<= word txid))
    (equal word 0)))

(local
 (defthm fn-hsr-prefixp-true-listp
   (implies (fn-hsr-prefixp p k) (true-listp p))))

(defun fn-hsr-scan-word (word c)
  (declare (xargs :guard t))
  (let ((i (fn-hsr-field 0 c)) (total (fn-hsr-field 1 c))
        (count (fn-hsr-field 2 c)) (selected (fn-hsr-field 3 c))
        (txid (fn-hsr-field 4 c)) (prefix (fn-hsr-field 5 c))
        (bad (fn-hsr-field 6 c))
        (capture (fn-hsr-field 7 c)) (lease (fn-hsr-field 8 c)))
    (cond ((not (and (fn-hsr-scan-shapep c) (unsigned-byte-p 64 word)))
           (mv '(:refused :scan-word) c))
          ((<= total i) (mv '(:refused :scan-complete) c))
          ((and (fn-hsr-selected-indexp i selected) (<= 6 (len prefix)))
           (mv '(:refused :scan-prefix) c))
          (t (mv :continue
                 (list (+ 1 i) total count selected txid
                       (if (fn-hsr-selected-indexp i selected)
                           (append prefix (list word)) prefix)
                       (or bad (not (fn-hsr-word-okp i count txid word)))
                       capture lease))))))

; Proof vocabulary, never evaluated by scan-word or its guard.
(defun fn-hsr-scan-invariantp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hsr-scan-shapep c)
       (equal (len (fn-hsr-field 5 c))
              (min 6 (nfix (- (fn-hsr-field 0 c) (* 6 (fn-hsr-field 3 c))))))))

(defun fn-hsr-selected-rest (i selected words)
  (declare (xargs :guard (and (natp i) (natp selected)) :measure (len words)))
  (if (consp words)
      (if (fn-hsr-selected-indexp i selected)
          (cons (car words) (fn-hsr-selected-rest (+ 1 i) selected (cdr words)))
        (fn-hsr-selected-rest (+ 1 i) selected (cdr words)))
    nil))

(local
 (defthm fn-hsr-prefixp-append-one
   (implies (and (natp k) (fn-hsr-prefixp p k) (< (len p) k) (unsigned-byte-p 64 w))
            (fn-hsr-prefixp (append p (list w)) k))
   :hints (("Goal" :induct (fn-hsr-prefixp p k)))))

(local
 (defthm fn-hsr-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))
(local
 (defthm fn-hsr-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-hsr-scan-begin-establishes-invariant
  (implies (and (unsigned-byte-p 64 total) (unsigned-byte-p 64 count)
                (unsigned-byte-p 64 selected) (unsigned-byte-p 64 txid)
                (<= (* 6 count) total) (< selected count))
           (fn-hsr-scan-invariantp
            (fn-hsr-scan-begin total count selected txid capture lease)))
  :hints (("Goal" :in-theory (enable fn-hsr-scan-invariantp fn-hsr-scan-begin
                                    fn-hsr-scan-shapep))))

(defthm fn-hsr-scan-word-preserves-identities
  (let ((next (mv-nth 1 (fn-hsr-scan-word word c))))
    (and (equal (fn-hsr-field 7 next) (fn-hsr-field 7 c))
         (equal (fn-hsr-field 8 next) (fn-hsr-field 8 c))))
  :hints (("Goal" :in-theory (e/d (fn-hsr-scan-word) (fn-hsr-scan-shapep)))))

(defthm fn-hsr-scan-word-progress-and-invariant
  (implies (and (fn-hsr-scan-invariantp c)
                (< (fn-hsr-field 0 c) (fn-hsr-field 1 c))
                (unsigned-byte-p 64 word))
           (let ((next (mv-nth 1 (fn-hsr-scan-word word c))))
             (and (equal (mv-nth 0 (fn-hsr-scan-word word c)) :continue)
                  (fn-hsr-scan-invariantp next)
                  (equal (fn-hsr-field 0 next) (+ 1 (fn-hsr-field 0 c)))
                  (equal (fn-hsr-field 1 next) (fn-hsr-field 1 c))
                  (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
                  (equal (fn-hsr-field 3 next) (fn-hsr-field 3 c))
                  (equal (fn-hsr-field 4 next) (fn-hsr-field 4 c)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hsr-scan-invariantp fn-hsr-scan-word
                              fn-hsr-scan-shapep fn-hsr-selected-indexp)
                             (fn-hsr-prefixp fn-hsr-word-okp)))))

(local
 (defthm fn-hsr-selected-rest-cons
   (equal (fn-hsr-selected-rest i selected (cons word rest))
          (if (fn-hsr-selected-indexp i selected)
              (cons word (fn-hsr-selected-rest (+ 1 i) selected rest))
            (fn-hsr-selected-rest (+ 1 i) selected rest)))
   :hints (("Goal" :expand (fn-hsr-selected-rest i selected (cons word rest))))))

(local
 (defthm fn-hsr-selected-rest-past-end
   (implies (and (natp i) (natp selected) (<= (+ 6 (* 6 selected)) i))
            (equal (fn-hsr-selected-rest i selected words) nil))
   :hints (("Goal" :induct (fn-hsr-selected-rest i selected words)
            :in-theory (enable fn-hsr-selected-rest fn-hsr-selected-indexp)))))

(defthm fn-hsr-scan-word-preserves-exact-selection
  (implies (and (fn-hsr-scan-invariantp c)
                (unsigned-byte-p 64 word))
           (let ((next (mv-nth 1 (fn-hsr-scan-word word c))))
             (equal (append (fn-hsr-field 5 c)
                            (fn-hsr-selected-rest (fn-hsr-field 0 c)
                                                  (fn-hsr-field 3 c) (cons word rest)))
                    (append (fn-hsr-field 5 next)
                            (fn-hsr-selected-rest (fn-hsr-field 0 next)
                                                  (fn-hsr-field 3 next) rest)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hsr-scan-invariantp fn-hsr-scan-word
                              fn-hsr-scan-shapep fn-hsr-selected-indexp)
                             (fn-hsr-prefixp fn-hsr-word-okp fn-hsr-selected-rest))
           :expand ((fn-hsr-selected-rest (fn-hsr-field 0 c)
                                           (fn-hsr-field 3 c) (cons word rest))))))

(local
 (defthm fn-hsr-selection-is-slice
   (implies (and (natp i) (natp selected)
                 (<= (nfix (- (+ 6 (* 6 selected)) i)) (len words)))
            (equal (fn-hsr-selected-rest i selected words)
                   (take (nfix (- (+ 6 (* 6 selected)) (max i (* 6 selected))))
                         (nthcdr (nfix (- (* 6 selected) i)) words))))
   :hints (("Goal" :induct (fn-hsr-selected-rest i selected words)
            :in-theory (enable fn-hsr-selected-rest fn-hsr-selected-indexp take nthcdr)))))

(local
 (defthm fn-hsr-nthcdr-add
   (implies (and (natp a) (natp b))
            (equal (nthcdr a (nthcdr b words)) (nthcdr (+ a b) words)))
   :hints (("Goal" :induct (nthcdr b words)))))
(local
 (defun fn-hsr-entry-ind (j n words)
   (declare (xargs :guard (and (natp j) (natp n)) :verify-guards nil :measure (nfix j)))
   (if (zp j) (list n words)
     (fn-hsr-entry-ind (1- j) (nfix (1- n)) (nthcdr 6 words)))))
(local
 (defthm fn-hsr-nth-decoded-entry
   (implies (and (natp j) (natp n) (< j n))
            (equal (nth j (pgs-decode-table words n))
                   (pgs-decode-entry (nthcdr (* 6 j) words))))
   :hints (("Goal" :induct (fn-hsr-entry-ind j n words)
            :expand ((pgs-decode-table words n) (nthcdr 0 words))
            :in-theory (e/d (pgs-decode-table nth) (pgs-decode-entry nthcdr))))))
(local
 (defun fn-hsr-nth-take-ind (i k words)
   (declare (xargs :measure (nfix i) :verify-guards nil))
   (if (zp i) (list k words)
     (fn-hsr-nth-take-ind (1- i) (nfix (1- k)) (cdr words)))))
(local
 (defthm fn-hsr-nth-take
   (implies (and (natp i) (natp k) (< i k))
            (equal (nth i (take k words)) (nth i words)))
   :hints (("Goal" :induct (fn-hsr-nth-take-ind i k words)
            :expand ((take k words))
            :in-theory (enable take nth)))))

(local
 (defthm fn-hsr-decode-take-six
   (equal (pgs-decode-entry (take 6 words)) (pgs-decode-entry words))
   :hints (("Goal" :in-theory (enable pgs-decode-entry take nth)))))

(local
 (defthm fn-hsr-len-take
   (equal (len (take k words)) (nfix k))
   :hints (("Goal" :induct (take k words) :in-theory (enable take)))))

(defthm fn-hsr-selection-refines-current-table-codec
  (implies (and (natp selected) (natp count) (< selected count)
                (<= (+ 6 (* 6 selected)) (len words)))
           (and (equal (len (fn-hsr-selected-rest 0 selected words)) 6)
                (equal (pgs-decode-entry (fn-hsr-selected-rest 0 selected words))
                       (nth selected (pgs-decode-table words count)))))
  :hints (("Goal" :in-theory (disable pgs-decode-entry pgs-decode-table
                                      fn-hsr-selected-rest))))

(defun fn-hsr-words-okp (i count txid words)
  (declare (xargs :guard t :verify-guards nil :measure (len words)))
  (if (consp words)
      (and (fn-hsr-word-okp i count txid (car words))
           (fn-hsr-words-okp (+ 1 i) count txid (cdr words)))
    t))

(defthm fn-hsr-scan-word-preserves-complete-shape-verdict
  (implies (and (fn-hsr-scan-invariantp c)
                (< (fn-hsr-field 0 c) (fn-hsr-field 1 c))
                (unsigned-byte-p 64 word))
           (let ((next (mv-nth 1 (fn-hsr-scan-word word c))))
             (equal (or (fn-hsr-field 6 c)
                        (not (fn-hsr-words-okp (fn-hsr-field 0 c)
                                               (fn-hsr-field 2 c)
                                               (fn-hsr-field 4 c) (cons word rest))))
                    (or (fn-hsr-field 6 next)
                        (not (fn-hsr-words-okp (fn-hsr-field 0 next)
                                               (fn-hsr-field 2 next)
                                               (fn-hsr-field 4 next) rest))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hsr-scan-invariantp fn-hsr-scan-word
                              fn-hsr-scan-shapep fn-hsr-selected-indexp)
                             (fn-hsr-prefixp fn-hsr-word-okp)))))

(defun fn-hsr-scan-entry (c)
  (declare (xargs :guard t))
  (if (and (fn-hsr-scan-shapep c)
           (equal (fn-hsr-field 0 c) (fn-hsr-field 1 c))
           (equal (len (fn-hsr-field 5 c)) 6))
      (pgs-decode-entry (fn-hsr-field 5 c))
    nil))

(defthm fn-hsr-complete-scan-has-full-entry
  (implies (and (fn-hsr-scan-invariantp c)
                (equal (fn-hsr-field 0 c) (fn-hsr-field 1 c)))
           (and (equal (len (fn-hsr-field 5 c)) 6)
                (equal (fn-hsr-scan-entry c) (pgs-decode-entry (fn-hsr-field 5 c)))))
  :hints (("Goal" :in-theory (e/d (fn-hsr-scan-invariantp fn-hsr-scan-shapep
                                    fn-hsr-scan-entry)
                                   (fn-hsr-prefixp pgs-decode-entry)))))

(in-theory (disable fn-hsr-scan-shapep fn-hsr-scan-begin fn-hsr-scan-word
                    fn-hsr-scan-invariantp fn-hsr-selected-rest fn-hsr-words-okp
                    fn-hsr-scan-entry))
