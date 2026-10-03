; A line renderer retains the original string and an offset. No coerce/list
; conversion is executed while emitting a bounded quantum. The logical
; residual uses the existing NNTP octet projection and framing vocabulary.
(in-package "ACL2")
(include-book "nntp-session")
(include-book "def-cursor")

(defun fn-sl-make (text position phase)
  (declare (xargs :guard t))
  (list text position phase))

(local
 (defthm fn-sl-first-character
   (implies (and (stringp text) (< 0 (length text)))
            (characterp (char text 0)))
   :hints (("Goal" :use ((:instance character-listp-coerce (str text)))
            :in-theory (e/d (char length character-listp) (character-listp-coerce))))))

(defun fn-sl-start (text)
  (declare (xargs :guard t
                  :verify-guards nil))
  (fn-sl-make text 0
              (if (and (stringp text) (< 0 (length text)))
                  (if (eql (char-code (char text 0)) 46) :stuff :text)
                :cr)))

(verify-guards fn-sl-start
  :hints (("Goal" :use fn-sl-first-character
           :in-theory (disable char fn-sl-first-character))))

(defun fn-sl-one (cur)
  (declare (xargs :guard t))
  (let ((text (fn-cur-at 0 cur))
        (position (fn-cur-at 1 cur))
        (phase (fn-cur-at 2 cur)))
    (cond
     ((eq phase :stuff)
      (mv '(46) (fn-sl-make text position :text)))
     ((eq phase :text)
      (if (and (stringp text) (natp position) (< position (length text)))
          (mv (list (char-code (char text position)))
              (fn-sl-make text (1+ position)
                          (if (< (1+ position) (length text)) :text :cr)))
        (mv '(13) (fn-sl-make text position :lf))))
     ((eq phase :cr) (mv '(13) (fn-sl-make text position :lf)))
     ((eq phase :lf) (mv '(10) nil))
     (t (mv nil nil)))))

(defun fn-sl-loop (cur bytes acc)
  (declare (xargs :guard (and (natp bytes) (true-listp acc)) :measure (nfix bytes)))
  (if (or (not cur) (zp bytes))
      (mv (revappend acc nil) cur)
    (mv-let (one next) (fn-sl-one cur)
      (fn-sl-loop next (1- bytes)
                  (if (consp one) (cons (car one) acc) acc)))))

(defun fn-sl-step (cur bytes)
  (declare (xargs :guard (natp bytes)))
  (fn-sl-loop cur bytes nil))

(defun fn-sl-remaining (cur)
  (declare (xargs :guard t :verify-guards nil))
  (let ((text (fn-cur-at 0 cur))
        (position (fn-cur-at 1 cur))
        (phase (fn-cur-at 2 cur)))
    (cond
     ((eq phase :stuff)
      (cons 46 (append (if (stringp text)
                          (fn-nntp-string-octets-aux
                           (nthcdr (if (natp position) position (length text)) (coerce text 'list)))
                        nil)
                      '(13 10))))
     ((eq phase :text)
      (append (if (stringp text)
                  (fn-nntp-string-octets-aux
                   (nthcdr (if (natp position) position (length text)) (coerce text 'list)))
                nil)
              '(13 10)))
     ((eq phase :cr) '(13 10))
     ((eq phase :lf) '(10))
     (t nil))))

(local
 (defthm fn-sl-nthcdr-open
   (implies (and (natp k) (< k (len xs)))
            (equal (nthcdr k xs) (cons (nth k xs) (nthcdr (1+ k) xs))))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-sl-octets-at-offset
   (implies (and (stringp text) (natp k) (< k (length text)))
            (equal (fn-nntp-string-octets-aux (nthcdr k (coerce text 'list)))
                   (cons (char-code (char text k))
                         (fn-nntp-string-octets-aux
                          (nthcdr (1+ k) (coerce text 'list))))))
   :hints (("Goal" :in-theory (e/d (char fn-nntp-string-octets-aux) (nthcdr))
            :use ((:instance fn-sl-nthcdr-open (xs (coerce text 'list))))))))

(local
 (defthm fn-sl-nthcdr-past
   (implies (and (natp k) (<= (len xs) k))
            (not (consp (nthcdr k xs))))))

(defun fn-sl-okp (cur)
  (declare (xargs :guard t))
  (or (not cur)
      (and (natp (fn-cur-at 1 cur))
           (or (not (member-eq (fn-cur-at 2 cur) '(:stuff :text)))
               (and (stringp (fn-cur-at 0 cur))
                    (<= (fn-cur-at 1 cur) (length (fn-cur-at 0 cur))))))))

(defthm fn-sl-start-is-ok
  (fn-sl-okp (fn-sl-start text)))

(defthm fn-sl-one-keeps-okp
  (implies (fn-sl-okp cur) (fn-sl-okp (mv-nth 1 (fn-sl-one cur))))
  :hints (("Goal" :in-theory (enable fn-sl-one fn-sl-okp fn-sl-make))))

(local
 (defthm fn-sl-octets-of-atom
   (implies (not (consp chars))
            (equal (fn-nntp-string-octets-aux chars) nil))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(defthm fn-sl-one-residual
  (equal (append (car (fn-sl-one cur))
                          (fn-sl-remaining (mv-nth 1 (fn-sl-one cur))))
                  (fn-sl-remaining cur))
  :hints (("Goal" :in-theory (e/d (fn-sl-one fn-sl-remaining fn-sl-okp fn-sl-make)
                                   (fn-nntp-string-octets-aux nthcdr char fn-sl-nthcdr-open)))))

(defthm fn-sl-one-byte-bound
  (<= (len (car (fn-sl-one cur))) 1)
  :rule-classes :linear)

(local
 (defthm fn-sl-one-output-shape
   (equal (car (fn-sl-one cur))
          (if (consp (car (fn-sl-one cur)))
              (list (car (car (fn-sl-one cur)))) nil))
   :hints (("Goal" :in-theory (enable fn-sl-one)))))

(local (in-theory (disable fn-sl-one-output-shape)))

(local
 (defthm fn-sl-one-residual-byte
   (implies (consp (car (fn-sl-one cur)))
            (equal (cons (car (car (fn-sl-one cur)))
                         (fn-sl-remaining (mv-nth 1 (fn-sl-one cur))))
                   (fn-sl-remaining cur)))
   :hints (("Goal" :in-theory (disable fn-sl-one fn-sl-remaining fn-sl-okp
                                       fn-sl-one-residual fn-sl-one-output-shape)
            :use (fn-sl-one-residual fn-sl-one-output-shape)))))

(local
 (defthm fn-sl-one-residual-empty
   (implies (not (consp (car (fn-sl-one cur))))
            (equal (fn-sl-remaining (mv-nth 1 (fn-sl-one cur)))
                   (fn-sl-remaining cur)))
   :hints (("Goal" :in-theory (disable fn-sl-one fn-sl-remaining fn-sl-okp
                                       fn-sl-one-residual fn-sl-one-output-shape)
            :use (fn-sl-one-residual fn-sl-one-output-shape)))))

(local
 (defthm fn-sl-append-assoc
   (equal (append (append x y) z) (append x (append y z)))))

; Normalize the reversed output accumulator before using the one-byte
; residual. Keep this fact in this book: a warm caller's append theory must
; not supply a rule that the renderer's clean certification world lacks.
(local
 (defthm fn-sl-append-revappend
   (equal (append (revappend acc suffix) rest)
          (revappend acc (append suffix rest)))
   :hints (("Goal" :induct (revappend acc suffix)
            :in-theory (enable revappend)))))

(local
 (defthm fn-sl-len-revappend
   (equal (len (revappend acc suffix)) (+ (len acc) (len suffix)))
   :hints (("Goal" :induct (revappend acc suffix)
            :in-theory (enable revappend)))))

(local
 (defthm fn-sl-revappend-output-list
   (implies (true-listp suffix) (true-listp (revappend acc suffix)))
   :hints (("Goal" :induct (revappend acc suffix)
            :in-theory (enable revappend)))))

(defthm fn-sl-loop-residual
  (equal (append (mv-nth 0 (fn-sl-loop cur bytes acc))
                          (fn-sl-remaining (mv-nth 1 (fn-sl-loop cur bytes acc))))
                  (append (revappend acc nil) (fn-sl-remaining cur)))
  :hints (("Goal" :induct (fn-sl-loop cur bytes acc)
           :in-theory (e/d (fn-sl-loop) (fn-sl-one fn-sl-remaining fn-sl-okp)))))

(defthm fn-sl-step-residual
  (equal (append (car (fn-sl-step cur bytes))
                          (fn-sl-remaining (mv-nth 1 (fn-sl-step cur bytes))))
                  (fn-sl-remaining cur))
  :hints (("Goal" :in-theory (e/d (fn-sl-step)
                                   (fn-sl-loop fn-sl-remaining fn-sl-okp fn-sl-loop-residual))
           :use ((:instance fn-sl-loop-residual (acc nil))))))

(defthm fn-sl-loop-byte-bound
  (<= (len (car (fn-sl-loop cur bytes acc))) (+ (nfix bytes) (len acc)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-sl-loop cur bytes acc)
           :in-theory (e/d (fn-sl-loop) (fn-sl-one)))))

(defthm fn-sl-step-byte-bound
  (<= (len (car (fn-sl-step cur bytes))) (nfix bytes))
  :rule-classes :linear)

(defthm fn-sl-loop-output-list
  (true-listp (car (fn-sl-loop cur bytes acc)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-sl-loop cur bytes acc)
           :in-theory (e/d (fn-sl-loop) (fn-sl-one)))))

(defthm fn-sl-step-output-list
  (true-listp (car (fn-sl-step cur bytes)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (fn-sl-step) (fn-sl-loop)))))

(defthm fn-sl-step-residual-onto
  (equal (append (car (fn-sl-step cur bytes))
                          (append (fn-sl-remaining (mv-nth 1 (fn-sl-step cur bytes))) suffix))
                  (append (fn-sl-remaining cur) suffix))
  :hints (("Goal" :in-theory (disable fn-sl-step fn-sl-remaining fn-sl-okp fn-sl-step-residual)
           :use fn-sl-step-residual)))

(defthm fn-sl-step-terminal-residual
  (implies (not (mv-nth 1 (fn-sl-step cur bytes)))
           (equal (append (car (fn-sl-step cur bytes)) suffix)
                  (append (fn-sl-remaining cur) suffix)))
  :hints (("Goal" :in-theory (disable fn-sl-step fn-sl-remaining fn-sl-okp
                                     fn-sl-step-residual-onto)
           :use fn-sl-step-residual-onto)))

(defthm fn-sl-loop-keeps-okp
  (implies (fn-sl-okp cur)
           (fn-sl-okp (mv-nth 1 (fn-sl-loop cur bytes acc))))
  :hints (("Goal" :induct (fn-sl-loop cur bytes acc)
           :in-theory (e/d (fn-sl-loop) (fn-sl-one fn-sl-okp)))))

(defthm fn-sl-step-keeps-okp
  (implies (fn-sl-okp cur)
           (fn-sl-okp (mv-nth 1 (fn-sl-step cur bytes))))
  :hints (("Goal" :in-theory (e/d (fn-sl-step) (fn-sl-loop fn-sl-okp)))))

(local
 (defthm fn-sl-positive-length-of-cons
   (implies (consp xs) (< 0 (len xs)))
   :rule-classes :linear))

(local
 (defthm fn-sl-octets-consp
   (equal (consp (fn-nntp-string-octets-aux chars)) (consp chars))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-sl-octets-head
   (implies (consp chars)
            (equal (car (fn-nntp-string-octets-aux chars))
                   (char-code (car chars))))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(defthm fn-sl-start-is-stuffed-line
  (equal (fn-sl-remaining (fn-sl-start text))
         (fn-nntp-stuff-lines (list (fn-nntp-string-octets text))))
  :hints (("Goal" :cases ((consp (coerce text 'list)))
           :in-theory (e/d (fn-sl-start fn-sl-remaining fn-sl-make
                            fn-nntp-string-octets fn-nntp-stuff-lines
                            fn-nntp-crlf fn-wire-stuff-line char)
                           (fn-nntp-string-octets-aux fn-sl-nthcdr-open)))))

(in-theory (disable fn-sl-one fn-sl-loop fn-sl-step fn-sl-remaining fn-sl-okp fn-sl-start))
