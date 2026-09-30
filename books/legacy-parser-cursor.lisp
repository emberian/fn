; Bounded legacy hydration. The source is an immutable arena handle; the
; output is five source spans, not copied or flattened field values.
(in-package "ACL2")
(include-book "nov-fields")
(include-book "payload-arena")
(include-book "reclaim-tombstone")

; Total constant-index record access. Every call below has a literal index
; at most ten; none follows the source, a field, or a growing accumulator.
(defun fn-lpc-at (i x)
  (declare (xargs :guard (natp i)))
  (if (zp i) (fn-ag-car x) (fn-lpc-at (1- i) (fn-ag-cdr x))))

(defun fn-lpc-put (i v x)
  (declare (xargs :guard (natp i)))
  (if (zp i) (cons v (fn-ag-cdr x))
    (cons (fn-ag-car x) (fn-lpc-put (1- i) v (fn-ag-cdr x)))))

; A span is (handle start length origin-pin). The caller retains the pin
; until all spans and their physical reads have settled.
(defun fn-lpc-span (h start end pin)
  (declare (xargs :guard (and (natp start) (natp end))))
  (list h start (nfix (- end start)) pin))

(defconst *fn-lpc-names*
  (list *fn-nov-subject-name* *fn-nov-from-name* *fn-nov-date-name*
        *fn-nov-message-id-name* *fn-nov-references-name*))

; :miss differs from nil, which is a completely matched name. CANDIDATES
; always has five entries, each a suffix of a fixed constant, or :miss.
(defun fn-lpc-name-byte (candidate byte)
  (declare (xargs :guard t))
  (if (and (consp candidate)
           (equal (car candidate) (fn-article-ascii-downcase-byte byte)))
      (cdr candidate) :miss))

(defun fn-lpc-name-step (candidates byte)
  (declare (xargs :guard t))
  (list (fn-lpc-name-byte (fn-lpc-at 0 candidates) byte)
        (fn-lpc-name-byte (fn-lpc-at 1 candidates) byte)
        (fn-lpc-name-byte (fn-lpc-at 2 candidates) byte)
        (fn-lpc-name-byte (fn-lpc-at 3 candidates) byte)
        (fn-lpc-name-byte (fn-lpc-at 4 candidates) byte)))

(defun fn-lpc-name-key (candidates)
  (declare (xargs :guard t))
  (cond ((equal (fn-lpc-at 0 candidates) nil) 0)
        ((equal (fn-lpc-at 1 candidates) nil) 1)
        ((equal (fn-lpc-at 2 candidates) nil) 2)
        ((equal (fn-lpc-at 3 candidates) nil) 3)
        ((equal (fn-lpc-at 4 candidates) nil) 4)
        (t nil)))

; Header record: phase, physical-line-length, current?, visible?, value
; start, last-line-end, selected-key, name candidates, five completed
; fields, first-unfolded-byte-seen?. All data-dependent information is
; scalar or an immutable reference; its shape is fixed.
(defun fn-lpc-header-begin ()
  (declare (xargs :guard t))
  (list :start 0 nil nil 0 0 nil *fn-lpc-names* '(nil nil nil nil nil) nil))

(defun fn-lpc-header-bad (s)
  (declare (xargs :guard t))
  (fn-lpc-put 0 :bad s))

(defun fn-lpc-close-fields (s h pin)
  (declare (xargs :guard t))
  (let ((key (fn-lpc-at 6 s)) (fields (fn-lpc-at 8 s)))
    (if (and (natp key) (< key 5) (not (fn-lpc-at key fields)))
        (fn-lpc-put key
                    (fn-lpc-span h (nfix (fn-lpc-at 4 s))
                                 (nfix (fn-lpc-at 5 s)) pin)
                    fields)
      fields)))

; Consume one value octet. The first unfolded SP is removed ONCE, even
; when the first physical line had an empty value and this byte is folded.
(defun fn-lpc-value-byte (s byte pos)
  (declare (xargs :guard (natp pos)))
  (if (not (fn-article-header-bytep byte))
      (fn-lpc-header-bad s)
    (list :value (+ 1 (nfix (fn-lpc-at 1 s))) (fn-lpc-at 2 s)
          (or (fn-lpc-at 3 s) (fn-article-vcharp byte))
          (if (fn-lpc-at 9 s) (fn-lpc-at 4 s)
            (if (equal byte 32) (+ 1 pos) pos))
          (fn-lpc-at 5 s) (fn-lpc-at 6 s) (fn-lpc-at 7 s)
          (fn-lpc-at 8 s) t)))

(defun fn-lpc-header-byte (s byte pos h pin)
  (declare (xargs :guard (natp pos)))
  (let ((phase (fn-lpc-at 0 s)))
    (cond
     ((eq phase :bad) s)
     ((eq phase :body)
      (cond ((equal byte 13) (fn-lpc-put 0 :body-cr s))
            ((equal byte 10) (fn-lpc-header-bad s)) (t s)))
     ((eq phase :body-cr)
      (if (equal byte 10) (fn-lpc-put 0 :body s) (fn-lpc-header-bad s)))
     ((eq phase :cr-start)
      (if (and (equal byte 10)
               (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)))
          (fn-lpc-put 8 (fn-lpc-close-fields s h pin)
                       (fn-lpc-put 0 :body s))
        (fn-lpc-header-bad s)))
     ((eq phase :cr-line)
      (if (equal byte 10)
          (fn-lpc-put 1 0 (fn-lpc-put 0 :start s))
        (fn-lpc-header-bad s)))
     ((equal byte 13)
      (cond ((eq phase :start) (fn-lpc-put 0 :cr-start s))
            ((or (eq phase :first) (eq phase :value))
             (fn-lpc-put 5 pos (fn-lpc-put 0 :cr-line s)))
            (t (fn-lpc-header-bad s))))
     ((or (equal byte 10)
          (<= *fn-article-max-line-octets* (nfix (fn-lpc-at 1 s))))
      (fn-lpc-header-bad s))
     ((eq phase :start)
      (if (fn-article-wspp byte)
          (if (fn-lpc-at 2 s) (fn-lpc-value-byte s byte pos)
            (fn-lpc-header-bad s))
        (if (and (fn-article-ftextp byte)
                 (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)))
            (list :name 1 t nil 0 0 nil
                  (fn-lpc-name-step *fn-lpc-names* byte)
                  (fn-lpc-close-fields s h pin) nil)
          (fn-lpc-header-bad s))))
     ((eq phase :name)
      (cond ((equal byte 58)
             (fn-lpc-put 6 (fn-lpc-name-key (fn-lpc-at 7 s))
              (fn-lpc-put 1 (+ 1 (nfix (fn-lpc-at 1 s)))
               (fn-lpc-put 0 :first s))))
            ((fn-article-ftextp byte)
             (fn-lpc-put 7 (fn-lpc-name-step (fn-lpc-at 7 s) byte)
              (fn-lpc-put 1 (+ 1 (nfix (fn-lpc-at 1 s))) s)))
            (t (fn-lpc-header-bad s))))
     ((eq phase :first)
      (if (fn-article-wspp byte) (fn-lpc-value-byte s byte pos)
        (fn-lpc-header-bad s)))
     ((eq phase :value) (fn-lpc-value-byte s byte pos))
     (t (fn-lpc-header-bad s)))))

; Separate facts scan: fn-hf-body-lines-of finds the FIRST CRLFCRLF even
; when the article parser has rejected its headers. The body count rejects
; NUL and unterminated final lines, which article-body-crlfp permits.
(defun fn-lpc-split-byte (matched byte)
  (declare (xargs :guard t))
  (cond ((equal matched 4) 4)
        ((equal matched 3) (cond ((equal byte 10) 4) ((equal byte 13) 1) (t 0)))
        ((equal matched 2) (if (equal byte 13) 3 0))
        ((equal matched 1) (cond ((equal byte 10) 2) ((equal byte 13) 1) (t 0)))
        (t (if (equal byte 13) 1 0))))

(defun fn-lpc-body-byte (s byte)
  (declare (xargs :guard t))
  (let ((phase (fn-lpc-at 0 s)) (count (nfix (fn-lpc-at 1 s))))
    (cond ((eq phase :bad) s)
          ((eq phase :cr) (if (equal byte 10) (list :line (+ 1 count))
                           (list :bad count)))
          ((equal byte 13) (list :cr count))
          ((or (equal byte 0) (equal byte 10)) (list :bad count))
          (t (list :inline count)))))

; Cursor: handle, length, origin-pin, offset, header machine, separator
; matcher, body-line machine, tombstone magic prefix still matches?.
(defun fn-lpc-begin (h n pin)
  (declare (xargs :guard (and (natp h) (natp n))))
  (list h n pin 0
        (if (<= n *fn-article-max-octets*) (fn-lpc-header-begin)
          (fn-lpc-header-bad (fn-lpc-header-begin)))
        0 '(:line 0) t))

(defun fn-lpc-byte (s byte)
  (declare (xargs :guard t))
  (let* ((pos (nfix (fn-lpc-at 3 s)))
         (matched (fn-lpc-at 5 s)))
    (list (fn-lpc-at 0 s) (fn-lpc-at 1 s) (fn-lpc-at 2 s) (+ 1 pos)
          (fn-lpc-header-byte (fn-lpc-at 4 s) byte pos
                              (fn-lpc-at 0 s) (fn-lpc-at 2 s))
          (fn-lpc-split-byte matched byte)
          (if (equal matched 4) (fn-lpc-body-byte (fn-lpc-at 6 s) byte)
            (fn-lpc-at 6 s))
          (and (fn-lpc-at 7 s)
               (or (<= 8 pos) (equal byte (fn-lpc-at pos *fn-rcl-magic*)))))))

(defun fn-lpc-verdict (s)
  (declare (xargs :guard t))
  (if (< (nfix (fn-lpc-at 3 s)) (nfix (fn-lpc-at 1 s))) :yield
    (if (eq (fn-lpc-at 0 (fn-lpc-at 4 s)) :body) :valid :invalid)))

(defun fn-lpc-field (s k)
  (declare (xargs :guard (and (natp k) (< k 5))))
  (if (eq (fn-lpc-verdict s) :valid)
      (fn-lpc-at k (fn-lpc-at 8 (fn-lpc-at 4 s))) nil))

(defun fn-lpc-body-lines (s)
  (declare (xargs :guard t))
  (if (and (equal (fn-lpc-at 5 s) 4)
           (eq (fn-lpc-at 0 (fn-lpc-at 6 s)) :line))
      (nfix (fn-lpc-at 1 (fn-lpc-at 6 s))) 0))

(defun fn-lpc-tombstonep (s)
  (declare (xargs :guard t))
  (and (<= *fn-rcl-tombstone-fixed* (nfix (fn-lpc-at 1 s)))
       (fn-lpc-at 7 s) t))

; Cheap maintained guard: four scalars. It never validates headers,
; accumulated fields, the source bytes, or the arena's whole contents.
(defun fn-lpc-ready-p (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (natp (fn-lpc-at 0 s)) (natp (fn-lpc-at 1 s))
       (natp (fn-lpc-at 3 s))
       (<= (fn-lpc-at 3 s) (fn-lpc-at 1 s))
       (< (fn-lpc-at 0 s) (fn-arena-count fn-arena))
       (equal (fn-lpc-at 1 s)
              (fn-arena-payload-len (fn-lpc-at 0 s) fn-arena))))

(defthm fn-lpc-byte-keeps-source
  (and (equal (fn-lpc-at 0 (fn-lpc-byte s byte)) (fn-lpc-at 0 s))
       (equal (fn-lpc-at 1 (fn-lpc-byte s byte)) (fn-lpc-at 1 s))
       (equal (fn-lpc-at 2 (fn-lpc-byte s byte)) (fn-lpc-at 2 s))
       (equal (fn-lpc-at 3 (fn-lpc-byte s byte))
              (+ 1 (nfix (fn-lpc-at 3 s)))))
  :hints (("Goal" :in-theory (union-theories
            '(fn-lpc-byte fn-lpc-at fn-ag-car fn-ag-cdr car-cons cdr-cons)
            (union-theories (theory 'minimal-theory)
                            (executable-counterpart-theory :here))))))

(defun fn-lpc-tick (s fuel fn-arena)
  (declare (xargs :stobjs fn-arena :measure (nfix fuel) :verify-guards nil
                  :guard (and (natp fuel) (fn-lpc-ready-p s fn-arena))
                  :guard-hints (("Goal" :in-theory (e/d (fn-lpc-ready-p) (fn-lpc-byte fn-lpc-at))))))
  (if (or (zp fuel) (<= (fn-lpc-at 1 s) (fn-lpc-at 3 s)))
      (mv s 0 0 (fn-lpc-verdict s))
    (mv-let (next consumed work verdict)
      (fn-lpc-tick
       (fn-lpc-byte s (fn-arena-get (fn-lpc-at 0 s) (fn-lpc-at 3 s) fn-arena))
       (1- fuel) fn-arena)
      (mv next (+ 1 consumed) (+ 1 work) verdict))))

(defthm fn-lpc-tick-bounded
  (implies (natp fuel)
           (and (natp (mv-nth 1 (fn-lpc-tick s fuel fn-arena)))
                (equal (mv-nth 1 (fn-lpc-tick s fuel fn-arena))
                       (mv-nth 2 (fn-lpc-tick s fuel fn-arena)))
                (<= (mv-nth 2 (fn-lpc-tick s fuel fn-arena)) fuel)))
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpc-tick) (fn-lpc-byte fn-lpc-verdict)))))

(defthm fn-lpc-tick-preserves-source
  (let ((out (mv-nth 0 (fn-lpc-tick s fuel fn-arena))))
    (and (equal (fn-lpc-at 0 out) (fn-lpc-at 0 s))
         (equal (fn-lpc-at 1 out) (fn-lpc-at 1 s))
         (equal (fn-lpc-at 2 out) (fn-lpc-at 2 s))))
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpc-tick) (fn-lpc-byte fn-lpc-at fn-lpc-verdict)))))

(defthm fn-lpc-tick-preserves-ready
  (implies (fn-lpc-ready-p s fn-arena)
           (fn-lpc-ready-p (mv-nth 0 (fn-lpc-tick s fuel fn-arena)) fn-arena))
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpc-tick fn-lpc-ready-p)
                           (fn-lpc-byte fn-lpc-verdict)))))

(defthm fn-lpc-begin-ready
  (implies (and (natp h) (< h (fn-arena-count fn-arena))
                (equal n (fn-arena-payload-len h fn-arena)))
           (fn-lpc-ready-p (fn-lpc-begin h n pin) fn-arena))
  :hints (("Goal" :in-theory (enable fn-lpc-begin fn-lpc-ready-p fn-lpc-at))))

(defthm fn-lpc-tick-work-natural
  (natp (mv-nth 2 (fn-lpc-tick s fuel fn-arena)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpc-tick) (fn-lpc-byte fn-lpc-at fn-lpc-verdict)))))

(verify-guards fn-lpc-tick
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-ready-p)
                (fn-lpc-byte fn-lpc-at fn-lpc-verdict fn-lpc-tick
                 fn-arena-count-is-len fn-arena-get-is-nth
                 fn-arena-payload-len-is-len-nth)))))

; One raw span byte. Normalization/emission has its own continuation,
; sharing the same immutable source handle and origin pin.
(defun fn-lpc-span-ready-p (span offset fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (natp offset) (natp (fn-lpc-at 0 span))
       (natp (fn-lpc-at 1 span)) (natp (fn-lpc-at 2 span))
       (< (fn-lpc-at 0 span) (fn-arena-count fn-arena))
       (<= (+ (fn-lpc-at 1 span) (fn-lpc-at 2 span))
           (fn-arena-payload-len (fn-lpc-at 0 span) fn-arena))
       (< offset (fn-lpc-at 2 span))))

(defun fn-lpc-span-get (span offset fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-lpc-span-ready-p span offset fn-arena)
                  :guard-hints (("Goal" :in-theory
                    (e/d (fn-lpc-span-ready-p)
                         (fn-lpc-at fn-arena-count-is-len
                          fn-arena-payload-len-is-len-nth))))))
  (fn-arena-get (fn-lpc-at 0 span) (+ (fn-lpc-at 1 span) offset) fn-arena))

(defthm fn-lpc-span-get-is-source-octet
  (equal (fn-lpc-span-get span offset fn-arena)
         (nth (+ (fn-lpc-at 1 span) offset)
              (nth (fn-lpc-at 0 span) fn-arena)))
  :hints (("Goal" :in-theory '(fn-lpc-span-get fn-arena-get-is-nth))))


(defthm fn-lpc-tick-position
  (implies (natp (fn-lpc-at 3 s))
           (equal (fn-lpc-at 3 (mv-nth 0 (fn-lpc-tick s fuel fn-arena)))
                  (+ (fn-lpc-at 3 s) (mv-nth 1 (fn-lpc-tick s fuel fn-arena)))))
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpc-tick)
                           (fn-lpc-byte fn-lpc-at fn-lpc-verdict)))))

(defthm fn-lpc-tick-productive
  (implies (and (fn-lpc-ready-p s fn-arena) (posp fuel)
                (< (fn-lpc-at 3 s) (fn-lpc-at 1 s)))
           (< 0 (mv-nth 2 (fn-lpc-tick s fuel fn-arena))))
  :hints (("Goal" :expand ((fn-lpc-tick s fuel fn-arena))
           :in-theory (e/d (fn-lpc-ready-p)
                           (fn-lpc-byte fn-lpc-at fn-lpc-verdict fn-lpc-tick)))))
