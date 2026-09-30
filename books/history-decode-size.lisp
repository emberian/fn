; Canonical size sidecars at the actual byte-fed decode boundary.
; The parser state and borrowed node representation remain unchanged.
(in-package "ACL2")
(include-book "history-decode-stream")
(include-book "store-tree-size")
(in-theory (disable fn-hdc-feed))

; All callers use fixed field indices. Never inspect a child tree.
(defun fn-hds-at (n x)
  (declare (xargs :guard (natp n)))
  (if (consp x)
      (if (zp n) (car x) (fn-hds-at (1- n) (cdr x)))
    nil))

; NIL is the sole accepted symbol alias that changes canonical size.
; Other package aliases change a one-octet package value, never its width.
; Match its three bytes as the existing decoder consumes them.
(defun fn-hds-nil-byte (byte s prefix)
  (declare (xargs :guard (and (fn-scc-octetp byte) (fn-hdc-statep s))))
  (and (eq (nth 0 s) :payload) (equal (nth 1 s) 4)
       (member-equal (nth 2 s) '(1 2)) (equal (nth 5 s) 3)
       (cond ((equal (nth 6 s) 3) (equal byte 78))
             ((equal (nth 6 s) 2) (and prefix (equal byte 73)))
             ((equal (nth 6 s) 1) (and prefix (equal byte 76)))
             (t nil))
       t))

; This reads a just-constructed leaf descriptor, not its borrowed bytes.
; An invalid descriptor has no usable carry; no guessed reserve is returned.
(defun fn-hds-leaf-carry (node nil-alias)
  (declare (xargs :guard t))
  (let ((kind (fn-hds-at 0 node)) (value (fn-hds-at 1 node))
        (count (fn-hds-at 4 node)))
    (cond ((eq kind :atom)
           (if (or (integerp value) (characterp value) (stringp value) (symbolp value))
               (fn-scs-atom value) nil))
          ((and (eq kind :span) (natp count))
           (cond ((equal value 6) (fn-scs-octets count))
                 ((equal value 3) (list (+ 2 (fn-scs-width count) count) nil nil))
                 ((equal value 4)
                  (if nil-alias (fn-scs-atom nil)
                    (list (+ 3 (fn-scs-width count) count) nil nil)))
                 (t nil)))
          (t nil))))

(defthm fn-hds-leaf-carry-shape
  (or (null (fn-hds-leaf-carry node nil-alias))
      (fn-scs-carryp (fn-hds-leaf-carry node nil-alias)))
  :hints (("Goal" :in-theory (enable fn-scs-carryp fn-scs-octets))))

(defun fn-hds-begin (offset length epoch lease)
  (declare (xargs :guard (and (natp offset) (natp length))))
  (mv (fn-hdc-begin offset length epoch lease) nil nil t))

; Four results: actual parser state, parallel size stack, NIL-prefix bit,
; and usable bit. Each byte causes at most one carry push or pair reduction.
; The usable bit is permanently lost on parser/metadata failure.
(defun fn-hds-feed (byte s sizes nil-prefix usable)
  (declare (xargs :guard (and (fn-scc-octetp byte) (fn-hdc-statep s))))
  (let* ((next (fn-hdc-feed byte s))
         (prefix (fn-hds-nil-byte byte s nil-prefix))
         (mode (nth 0 s)) (next-mode (nth 0 next)))
    (cond
     ((or (not usable) (eq next-mode :refused)) (mv next sizes prefix nil))
     ((or (member-eq mode '(:done :refused)) (>= (nth 7 s) (nth 8 s)))
      (mv next sizes nil-prefix usable))
     ((and (eq mode :op) (equal byte 5)
           (member-eq next-mode '(:op :done)))
      (if (and (consp sizes) (consp (cdr sizes))
               (fn-scs-carryp (car sizes)) (fn-scs-carryp (cadr sizes)))
          (mv next (cons (fn-scs-cons (cadr sizes) (car sizes)) (cddr sizes)) prefix t)
        (mv next sizes prefix nil)))
     ((and (member-eq next-mode '(:op :done))
           (or (and (eq mode :op) (equal byte 0))
               (member-eq mode '(:char :length :digits :payload))))
      (let ((carry (fn-hds-leaf-carry (fn-hds-at 0 (nth 9 next)) prefix)))
        (if carry (mv next (cons carry sizes) prefix t)
          (mv next sizes prefix nil))))
     (t (mv next sizes prefix usable)))))

; Exact projection of the actual decoder, including every refusal branch.
(defthm fn-hds-feed-parser-is-actual-by-definition
  (equal (mv-nth 0 (fn-hds-feed byte s sizes nil-prefix usable))
         (fn-hdc-feed byte s))
  :hints (("Goal" :in-theory (e/d (fn-hds-feed)
                                  (fn-hdc-feed fn-hds-leaf-carry fn-hds-nil-byte)))))

(defthm fn-hds-begin-parser-is-actual-by-definition
  (equal (mv-nth 0 (fn-hds-begin offset length epoch lease))
         (fn-hdc-begin offset length epoch lease)))

(defthm fn-hds-unusable-carry-stays-unusable
  (implies (not usable)
           (not (mv-nth 3 (fn-hds-feed byte s sizes nil-prefix usable)))))

(defthm fn-hds-feed-preserves-lifetime
  (let ((next (mv-nth 0 (fn-hds-feed byte s sizes nil-prefix usable))))
    (and (equal (nth 8 next) (nth 8 s))
         (equal (nth 10 next) (nth 10 s))
         (equal (nth 11 next) (nth 11 s))))
  :hints (("Goal" :in-theory (disable fn-hds-feed fn-hdc-feed))))

(in-theory (disable fn-hds-at fn-hds-nil-byte fn-hds-leaf-carry
                    fn-hds-begin fn-hds-feed))

; Constructor correspondence used at the decoder's actual leaf push.
; Symbol normalization preserves its name; NIL alone selects the NIL opcode.
(defthm fn-hds-atom-leaf-carry-exact
  (implies (or (integerp x) (characterp x) (stringp x) (symbolp x))
           (equal (fn-hds-leaf-carry (fn-hdc-atom x) nil-alias)
                  (fn-scs-summary x)))
  :hints (("Goal" :in-theory (enable fn-hds-leaf-carry fn-hds-at fn-hdc-atom))))

(defthm fn-hds-octets-leaf-carry-exact
  (implies (and (fn-scc-octet-listp bytes) (equal count (len bytes)))
           (equal (fn-hds-leaf-carry (fn-hdc-span 6 pkg offset count) nil-alias)
                  (fn-scs-summary bytes)))
  :hints (("Goal" :in-theory (e/d (fn-hds-leaf-carry fn-hds-at fn-hdc-span)
                                  (fn-scs-octets)))))

(defthm fn-hds-string-leaf-carry-exact
  (implies (and (stringp text) (equal count (length text)))
           (equal (fn-hds-leaf-carry (fn-hdc-span 3 pkg offset count) nil-alias)
                  (fn-scs-summary text)))
  :hints (("Goal" :use ((:instance fn-scs-atom-establishes-summary (x text)))
           :in-theory (e/d (fn-hds-leaf-carry fn-hds-at fn-hdc-span
                               fn-scs-atom fn-scs-atom-size fn-scc-octetp)
                            (fn-scs-atom-establishes-summary fn-scs-width
                             fn-scs-atom-size-is-encoded-length
                             fn-scs-width-is-digit-length)))))

(defthm fn-hds-symbol-leaf-carry-exact
  (implies (and (symbolp sym) (equal count (length (symbol-name sym)))
                (iff nil-alias (null sym)))
           (equal (fn-hds-leaf-carry (fn-hdc-span 4 pkg offset count) nil-alias)
                  (fn-scs-summary sym)))
  :hints (("Goal" :use ((:instance fn-scs-atom-establishes-summary (x sym)))
           :in-theory (e/d (fn-hds-leaf-carry fn-hds-at fn-hdc-span
                               fn-scs-atom fn-scs-atom-size fn-scc-octetp)
                            (fn-scs-atom-establishes-summary fn-scs-width
                             fn-scs-atom-size-is-encoded-length
                             fn-scs-width-is-digit-length)))))

; The final byte of the actual streaming matcher completes exactly the name
; comparison, without coercing/interning a name or revisiting earlier bytes.
(defthm fn-hds-nil-byte-completes-name
  (implies (and (eq (nth 0 s) :payload) (equal (nth 1 s) 4)
                (member-equal (nth 2 s) '(1 2)) (equal (nth 5 s) 3)
                (equal (nth 6 s) 1)
                (equal prefix (equal (take 2 name) '(78 73)))
                (equal byte (nth 2 name)))
           (equal (fn-hds-nil-byte byte s prefix)
                  (equal (take 3 name) '(78 73 76))))
  :hints (("Goal" :in-theory (enable fn-hds-nil-byte take nth)
           :expand ((take 3 name) (take 2 name)
                    (take 2 (cdr name)) (take 1 (cdr name))
                    (take 1 (cddr name))))))
