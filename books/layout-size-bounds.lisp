; Proof interfaces for actual codec sizes, requested only by their consumers.
; Schema MAX-SIZE bounds accepted values; these bounds cover the field store.
(in-package "ACL2")
(include-book "layout")
(fn2-book-layer :b)

(encapsulate ()
 (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(defthm fn2-layout-varsize-coarse-bound
  (<= (fn2-layout-varsize v) (+ 1 (floor (nfix v) 128)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-layout-varsize v)
           :in-theory (e/d (fn2-layout-varsize) (floor))))))

(defun fn2-codec-storage-field-bound (kind value-width ref-width)
  (declare (xargs :verify-guards nil))
  (let* ((width (fn2-layout-width kind))
         (tag (fn2-layout-kind-code kind))
         (ref-max (- (expt 2 ref-width) 1)))
    (cond (width width)
          ((= tag 10) (+ 1 (floor ref-max 128) ref-max))
          ((member-equal tag '(15 16)) (+ (if (= tag 15) 2 4) ref-max))
          (t (+ 1 (floor (- (expt 2 value-width) 1) 128))))))

(defun fn2-codec-storage-bound (layout value-width ref-width)
  (declare (xargs :verify-guards nil))
  (if (atom layout) 0
    (+ (fn2-codec-storage-field-bound (cadar layout) value-width ref-width)
       (fn2-codec-storage-bound (cdr layout) value-width ref-width))))

(defun fn2-codec-has-size-tagp (layout tags)
  (declare (xargs :verify-guards nil))
  (and (consp layout)
       (or (member-equal (fn2-layout-kind-code (cadar layout)) tags)
           (fn2-codec-has-size-tagp (cdr layout) tags))))
(defun fn2-codec-varsize-bound-event (name suffix width)
  (declare (xargs :verify-guards nil))
  `(local
    (defthm ,(fn2-codec-symbol name suffix)
      (implies (unsigned-byte-p ,width v)
               (<= (fn2-layout-varsize v)
                   ,(+ 1 (floor (- (expt 2 width) 1) 128))))
      :rule-classes nil
      :hints (("Goal" :use fn2-layout-varsize-coarse-bound
               :in-theory (e/d (unsigned-byte-p integer-range-p)
                               (fn2-layout-varsize floor)))))))
(defun fn2-codec-reference-bound-event (name width)
  (declare (xargs :verify-guards nil))
  `(local
    (defthm ,(fn2-codec-symbol name "-REF-LENGTH-STORAGE-BOUND")
      (implies (unsigned-byte-p ,width v) (<= v ,(- (expt 2 width) 1)))
      :rule-classes nil
      :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p))))))
(defun fn2-codec-sizer-bound-events (name layout count value-width ref-width)
  (declare (xargs :verify-guards nil))
  (if (atom layout) nil
    (let* ((step (fn2-codec-sizer-name name (caar layout)))
           (tail (and (consp (cdr layout)) (fn2-codec-sizer-name name (caadr layout))))
           (kind (cadar layout)) (tag (fn2-layout-kind-code kind))
           (i `(+ base ,(fn2-codec-field name (caar layout))))
           (room `(and (fn2-fields-wfp fn2-fields) (natp base)
                       (<= (+ base ,count) (fn2-fields-rows fn2-fields)))))
      (append (fn2-codec-sizer-bound-events name (cdr layout) count value-width ref-width)
        `((defthm ,(fn2-codec-symbol step "-BOUND")
            (implies (and (fn2-fieldsp fn2-fields) ,room)
                     (<= (,step base fn2-fields)
                         ,(fn2-codec-storage-bound layout value-width ref-width)))
            :rule-classes :linear
            :hints (("Goal"
                     ,@(let* ((reader (if (member-equal tag '(10 15 16))
                                                'fn2-fields-ref-len 'fn2-fields-value))
                               (value `(,reader ,i fn2-fields))
                               (facts
                                (append
                                 (and tail `((:instance ,(fn2-codec-symbol tail "-BOUND"))))
                                 (and (not (fn2-layout-width kind))
                                   `((:instance ,(fn2-codec-symbol reader "-NATP") (i ,i))
                                     (:instance ,(fn2-codec-symbol reader "-BOUND") (i ,i))
                                     ,@(and (member-equal tag '(10 15 16))
                                        `((:instance ,(fn2-codec-symbol name "-REF-LENGTH-STORAGE-BOUND")
                                           (v ,value))))
                                     ,@(and (not (member-equal tag '(15 16)))
                                        `((:instance
                                           ,(fn2-codec-symbol name (if (= tag 10)
                                              "-VARSIZE-REF-STORAGE-BOUND"
                                              "-VARSIZE-VALUE-STORAGE-BOUND"))
                                           (v ,value)))))))))
                         (and facts `(:use ,facts)))
                     ; Compose only with the tail's named contract.
                     :in-theory (e/d (,step) (fn2-layout-varsize floor ,@(and tail (list tail))))))))))))

(defun fn2-codec-size-bound-events (name layout value-width ref-width)
  (declare (xargs :verify-guards nil))
  (let* ((count (len layout)) (sizefn (fn2-codec-symbol name "-SIZE"))
         (storage-max (fn2-codec-constant name "-STORAGE-MAX-SIZE"))
         (first (fn2-codec-sizer-name name (caar layout)))
         (room `(and (fn2-fields-wfp fn2-fields) (natp base)
                     (<= (+ base ,count) (fn2-fields-rows fn2-fields)))))
    `(encapsulate ()
       (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
       (local (in-theory *fn2-codec-proof-runes*))
       (local (in-theory (disable fn2-fieldsp fn2-fields-wfp fn2-fields-rows
                                 fn2-fields-value fn2-fields-ref-len nth)))
       ,@(and (fn2-codec-has-size-tagp layout '(10 15 16))
              (list (fn2-codec-reference-bound-event name ref-width)))
       ,@(and (fn2-codec-has-size-tagp layout '(5 8))
              (list (fn2-codec-varsize-bound-event name "-VARSIZE-VALUE-STORAGE-BOUND" value-width)))
       ,@(and (fn2-codec-has-size-tagp layout '(10))
              (list (fn2-codec-varsize-bound-event name "-VARSIZE-REF-STORAGE-BOUND" ref-width)))
       ; This coarse upper bound uses actual widths, not schema payload limits.
       (defconst ,storage-max ,(fn2-codec-storage-bound layout value-width ref-width))
       ,@(fn2-codec-sizer-bound-events name layout count value-width ref-width)
       (defthm ,(fn2-codec-symbol sizefn "-BOUND")
         (implies (and (fn2-fieldsp fn2-fields) ,room)
                  (<= (,sizefn base fn2-fields) ,storage-max))
         :rule-classes :linear
         :hints (("Goal" :use (:instance ,(fn2-codec-symbol first "-BOUND"))
                  :in-theory (e/d (,sizefn) (,first))))))))

(defmacro defcodec-size-bounds (name)
  `(make-event
    (let* ((codec (cdr (assoc-eq ',name (table-alist 'fn2-layouts (w state)))))
           (layout (cadr (member-eq :layout codec)))
           (row (cdr (assoc-eq 'fn2-fields (table-alist 'fn2-columns (w state)))))
           (columns (cadr (member-eq :columns row)))
           (value-width (fn2-columns-width (cadr (assoc-eq 'value columns))))
           (ref-width (fn2-columns-width (cadr (assoc-eq 'ref-len columns)))))
      (if (and codec (fn2-layoutp layout) (consp layout)
               (equal value-width (cadr (member-eq :value-width codec))))
          (value (fn2-codec-size-bound-events ',name layout value-width ref-width))
        (er soft 'defcodec-size-bounds "No matching registered codec ~x0." ',name)))))
