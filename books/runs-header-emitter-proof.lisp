; Proof generator for the scalar emitters in the two run page headers.
(in-package "ACL2")
(include-book "runs-restart-write-proof")
(include-book "runs-overview-emit-proof")

(defthmd fn2-run-encode-valid-tag-byte
  (implies (unsigned-byte-p 8 v) (equal (fn2-layout-le 1 v) (list v)))
  :hints (("Goal" :in-theory (enable fn2-layout-le))))

(defthmd fn2-run-encode-span-length
  (equal (len (append a b)) (+ (len a) (len b))))

(defthmd fn2-run-encode-varint-width
  (equal (len (fn2-layout-varoctets v)) (fn2-layout-varsize v))
  :hints (("Goal" :induct (fn2-layout-varsize v))))

(defun fn2-run-header-field-terms (layout i)
  (if (atom layout) nil
    (cons `(fn2-fields-value (+ base ,i) f) (fn2-run-header-field-terms (cdr layout) (1+ i)))))

(defun fn2-run-header-value-tests (layout terms)
  (declare (xargs :verify-guards nil))
  (if (atom layout) nil
    (let ((tag (fn2-layout-kind-code (cadar layout))) (v (car terms)))
      (cons (case tag
              (1 `(unsigned-byte-p 8 ,v)) (3 `(unsigned-byte-p 32 ,v))
              (9 `(and (unsigned-byte-p 8 ,v) (< ,v ,(len (caddr (cadar layout))))))
              (otherwise `(unsigned-byte-p 60 ,v)))
            (fn2-run-header-value-tests (cdr layout) (cdr terms))))))

(defun fn2-run-header-encoder-definitions (name layout)
  (if (atom layout) nil
    (list* (fn2-codec-sizer-name name (caar layout)) (fn2-codec-checker-name name (caar layout))
           (fn2-run-header-encoder-definitions name (cdr layout)))))

(defun fn2-run-header-emitter-events (name layout i fixed)
  (declare (xargs :verify-guards nil))
  (if (atom layout) nil
    (let* ((step (fn2-codec-emitter-name name (caar layout))) (width (fn2-layout-width (cadar layout)))
           (terms (fn2-run-header-field-terms layout i)) (bytes `(fn2-layout-octets ',layout (list ,@terms)))
           (start (if fixed `(+ off ,fixed) 'next)))
      (append (fn2-run-header-emitter-events name (cdr layout) (1+ i) (and fixed width (+ fixed width)))
        (list
         `(local
           (defthm ,(fn2-codec-symbol step "-WRITES-HEADER-BYTES")
             (let* ((bytes ,bytes) (load (fn2-run-load-bytes bytes slot gen ,start pk ps pg pool)))
               (implies (and (natp base) (natp off) (natp next) ,@(fn2-run-header-value-tests layout terms)
                             (equal (car load) :ok))
                        (equal (,step base slot gen off next pk ps pg f pool)
                               (list :ok (+ ,start (len bytes)) (mv-nth 1 load)))))
             :hints (("Goal" :do-not '(preprocess) :do-not-induct t
                      :expand ((:free (vals) (fn2-layout-octets ',layout vals)))
                      :in-theory (e/d (,step fn2-layout-field-octets fn2-run-fixed-writes-layout-octets
                                       fn2-run-varint-writes-layout-octets fn2-run-load-byte-segments
                                       fn2-run-encode-valid-tag-byte fn2-run-encode-span-length)
                                  (fn2-layout-octets fn2-layout-le fn2-layout-varoctets fn2-run-load-bytes
                                   fn2-codec-emit-fixed fn2-codec-emit-varint fn2-fields-value binary-append nth)))))))))))

(defmacro fn2-run-prove-header-encoder (name layout)
  `(make-event
    (let* ((layout ,layout) (name ',name) (terms (fn2-run-header-field-terms layout 0))
           (encode (fn2-codec-symbol name "-ENCODE")))
      (value
       (cons 'progn
        (append (fn2-run-header-emitter-events name layout 0 0)
         (list
          `(defthmd ,(fn2-codec-symbol name "-WRITES-SCALAR-HEADER")
             (let* ((bytes (fn2-layout-octets ',layout (list ,@terms))) (end (+ off (len bytes)))
                    (load (fn2-run-load-bytes bytes slot gen off pk ps pg pool)))
               (implies (and (natp base) (unsigned-byte-p 32 off) ,@(fn2-run-header-value-tests layout terms)
                             (equal (fn2-layout-range-code slot gen off end t pk ps pg pool) :ok)
                             (equal (car load) :ok))
                        (equal (,encode base slot gen off pk ps pg f pool)
                               (list :ok end (mv-nth 1 load)))))
             :hints (("Goal" :do-not-induct t :do-not '(preprocess)
                      :in-theory (e/d (,encode ,(fn2-codec-symbol name "-SIZE")
                                       ,(fn2-codec-symbol name "-CHECK-VALUES")
                                       ,@(fn2-run-header-encoder-definitions name layout)
                                       fn2-layout-field-octets fn2-layout-octets fn2-run-encode-span-length
                                       fn2-run-encode-varint-width)
                                  (fn2-layout-le fn2-layout-varoctets fn2-layout-varsize
                                   fn2-layout-range-code fn2-run-load-bytes fn2-fields-value binary-append nth))))))))))))
