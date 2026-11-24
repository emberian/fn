; The parent writer emits the scalar fields of an overview index row
; before copying its digest and writing its entry count.
(in-package "ACL2")
(include-book "runs-header-emitter-proof")

(defconst *fn2-run-index-reference-prefix* (take (+ 2 *fn2-format-ref-field-expected-hash*) *fn2-overview-index*))

(defun-nx fn2-run-index-prefix-octets (base f)
  (fn2-layout-octets *fn2-run-index-reference-prefix*
                      (fn2-run-unload-values *fn2-run-index-reference-prefix* base f nil)))

(defmacro fn2-run-index-prefix-values-p (base f)
  (sublis (list (cons 'base base) (cons 'f f))
          (cons 'and (fn2-run-header-value-tests *fn2-run-index-reference-prefix*
                        (fn2-run-header-field-terms *fn2-run-index-reference-prefix* 0)))))

(local
 (defun fn2-run-layout-emitter-names (name layout)
   (if (atom layout) nil
     (cons (fn2-codec-emitter-name name (caar layout))
           (fn2-run-layout-emitter-names name (cdr layout))))))

(defthmd fn2-run-index-emits-reference-prefix
  (let* ((bytes (fn2-run-index-prefix-octets base f))
         (write (fn2-run-load-bytes bytes slot gen off pk ps pg pool))
         (actual (fn2-overview-index-emit-group base slot gen off off pk ps pg f pool)))
    (implies (and (natp base) (natp off) (fn2-run-index-prefix-values-p base f) (equal (car write) :ok))
             (equal actual (fn2-overview-index-emit-child-expected-hash base slot gen off (+ off (len bytes))
                            pk ps pg f (mv-nth 1 write)))))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
           :in-theory (union-theories
                       (e/d (fn2-run-index-prefix-octets fn2-run-unload-values fn2-layout-octets fn2-layout-field-octets
                             fn2-run-encode-span-length fn2-run-encode-valid-tag-byte
                             fn2-run-load-byte-segments fn2-run-varint-writes-layout-octets
                             fn2-run-fixed-writes-layout-octets)
                            (fn2-run-load-bytes fn2-codec-emit-varint fn2-codec-emit-fixed
                             fn2-fields-value fn2-layout-varoctets fn2-layout-le binary-append
                             fn2-run-read-bytes fn2-fields-ref-slot fn2-fields-ref-off fn2-fields-ref-gen fn2-fields-ref-len
                             fn2-overview-index-emit-child-expected-hash))
                       (fn2-run-layout-emitter-names 'fn2-overview-index *fn2-run-index-reference-prefix*)))))

(defmacro fn2-run-index-digest-field (base)
  `(+ ,base 2 *fn2-format-ref-field-expected-hash*))

(defun-nx fn2-run-index-count-octets (base f)
  (fn2-layout-varoctets (fn2-fields-value (+ base *fn2-overview-index-field-child-entries*) f)))

(defun-nx fn2-run-index-digest-octets (base f pool)
  (let ((i (fn2-run-index-digest-field base)))
    (fn2-run-read-bytes (fn2-fields-ref-len i f) (fn2-fields-ref-slot i f) (fn2-fields-ref-gen i f)
                        (fn2-fields-ref-off i f) 9 0 1 pool)))

(local
 (defthm fn2-run-index-bytes-associative
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn2-run-index-read-byte-count
   (equal (len (fn2-run-read-bytes n slot gen off pk ps pg pool)) (nfix n))
   :hints (("Goal" :induct (fn2-run-read-bytes n slot gen off pk ps pg pool)
            :in-theory (disable fn2-pool-read)))))

(defthmd fn2-run-index-wire-segments
  (let* ((i (fn2-run-index-digest-field base))
         (prefix (append (fn2-run-index-prefix-octets base f) '(1)))
         (body (fn2-run-index-digest-octets base f pool))
         (count (fn2-run-index-count-octets base f))
         (bytes (fn2-layout-octets *fn2-overview-index* (fn2-run-unload-values *fn2-overview-index* base f pool))))
    (implies (and (natp base) (equal (fn2-fields-value i f) 1) (equal (fn2-fields-ref-len i f) 32))
             (and (equal bytes (append prefix body count))
                  (equal (len body) 32)
                  (equal (fn2-overview-index-size base f) (+ (len prefix) 32 (len count))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories
                        (e/d (fn2-run-index-prefix-octets fn2-run-index-digest-octets fn2-run-index-count-octets
                              fn2-run-unload-values fn2-layout-octets fn2-layout-field-octets fn2-overview-index-size
                              fn2-run-encode-span-length fn2-run-encode-varint-width)
                             (fn2-layout-varoctets fn2-layout-varsize fn2-layout-le fn2-run-read-bytes fn2-fields-value
                              fn2-fields-ref-len fn2-fields-ref-gen fn2-fields-ref-slot fn2-fields-ref-off))
                        (fn2-run-header-encoder-definitions 'fn2-overview-index *fn2-overview-index*)))))

(local
 (defthm fn2-run-index-varint-octet-list
   (implies (natp v) (fn-b3-octet-listp (fn2-layout-varoctets v)))
   :hints (("Goal" :induct (fn2-layout-varoctets v)))))

(local
 (defthm fn2-run-index-append-octets
   (implies (and (fn-b3-octet-listp a) (fn-b3-octet-listp b)) (fn-b3-octet-listp (append a b)))))

(defthmd fn2-run-index-scalars-are-octets
  (implies (and (natp base) (fn2-run-index-prefix-values-p base f)
                (natp (fn2-fields-value (+ base *fn2-overview-index-field-child-entries*) f)))
           (and (fn-b3-octet-listp (append (fn2-run-index-prefix-octets base f) '(1)))
                (fn-b3-octet-listp (fn2-run-index-count-octets base f))))
  :hints (("Goal" :in-theory (e/d (fn2-run-index-prefix-octets fn2-run-index-digest-octets fn2-run-index-count-octets
                             fn2-run-unload-values fn2-layout-octets fn2-layout-field-octets)
                       (fn2-layout-varoctets fn2-layout-le fn2-run-read-bytes fn2-poolp fn2-pool-wfp
                        fn2-fields-value fn2-fields-ref-gen fn2-fields-ref-slot fn2-fields-ref-len fn2-fields-ref-off)))))
