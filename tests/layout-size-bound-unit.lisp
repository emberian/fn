(in-package "ACL2")
(include-book "../books/layout-size-bounds")

; The retirement producer writes this actual four-field body length into a
; u60 journal field. Its guard should use the generated bound, not unfold
; every field's sizer or invoke the pool-dependent value checker.
(deflayout fn2-codec-size-values
  '((extent :u60) (writer-epoch :u60) (allocation :u60) (commit :u60)))
(make-event
 (let ((world (w state)))
  (value `(defconst *fn2-codec-size-incoming-runes*
            ',(intersection-equal (current-theory :here) *fn2-codec-proof-runes*)))))
(defcodec-size-bounds fn2-codec-size-values)
(assert-event
 (let ((world (w state)))
  (equal (intersection-equal (current-theory :here) *fn2-codec-proof-runes*)
         *fn2-codec-size-incoming-runes*)))
(defun fn2-codec-size-store-length (base out fn2-fields)
  (declare (xargs :stobjs fn2-fields
    :guard (and (fn2-fields-wfp fn2-fields) (natp base)
                (<= (+ base 4) (fn2-fields-rows fn2-fields))
                (natp out) (< out (fn2-fields-rows fn2-fields)))
    :guard-hints (("Goal" :in-theory
                   (disable fn2-codec-size-values-size fn2-fields-rows
                            fn2-fields-value fn2-fieldsp fn2-fields-wfp)))))
  (fn2-fields-set-value out (fn2-codec-size-values-size base fn2-fields) fn2-fields))
(assert-event
 (eq (symbol-class 'fn2-codec-size-store-length (w state)) :common-lisp-compliant))
(fn2-fields-preserves fn2-codec-size-store-length (base out fn2-fields)
 :raw-rows t
 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (natp base)
        (<= (+ base 4) (fn2-fields-rows fn2-fields))
        (natp out) (< out (fn2-fields-rows fn2-fields)))
 :hints (("Goal" :in-theory (disable fn2-codec-size-values-size fn2-fields-rows))))

; The schema limits describe accepted payloads, not arbitrary stored lengths.
; Exercise all three length prefixes alongside fixed and variable scalars.
(deflayout fn2-codec-size-mixed
  '((counter :varint) (bytes (:octets 0)) (short (:octets16 0))
    (long (:octets32 0)) (fixed :u64be) (hash :digest) (padding (:zero 2))))
(defcodec-size-bounds fn2-codec-size-mixed)

(defun fn2-codec-size-bound-controls (fn2-fields)
  (declare (xargs :stobjs fn2-fields))
  (let* ((fn2-fields (fn2-fields-init 8 fn2-fields))
         (fn2-fields (fn2-fields-set-value 0 1152921504606846975 fn2-fields))
         (fn2-fields (fn2-fields-set-value 1 1152921504606846975 fn2-fields))
         (fn2-fields (fn2-fields-set-value 2 1152921504606846975 fn2-fields))
         (fn2-fields (fn2-fields-set-value 3 1152921504606846975 fn2-fields))
         (positive
          (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
               (<= 4 (fn2-fields-rows fn2-fields))
               (equal (fn2-codec-size-values-size 0 fn2-fields) 36)
               (<= (fn2-codec-size-values-size 0 fn2-fields)
                   *fn2-codec-size-values-storage-max-size*)))
         (fn2-fields (fn2-codec-size-store-length 0 7 fn2-fields))
         (stored (equal (fn2-fields-value 7 fn2-fields) 36))
         (fn2-fields (fn2-fields-set-ref-len 1 128 fn2-fields))
         (fn2-fields (fn2-fields-set-ref-len 2 65536 fn2-fields))
         (fn2-fields (fn2-fields-set-ref-len 3 4294967295 fn2-fields))
         (size (fn2-codec-size-mixed-size 0 fn2-fields))
         (expected (+ 9 (+ 2 128) (+ 2 65536) (+ 4 4294967295) 8 33 2)))
    (mv (and positive stored
             (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
             (<= 7 (fn2-fields-rows fn2-fields))
             (equal size expected)
             ; Removing checked-value constraints refutes the schema bound.
             (> expected *fn2-codec-size-mixed-max-size*)
             ; The representation-derived theorem still applies.
             (<= expected *fn2-codec-size-mixed-storage-max-size*))
        fn2-fields)))
(defun fn2-codec-size-bound-unit ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (ok fn2-fields) (fn2-codec-size-bound-controls fn2-fields) ok)))
(assert-event (fn2-codec-size-bound-unit))
