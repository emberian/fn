; Decode a stored run header or its enclosing page header. A watch below
; the decoded region includes the range query and the preceding header.
(in-package "ACL2")
(include-book "runs-page-id-proof")
(include-book "runs-format-page-header-decode-proof")
(include-book "runs-data-header-decode-proof")
(include-book "runs-page-format")

(defun-nx fn2-run-header-scalars-p (layout vals)
  (if (atom layout) (null vals)
    (and (consp vals) (consp (car layout)) (consp (cdar layout))
         (fn2-run-scalar-kindp (cadar layout)) (unsigned-byte-p 60 (car vals))
         (fn2-run-header-scalars-p (cdr layout) (cdr vals)))))

(local
 (defun-nx fn2-run-header-field-walk (j layout vals)
   (if (or (zp j) (atom layout)) vals
     (fn2-run-header-field-walk (1- j) (cdr layout) (cdr vals)))))

(local
 (defthm fn2-run-header-scalar-at
   (implies (and (fn2-run-header-scalars-p layout vals) (natp j) (< j (len layout)))
            (and (fn2-run-scalar-prefixp j layout) (unsigned-byte-p 60 (nth j vals))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-run-header-field-walk j layout vals) :expand ((fn2-run-header-scalars-p layout vals)
                    (fn2-run-scalar-prefixp j layout) (nth j vals))
            :in-theory (disable fn2-run-scalar-kindp unsigned-byte-p)))))

(defun-nx fn2-run-stored-header-p (layout vals slot gen off end pk ps pg pool)
  (let* ((bytes (fn2-layout-octets layout vals)) (bound (+ off (len bytes))))
    (and (fn2-run-values-layoutp layout vals) (fn2-run-header-scalars-p layout vals)
         (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= bound end) (<= (len bytes) *fn2-codec-decode-fuel*)
         (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
         (fn2-poolp pool) (fn2-pool-wfp pool) (natp (fn2-pool-base slot pool))
         (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
         (equal (fn2-run-read-bytes (len bytes) slot gen off pk ps pg pool) bytes))))

(local
 (defthm fn2-run-scan-stored-header-field
   (let ((scan (fn2-layout-scan layout *fn2-codec-decode-fuel* base 0 0 0 0 0 0 off slot gen end pk ps pg f pool)))
     (implies (and (fn2-run-stored-header-p layout vals slot gen off end pk ps pg pool)
                   (natp base) (natp watch) (< watch (+ base (len layout)))
                   (<= (+ base (len layout)) (fn2-fields-rows f)))
              (and (equal (car scan) :ok) (equal (mv-nth 8 scan) (+ off (len (fn2-layout-octets layout vals))))
                   (equal (fn2-fields-value watch (mv-nth 9 scan))
                          (if (< watch base) (fn2-fields-value watch f) (nth (- watch base) vals))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess) :cases ((< watch base))
            :use ((:instance fn2-run-header-scalar-at (j (- watch base)))
                  (:instance fn2-run-readable-page-prefix (bound (+ off (len (fn2-layout-octets layout vals)))))
                  (:instance fn2-run-page-scan-consumes-admitted-row (row vals) (fuel *fn2-codec-decode-fuel*))
                  (:instance fn2-run-page-scan-returns-source-scalar (row vals) (fuel *fn2-codec-decode-fuel*) (j (- watch base))))
            :in-theory (e/d (fn2-run-stored-header-p)
                     (fn2-run-header-scalars-p fn2-run-scalar-prefixp fn2-layout-octets fn2-run-values-layoutp
                      fn2-layout-scan fn2-run-read-bytes fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code
                      fn2-fields-rows fn2-fields-value nth len unsigned-byte-p))))))

(local
 (defthm fn2-run-header-field-after-decoder-save
   (equal (fn2-fields-value watch (fn2-codec-save base ph pos v hi size ref payload next f)) (fn2-fields-value watch f))
   :hints (("Goal" :in-theory (e/d (fn2-codec-save fn2-fields-value) (nth update-nth unsigned-byte-p))))))

(defmacro fn2-run-read-stored-header (name)
   (let ((layout (fn2-codec-constant name "")) (decode (fn2-codec-symbol name "-DECODE"))
         (start (fn2-codec-symbol name "-START")))
     `(defthmd ,(fn2-codec-symbol name "-READS-STORED-FIELD")
        (let ((res (,decode base slot gen off end pk ps pg f pool)))
          (implies (and (fn2-run-stored-header-p ,layout vals slot gen off end pk ps pg pool)
                        (natp base) (natp watch) (< watch (+ base (len ,layout)))
                        (<= (+ base (len ,layout)) (fn2-fields-rows f)))
                   (and (equal (car res) :ok)
                        (equal (mv-nth 1 res) (+ off (len (fn2-layout-octets ,layout vals))))
                        (equal (fn2-fields-value watch (mv-nth 2 res))
                               (if (< watch base) (fn2-fields-value watch f) (nth (- watch base) vals))))))
        :hints (("Goal" :do-not '(preprocess)
                 :use (,(fn2-codec-symbol name "-DECODE-REFINES-LAYOUT")
                       (:instance fn2-run-scan-stored-header-field (layout ,layout) (f (,start base f))))
                 :in-theory (e/d (,start fn2-run-stored-header-p)
                         (,decode fn2-run-header-scalars-p fn2-run-values-layoutp fn2-run-read-bytes
                          fn2-layout-scan fn2-codec-save fn2-fields-value fn2-fields-rows fn2-poolp fn2-pool-wfp
                          fn2-pool-base fn2-layout-range-code fn2-layout-octets unsigned-byte-p nth len)))))))

(fn2-run-read-stored-header fn2-format-page-header)
(fn2-run-read-stored-header fn2-run-page-header)
