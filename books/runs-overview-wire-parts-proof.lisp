; A stored overview row consists of its four scalar IDs, the encoded length,
; and the line itself. Each part lies in the same checked page window.
(in-package "ACL2")
(include-book "runs-overview-source-proof")
(local (include-book "runs-header-values-proof"))
(local (include-book "runs-restart-lookup-proof"))

(defmacro fn2-run-overview-id-layout () '(take 4 *fn2-overview-entry*))

(local
 (defthm fn2-run-overview-prefix-valid
   (implies (fn2-run-values-layoutp *fn2-overview-entry* row)
            (fn2-run-header-values-valid-p (fn2-run-overview-id-layout) (take 4 row)))
   :hints (("Goal" :use ((:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 0) (id 'group))
                         (:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 1) (id 'group-number))
                         (:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 2) (id 'article))
                         (:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 3) (id 'position)))
            :in-theory (e/d (take nth) (fn2-run-values-layoutp unsigned-byte-p))
            :expand ((:free (x) (take 4 x)) (:free (x) (take 3 x)) (:free (x) (take 2 x)) (:free (x) (take 1 x))
                     (:free (x) (nth 0 x)) (:free (x) (nth 1 x)) (:free (x) (nth 2 x)) (:free (x) (nth 3 x)))))))

(local
 (defthm fn2-run-encoding-with-tail
   (equal (fn2-layout-octets (append prefix suffix) row)
          (append (fn2-layout-octets prefix (take (len prefix) row))
                  (fn2-layout-octets suffix (nthcdr (len prefix) row))))
   :hints (("Goal" :induct (fn2-layout-octets prefix row)
            :in-theory (disable fn2-layout-field-octets)))))

(local
 (defthm fn2-run-line-wire
   (implies (true-listp (car tail))
            (equal (fn2-layout-octets '((line (:octets 1024))) tail)
                   (append (fn2-layout-varoctets (len (car tail))) (car tail))))
   :hints (("Goal" :in-theory (enable fn2-layout-octets fn2-layout-field-octets)))))

(local
 (defthm fn2-run-wire-append-size
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn2-run-line-after-ids
   (equal (car (nthcdr 4 row)) (nth 4 row))
   :hints (("Goal" :in-theory (enable nth nthcdr)
            :expand ((:free (x) (nthcdr 4 x)) (:free (x) (nthcdr 3 x)) (:free (x) (nthcdr 2 x)) (:free (x) (nthcdr 1 x))
                     (:free (x) (nth 4 x)) (:free (x) (nth 3 x)) (:free (x) (nth 2 x)) (:free (x) (nth 1 x)))))))

(local
 (defthm fn2-run-overview-wire-is-prefix-and-line
   (implies (true-listp (nth 4 row))
            (equal (fn2-layout-octets *fn2-overview-entry* row)
                   (append (fn2-layout-octets (fn2-run-overview-id-layout) (take 4 row))
                           (append (fn2-layout-varoctets (len (nth 4 row))) (nth 4 row)))))
   :hints (("Goal" :use ((:instance fn2-run-encoding-with-tail (prefix (fn2-run-overview-id-layout)) (suffix '((line (:octets 1024)))))
                         (:instance fn2-run-line-wire (tail (nthcdr 4 row))))
            :in-theory (disable fn2-run-line-wire fn2-layout-octets fn2-layout-varoctets binary-append nth nthcdr)))))

(defthm fn2-run-overview-stored-parts
  (let* ((layout (fn2-run-overview-id-layout)) (ids (take 4 row)) (line (nth 4 row))
         (prefix (fn2-layout-octets layout ids)) (hdr (fn2-layout-varoctets (len line)))
         (wire (fn2-layout-octets *fn2-overview-entry* row)) (at (+ off (len prefix))))
    (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row) (natp off)
                  (equal (fn2-run-read-bytes (len wire) slot gen off pk ps pg pool) wire))
             (and (fn2-run-values-layoutp layout ids) (true-listp line) (<= (len line) 1024)
                  (equal (len wire) (+ (len prefix) (len hdr) (len line)))
                  (equal (fn2-run-read-bytes (len prefix) slot gen off pk ps pg pool) prefix)
                  (equal (fn2-run-read-bytes (+ (len hdr) (len line)) slot gen at pk ps pg pool)
                         (append hdr line)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-overview-prefix-valid (:instance fn2-run-overview-admitted-row (values row)) fn2-run-admitted-line-fits-source
                 (:instance fn2-run-typed-header-has-canonical-encoding (layout (fn2-run-overview-id-layout)) (vals (take 4 row)))
                 (:instance fn2-run-read-stored-segments (at off)
                    (left (fn2-layout-octets (fn2-run-overview-id-layout) (take 4 row)))
                    (right (append (fn2-layout-varoctets (len (nth 4 row))) (nth 4 row)))))
           :in-theory (disable fn2-run-values-layoutp fn2-run-read-bytes fn2-layout-octets fn2-layout-varoctets
                                fn2-run-header-values-valid-p fn2-run-header-scalars-p fn-b3-octet-listp
                                binary-append))))
