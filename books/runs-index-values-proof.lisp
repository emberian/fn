; A parent index row assembled from a child key, address and digest has
; the canonical encoding accepted by the page reader.
(in-package "ACL2")
(include-book "runs-child-reference-values-proof")
(include-book "runs-header-varint-parse-proof")

(local
 (defun fn2-run-index-digest-walk (body pos next)
   (if (atom body) (list pos next)
     (fn2-run-index-digest-walk (cdr body) (+ 1 (nfix pos)) (+ 1 (nfix next))))))

(local (defthm fn2-run-index-empty-prefix
         (implies (equal (len a) 0) (equal (append a b) b))))

(local
 (defthm fn2-run-index-parse-digest-body
   (implies (and (consp body) (natp pos) (natp next) (equal (+ pos (len body)) 32))
            (equal (fn2-layout-parse-field :digest bytes (append body suffix) pos 1 0 32 ref 1 next)
                   (list :ok (cons 1 (take 32 (nthcdr ref bytes))) suffix)))
   :hints (("Goal" :induct (fn2-run-index-digest-walk body pos next)
            :expand ((:free (b r p n) (fn2-layout-parse-field :digest bytes (cons b r) p 1 0 32 ref 1 n)))
            :in-theory (e/d (fn2-layout-byte) (fn2-layout-parse-field take nthcdr))))))

(local
 (defthm fn2-run-take-digest-prefix
   (implies (and (true-listp a) (equal n (len a))) (equal (take n (append a b)) a))
   :hints (("Goal" :induct (len a)))))

(local (defthm fn2-run-index-digest-proper-list (implies (fn-b3-octet-listp x) (true-listp x))))

(local
 (defthm fn2-run-index-parse-digest
   (implies (and (fn-b3-octet-listp body) (equal (len body) 32))
            (equal (fn2-layout-parse-field :digest (cons 1 (append body suffix)) (cons 1 (append body suffix)) 0 0 0 0 0 0 0)
                   (list :ok (cons 1 body) suffix)))
   :hints (("Goal" :do-not-induct t :cases ((consp body))
            :use ((:instance fn2-run-take-digest-prefix (n 32) (a body) (b suffix))
                  (:instance fn2-run-index-parse-digest-body (pos 0) (bytes (cons 1 (append body suffix))) (ref 1) (next 1)))
            :expand ((:free (bs) (fn2-layout-parse-field :digest bs (cons 1 (append body suffix)) 0 0 0 0 0 0 0)))
            :in-theory (e/d (fn2-layout-byte) (fn2-layout-parse-field binary-append))))))

(local
 (defun fn2-run-index-value-valid-p (kind v)
   (declare (xargs :verify-guards nil))
   (case (fn2-layout-kind-code kind)
     ((5 8) (unsigned-byte-p 60 v))
     (9 (and (unsigned-byte-p 8 v) (< v (len (caddr kind)))))
     (7 (and (equal kind :digest) (consp v) (equal (car v) 1) (fn-b3-octet-listp (cdr v)) (equal (len (cdr v)) 32)))
     (otherwise nil))))

(local
 (defthm fn2-run-index-field-and-tail
   (let ((bytes (append (fn2-layout-field-octets kind v) suffix)))
     (implies (fn2-run-index-value-valid-p kind v)
              (equal (fn2-layout-parse-field kind bytes bytes 0 0 0 0 0 0 0) (list :ok v suffix))))
   :hints (("Goal" :do-not-induct t :cases ((equal kind :digest) (equal (fn2-layout-kind-code kind) 9))
            :use ((:instance fn2-run-parse-header-varint (k kind) (n v) (bytes (append (fn2-layout-varoctets v) suffix)))
                  (:instance fn2-run-index-parse-digest (body (cdr v))))
            :expand ((append v suffix) (append (list v) suffix) (:free (input) (fn2-layout-parse-field kind input (cons v suffix) 0 0 0 0 0 0 0)))
            :in-theory (e/d (fn2-layout-field-octets fn2-layout-byte)
                         (fn2-layout-parse-field fn2-layout-varoctets fn2-layout-kind-code binary-append fn-b3-octet-listp))))))

(local
 (defun fn2-run-index-values-valid-p (layout vals)
   (declare (xargs :verify-guards nil))
   (if (atom layout) (null vals)
     (and (consp vals) (fn2-run-index-value-valid-p (cadar layout) (car vals))
          (fn2-run-index-values-valid-p (cdr layout) (cdr vals))))))

(local
 (defthm fn2-run-index-values-parse
   (implies (fn2-run-index-values-valid-p layout vals)
            (equal (fn2-layout-parse layout (fn2-layout-octets layout vals)) (list :ok vals nil)))
   :hints (("Goal" :induct (fn2-run-index-values-valid-p layout vals)
            :expand ((fn2-layout-octets layout vals) (:free (bytes) (fn2-layout-parse layout bytes)))
            :in-theory (disable fn2-run-index-value-valid-p fn2-layout-parse-field fn2-layout-field-octets binary-append)))))

(local (defthm fn2-run-index-varint-bytes (implies (natp v) (fn-b3-octet-listp (fn2-layout-varoctets v)))
         :hints (("Goal" :induct (fn2-layout-varoctets v)))))
(local (defthm fn2-run-index-octet-list-append
         (implies (and (fn-b3-octet-listp a) (fn-b3-octet-listp b)) (fn-b3-octet-listp (append a b)))))
(local
 (defthm fn2-run-index-value-octets
   (implies (fn2-run-index-value-valid-p k v) (fn-b3-octet-listp (fn2-layout-field-octets k v)))
   :hints (("Goal" :in-theory (e/d (fn2-layout-field-octets) (fn2-layout-varoctets fn2-layout-kind-code))))))
(local
 (defthm fn2-run-index-values-octets
   (implies (fn2-run-index-values-valid-p layout vals) (fn-b3-octet-listp (fn2-layout-octets layout vals)))
   :hints (("Goal" :induct (fn2-run-index-values-valid-p layout vals)
            :in-theory (disable fn2-layout-field-octets fn2-run-index-value-valid-p binary-append fn-b3-octet-listp)))))

(local
 (defthm fn2-run-index-digest-bytes
   (let ((bytes (fn2-page-parent-octets k n words)))
     (and (fn-b3-octet-listp bytes) (equal (len bytes) (nfix n))))
   :hints (("Goal" :induct (fn2-page-parent-octets k n words)
            :in-theory (e/d (fn2-page-parent-octets) (fn2-fc-word-byte mod floor nth))))))

(defthmd fn2-run-child-row-has-canonical-encoding
  (let ((row (fn2-run-overview-child-row key w hrow writers ds)))
    (implies (and (unsigned-byte-p 60 (car key)) (unsigned-byte-p 60 (cadr key))
                  (fn2-run-writersp writers) (fn2-run-writers-wfp writers) (natp w) (< w (fn2-run-writers-rows writers))
                  (< (fn2-run-writers-page-kind w writers) (len (caddr *fn2-format-page-kind*))))
             (fn2-run-values-layoutp *fn2-overview-index* row)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-run-overview-child-row fn2-run-values-layoutp)
                         (fn2-layout-parse fn2-layout-octets fn2-digest-list fn2-page-parent-octets
                          fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows fn2-run-writers-page-kind
                          fn2-run-writers-unit fn2-run-writers-counter fn2-run-writers-entries fn2-run-writers-epoch)))))
