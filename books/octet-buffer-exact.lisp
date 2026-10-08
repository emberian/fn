; Exact-capacity octet buffers for charged ownership. Unlike scratch buffers,
; no spare capacity survives clear, and logical length is allocated octets.
(in-package "ACL2")
(include-book "octets-stobj")

(defstobj fn-obe$c
  (fn-obe$c-bytes :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  :inline t)
(defun fn-obe$ap (x) (declare (xargs :guard t)) (fn-cbor-octet-listp x))
(defun create-fn-obe$a () (declare (xargs :guard t)) nil)
(defun fn-obe$a-len (x) (declare (xargs :guard (fn-obe$ap x))) (len x))
(defun fn-obe$a-get (i x)
  (declare (xargs :guard (and (fn-obe$ap x) (natp i) (< i (fn-obe$a-len x))))) (nth i x))
(defun fn-obe$a-put (i v x)
  (declare (xargs :guard (and (fn-obe$ap x) (natp i) (< i (fn-obe$a-len x)) (fn-cbor-octetp v))))
  (update-nth i v x))
(defun fn-obe$a-clear (x) (declare (xargs :guard (fn-obe$ap x)) (ignore x)) nil)
(defun fn-obe$a-resize (n x)
  (declare (xargs :guard (and (fn-obe$ap x) (natp n)))) (resize-list x n 0))
(defun fn-obe$c-len (fn-obe$c) (declare (xargs :stobjs fn-obe$c)) (fn-obe$c-bytes-length fn-obe$c))
(defun fn-obe$c-get (i fn-obe$c)
  (declare (xargs :stobjs fn-obe$c :guard (and (natp i) (< i (fn-obe$c-bytes-length fn-obe$c)))))
  (fn-obe$c-bytesi i fn-obe$c))
(defun fn-obe$c-put (i v fn-obe$c)
  (declare (xargs :stobjs fn-obe$c :guard (and (natp i) (< i (fn-obe$c-bytes-length fn-obe$c)) (fn-cbor-octetp v))
                  :guard-hints (("Goal" :in-theory (enable fn-cbor-octetp)))))
  (update-fn-obe$c-bytesi i v fn-obe$c))
(defun fn-obe$c-clear (fn-obe$c)
  (declare (xargs :stobjs fn-obe$c)) (resize-fn-obe$c-bytes 0 fn-obe$c))
(defun fn-obe$c-resize (n fn-obe$c)
  (declare (xargs :stobjs fn-obe$c :guard (natp n))) (resize-fn-obe$c-bytes n fn-obe$c))
(defun fn-obe$corr (c a)
  (declare (xargs :guard t)) (and (fn-obe$cp c) (equal (nth 0 c) a)))

(defthm fn-obe-bytesp-is-octets
  (equal (fn-obe$c-bytesp x) (fn-cbor-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-obe$c-bytesp fn-cbor-octet-listp fn-cbor-octetp))))

(defthm fn-obe-octet-list-update
  (implies (and (fn-cbor-octet-listp x) (natp i) (< i (fn-obe$a-len x)) (fn-cbor-octetp v))
           (fn-cbor-octet-listp (update-nth i v x))))
(defthm fn-obe-octet-list-resize
  (implies (and (fn-cbor-octet-listp x) (natp n))
           (fn-cbor-octet-listp (resize-list x n 0))))

(defthm create-fn-obe{correspondence} (fn-obe$corr (create-fn-obe$c) (create-fn-obe$a)))
(defthm create-fn-obe{preserved} (fn-obe$ap (create-fn-obe$a)))
(defthm fn-obe-len{correspondence}
  (implies (and (fn-obe$corr c a) (fn-obe$ap a)) (equal (fn-obe$c-len c) (fn-obe$a-len a))))
(defthm fn-obe-get{correspondence}
  (implies (and (fn-obe$corr c a) (fn-obe$ap a) (natp i) (< i (fn-obe$a-len a)))
           (equal (fn-obe$c-get i c) (fn-obe$a-get i a))))
(defthm fn-obe-get{guard-thm}
  (implies (and (fn-obe$corr c a) (fn-obe$ap a) (natp i) (< i (fn-obe$a-len a)))
           (and (natp i) (< i (fn-obe$c-bytes-length c)))))
(defthm fn-obe-put{correspondence}
  (implies (and (fn-obe$corr c a) (fn-obe$ap a) (natp i) (< i (fn-obe$a-len a)) (fn-cbor-octetp v))
           (fn-obe$corr (fn-obe$c-put i v c) (fn-obe$a-put i v a))))
(defthm fn-obe-put{guard-thm}
  (implies (and (fn-obe$corr c a) (fn-obe$ap a) (natp i) (< i (fn-obe$a-len a)) (fn-cbor-octetp v))
           (and (natp i) (< i (fn-obe$c-bytes-length c)) (fn-cbor-octetp v))))
(defthm fn-obe-put{preserved}
  (implies (and (fn-obe$ap a) (natp i) (< i (fn-obe$a-len a)) (fn-cbor-octetp v))
           (fn-obe$ap (fn-obe$a-put i v a))))
(defthm fn-obe-clear{correspondence}
  (implies (and (fn-obe$corr c a) (fn-obe$ap a))
           (fn-obe$corr (fn-obe$c-clear c) (fn-obe$a-clear a))))
(defthm fn-obe-clear{preserved}
  (implies (fn-obe$ap a) (fn-obe$ap (fn-obe$a-clear a))))
(defthm fn-obe-resize{correspondence}
  (implies (and (fn-obe$corr c a) (fn-obe$ap a) (natp n))
           (fn-obe$corr (fn-obe$c-resize n c) (fn-obe$a-resize n a))))
(defthm fn-obe-resize{preserved}
  (implies (and (fn-obe$ap a) (natp n)) (fn-obe$ap (fn-obe$a-resize n a))))

(defabsstobj fn-obe
  :foundation fn-obe$c
  :recognizer (fn-obe-p :logic fn-obe$ap :exec fn-obe$cp)
  :creator (create-fn-obe :logic create-fn-obe$a :exec create-fn-obe$c)
  :corr-fn fn-obe$corr
  :exports ((fn-obe-len :logic fn-obe$a-len :exec fn-obe$c-len)
            (fn-obe-get :logic fn-obe$a-get :exec fn-obe$c-get)
            (fn-obe-put :logic fn-obe$a-put :exec fn-obe$c-put :protect t)
            (fn-obe-clear :logic fn-obe$a-clear :exec fn-obe$c-clear :protect t)
            (fn-obe-resize :logic fn-obe$a-resize :exec fn-obe$c-resize :protect t)))

; These name allocated array octets, not the allocator's total heap footprint.
(defthm fn-obe-correspondence-counts-allocated-octets
  (implies (fn-obe$corr c a) (equal (fn-obe$c-bytes-length c) (len a))))
(defthm fn-obe-clear-releases-the-array
  (equal (fn-obe$c-bytes-length (fn-obe$c-clear c)) 0))
