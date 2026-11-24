; Hashing an addressed byte span depends on the backing octets. Changing
; the descriptors through which those octets are reached preserves the hash.
(in-package "ACL2")
(include-book "blake3")

(defun-nx fn2-pool-same-bytes-p (a b)
  (equal (nth *fn2-pool-datai* a) (nth *fn2-pool-datai* b)))

(defequiv fn2-pool-same-bytes-p)

(local
 (defcong fn2-pool-same-bytes-p equal (fn2-pool-datai off pool) 2
   :hints (("Goal" :in-theory (enable fn2-pool-datai fn2-pool-same-bytes-p)))))

(local (in-theory (disable fn2-pool-same-bytes-p fn2-pool-datai fn-b3-compress-core fn-b3-word mv-nth)))

(local
 (defmacro fn2-b3-storage-congruence (call &optional induct)
   `(defcong fn2-pool-same-bytes-p equal ,call ,(len (cdr call))
      :hints (("Goal" :do-not '(preprocess) ,@(and induct (list :induct call))
               :in-theory (enable ,(car call)))))))

(local (fn2-b3-storage-congruence (fn-b3-pool-word off pool)))
(local (fn2-b3-storage-congruence (fn-b3-pool-blocks off counter count j c0 c1 c2 c3 c4 c5 c6 c7 pool) t))
(local (fn2-b3-storage-congruence (fn-b3-pool-tree off chunks counter pool) t))
(local (fn2-b3-storage-congruence (fn2-b3-subtree-cv-into dst off len counter ds pool)))
(local (fn2-b3-storage-congruence (fn2-b3-pool-message row off i b3 pool) t))
(local (fn2-b3-storage-congruence (fn2-b3-chunk-output-into row off counter ds b3 pool)))
(local (fn2-b3-storage-congruence (fn2-b3-bulk row off len counter lastp ds b3 pool)))

(defcong fn2-pool-same-bytes-p equal (fn2-b3-span row off counter lastp ds b3 pool) 7
  :hints (("Goal" :do-not '(preprocess) :in-theory (enable fn2-b3-span))))

(defcong fn2-pool-same-bytes-p equal (fn2-b3-fragment-into row off n ds b3 pool) 6
  :hints (("Goal" :do-not '(preprocess) :induct (fn2-b3-fragment-into row off n ds b3 pool)
           :in-theory (enable fn2-b3-fragment-into))))
