(in-package "ACL2")
(include-book "format-page-hash-feed-proof")

(local (in-theory (current-theory 'fc-g-update)))

(defthm fn2-page-update-consumes-octets
  (implies (and (fc-g (append bytes rest) ans ds b3)
                (fn2-b3-covers bytes off pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest)
                (natp off) (<= (len bytes) 4096) (<= (+ off (len bytes)) 65536) (fn2-hash-page-windowp pool))
   (let* ((r (fn2-b3-update 0 0 1 off (len bytes) 9 0 1 ds b3 pool)) (k (mv-nth 1 r)))
     (and (natp k) (<= k (len bytes))
          (fc-g (append (fn-b3-nthcdrx k bytes) rest) ans (mv-nth 2 r) (mv-nth 3 r)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fc-g-fragment (bytes (fn-b3-firstn (fn2-b3-fragment-count 0 0 1 off (len bytes) 9 0 1 b3 pool) bytes))
             (rest (append (fn-b3-nthcdrx (fn2-b3-fragment-count 0 0 1 off (len bytes) 9 0 1 b3 pool) bytes) rest)))
          (:instance fn2-page-feed-consumes-octets (bytes (fn-b3-nthcdrx (fn2-b3-fragment-count 0 0 1 off (len bytes) 9 0 1 b3 pool) bytes))
             (off (+ off (fn2-b3-fragment-count 0 0 1 off (len bytes) 9 0 1 b3 pool)))
             (consumed (fn2-b3-fragment-count 0 0 1 off (len bytes) 9 0 1 b3 pool))
             (ds (mv-nth 0 (fn2-b3-fragment-into 0 off (fn2-b3-fragment-count 0 0 1 off (len bytes) 9 0 1 b3 pool) ds b3 pool)))
             (b3 (mv-nth 1 (fn2-b3-fragment-into 0 off (fn2-b3-fragment-count 0 0 1 off (len bytes) 9 0 1 b3 pool) ds b3 pool))))
          (:instance fn2-page-feed-consumes-octets (off off) (consumed 0))
          (:instance fn2-b3-covers-drop (xs bytes) (n (fn2-b3-fragment-count 0 0 1 off (len bytes) 9 0 1 b3 pool)) (fn2-pool pool))
          fn2-hash-page-window-base)
    :in-theory (e/d (fn2-b3-update min) (fc-g-fragment)))))
