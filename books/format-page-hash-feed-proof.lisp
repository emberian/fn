(in-package "ACL2")
(include-book "format-page-hash-span-proof")

(local (in-theory (current-theory 'fc-drop-cdr)))

(defun-nx fn2-hash-page-windowp (pool)
  (and (equal (fn2-pool-readable-code 0 1 9 0 1 pool) :ok)
       (equal (fn2-pool-base 0 pool) 0)
       (<= 65536 (fn2-pool-fill 0 pool))
       (<= 65536 (fn2-pool-data-length pool))))

(defthmd fn2-hash-page-window-read
  (implies (and (fn2-hash-page-windowp pool) (natp off) (< off 65536))
           (equal (fn2-b3-read 0 1 off 9 0 1 pool) (list :ok (fn2-pool-datai off pool))))
  :hints (("Goal" :in-theory (e/d (fn2-hash-page-windowp fn2-b3-read fn2-pool-read)
                                   (fn2-pool-readable-code fn2-pool-base fn2-pool-fill fn2-pool-data-length)))))

(defthmd fn2-hash-page-window-base
  (implies (fn2-hash-page-windowp pool) (equal (fn2-pool-slot-base 0 pool) 0))
  :hints (("Goal" :in-theory (enable fn2-hash-page-windowp fn2-pool-slot-base))))

(local (in-theory (disable fn2-hash-page-windowp)))

(defun-nx fn2-page-feed-induct (bytes off consumed ds b3 pool)
  (declare (xargs :measure (len bytes)))
  (cond ((atom bytes) (list off consumed ds b3))
        ((or (not (fn2-b3-roomp 0 b3)) (>= off 4294967295) (>= consumed 4096)) nil)
        ((and (<= 1024 (len bytes))
              (fn2-b3-can-span 0 0 1 off (len bytes) consumed 9 0 1 b3 pool))
         (let ((r (fn2-b3-span 0 off (fn2-b3-next-counter 0 b3) (< (len bytes) 2048) ds b3 pool)))
           (fn2-page-feed-induct (fn-b3-nthcdrx 1024 bytes) (+ off 1024) (+ consumed 1024)
                           (mv-nth 0 r) (mv-nth 1 r) pool)))
        (t (let ((r (fn2-b3-byte 0 (car bytes) ds b3)))
             (fn2-page-feed-induct (cdr bytes) (1+ off) (1+ consumed) (mv-nth 0 r) (mv-nth 1 r) pool)))))
(defthm fn2-page-feed-consumes-octets
  (implies (and (fc-g (append bytes rest) ans ds b3)
                (fn2-b3-covers bytes off pool) (fn-b3-octet-listp bytes) (fn-b3-octet-listp rest)
                (natp off) (natp consumed) (<= (+ off (len bytes)) 65536) (fn2-hash-page-windowp pool))
   (let* ((r (fn2-b3-feed 0 0 1 off (len bytes) consumed 9 0 1 ds b3 pool))
          (k (- (mv-nth 1 r) consumed)))
     (and (natp k) (<= k (len bytes))
          (fc-g (append (fn-b3-nthcdrx k bytes) rest) ans (mv-nth 2 r) (mv-nth 3 r)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-page-feed-induct bytes off consumed ds b3 pool)
              :expand ((:free (left) (fn2-b3-feed 0 0 1 off left consumed 9 0 1 ds b3 pool)))
              :do-not '(generalize eliminate-destructors))
          ("Subgoal *1/4" :use ((:instance fc-g-byte (b (car bytes)) (xs (append (cdr bytes) rest)))
                          fn2-hash-page-window-read
                          (:instance fn2-b3-covers-head (xs bytes) (fn2-pool pool))
                          (:instance fn2-b3-can-span-bounds (row 0) (slot 0) (gen 1) (left (len bytes))
                             (okind 9) (oslot 0) (ogen 1) (fn2-b3 b3) (fn2-pool pool)))
           :expand ((append bytes rest) (:free (left) (fn2-b3-feed 0 0 1 off left consumed 9 0 1 ds b3 pool))))
          ("Subgoal *1/3" :use (fn2-page-span-consumes-chunk
                          (:instance fn2-b3-covers-drop (xs bytes) (n 1024) (fn2-pool pool))
                          fn2-hash-page-window-base)
           :expand ((:free (left) (fn2-b3-feed 0 0 1 off left consumed 9 0 1 ds b3 pool))))))
