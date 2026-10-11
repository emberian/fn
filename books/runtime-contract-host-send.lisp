; fn: what the host sends for an :out use is the lease's bytes (Builder A, the host lease).
;
; The host lease renders ARTICLE in place into a pool buffer the connection's instance holds as its workspace
; (option (b), settled with Builder C), and writes an :out use's range straight from the pool's octet array
; (fnn-transport-write-now over the array, no copy).  This book is the host's side of that write: under the
; abstract stobj's correspondence and the contract invariant, the array range the host writes for an
; outstanding :send/:pwrite/:bp-send use, [base(H)+OFF, +LEN), is exactly the use's window of the buffer's
; bytes.  That window is stable until the use's completion (books/runtime-contract.lisp
; fn-rtc-outstanding-use-is-stable).
(in-package "ACL2")
(include-book "runtime-contract-pool")

(local (defthm fn-rtchs-use-okp-of-member
  (implies (and (fn-rtc-uses-okp uses s) (member-equal u uses))
           (fn-rtc-use-okp u s))
  :hints (("Goal" :in-theory (disable fn-rtc-use-okp)))))
(local (defthm fn-rtchs-invp-uses-okp
  (implies (fn-rtc-invp s) (fn-rtc-uses-okp (fn-rtc-uses s) s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-invp) (theory 'minimal-theory))))))
(local (defun fn-rtchs-ind (k h n)
  (if (zp k) (list h n) (fn-rtchs-ind (- k 1) (+ 1 h) (- n 1)))))
(defthm fn-rtchs-get-of-c-pool
  (implies (and (natp k) (< k (nfix n)) (natp h))
           (equal (fn-rtc-get k (fn-rtc-c-pool h n cfg meta bytes))
                  (fn-rtc-c-buffer (+ h k) cfg meta bytes)))
  :hints (("Goal" :induct (fn-rtchs-ind k h n) :in-theory (disable fn-rtc-c-buffer))))
(local (defthm fn-rtchs-buf-base-natp (natp (fn-rtc-buf-base h cfg)) :rule-classes :type-prescription))
(local (defthm fn-rtchs-config-of-make (equal (fn-rtc-config (fn-rtc-make c sl p u m n)) c)
  :hints (("Goal" :in-theory (enable fn-rtc-config fn-rtc-make)))))
(defthm fn-rtchs-buffer-of-corr
  (implies (and (fn-rtc-st$corr c s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s))))
           (equal (fn-rtc-b-bytes (fn-rtc-buffer h s))
                  (fn-rtc-c-octets (fn-rtc-buf-base h (fn-rtc-config s))
                                   (nfix (fn-rtc-get 2 (nth h (nth *fn-rtc-c-metai* c))))
                                   (nth *fn-rtc-c-bytesi* c))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-st$corr fn-rtc-c-abs fn-rtc-c-buffer fn-rtc-b-bytes)
                                  (fn-rtc-c-octets fn-rtc-c-pool fn-rtc-st$cp fn-rtc-c-wfp fn-rtc-buf-base
                                   fn-rtc-nbufs fn-rtc-buffer))
           :use ((:instance fn-rtchs-get-of-c-pool (k h) (h 0) (n (fn-rtc-nbufs (nth *fn-rtc-c-cfg* c)))
                            (cfg (nth *fn-rtc-c-cfg* c)) (meta (nth *fn-rtc-c-metai* c))
                            (bytes (nth *fn-rtc-c-bytesi* c)))))))
(defthm fn-rtchs-out-use-in-range
  (implies (and (fn-rtc-use-okp u s)
                (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*)
                (fn-rtc-handlep (fn-rtc-u-hd u)))
           (let* ((hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)))
             (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                  (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                      (len (fn-rtc-b-bytes (fn-rtc-buffer h s)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp) (fn-rtc-buffer fn-rtc-b-bytes fn-rtc-nbufs fn-rtc-h-buf
                                                    fn-rtc-h-off fn-rtc-h-len fn-rtc-config fn-rtc-buf-cap
                                                    fn-rtc-holders fn-rtc-usep fn-rtc-current-p)))))
(defthm fn-rtchs-window-of-octets
  (implies (and (natp b) (natp off) (natp len) (<= (+ off len) (nfix fl)))
           (equal (take len (nthcdr off (fn-rtc-c-octets b fl arr)))
                  (fn-rtc-c-octets (+ b off) len arr)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-rtc-c-octets)
                  :expand ((:free (i x) (fn-rtc-c-octets i 0 x))))))
(defthm fn-rtc-host-send-range-is-the-lease
  (implies (and (fn-rtc-st$corr c s)
                (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*)
                (fn-rtc-handlep (fn-rtc-u-hd u)))
           (let* ((hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)))
             (equal (fn-rtc-c-octets (+ (fn-rtc-buf-base h (fn-rtc-config s)) (fn-rtc-h-off hd))
                                     (fn-rtc-h-len hd) (nth *fn-rtc-c-bytesi* c))
                    (take (fn-rtc-h-len hd)
                          (nthcdr (fn-rtc-h-off hd) (fn-rtc-b-bytes (fn-rtc-buffer h s)))))))
  :hints (("Goal" :in-theory (union-theories '((:type-prescription fn-rtc-h-buf) (:type-prescription fn-rtc-h-off)
                                               (:type-prescription fn-rtc-h-len) (:type-prescription fn-rtc-buf-base)
                                               (:type-prescription fn-rtc-c-octets) (:type-prescription fn-rtchs-buf-base-natp)
                                               fn-rtc-c-len-of-octets natp nfix)
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtchs-use-okp-of-member (uses (fn-rtc-uses s)))
                 fn-rtchs-invp-uses-okp
                 (:instance fn-rtchs-out-use-in-range)
                 (:instance fn-rtchs-buffer-of-corr (h (fn-rtc-h-buf (fn-rtc-u-hd u))))
                 (:instance fn-rtchs-window-of-octets
                            (b (fn-rtc-buf-base (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-config s)))
                            (off (fn-rtc-h-off (fn-rtc-u-hd u))) (len (fn-rtc-h-len (fn-rtc-u-hd u)))
                            (fl (nfix (fn-rtc-get 2 (nth (fn-rtc-h-buf (fn-rtc-u-hd u)) (nth *fn-rtc-c-metai* c)))))
                            (arr (nth *fn-rtc-c-bytesi* c)))))))

; -----------------------------------------------------------------------------
; HL3: the in-place render (puts into the instance's workspace) is the contract's :write request, so every
; contract keystone covers it.  The empty window is excluded: req-write rebuilds the state record, puts do not.
(defun fn-rtc-st$a-puts (h off w s)
  (declare (xargs :guard t))
  (if (consp w)
      (fn-rtc-st$a-puts h (+ 1 (nfix off)) (cdr w) (fn-rtc-st$a-put h off (car w) s))
    s))
(local (progn
(defthm fn-rtchl-get-of-set
  (equal (fn-rtc-get i (fn-rtc-set j v l))
         (if (and (equal (nfix i) (nfix j)) (< (nfix j) (len l))) v (fn-rtc-get i l))))
(defthm fn-rtchl-set-of-set
  (equal (fn-rtc-set j v2 (fn-rtc-set j v1 l)) (fn-rtc-set j v2 l)))
(defthm fn-rtchl-len-of-set (equal (len (fn-rtc-set j v l)) (len l)))
(defthm fn-rtchl-get-past-len (implies (<= (len l) (nfix i)) (equal (fn-rtc-get i l) nil)))
(defthm fn-rtchl-with-buffer-accessors
  (and (equal (fn-rtc-config (fn-rtc-with-buffer h b s)) (fn-rtc-config s))
       (equal (fn-rtc-uses (fn-rtc-with-buffer h b s)) (fn-rtc-uses s))
       (equal (fn-rtc-buffer k (fn-rtc-with-buffer h b s))
              (if (and (equal (nfix k) (nfix h)) (< (nfix h) (len (fn-rtc-pool s)))) b (fn-rtc-buffer k s)))
       (equal (fn-rtc-with-buffer h b2 (fn-rtc-with-buffer h b1 s)) (fn-rtc-with-buffer h b2 s)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer fn-rtc-config fn-rtc-uses fn-rtc-buffer fn-rtc-pool
                                     fn-rtc-make fn-rtc-slots fn-rtc-mstates fn-rtc-next-op))))
(defthm fn-rtchl-len-take (equal (len (take n l)) (nfix n)))
(defthm fn-rtchl-take-append-len
  (implies (and (true-listp a) (natp k))
           (equal (take (+ (len a) k) (append a b)) (append a (take k b)))))
(defthm fn-rtchl-nthcdr-append-len
  (implies (natp k)
           (equal (nthcdr (+ (len a) k) (append a b)) (nthcdr k b))))
(defthm fn-rtchl-nthcdr-nthcdr
  (implies (and (natp i) (natp j)) (equal (nthcdr i (nthcdr j l)) (nthcdr (+ i j) l))))
(defthm fn-rtchl-append-assoc (equal (append (append a b) c) (append a (append b c))))
(defthm fn-rtchl-true-listp-take (true-listp (take n l)))
(defthm fn-rtchl-take-len-tlf
  (implies (and (natp off) (<= off (len b)))
           (equal (len (take off (true-list-fix b))) off)))
(defthm fn-rtchl-take-1 (equal (take 1 (cons a b)) (list a)))
(defthm fn-rtchl-len-tlf (equal (len (true-list-fix x)) (len x)))
(defthm fn-rtchl-nthcdr-cons (implies (natp k) (equal (nthcdr (+ 1 k) (cons a x)) (nthcdr k x))))
(defthm fn-rtchl-splice-compose
  (implies (and (natp off) (<= off (len bytes)))
           (equal (fn-rtc-splice (fn-rtc-splice bytes off (list o)) (+ 1 off) rest)
                  (fn-rtc-splice bytes off (cons o rest))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice) (take nthcdr))
                  :use ((:instance fn-rtchl-take-append-len (a (take off (true-list-fix bytes))) (k 1)
                                   (b (cons o (nthcdr (+ 1 off) (true-list-fix bytes)))))
                        (:instance fn-rtchl-nthcdr-append-len (a (take off (true-list-fix bytes)))
                                   (k (+ 1 (len rest))) (b (cons o (nthcdr (+ 1 off) (true-list-fix bytes)))))))))
(defthm fn-rtchl-len-splice
  (implies (and (natp off) (<= off (len bytes)))
           (equal (len (fn-rtc-splice bytes off data))
                  (max (len bytes) (+ off (len data)))))
  :hints (("Goal" :in-theory (enable fn-rtc-splice))))
))
(defthm fn-rtc-puts-is-the-write-request
  (let ((b (fn-rtc-buffer h s)))
    (implies (and (consp w) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                  (equal (fn-rtc-b-owner b) (list :workspace id inc))
                  (natp g) (equal (fn-rtc-get 0 b) g)
                  (natp off) (<= off (len (fn-rtc-b-bytes b)))
                  (fn-cbor-octet-listp w)
                  (<= (+ off (len w)) (fn-rtc-buf-cap h (fn-rtc-config s))))
             (equal (fn-rtc-st$a-puts h off w s)
                    (mv-nth 0 (fn-rtc-req-write (list :write h g off w) id inc s)))))
  :hints (("Goal" :induct (fn-rtc-st$a-puts h off w s)
                  :in-theory (e/d (fn-rtc-st$a-put fn-rtc-st$a-splice fn-rtc-splice-okp fn-rtc-splice-target-p
                                   fn-rtc-req-write fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes)
                                  (fn-rtc-splice fn-rtc-with-buffer fn-rtc-buf-cap fn-rtc-nbufs fn-rtc-config
                                   fn-rtc-buffer fn-rtc-uses)))))

; HL1b: under the invariant, a buffer an outstanding :out use names is (:leased id inc :out), never a workspace and
; never the target of an :in use, so no splice (nor put, its one-octet case) changes it until the use completes.
(local (progn
(defthm fn-rtchs-out-use-owner
  (implies (and (fn-rtc-use-okp u s)
                (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*)
                (fn-rtc-handlep (fn-rtc-u-hd u)))
           (let ((o (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
             (and (eq (fn-rtc-get 0 o) :leased) (eq (fn-rtc-get 3 o) :out))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp) (fn-rtc-buffer fn-rtc-b-bytes fn-rtc-nbufs fn-rtc-h-buf
                                                    fn-rtc-h-off fn-rtc-h-len fn-rtc-config fn-rtc-buf-cap
                                                    fn-rtc-holders fn-rtc-usep fn-rtc-current-p)))))
(defthm fn-rtchs-in-use-owner
  (implies (and (fn-rtc-use-okp u s)
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (fn-rtc-handlep (fn-rtc-u-hd u)))
           (let ((o (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
             (and (eq (fn-rtc-get 0 o) :leased) (eq (fn-rtc-get 3 o) :in))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp) (fn-rtc-buffer fn-rtc-b-bytes fn-rtc-nbufs fn-rtc-h-buf
                                                    fn-rtc-h-off fn-rtc-h-len fn-rtc-config fn-rtc-buf-cap
                                                    fn-rtc-holders fn-rtc-usep fn-rtc-current-p)))))
(defthm fn-rtchs-in-use-on-means-in-lease
  (implies (and (fn-rtc-uses-okp uses2 s) (fn-rtc-in-use-on-p h uses2))
           (let ((o (fn-rtc-b-owner (fn-rtc-buffer h s))))
             (and (eq (fn-rtc-get 0 o) :leased) (eq (fn-rtc-get 3 o) :in))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-rtc-in-use-on-p h uses2)
                  :in-theory (disable fn-rtc-use-okp fn-rtc-buffer fn-rtc-b-owner fn-rtc-h-buf fn-rtc-u-hd
                                      fn-rtc-handlep))
          ("Subgoal *1/1" :use ((:instance fn-rtchs-in-use-owner (u (car uses2)))))))
))
(defthm fn-hl-splice-keeps-out-use-bytes
  (implies (and (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*)
                (fn-rtc-handlep (fn-rtc-u-hd u)))
           (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-st$a-splice h2 off data s))
                  (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-st$a-splice fn-rtc-splice-okp fn-rtc-splice-target-p)
                                  (fn-rtc-invp fn-rtc-use-okp fn-rtc-in-use-on-p fn-rtc-splice fn-rtc-buffer
                                   fn-rtc-b-owner fn-rtc-h-buf fn-rtc-u-hd fn-rtc-handlep))
           :use ((:instance fn-rtchs-use-okp-of-member (uses (fn-rtc-uses s)))
                 fn-rtchs-invp-uses-okp
                 fn-rtchs-out-use-owner
                 (:instance fn-rtchs-in-use-on-means-in-lease (h h2) (uses2 (fn-rtc-uses s)))))))
