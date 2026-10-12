(in-package "ACL2")
(include-book "def-span-scan")
(include-book "nntp-syntax")
(include-book "runtime-contract-host-send")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-dsw-view (h base j s)
  (declare (xargs :guard (and (fn-rtc-st$ap s) (natp base) (natp j) (<= base j)) :verify-guards nil))
  (take (- j base) (nthcdr base (fn-rtc-b-bytes (fn-rtc-buffer h s)))))

(defun fn-dsw-roomp (h j m fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard t))
  (let ((cfg (fn-rtc-st-config fn-rtc-st)))
    (and (natp h) (< h (fn-rtc-nbufs cfg))
         (fn-rtc-splice-target-p h (fn-rtc-st-owner h fn-rtc-st) (fn-rtc-st-uses fn-rtc-st))
         (natp j) (<= j (fn-rtc-st-fill h fn-rtc-st))
         (<= (+ j (nfix m)) (fn-rtc-buf-cap h cfg)))))

(local (progn
(defthm fn-dsw-get-of-set
  (equal (fn-rtc-get i (fn-rtc-set j v l))
         (if (and (equal (nfix i) (nfix j)) (< (nfix j) (len l))) v (fn-rtc-get i l))))
(defthm fn-dsw-set-of-set
  (equal (fn-rtc-set j v2 (fn-rtc-set j v1 l)) (fn-rtc-set j v2 l)))
(defthm fn-dsw-len-of-set (equal (len (fn-rtc-set j v l)) (len l)))
(defthm fn-dsw-get-past-len (implies (<= (len l) (nfix i)) (equal (fn-rtc-get i l) nil)))
(defthm fn-dsw-with-buffer-accessors
  (and (equal (fn-rtc-config (fn-rtc-with-buffer h b s)) (fn-rtc-config s))
       (equal (fn-rtc-uses (fn-rtc-with-buffer h b s)) (fn-rtc-uses s))
       (equal (fn-rtc-buffer k (fn-rtc-with-buffer h b s))
              (if (and (equal (nfix k) (nfix h)) (< (nfix h) (len (fn-rtc-pool s)))) b (fn-rtc-buffer k s)))
       (equal (fn-rtc-with-buffer h b2 (fn-rtc-with-buffer h b1 s)) (fn-rtc-with-buffer h b2 s)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer fn-rtc-config fn-rtc-uses fn-rtc-buffer fn-rtc-pool
                                     fn-rtc-make fn-rtc-slots fn-rtc-mstates fn-rtc-next-op))))
(defthm fn-dsw-len-take (equal (len (take n l)) (nfix n)))
(defthm fn-dsw-take-append-len
  (implies (and (true-listp a) (natp k))
           (equal (take (+ (len a) k) (append a b)) (append a (take k b)))))
(defthm fn-dsw-nthcdr-append-len
  (implies (natp k)
           (equal (nthcdr (+ (len a) k) (append a b)) (nthcdr k b))))
(defthm fn-dsw-nthcdr-nthcdr
  (implies (and (natp i) (natp j)) (equal (nthcdr i (nthcdr j l)) (nthcdr (+ i j) l))))
(defthm fn-dsw-append-assoc (equal (append (append a b) c) (append a (append b c))))
(defthm fn-dsw-true-listp-take (true-listp (take n l)))
(defthm fn-dsw-take-len-tlf
  (implies (and (natp off) (<= off (len b)))
           (equal (len (take off (true-list-fix b))) off)))
(defthm fn-dsw-take-1 (equal (take 1 (cons a b)) (list a)))
(defthm fn-dsw-len-tlf (equal (len (true-list-fix x)) (len x)))
(defthm fn-dsw-nthcdr-cons (implies (natp k) (equal (nthcdr (+ 1 k) (cons a x)) (nthcdr k x))))
(defthm fn-dsw-splice-compose
  (implies (and (natp off) (<= off (len bytes)))
           (equal (fn-rtc-splice (fn-rtc-splice bytes off (list o)) (+ 1 off) rest)
                  (fn-rtc-splice bytes off (cons o rest))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice) (take nthcdr))
                  :use ((:instance fn-dsw-take-append-len (a (take off (true-list-fix bytes))) (k 1)
                                   (b (cons o (nthcdr (+ 1 off) (true-list-fix bytes)))))
                        (:instance fn-dsw-nthcdr-append-len (a (take off (true-list-fix bytes)))
                                   (k (+ 1 (len rest))) (b (cons o (nthcdr (+ 1 off) (true-list-fix bytes)))))))))
(defthm fn-dsw-len-splice
  (implies (and (natp off) (<= off (len bytes)))
           (equal (len (fn-rtc-splice bytes off data))
                  (max (len bytes) (+ off (len data)))))
  :hints (("Goal" :in-theory (enable fn-rtc-splice))))
))

(defun fn-dsw-append-loop (h j octets fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (natp j) :verify-guards nil))
  (if (consp octets)
      (let ((fn-rtc-st (fn-rtc-st-put h j (car octets) fn-rtc-st)))
        (fn-dsw-append-loop h (+ 1 j) (cdr octets) fn-rtc-st))
    fn-rtc-st))

(defun fn-dsw-append (h j octets fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard t :verify-guards nil))
  (if (and (fn-cbor-octet-listp octets) (fn-dsw-roomp h j (len octets) fn-rtc-st))
      (let ((fn-rtc-st (fn-dsw-append-loop h j octets fn-rtc-st)))
        (mv :done (+ j (len octets)) fn-rtc-st))
    (mv :refused j fn-rtc-st)))

(defun fn-dsw-copy-loop (h i end j fn-octets fn-rtc-st)
  (declare (xargs :stobjs (fn-octets fn-rtc-st) :verify-guards nil
                  :guard (and (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets)) (natp j))
                  :measure (nfix (- (nfix end) (nfix i)))))
  (if (and (natp i) (natp end) (< i end))
      (let ((fn-rtc-st (fn-rtc-st-put h j (fn-dss-copy-f (fn-octets-get i fn-octets)) fn-rtc-st)))
        (fn-dsw-copy-loop h (+ 1 i) end (+ 1 j) fn-octets fn-rtc-st))
    fn-rtc-st))

(defun fn-dsw-copy (h i end j fn-octets fn-rtc-st)
  (declare (xargs :stobjs (fn-octets fn-rtc-st) :verify-guards nil
                  :guard (and (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets)))))
  (mbe :logic (fn-dsw-append h j (fn-dss-copy-list (fn-oct-slice-list i end fn-octets)) fn-rtc-st)
       :exec (if (fn-dsw-roomp h j (- end i) fn-rtc-st)
                 (let ((fn-rtc-st (fn-dsw-copy-loop h i end j fn-octets fn-rtc-st)))
                   (mv :done (+ j (- end i)) fn-rtc-st))
               (mv :refused j fn-rtc-st))))

(defun fn-dsw-string-loop (h i end j dss-str fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (stringp dss-str) (natp i) (natp end) (<= i end) (<= end (length dss-str)) (natp j))
                  :measure (nfix (- (nfix end) (nfix i)))))
  (if (and (natp i) (natp end) (< i end))
      (let ((fn-rtc-st (fn-rtc-st-put h j (fn-dss-copy-f (char-code (char dss-str i))) fn-rtc-st)))
        (fn-dsw-string-loop h (+ 1 i) end (+ 1 j) dss-str fn-rtc-st))
    fn-rtc-st))

(defun fn-dsw-copy-string (h i end j dss-str fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (stringp dss-str) (natp i) (natp end) (<= i end) (<= end (length dss-str)))))
  (mbe :logic (fn-dsw-append h j (fn-dss-copy-list (non-exec (fn-oct-slice-list i end (fn-nntp-string-octets dss-str)))) fn-rtc-st)
       :exec (if (fn-dsw-roomp h j (- end i) fn-rtc-st)
                 (let ((fn-rtc-st (fn-dsw-string-loop h i end j dss-str fn-rtc-st)))
                   (mv :done (+ j (- end i)) fn-rtc-st))
               (mv :refused j fn-rtc-st))))

(defun fn-dsw-decimal-count (n)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (natp n) (if (< n 10) 1 (+ 1 (fn-dsw-decimal-count (floor n 10)))) 0))

(defun fn-dsw-decimal-loop (h end n fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil
                  :guard (and (natp n) (natp end) (<= (fn-dsw-decimal-count n) end))
                  :ruler-extenders :all
                  :measure (nfix n)))
  (if (not (natp n)) fn-rtc-st
    (let ((fn-rtc-st (if (< n 10) fn-rtc-st
                      (fn-dsw-decimal-loop h (- end 1) (floor n 10) fn-rtc-st))))
      (fn-rtc-st-put h (- end 1) (+ 48 (mod n 10)) fn-rtc-st))))

(defun fn-dsw-decimal (h j n fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard t :verify-guards nil))
  (mbe :logic (fn-dsw-append h j (fn-nntp-decimal n) fn-rtc-st)
       :exec (let ((m (fn-dsw-decimal-count n)))
               (if (fn-dsw-roomp h j m fn-rtc-st)
                   (let ((fn-rtc-st (if (natp n) (fn-dsw-decimal-loop h (+ j m) n fn-rtc-st) fn-rtc-st)))
                     (mv :done (+ j m) fn-rtc-st))
                 (mv :refused j fn-rtc-st)))))

























; ---- Window proof package
(local (defthm fn-dsw-roomp-is-length-check
  (equal (and (fn-cbor-octet-listp data) (fn-dsw-roomp h j (len data) s))
         (fn-rtc-splice-okp h j data s))
  :hints (("Goal" :in-theory (enable fn-dsw-roomp fn-rtc-splice-okp
                                    fn-rtc-st$a-config fn-rtc-st$a-owner fn-rtc-st$a-uses fn-rtc-st$a-fill fn-rtc-bytes)))))

(local (defthm fn-dsw-set-original
  (implies (true-listp l) (equal (fn-rtc-set i (fn-rtc-get i l) l) l))
  :hints (("Goal" :induct (fn-rtc-set i (fn-rtc-get i l) l)))))

(local (defthm fn-dsw-state-rebuild
  (implies (fn-rtc-st$ap s)
    (equal (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-pool s)
                        (fn-rtc-uses s) (fn-rtc-mstates s) (fn-rtc-next-op s)) s))
  :hints (("Goal" :expand ((len s) (len (cdr s)) (len (cddr s)) (len (cdddr s))
                            (len (cddddr s)) (len (cdr (cddddr s))))
           :in-theory (enable fn-rtc-st$ap fn-rtc-shapep fn-rtc-get fn-rtc-make
                                    fn-rtc-config fn-rtc-slots fn-rtc-pool fn-rtc-uses fn-rtc-mstates fn-rtc-next-op)))))

(local (defthm fn-dsw-buffer-rebuild
  (implies (and (true-listp b) (equal (len b) 3))
    (equal (list (fn-rtc-get 0 b) (fn-rtc-get 1 b) (fn-rtc-get 2 b)) b))
  :hints (("Goal" :expand ((len b) (len (cdr b)) (len (cddr b)))
           :in-theory (enable fn-rtc-get)))))

(local (defthm fn-dsw-splice-empty-bytes
  (implies (and (true-listp bytes) (natp off) (<= off (len bytes)))
    (equal (fn-rtc-splice bytes off nil) bytes))
  :hints (("Goal" :in-theory (enable fn-rtc-splice)))))

(local (defthm fn-dsw-update-original
  (implies (and (true-listp l) (natp i) (< i (len l)))
    (equal (update-nth i (nth i l) l) l))
  :hints (("Goal" :induct (nth i l) :in-theory (enable nth update-nth)))))
(local (defthm fn-dsw-state-pool-shape
  (implies (fn-rtc-st$ap s)
    (and (true-listp (fn-rtc-pool s))
         (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (enable fn-rtc-st$ap fn-rtc-shapep)))))

(local (defthm fn-dsw-state-buffer-shape
  (implies (fn-rtc-st$ap s)
    (and (fn-cbor-octet-listp (fn-rtc-b-bytes (fn-rtc-buffer h s)))
         (implies (< (nfix h) (fn-rtc-nbufs (fn-rtc-config s)))
           (and (true-listp (fn-rtc-buffer h s)) (equal (len (fn-rtc-buffer h s)) 3)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-st$ap fn-rtc-b-bytes) (fn-rtc-c-shapep-buffer))
           :use fn-rtc-c-shapep-buffer))))

(local (defthm fn-dsw-with-original-buffer
  (implies (fn-rtc-st$ap s) (equal (fn-rtc-with-buffer h (fn-rtc-buffer h s) s) s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-with-buffer fn-rtc-buffer fn-dsw-set-original
                         fn-dsw-state-pool-shape fn-dsw-state-rebuild) (theory 'minimal-theory))))))

(local (defthm fn-dsw-splice-empty
  (implies (fn-rtc-st$ap s) (equal (fn-rtc-st$a-splice h j nil s) s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$a-splice fn-rtc-splice-okp fn-rtc-b-bytes
                         fn-dsw-splice-empty-bytes fn-dsw-state-buffer-shape fn-dsw-buffer-rebuild
                         fn-dsw-with-original-buffer fn-cbor-octet-listp-implies-true-listp natp nfix len
                         fn-cbor-octet-listp default-+-1 default-+-2 default-<-1 default-<-2)
                         (theory 'minimal-theory))
           :use ((:instance fn-dsw-state-buffer-shape)
                 (:instance fn-cbor-octet-listp-implies-true-listp (xs (fn-rtc-b-bytes (fn-rtc-buffer h s)))))))))

(local (defthm fn-dsw-puts-is-splice
  (implies (and (fn-rtc-st$ap s) (fn-rtc-splice-okp h j data s))
    (equal (fn-dsw-append-loop h j data s) (fn-rtc-st$a-splice h j data s)))
  :hints (("Goal" :induct (fn-dsw-append-loop h j data s)
           :in-theory (e/d (fn-rtc-st$a-put fn-rtc-st$a-splice fn-rtc-splice-okp fn-rtc-b-owner fn-rtc-b-bytes)
                           (fn-rtc-splice fn-rtc-with-buffer fn-rtc-buf-cap fn-rtc-nbufs fn-rtc-config fn-rtc-buffer
                            fn-rtc-uses fn-rtc-get fn-rtc-st$ap))
           )
          ("Subgoal *1/1" :use ((:instance fn-dsw-state-buffer-shape)
                                (:instance fn-rtc-st-put{preserved} (fn-rtc-st s) (off j) (o (car data))))))))

(defthmd fn-dsw-append-loop-is-puts
  (implies (natp j)
           (equal (fn-dsw-append-loop h j data s) (fn-rtc-st$a-puts h j data s)))
  :hints (("Goal" :induct (fn-dsw-append-loop h j data s)
           :in-theory (e/d (fn-rtc-st$a-puts) (fn-rtc-st$a-put)))))

(defthmd fn-dsw-splice-is-puts
  (implies (and (fn-rtc-st$ap s) (fn-rtc-splice-okp h j data s))
           (equal (fn-rtc-st$a-splice h j data s) (fn-rtc-st$a-puts h j data s)))
  :hints (("Goal" :use fn-dsw-puts-is-splice
           :in-theory (union-theories '(fn-rtc-splice-okp fn-dsw-append-loop-is-puts natp nfix)
                                       (theory 'minimal-theory)))))

(defthm fn-dsw-append-is-splice
  (implies (fn-rtc-st$ap s)
    (equal (fn-dsw-append h j data s)
           (if (fn-rtc-splice-okp h j data s)
               (mv :done (+ j (len data)) (fn-rtc-st$a-splice h j data s))
             (mv :refused j s))))
  :hints (("Goal" :in-theory (union-theories '(fn-dsw-append) (theory 'minimal-theory)) :use (fn-dsw-roomp-is-length-check fn-dsw-puts-is-splice))))

(defthm fn-dsw-copy-is-splice
  (implies (fn-rtc-st$ap s)
    (let ((data (fn-dss-copy-list (fn-oct-slice-list i end fn-octets))))
      (equal (fn-dsw-copy h i end j fn-octets s)
             (if (fn-rtc-splice-okp h j data s)
                 (mv :done (+ j (len data)) (fn-rtc-st$a-splice h j data s))
               (mv :refused j s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-dsw-copy fn-dsw-append-is-splice) (theory 'minimal-theory)))))

(defthm fn-dsw-copy-string-is-splice
  (implies (fn-rtc-st$ap s)
    (let ((data (fn-dss-copy-list (fn-oct-slice-list i end (fn-nntp-string-octets dss-str)))))
      (equal (fn-dsw-copy-string h i end j dss-str s)
             (if (fn-rtc-splice-okp h j data s)
                 (mv :done (+ j (len data)) (fn-rtc-st$a-splice h j data s))
               (mv :refused j s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-dsw-copy-string fn-dsw-append-is-splice) (theory 'minimal-theory)))))

(defthm fn-dsw-decimal-is-splice
  (implies (fn-rtc-st$ap s)
    (let ((data (fn-nntp-decimal n)))
      (equal (fn-dsw-decimal h j n s)
             (if (fn-rtc-splice-okp h j data s)
                 (mv :done (+ j (len data)) (fn-rtc-st$a-splice h j data s))
               (mv :refused j s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-dsw-decimal fn-dsw-append-is-splice) (theory 'minimal-theory)))))

(defthm fn-dsw-copy-refuses-past-capacity
  (implies (and (fn-rtc-st$ap s)
                (< (fn-rtc-buf-cap h (fn-rtc-config s))
                   (+ j (len (fn-dss-copy-list (fn-oct-slice-list i end fn-octets))))))
    (equal (fn-dsw-copy h i end j fn-octets s) (mv :refused j s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice-okp) (fn-dsw-copy fn-dsw-copy-string fn-dsw-decimal fn-dsw-append fn-rtc-st$a-splice fn-dss-copy-list fn-oct-slice-list fn-nntp-decimal fn-rtc-buffer fn-rtc-buf-cap fn-rtc-config)))))

(defthm fn-dsw-copy-string-refuses-past-capacity
  (implies (and (fn-rtc-st$ap s)
                (< (fn-rtc-buf-cap h (fn-rtc-config s))
                   (+ j (len (fn-dss-copy-list (fn-oct-slice-list i end (fn-nntp-string-octets dss-str)))))))
    (equal (fn-dsw-copy-string h i end j dss-str s) (mv :refused j s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice-okp) (fn-dsw-copy fn-dsw-copy-string fn-dsw-decimal fn-dsw-append fn-rtc-st$a-splice fn-dss-copy-list fn-oct-slice-list fn-nntp-decimal fn-rtc-buffer fn-rtc-buf-cap fn-rtc-config)))))

(defthm fn-dsw-append-refuses-past-capacity
  (implies (and (fn-rtc-st$ap s) (< (fn-rtc-buf-cap h (fn-rtc-config s)) (+ j (len data))))
    (equal (fn-dsw-append h j data s) (mv :refused j s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice-okp) (fn-dsw-copy fn-dsw-copy-string fn-dsw-decimal fn-dsw-append fn-rtc-st$a-splice fn-dss-copy-list fn-oct-slice-list fn-nntp-decimal fn-rtc-buffer fn-rtc-buf-cap fn-rtc-config)))))

(defthm fn-dsw-decimal-refuses-past-capacity
  (implies (and (fn-rtc-st$ap s) (< (fn-rtc-buf-cap h (fn-rtc-config s)) (+ j (len (fn-nntp-decimal n)))))
    (equal (fn-dsw-decimal h j n s) (mv :refused j s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice-okp) (fn-dsw-copy fn-dsw-copy-string fn-dsw-decimal fn-dsw-append fn-rtc-st$a-splice fn-dss-copy-list fn-oct-slice-list fn-nntp-decimal fn-rtc-buffer fn-rtc-buf-cap fn-rtc-config)))))

(local (defthm fn-dsw-nthcdr-append-within
  (implies (and (natp base) (<= base (len bytes)))
    (equal (nthcdr base (append bytes data)) (append (nthcdr base bytes) data)))
  :hints (("Goal" :induct (nthcdr base bytes)))))

(local (defthm fn-dsw-take-whole
  (implies (true-listp bytes) (equal (take (len bytes) bytes) bytes))))

(local (defthm fn-dsw-whole-view
  (implies (and (true-listp bytes) (natp base) (<= base (len bytes)))
    (equal (take (- (len bytes) base) (nthcdr base bytes)) (nthcdr base bytes)))
  :hints (("Goal" :induct (nthcdr base bytes)))))

(local (defthm fn-dsw-splice-at-fill
  (implies (and (true-listp bytes) (true-listp data))
    (equal (fn-rtc-splice bytes (len bytes) data) (append bytes data)))
  :hints (("Goal" :in-theory (enable fn-rtc-splice)))))

(local (defthm fn-dsw-view-appends-bytes
  (implies (and (true-listp bytes) (true-listp data) (natp base) (<= base (len bytes)))
    (equal (take (+ (len bytes) (len data) (- base)) (nthcdr base (append bytes data)))
           (append (take (- (len bytes) base) (nthcdr base bytes)) data)))
  :hints (("Goal" :in-theory (e/d () (take nthcdr fn-dsw-whole-view))
           :use ((:instance fn-dsw-whole-view (bytes (append bytes data)))
                 (:instance fn-dsw-whole-view))))))

(defthm fn-dsw-view-appends
  (implies (and (fn-rtc-st$ap s) (natp base) (<= base j)
                (fn-rtc-splice-okp h j data s) (equal j (fn-rtc-st$a-fill h s)))
    (equal (fn-dsw-view h base (+ j (len data)) (fn-rtc-st$a-splice h j data s))
           (append (fn-dsw-view h base j s) data)))
  :hints (("Goal" :in-theory (e/d (fn-dsw-view fn-rtc-st$a-fill fn-rtc-bytes fn-rtc-st$a-splice
                                     fn-rtc-splice-okp fn-rtc-b-bytes)
                                    (fn-rtc-st$ap fn-rtc-shapep take nthcdr len fn-cbor-octet-listp fn-rtc-splice fn-rtc-with-buffer fn-rtc-buffer fn-rtc-config fn-rtc-pool fn-rtc-get
                                     fn-rtc-buf-cap fn-rtc-nbufs fn-rtc-uses))
           :use ((:instance fn-dsw-state-buffer-shape)
                 (:instance fn-cbor-octet-listp-implies-true-listp (xs (fn-rtc-b-bytes (fn-rtc-buffer h s))))
                 (:instance fn-cbor-octet-listp-implies-true-listp (xs data))
                 (:instance fn-dsw-view-appends-bytes (bytes (fn-rtc-b-bytes (fn-rtc-buffer h s))))))))

(local (defthm fn-dsw-take-zero
  (equal (take 0 xs) nil) :hints (("Goal" :in-theory (enable take)))))
(local (defthm fn-dsw-append-nil
  (implies (true-listp xs) (equal (append xs nil) xs))))
(local (defthm fn-dsw-splice-prefix
  (implies (and (true-listp bytes) (true-listp data) (natp j) (<= j (len bytes)))
    (equal (take (+ j (len data)) (fn-rtc-splice bytes j data))
           (append (take j bytes) data)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-rtc-splice) (take nthcdr))
           :use ((:instance fn-dsw-take-append-len (a (take j bytes)) (k (len data))
                            (b (append data (nthcdr (+ j (len data)) bytes))))
                 (:instance fn-dsw-take-append-len (a data) (k 0)
                            (b (nthcdr (+ j (len data)) bytes))))))))
(local (defthm fn-dsw-splice-zero-prefix
  (implies (and (true-listp bytes) (true-listp data))
    (equal (take (len data) (fn-rtc-splice bytes 0 data)) data))
  :hints (("Goal" :in-theory (disable fn-rtc-splice take)
           :use ((:instance fn-dsw-splice-prefix (j 0)))))))
(local (defthm fn-dsw-splice-cons
  (implies (and (posp j) (<= j (+ 1 (len bytes))))
    (equal (fn-rtc-splice (cons o bytes) j data)
           (cons o (fn-rtc-splice bytes (- j 1) data))))
  :hints (("Goal" :in-theory (enable fn-rtc-splice take nthcdr)))))
(local (defun fn-dsw-view-splice-ind (base j bytes)
  (declare (xargs :measure (nfix base)))
  (if (and (posp base) (consp bytes))
      (fn-dsw-view-splice-ind (- base 1) (- j 1) (cdr bytes))
    (list base j bytes))))
(local (defthm fn-dsw-view-splice-bytes
  (implies (and (true-listp bytes) (true-listp data) (natp base) (natp j)
                (<= base j) (<= j (len bytes)))
    (equal (take (- (+ j (len data)) base) (nthcdr base (fn-rtc-splice bytes j data)))
           (append (take (- j base) (nthcdr base bytes)) data)))
  :hints (("Goal" :induct (fn-dsw-view-splice-ind base j bytes)
           :in-theory (e/d (nthcdr) (fn-rtc-splice take))
           :expand ((take (- j base) (nthcdr base bytes)))))))

; The same view bridge also covers overwrite below the old fill. K-W2's
; fill equality is redundant, and has no hypothesis-removal counterexample.
(defthm fn-dsw-view-appends-within-fill
  (implies (and (fn-rtc-st$ap s) (natp base) (<= base j) (fn-rtc-splice-okp h j data s))
    (equal (fn-dsw-view h base (+ j (len data)) (fn-rtc-st$a-splice h j data s))
           (append (fn-dsw-view h base j s) data)))
  :hints (("Goal" :in-theory (e/d (fn-dsw-view fn-rtc-st$a-splice fn-rtc-splice-okp fn-rtc-b-bytes)
                                   (fn-rtc-st$ap fn-rtc-shapep take nthcdr len fn-cbor-octet-listp fn-rtc-splice
                                    fn-rtc-with-buffer fn-rtc-buffer fn-rtc-config fn-rtc-pool fn-rtc-get fn-rtc-buf-cap
                                    fn-rtc-nbufs fn-rtc-uses))
           :use ((:instance fn-dsw-state-buffer-shape)
                 (:instance fn-cbor-octet-listp-implies-true-listp (xs (fn-rtc-b-bytes (fn-rtc-buffer h s))))
                 (:instance fn-cbor-octet-listp-implies-true-listp (xs data))
                 (:instance fn-dsw-view-splice-bytes (bytes (fn-rtc-b-bytes (fn-rtc-buffer h s))))))))

(local (defthm fn-dsw-copy-list-length
  (equal (len (fn-dss-copy-list data)) (len data))))
(local (defthm fn-dsw-copy-list-octets
  (implies (fn-cbor-octet-listp data) (fn-cbor-octet-listp (fn-dss-copy-list data)))
  :hints (("Goal" :induct (fn-dss-copy-list data))
          ("Subgoal *1/1" :use ((:instance fn-dss-copy-f-octet (o (car data))))))))
(local (defthm fn-dsw-slice-length
  (implies (and (natp i) (natp end))
    (equal (len (fn-oct-slice-list i end xs)) (nfix (- end i))))
  :hints (("Goal" :induct (fn-oct-slice-list i end xs)
           :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr))))))
(local (defthm fn-dsw-slice-octets
  (implies (and (fn-cbor-octet-listp xs) (natp i) (natp end) (<= end (len xs)))
    (fn-cbor-octet-listp (fn-oct-slice-list i end xs)))
  :hints (("Goal" :induct (fn-oct-slice-list i end xs)
           :in-theory (e/d (fn-oct-slice-list fn-oct-get-is-nth) (fn-oct-slice-list-is-take-nthcdr))))))
(local (defthm fn-dsw-copy-loop-is-append-loop
  (implies (and (natp i) (natp end) (natp j))
    (equal (fn-dsw-copy-loop h i end j xs s)
           (fn-dsw-append-loop h j (fn-dss-copy-list (fn-oct-slice-list i end xs)) s)))
  :hints (("Goal" :induct (fn-dsw-copy-loop h i end j xs s)
           :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr fn-rtc-st$a-put))))))

(local (defthm fn-dsw-string-aux-length
  (equal (len (fn-nntp-string-octets-aux cs)) (len cs))
  :hints (("Goal" :induct (fn-nntp-string-octets-aux cs)
           :in-theory (enable fn-nntp-string-octets-aux)))))
(local (defthm fn-dsw-string-length
  (implies (stringp text) (equal (len (fn-nntp-string-octets text)) (length text)))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets fn-nntp-string-octets-aux)))))
(local (defthm fn-dsw-string-aux-nth
  (implies (and (natp i) (< i (len cs)))
    (equal (nth i (fn-nntp-string-octets-aux cs)) (char-code (nth i cs))))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux nth)))))
(local (defthm fn-dsw-string-get
  (implies (and (stringp text) (natp i) (< i (length text)))
    (equal (fn-octets-get i (fn-nntp-string-octets text)) (char-code (char text i))))
  :hints (("Goal" :in-theory (enable fn-oct-get-is-nth fn-nntp-string-octets char)))))
(local (defthm fn-dsw-string-octets
  (implies (character-listp cs) (fn-cbor-octet-listp (fn-nntp-string-octets-aux cs)))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux fn-cbor-octetp)))))
(local (defthm fn-dsw-string-model-octets
  (fn-cbor-octet-listp (fn-nntp-string-octets text))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets)))))
(local (defthm fn-dsw-string-loop-is-copy-loop
  (implies (and (stringp text) (natp i) (natp end) (<= end (length text)))
    (equal (fn-dsw-string-loop h i end j text s)
           (fn-dsw-copy-loop h i end j (fn-nntp-string-octets text) s)))
  :hints (("Goal" :induct (fn-dsw-string-loop h i end j text s)
           :in-theory (e/d (fn-oct-get-is-nth fn-nntp-string-octets char)
                           (fn-oct-slice-list-is-take-nthcdr fn-rtc-st$a-put))
           :expand ((fn-dsw-copy-loop h i end j (fn-nntp-string-octets text) s))))))

(local (defthm fn-dsw-roomp-position
  (implies (fn-dsw-roomp h j m s) (natp j))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-dsw-roomp)))))

(verify-guards fn-dsw-view
  :hints (("Goal" :use ((:instance fn-dsw-state-buffer-shape)
                         (:instance fn-cbor-octet-listp-implies-true-listp (xs (fn-rtc-b-bytes (fn-rtc-buffer h s)))))
           :in-theory (e/d (fn-rtc-b-bytes) (fn-rtc-buffer fn-rtc-st$ap)))))
(verify-guards fn-dsw-append-loop)
(verify-guards fn-dsw-append)
(verify-guards fn-dsw-copy-loop)
(verify-guards fn-dsw-copy
  :hints (("Goal" :in-theory (e/d (fn-dsw-append) (fn-dsw-append-loop fn-dsw-copy-loop fn-oct-slice-list
                                                  fn-dss-copy-list fn-dsw-roomp)))))
(verify-guards fn-dsw-string-loop)
(verify-guards fn-dsw-copy-string
  :hints (("Goal" :in-theory (e/d (fn-dsw-append) (fn-dsw-append-loop fn-dsw-copy-loop fn-dsw-string-loop
                                                  fn-oct-slice-list fn-dss-copy-list fn-dsw-roomp)))))

(local (defthm fn-dsw-explode-append
  (implies (and (posp n) (true-listp acc))
    (equal (explode-nonnegative-integer n 10 (append acc tail))
           (append (explode-nonnegative-integer n 10 acc) tail)))
  :hints (("Goal" :induct (explode-nonnegative-integer n 10 acc)
           :in-theory (e/d (explode-nonnegative-integer) (digit-to-char floor mod))))))
(local (defthm fn-dsw-string-aux-append
  (equal (fn-nntp-string-octets-aux (append a b))
         (append (fn-nntp-string-octets-aux a) (fn-nntp-string-octets-aux b)))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))
(local (defthm fn-dsw-digit-code
  (implies (and (natp d) (< d 10)) (equal (char-code (digit-to-char d)) (+ 48 d)))
  :hints (("Goal" :in-theory (enable digit-to-char) :cases ((equal d 0) (equal d 1) (equal d 2)
                      (equal d 3) (equal d 4) (equal d 5) (equal d 6) (equal d 7) (equal d 8) (equal d 9))))))
(local (defthm fn-dsw-decimal-small
  (implies (and (natp n) (< n 10)) (equal (fn-nntp-decimal n) (list (+ 48 n))))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal fn-nntp-decimal-rev explode-nonnegative-integer
                                    fn-nntp-string-octets-aux)))))
(local (defthm fn-dsw-decimal-step
  (implies (and (natp n) (<= 10 n))
    (equal (fn-nntp-decimal n) (append (fn-nntp-decimal (floor n 10)) (list (+ 48 (mod n 10))))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-decimal fn-nntp-decimal-rev fn-nntp-string-octets-aux)
                                    (explode-nonnegative-integer))
           :expand ((explode-nonnegative-integer n 10 nil))
           :use ((:instance fn-dsw-explode-append (n (floor n 10)) (acc nil) (tail (list (digit-to-char (mod n 10))))))))))
(local (defthm fn-dsw-decimal-non-natural
  (implies (not (natp n)) (equal (fn-nntp-decimal n) nil))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal)))))
(local (defthm fn-dsw-decimal-count-is-length
  (equal (fn-dsw-decimal-count n) (len (fn-nntp-decimal n)))
  :hints (("Goal" :induct (fn-dsw-decimal-count n)
           :in-theory (e/d () (fn-nntp-decimal fn-nntp-decimal-rev))
           :expand ((fn-dsw-decimal-count n)))
          ("Subgoal *1/2" :in-theory (enable fn-nntp-decimal)))))
(local (defthm fn-dsw-decimal-octets
  (fn-cbor-octet-listp (fn-nntp-decimal n))
  :hints (("Goal" :induct (fn-dsw-decimal-count n)
           :in-theory (e/d (fn-cbor-octetp) (fn-nntp-decimal fn-nntp-decimal-rev))
           :expand ((fn-dsw-decimal-count n)))
          ("Subgoal *1/2" :in-theory (enable fn-nntp-decimal)))))
(local (defthm fn-dsw-append-loop-append
  (implies (natp j)
    (equal (fn-dsw-append-loop h j (append a b) s)
           (fn-dsw-append-loop h (+ j (len a)) b (fn-dsw-append-loop h j a s))))
  :hints (("Goal" :induct (fn-dsw-append-loop h j a s)
           :in-theory (disable fn-rtc-st$a-put fn-dsw-append-loop-is-puts)))))
(local (defthm fn-dsw-decimal-loop-is-append-loop
  (implies (and (natp n) (natp j))
    (equal (fn-dsw-decimal-loop h (+ j (fn-dsw-decimal-count n)) n s)
           (fn-dsw-append-loop h j (fn-nntp-decimal n) s)))
  :hints (("Goal" :induct (fn-dsw-decimal-loop h (+ j (fn-dsw-decimal-count n)) n s)
           :in-theory (e/d (fn-dsw-decimal-count) (fn-nntp-decimal fn-nntp-decimal-rev fn-rtc-st$a-put
                                                  fn-dsw-append-loop-is-puts))
           :expand ((fn-dsw-decimal-loop h (+ j (fn-dsw-decimal-count n)) n s))))))
(local (defthm fn-dsw-append-loop-empty
  (equal (fn-dsw-append-loop h j nil s) s)
  :hints (("Goal" :in-theory (enable fn-dsw-append-loop)))))
(verify-guards fn-dsw-decimal-count)
(verify-guards fn-dsw-decimal-loop
  :hints (("Goal" :in-theory (enable fn-dsw-decimal-count))))
(verify-guards fn-dsw-decimal
  :hints (("Goal" :use ((:instance fn-dsw-decimal-loop-is-append-loop (s fn-rtc-st)))
           :in-theory (e/d (fn-dsw-append fn-dsw-roomp)
                           (fn-nntp-decimal fn-dsw-decimal-count fn-dsw-decimal-loop fn-dsw-append-loop
                            fn-dsw-append-is-splice fn-dsw-puts-is-splice fn-rtc-st$ap fn-rtc-shapep
                            fn-rtc-config fn-rtc-nbufs fn-rtc-buf-cap fn-rtc-buffer fn-rtc-get
                            fn-rtc-splice-okp fn-rtc-st$a-splice)))))
