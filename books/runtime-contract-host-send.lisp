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
(local (defthm fn-rtchs-send-range-of-a-handle
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
                            (arr (nth *fn-rtc-c-bytesi* c))))))))
; An :out use's handle is a handle (fn-rtc-usep), so the keystone needs no handle hypothesis.
(local (defthm fn-rtchs-out-use-has-a-handle
  (implies (and (fn-rtc-use-okp u s) (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*))
           (fn-rtc-handlep (fn-rtc-u-hd u)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd)
                                  (fn-rtc-handlep fn-rtc-buffer fn-rtc-current-p))))))
(defthm fn-rtc-host-send-range-is-the-lease
  (implies (and (fn-rtc-st$corr c s)
                (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*))
           (let* ((hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)))
             (equal (fn-rtc-c-octets (+ (fn-rtc-buf-base h (fn-rtc-config s)) (fn-rtc-h-off hd))
                                     (fn-rtc-h-len hd) (nth *fn-rtc-c-bytesi* c))
                    (take (fn-rtc-h-len hd)
                          (nthcdr (fn-rtc-h-off hd) (fn-rtc-b-bytes (fn-rtc-buffer h s)))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-rtchs-use-okp-of-member (uses (fn-rtc-uses s)))
                 fn-rtchs-invp-uses-okp
                 fn-rtchs-out-use-has-a-handle
                 fn-rtchs-send-range-of-a-handle))))

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
(local (defthm fn-rtchl-puts-in-range-is-the-write-request
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
                                   fn-rtc-buffer fn-rtc-uses))))))
; Outside the buffer table, or past the buffer's bytes, both sides refuse: no put lands, and
; req-write leaves the state.  So those are no hypotheses of the keystone.
(local (defthm fn-rtchl-puts-refused
  (implies (and (natp off)
                (not (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                          (<= off (len (fn-rtc-b-bytes (fn-rtc-buffer h s)))))))
           (equal (fn-rtc-st$a-puts h off w s) s))
  :hints (("Goal" :induct (fn-rtc-st$a-puts h off w s)
                  :in-theory (e/d (fn-rtc-st$a-put fn-rtc-st$a-splice fn-rtc-splice-okp)
                                  (fn-rtc-splice fn-rtc-with-buffer fn-rtc-buf-cap fn-rtc-nbufs fn-rtc-config
                                   fn-rtc-buffer fn-rtc-uses fn-rtc-b-bytes fn-rtc-splice-target-p))))))
(defthm fn-rtc-puts-is-the-write-request
  (let ((b (fn-rtc-buffer h s)))
    (implies (and (consp w)
                  (equal (fn-rtc-b-owner b) (list :workspace id inc))
                  (natp g) (equal (fn-rtc-get 0 b) g)
                  (natp off)
                  (fn-cbor-octet-listp w)
                  (<= (+ off (len w)) (fn-rtc-buf-cap h (fn-rtc-config s))))
             (equal (fn-rtc-st$a-puts h off w s)
                    (mv-nth 0 (fn-rtc-req-write (list :write h g off w) id inc s)))))
  :hints (("Goal" :cases ((and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                               (<= off (len (fn-rtc-b-bytes (fn-rtc-buffer h s)))))))
          ("Subgoal 2" :in-theory (e/d (fn-rtc-req-write fn-rtc-b-gen)
                                       (fn-rtc-st$a-puts fn-rtc-buffer fn-rtc-b-bytes fn-rtc-b-owner fn-rtc-buf-cap
                                        fn-rtc-nbufs fn-rtc-config fn-rtc-with-buffer fn-rtc-splice))
                       :use fn-rtchl-puts-refused)
          ("Subgoal 1" :in-theory (theory 'minimal-theory) :use fn-rtchl-puts-in-range-is-the-write-request)))

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
(local (defthm fn-rtchs-splice-keeps-a-handled-out-use
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
                 (:instance fn-rtchs-in-use-on-means-in-lease (h h2) (uses2 (fn-rtc-uses s))))))))
(defthm fn-hl-splice-keeps-out-use-bytes
  (implies (and (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*))
           (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-st$a-splice h2 off data s))
                  (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-rtchs-use-okp-of-member (uses (fn-rtc-uses s)))
                 fn-rtchs-invp-uses-okp
                 fn-rtchs-out-use-has-a-handle
                 fn-rtchs-splice-keeps-a-handled-out-use))))
;
; HL5a: one leased quantum.  The window OUT, rendered at offset 0 of the instance's workspace H (the puts,
; HL3: the :write request) and submitted as (:submit :send (h g 0 n) nil) at H's generation G, is the
; outstanding use (:send id inc op (h g 0 n)) at the next operation number, and the array range the host writes for it, [base(H), +n), is OUT.  The host executor's
; quantum (fnn-lease-article-quantum) is this state's step.  No invariant hypothesis: the correspondence
; with the concrete stobj carries the facts it would (a natural generation, a pool of nbufs buffers).
(defun fn-hl-render-ready-p (h id inc s)
  (declare (xargs :guard t))
  (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
       (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) (list :workspace id inc))))

(defun fn-hl-quantum-state (h out id inc s)
  (declare (xargs :guard t))
  (let ((g (fn-rtc-get 0 (fn-rtc-buffer h s))))
    (mv-let (s3 acts refused cost)
      (fn-rtc-req-submit (list :submit :send (list h g 0 (len out)) nil) id inc (fn-rtc-st$a-puts h 0 out s))
      (declare (ignore acts refused cost))
      s3)))

(local (progn
(defun fn-hlq-s2 (h out id inc s)
  (declare (xargs :guard t))
  (let ((b (fn-rtc-buffer h s)))
    (fn-rtc-with-buffer h (list (fn-rtc-get 0 b) (list :workspace id inc) (fn-rtc-splice (fn-rtc-b-bytes b) 0 out)) s)))
(defthm fn-hlq-puts-is-s2
  (implies (and (fn-hl-render-ready-p h id inc s)
                (natp (fn-rtc-get 0 (fn-rtc-buffer h s)))
                (consp out) (fn-cbor-octet-listp out)
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config s))))
           (equal (fn-rtc-st$a-puts h 0 out s) (fn-hlq-s2 h out id inc s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-req-write fn-hl-render-ready-p fn-rtc-b-gen)
                                  (fn-rtc-st$a-puts fn-rtc-with-buffer fn-rtc-splice fn-rtc-buffer fn-rtc-b-bytes
                                   fn-rtc-b-owner fn-rtc-buf-cap fn-rtc-nbufs fn-rtc-config))
           :use ((:instance fn-rtc-puts-is-the-write-request (off 0) (w out)
                            (g (fn-rtc-get 0 (fn-rtc-buffer h s))))))))
(defthm fn-hlq-take-0 (equal (take 0 x) nil))
(defthm fn-hlq-take-of-append-len
  (implies (true-listp a) (equal (take (len a) (append a b)) a)))
(defthm fn-hlq-take-of-splice-0
  (implies (true-listp out)
           (and (equal (take (len out) (fn-rtc-splice bytes 0 out)) out)
                (<= (len out) (len (fn-rtc-splice bytes 0 out)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice) (take nthcdr)))))
(defthm fn-hlq-next-op-of-with-buffer
  (equal (fn-rtc-next-op (fn-rtc-with-buffer h b s)) (fn-rtc-next-op s))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer fn-rtc-make fn-rtc-next-op))))
(defthm fn-hlq-submit-of-s2
  (let* ((g (fn-rtc-get 0 (fn-rtc-buffer h s)))
         (s3 (mv-nth 0 (fn-rtc-req-submit (list :submit :send (list h g 0 (len out)) nil) id inc
                                          (fn-hlq-s2 h out id inc s)))))
    (implies (and (fn-hl-render-ready-p h id inc s)
                  (natp g)
                  (fn-rtc-live-p id inc s)
                  (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
                  (true-listp out)
                  (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config s)))
                  (< h (len (fn-rtc-pool s))))
             (and (member-equal (list :send id inc (fn-rtc-next-op s) (list h g 0 (len out))) (fn-rtc-uses s3))
                  (equal (fn-rtc-b-bytes (fn-rtc-buffer h s3)) (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h s)) 0 out))
                  (equal (fn-rtc-config s3) (fn-rtc-config s)))))
  :hints (("Goal" :do-not (quote (preprocess)) :in-theory (e/d (fn-rtc-req-submit fn-rtc-submit-okp fn-hlq-s2 fn-hl-render-ready-p fn-rtc-issue
                                   fn-rtc-buffered-kind-p fn-rtc-kind-extrap fn-rtc-extrap fn-rtc-handlep
                                   fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-b-gen fn-rtc-b-owner
                                   fn-rtc-b-bytes fn-rtc-live-p fn-rtc-slot)
                                  (fn-rtc-splice fn-rtc-buf-cap fn-rtc-nbufs fn-rtc-use-bound fn-rtc-c-get-is-nth fn-rtc-c-get-non-natp)))))
(defthm fn-hlq-splice-frame
  (and (equal (fn-rtc-get 0 (fn-rtc-buffer k (fn-rtc-st$a-splice h off data s))) (fn-rtc-get 0 (fn-rtc-buffer k s)))
       (equal (len (fn-rtc-pool (fn-rtc-st$a-splice h off data s))) (len (fn-rtc-pool s)))
       (equal (fn-rtc-config (fn-rtc-st$a-splice h off data s)) (fn-rtc-config s))
       (equal (fn-rtc-next-op (fn-rtc-st$a-splice h off data s)) (fn-rtc-next-op s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-st$a-splice fn-rtc-with-buffer fn-rtc-buffer fn-rtc-pool fn-rtc-config fn-rtc-make fn-rtc-next-op)
                                  (fn-rtc-splice-okp fn-rtc-splice)))))
(defthm fn-hlq-puts-frame
  (and (equal (fn-rtc-get 0 (fn-rtc-buffer k (fn-rtc-st$a-puts h off w s))) (fn-rtc-get 0 (fn-rtc-buffer k s)))
       (equal (len (fn-rtc-pool (fn-rtc-st$a-puts h off w s))) (len (fn-rtc-pool s)))
       (equal (fn-rtc-config (fn-rtc-st$a-puts h off w s)) (fn-rtc-config s))
       (equal (fn-rtc-next-op (fn-rtc-st$a-puts h off w s)) (fn-rtc-next-op s)))
  :hints (("Goal" :induct (fn-rtc-st$a-puts h off w s)
           :in-theory (e/d (fn-rtc-st$a-put) (fn-rtc-st$a-splice fn-rtc-buffer fn-rtc-pool fn-rtc-config fn-rtc-next-op)))))
(defthm fn-hlq-submit-send-frame
  (let ((s3 (mv-nth 0 (fn-rtc-req-submit (list :submit :send (list h (fn-rtc-get 0 (fn-rtc-buffer h s)) 0 n) nil) id inc s))))
    (implies (natp h)
             (and (equal (fn-rtc-get 0 (fn-rtc-buffer h s3)) (fn-rtc-get 0 (fn-rtc-buffer h s)))
                  (equal (len (fn-rtc-pool s3)) (len (fn-rtc-pool s)))
                  (equal (fn-rtc-config s3) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-req-submit fn-rtc-submit-okp fn-rtc-issue fn-rtc-with-buffer fn-rtc-make
                                   fn-rtc-buffer fn-rtc-pool fn-rtc-config fn-rtc-b-gen fn-rtc-handlep fn-rtc-h-gen
                                   fn-rtc-h-buf fn-rtc-buffered-kind-p)
                                  (fn-rtc-splice fn-rtc-buf-cap fn-rtc-nbufs fn-rtc-use-bound fn-rtc-live-p
                                   fn-rtc-kind-out-p fn-rtc-kind-extrap)))))
(defun fn-hlq-ind-km (j k meta)
  (declare (xargs :measure (len meta)))
  (if (or (zp j) (atom meta)) (list j k meta) (fn-hlq-ind-km (- j 1) (+ 1 k) (cdr meta))))
(defthm fn-hlq-gen-natp-of-metas-okp-at
  (implies (and (fn-rtc-c-metas-okp k meta cfg) (natp k) (natp j) (< j (len meta)))
           (natp (fn-rtc-get 0 (nth j meta))))
  :hints (("Goal" :induct (fn-hlq-ind-km j k meta) :in-theory (e/d (nth) (fn-rtc-buf-cap)))))
(defthm fn-hlq-corr-gives-gen-and-pool
  (implies (and (fn-rtc-st$corr c x) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config x))))
           (and (natp (fn-rtc-get 0 (fn-rtc-buffer h x)))
                (equal (len (fn-rtc-pool x)) (fn-rtc-nbufs (fn-rtc-config x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-st$corr fn-rtc-c-abs fn-rtc-c-wfp fn-rtc-buffer fn-rtc-pool fn-rtc-config
                                   fn-rtc-make fn-rtc-c-buffer)
                                  (fn-rtc-c-octets fn-rtc-c-pool fn-rtc-st$cp fn-rtc-buf-base fn-rtc-nbufs
                                   fn-rtc-c-metas-okp fn-rtc-configp))
           :use ((:instance fn-rtchs-get-of-c-pool (k h) (h 0) (n (fn-rtc-nbufs (nth *fn-rtc-c-cfg* c)))
                            (cfg (nth *fn-rtc-c-cfg* c)) (meta (nth *fn-rtc-c-metai* c))
                            (bytes (nth *fn-rtc-c-bytesi* c)))
                 (:instance fn-hlq-gen-natp-of-metas-okp-at (k 0) (j h) (meta (nth *fn-rtc-c-metai* c))
                            (cfg (nth *fn-rtc-c-cfg* c)))))))
(defthm fn-hlq-submit-empty
  (let* ((g (fn-rtc-get 0 (fn-rtc-buffer h s)))
         (s3 (mv-nth 0 (fn-rtc-req-submit (list :submit :send (list h g 0 0) nil) id inc s))))
    (implies (and (fn-hl-render-ready-p h id inc s) (natp g)
                  (fn-rtc-live-p id inc s)
                  (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s))))
             (member-equal (list :send id inc (fn-rtc-next-op s) (list h g 0 0)) (fn-rtc-uses s3))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rtc-req-submit fn-rtc-submit-okp fn-hl-render-ready-p fn-rtc-issue
                                   fn-rtc-buffered-kind-p fn-rtc-kind-extrap fn-rtc-extrap fn-rtc-handlep
                                   fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-b-gen fn-rtc-b-owner
                                   fn-rtc-live-p fn-rtc-slot)
                                  (fn-rtc-splice fn-rtc-buf-cap fn-rtc-nbufs fn-rtc-use-bound)))))
(defthm fn-hlq-octet-list-atom (implies (and (fn-cbor-octet-listp x) (not (consp x))) (equal x nil)) :rule-classes nil)
(defthm fn-hlq-nthcdr-0 (equal (nthcdr 0 x) x))
(defthm fn-hlq-plus-0 (implies (acl2-numberp x) (equal (+ x 0) x)))
(defthm fn-hlq-len-of-consp (implies (consp x) (< 0 (len x))) :rule-classes :linear)
(defthm fn-hlq-octet-list-true (implies (fn-cbor-octet-listp x) (true-listp x)) :rule-classes nil)
))
(defthm fn-hl-leased-quantum-sends-the-window
  (implies (and (fn-hl-render-ready-p h id inc s)
                (fn-rtc-live-p id inc s)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
                (fn-cbor-octet-listp out)
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config s)))
                (fn-rtc-st$corr c (fn-hl-quantum-state h out id inc s)))
           (and (member-equal (list :send id inc (fn-rtc-next-op s)
                                    (list h (fn-rtc-get 0 (fn-rtc-buffer h s)) 0 (len out)))
                              (fn-rtc-uses (fn-hl-quantum-state h out id inc s)))
                (equal (fn-rtc-c-octets (fn-rtc-buf-base h (fn-rtc-config s)) (len out)
                                        (nth *fn-rtc-c-bytesi* c))
                       out)))
  :hints (("Goal" :cases ((consp out)) :in-theory (theory 'minimal-theory)
           :use ((:instance fn-hl-render-ready-p)
                 (:instance fn-hlq-puts-frame (k h) (off 0) (w out))
                 (:instance fn-hlq-submit-send-frame (n (len out)) (s (fn-rtc-st$a-puts h 0 out s)))
                 (:instance fn-hlq-corr-gives-gen-and-pool (x (fn-hl-quantum-state h out id inc s)))
                 (:instance fn-hl-quantum-state)))
          ("Subgoal 2" :in-theory (union-theories '(fn-rtc-c-octets zp fn-rtc-st$a-puts len (:e len)) (theory 'minimal-theory))
           :use ((:instance fn-hlq-octet-list-atom (x out))
                 (:instance fn-hlq-submit-empty)))
          ("Subgoal 1" :in-theory (union-theories '(fn-hlq-nthcdr-0 fn-hlq-plus-0 fn-hlq-len-of-consp fn-rtc-c-len-of-octets natp nfix
                                               (:type-prescription fn-rtc-buf-base-natp)
                                               (:type-prescription fn-rtc-buf-base) (:type-prescription len)
                                               (:type-prescription fn-rtc-c-octets))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlq-puts-is-s2)
                 (:instance fn-hlq-submit-of-s2)
                 (:instance fn-hlq-take-of-splice-0 (bytes (fn-rtc-b-bytes (fn-rtc-buffer h s))))
                 (:instance fn-hlq-octet-list-true (x out))
                 (:instance fn-rtchs-buffer-of-corr
                            (s (mv-nth 0 (fn-rtc-req-submit (list :submit :send (list h (fn-rtc-get 0 (fn-rtc-buffer h s)) 0 (len out)) nil)
                                                            id inc (fn-hlq-s2 h out id inc s)))))
                 (:instance fn-rtchs-window-of-octets
                            (b (fn-rtc-buf-base h (fn-rtc-config s))) (off 0) (len (len out))
                            (fl (nfix (fn-rtc-get 2 (nth h (nth *fn-rtc-c-metai* c)))))
                            (arr (nth *fn-rtc-c-bytesi* c)))))))
