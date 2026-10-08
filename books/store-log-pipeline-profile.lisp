; Queue preflight for the profile's encoded log-octet cap. No candidate is
; removed from the queue until room for any profile-sized record is known.
(in-package "ACL2")
(include-book "store-log-pipeline")
(local (in-theory (disable (tau-system))))

(defun fn-olr-gc-octet-bound (records prevlen unit)
  (declare (xargs :guard t))
  (+ (fn-lg-pack-len records)
     (* (len records) (+ 10 (max 32 (nfix prevlen)) 32 (nfix unit)))))

(local
 (encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-lg-gc-pad-at-most-unit
  (<= (fn-lg-pad-len n unit) (nfix unit))
  :hints (("Goal" :in-theory (enable fn-lg-pad-len))))))
(local
 (defthm fn-lg-gc-pack-of-cut
  (implies (and (natp k) (<= k (len records)))
    (equal (+ (fn-lg-pack-len (fn-bs-take k records))
              (fn-lg-pack-len (nthcdr k records)))
           (fn-lg-pack-len records)))
  :hints (("Goal" :induct (nthcdr k records)
           :in-theory (enable fn-bs-take fn-lg-pack-len)))))
(local
 (defthm fn-lg-gc-body-at-most-pack
  (<= (fn-lgc-chunk-body-len records) (fn-lg-pack-len records))
  :hints (("Goal" :in-theory (enable fn-lgc-chunk-body-len fn-lg-pack-len)))))

(encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-lgc-log-len-bounded-by-records
  (<= (fn-lgc-log-len records prevlen unit)
      (fn-olr-gc-octet-bound records prevlen unit))
  :hints (("Goal" :induct (fn-lgc-log-len records prevlen unit) :nonlinearp t
           :in-theory (e/d (fn-lgc-log-len fn-olr-gc-octet-bound)
                            (fn-lgc-chunk-body-len fn-lg-pack-len fn-bs-take
                             fn-lg-pad-len fn-lg-chunk-len fn-lg-gc-pack-of-cut
                             fn-lg-gc-body-at-most-pack fn-lg-gc-pad-at-most-unit
                             fn-lg-chunk-len-bounds)))
          ("Subgoal *1/1"
           :use ((:instance fn-lg-gc-pack-of-cut (k (fn-lg-chunk-len records)))
                 (:instance fn-lg-gc-body-at-most-pack
                   (records (fn-bs-take (fn-lg-chunk-len records) records)))
                 (:instance fn-lg-gc-pad-at-most-unit
                   (n (+ 42 (nfix prevlen)
                         (fn-lgc-chunk-body-len (fn-bs-take (fn-lg-chunk-len records) records)))))
                 fn-lg-chunk-len-bounds)))))

(defun fn-olr-gc-queue-roomp (ks max-record bmax omax unit)
  (declare (xargs :guard (true-listp ks)))
  (let* ((records (fn-lgk-batch ks))
         (overhead (+ 10 (max 32 (len (fn-lgk-last ks))) 32 (nfix unit))))
    (and (posp bmax) (natp omax) (posp unit)
         (< (len records) bmax)
         (or (not (consp records))
             (<= (+ (fn-olr-gc-octet-bound records (len (fn-lgk-last ks)) unit)
                    4 (nfix max-record) overhead)
                 omax)))))

(local
 (defthm fn-lg-gc-pack-append
  (equal (fn-lg-pack-len (append a b)) (+ (fn-lg-pack-len a) (fn-lg-pack-len b)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-lg-pack-len)))))
(local
 (defthm fn-lg-gc-pack-fix
  (equal (fn-lg-pack-len (true-list-fix a)) (fn-lg-pack-len a))
  :hints (("Goal" :induct (len a) :in-theory (enable fn-lg-pack-len true-list-fix)))))

(local
 (defthm fn-lg-gc-prepared-length
  (equal (fn-lgc-append-len (fn-lgc-prepare (fn-lgk-pipe-kernel-view ks) record) unit)
         (fn-lgc-log-len
          (if (equal (fn-lgk-phase ks) :fault) (fn-lgk-batch ks)
            (append (true-list-fix (fn-lgk-batch ks)) (list record)))
          (len (fn-lgk-last ks)) unit))
  :hints (("Goal" :in-theory
           (e/d (fn-lgc-append-len fn-lgc-prepare fn-lgk-pipe-kernel-view
                  fn-lgk-pipe-countedp fn-lgc-of fn-lgc-batch fn-lgc-last
                  fn-lgc-phase fn-lgc-make fn-lgk-batch fn-lgk-last fn-lgk-phase)
                (fn-lgc-log-len))))))
(local
 (defthm fn-lg-gc-bound-append-one
  (equal (fn-olr-gc-octet-bound (append records (list record)) prevlen unit)
         (+ (fn-olr-gc-octet-bound records prevlen unit)
            4 (len record) 10 (max 32 (nfix prevlen)) 32 (nfix unit)))
  :hints (("Goal" :in-theory
           (e/d (fn-olr-gc-octet-bound)
                (fn-lg-pack-len true-list-fix))))))

(defthm fn-olr-gc-queue-room-implies-profile-fit
  (implies (and (fn-olr-gc-queue-roomp ks max-record bmax omax unit)
                (consp (fn-lgk-batch ks))
                (<= (len record) (nfix max-record)))
    (fn-olr-gc-profile-fitp ks record bmax omax unit))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgc-log-len-bounded-by-records
                    (records (append (true-list-fix (fn-lgk-batch ks)) (list record)))
                    (prevlen (len (fn-lgk-last ks))))
                 (:instance fn-lgc-log-len-bounded-by-records
                    (records (fn-lgk-batch ks)) (prevlen (len (fn-lgk-last ks)))))
           :in-theory
           (e/d (fn-olr-gc-queue-roomp fn-olr-gc-profile-fitp)
                (fn-olr-gc-octet-bound fn-lgc-prepare fn-lgc-append-len
                 fn-lgk-pipe-kernel-view fn-lgc-log-len fn-lgc-log-len-bounded-by-records
                 fn-lgk-batch fn-lgk-last fn-lgk-phase max fn-lg-pack-len)))))

(defthm fn-olr-gc-queue-room-prevents-full
  (let ((ks (fn-lgk-pipe-ks p)))
    (implies (and (not (fn-lgk-pipe-behind p))
                  (fn-olr-gc-queue-roomp ks max-record bmax omax unit)
                  (consp (fn-lgk-batch ks))
                  (<= (len record) (nfix max-record))
                  (natp txid) (equal txid (fn-lgk-next-txid ks))
                  (not (equal (fn-lgk-phase ks) :fault)))
      (equal (car (fn-lgk-pipe-take p record txid (len (fn-lgk-batch ks))
                                   (fn-lg-pack-len (fn-lgk-batch ks)) bmax omax unit))
             :taken)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-olr-gc-queue-room-implies-profile-fit (ks (fn-lgk-pipe-ks p))))
           :in-theory
           (e/d (fn-lgk-pipe-take fn-lgk-pipe-kernel-take fn-lgk-pipe-countedp
                  fn-lgc-take fn-olr-take fn-olr-gc-queue-roomp fn-olr-gc-octet-bound
                  fn-lgc-next-txid fn-lgk-next-txid fn-lgc-phase fn-lgk-phase)
                (fn-olr-gc-profile-fitp fn-olr-gc-queue-room-implies-profile-fit
                 fn-lg-pack-len fn-lgk-batch fn-lgk-last fn-lgc-prepare fn-lgk-prepare)))))
