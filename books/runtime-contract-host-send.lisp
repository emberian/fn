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
