; PRF-1132: actual concrete executive capacity after explicit reservation.
; No compiled allocator/header/frame/lifetime or host admission assertion.
(in-package "ACL2")
(include-book "decoded-window-initial-retained-state")

(defthm fn-piwc-append-octet-keeps-funded-capacity
 (implies (and (natp (fn-octets$c-fill fn-octets$c))
               (< (fn-octets$c-fill fn-octets$c)
                  (fn-octets$c-buf-length fn-octets$c)))
  (let ((new (fn-octets$c-append-octet o fn-octets$c)))
   (and (equal (fn-octets$c-buf-length new)
               (fn-octets$c-buf-length fn-octets$c))
        (equal (fn-octets$c-fill new) (+ 1 (fn-octets$c-fill fn-octets$c))))))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet))))

(defthm fn-piwc-write-list-keeps-funded-capacity
 (implies (and (natp (fn-octets$c-fill fn-octets$c))
               (<= (+ (fn-octets$c-fill fn-octets$c) (len xs))
                   (fn-octets$c-buf-length fn-octets$c)))
  (let ((new (fn-oct-write-list xs fn-octets$c)))
   (and (equal (fn-octets$c-buf-length new)
               (fn-octets$c-buf-length fn-octets$c))
        (equal (fn-octets$c-fill new)
               (+ (fn-octets$c-fill fn-octets$c) (len xs))))))
 :hints (("Goal" :induct (fn-oct-write-list xs fn-octets$c)
           :in-theory (enable fn-oct-write-list))))

(local
 (defthm fn-piwc-back-loop-keeps-capacity
  (implies (<= end (fn-octets$c-buf-length fn-octets$c))
   (equal (fn-octets$c-buf-length (fn-oct-back-loop src dst end fn-octets$c))
          (fn-octets$c-buf-length fn-octets$c)))
  :hints (("Goal" :induct (fn-oct-back-loop src dst end fn-octets$c)
            :in-theory (enable fn-oct-back-loop)))))

(defthm fn-piwc-append-back-keeps-funded-capacity
 (implies (and (natp (fn-octets$c-fill fn-octets$c)) (natp n)
               (<= (+ (fn-octets$c-fill fn-octets$c) n)
                   (fn-octets$c-buf-length fn-octets$c)))
  (let ((new (fn-octets$c-append-back off n fn-octets$c)))
   (and (equal (fn-octets$c-buf-length new)
               (fn-octets$c-buf-length fn-octets$c))
        (equal (fn-octets$c-fill new) (+ (fn-octets$c-fill fn-octets$c) n)))))
 :hints (("Goal" :use ((:instance fn-piwc-back-loop-keeps-capacity
                       (src (- (fn-octets$c-fill fn-octets$c) off))
                       (dst (fn-octets$c-fill fn-octets$c))
                       (end (+ (fn-octets$c-fill fn-octets$c) n))))
           :in-theory (e/d (fn-octets$c-append-back)
                            (fn-oct-back-loop fn-piwc-back-loop-keeps-capacity)))))
