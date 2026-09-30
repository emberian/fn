; Resource refinement for the registered congruent RX from-list reference.
; Physical capacity is a maintained installation premise, not logical bytes.
(in-package "ACL2")
(include-book "receiver-provider")
(defthm fn-rxp-write-list-with-room-preserves-capacity
 (implies (and (natp (fn-octets$c-fill fn-octets$c))
               (<= (+ (fn-octets$c-fill fn-octets$c) (len bytes))
                   (fn-octets$c-buf-length fn-octets$c)))
          (and (equal (fn-octets$c-buf-length (fn-oct-write-list bytes fn-octets$c))
                      (fn-octets$c-buf-length fn-octets$c))
               (equal (fn-octets$c-fill (fn-oct-write-list bytes fn-octets$c))
                      (+ (fn-octets$c-fill fn-octets$c) (len bytes)))))
 :hints (("Goal" :induct (fn-oct-write-list bytes fn-octets$c)
                 :in-theory (enable fn-oct-write-list fn-octets$c-append-octet))))
(defthm fn-rxp-installed-from-list-does-not-resize
 (implies (and (<= 4096 (fn-octets$c-buf-length fn-octets$c))
               (<= (len bytes) 4096))
          (and (equal (fn-octets$c-buf-length
                        (fn-octets$c-from-list bytes fn-octets$c))
                      (fn-octets$c-buf-length fn-octets$c))
               (equal (fn-octets$c-fill (fn-octets$c-from-list bytes fn-octets$c))
                      (len bytes))))
 :hints (("Goal" :use ((:instance fn-rxp-write-list-with-room-preserves-capacity
                                    (fn-octets$c (fn-octets$c-clear fn-octets$c))))
                 :in-theory (e/d (fn-octets$c-from-list fn-octets$c-clear)
                                 (fn-oct-write-list fn-octets$c-append-octet
                                  fn-rxp-write-list-with-room-preserves-capacity)))))
