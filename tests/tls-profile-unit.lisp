; Configuration decisions and transport staging geometry are ACL2-owned.
(in-package "ACL2")
(include-book "../books/tls-kind")
(defconst *fn2-tls-profile-probe*
 '((:tls-certificate . "fixture.pem") (:tls-key . "fixture.key")
   (:c . 3) (:pool-classes . ((6 . 4096) (2 . 65536)))
   (:tls-window . 512) (:tls-handshakes . 1) (:tls-handshake-ms . 1000)))
(assert-event (fn2-tls-profilep *fn2-tls-profile-probe*))
(assert-event (equal (fn2-tls-admission-capacity *fn2-tls-profile-probe*) 1))
(assert-event (equal (fn2-tls-seed-capacity *fn2-tls-profile-probe*) 4096))
(assert-event (equal (fn2-tls-seed-reservation-bytes *fn2-tls-profile-probe*) 12288))
; BIO capacity is independent of the retained RX span, with no truncation cap.
(assert-event (> (fn2-tls-seed-capacity *fn2-tls-profile-probe*)
                 (fn2-tls-setting :tls-window 16384 *fn2-tls-profile-probe*)))
(assert-event (equal (fn2-tls-admission-capacity nil) 0))
(assert-event (not (fn2-tls-profilep '((:tls-certificate . "fixture.pem")))))
(assert-event (not (fn2-tls-profilep
 (put-assoc-equal :tls-key "" *fn2-tls-profile-probe*))))
(assert-event (not (fn2-tls-profilep
 (put-assoc-equal :tls-handshakes 0 *fn2-tls-profile-probe*))))
(assert-event (not (fn2-tls-profilep
 (put-assoc-equal :tls-handshakes #x10000 *fn2-tls-profile-probe*))))
(assert-event (not (fn2-tls-profilep
 (put-assoc-equal :tls-window #x80000000 *fn2-tls-profile-probe*))))
(assert-event (not (fn2-tls-profilep
 (put-assoc-equal :tls-handshake-ms #x100000000 *fn2-tls-profile-probe*))))
