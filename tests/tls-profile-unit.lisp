; Configuration decisions and transport staging geometry are ACL2-owned.
(in-package "ACL2")
(include-book "../books/tls-kind")
(defconst *fn2-tls-profile-probe*
 '((:tls-certificate . "fixture.pem") (:tls-key . "fixture.key")
   (:c . 3) (:pool-classes . ((6 . 4096) (2 . 65536)))
   (:tls-window . 512) (:tls-handshakes . 1) (:tls-handshake-ms . 1000)))
(assert-event (fn2-tls-profilep *fn2-tls-profile-probe*))
(assert-event (equal (fn2-tls-admission-capacity *fn2-tls-profile-probe*) 1))
(assert-event (equal (fn2-codec-seed-capacity *fn2-tls-profile-probe*) 4096))
(assert-event (equal (fn2-codec-seed-reservation-bytes *fn2-tls-profile-probe*) 12288))
; BIO capacity is independent of the retained RX span, with no truncation cap.
(assert-event (> (fn2-codec-seed-capacity *fn2-tls-profile-probe*)
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

; Whole-antecedent/conclusion witness for the actual host span callee.
(defun fn2-tls-span-positive ()
 (declare (xargs :guard t))
 (mv-let (code count) (fn2-host-tls-span 100 97 2 8)
  (and (equal code :ok) (equal count 2) (natp count)
       (<= count 8) (<= count 2) (<= (+ 97 count) 100))))
; Removing successful admission permits an invalid observed BIO room. It
; must be refused; the admitted-span bound does not apply to that observation.
(defun fn2-tls-span-negative ()
 (declare (xargs :guard t))
 (mv-let (code count) (fn2-host-tls-span 100 97 -1 8)
  (and (equal code :bounds) (not (<= count -1)))))
(assert-event (mv-let (code count) (fn2-host-tls-span 2 3 8 8)
 (equal (list code count) '(:bounds 0))))

(defun fn2-tls-stage-span-positive ()
 (declare (xargs :guard t))
 (mv-let (code count) (fn2-host-tls-stage-span 100 97 100 8)
  (and (equal code :ok) (natp count) (equal count 3)
       (<= count 8) (<= (+ 97 count) 100))))
(defun fn2-tls-stage-span-negative ()
 (declare (xargs :guard t))
 (mv-let (code count) (fn2-host-tls-stage-span 100 97 -1 8)
  (and (equal code :bounds) (not (<= (+ 97 count) -1)))))
(assert-event (mv-let (code count) (fn2-host-tls-stage-span 100 0 99 8)
 (equal (list code count) '(:bounds 0))))

(fn2-assert-owed-teeth fn2-host-tls-span-bounded fn2-host-tls-stage-span-bounded)

(defun fn2-tls-turn-budget-positive ()
 (declare (xargs :guard t))
 (mv-let (code next) (fn2-host-tls-next-turn 2)
  (and (equal code :ok) (natp next) (equal next 1) (< next 2))))
(defun fn2-tls-turn-budget-negative ()
 (declare (xargs :guard t))
 (mv-let (code next) (fn2-host-tls-next-turn 0)
  (and (equal code :exhausted) (not (< next 0)))))
(assert-event (not (fn2-tls-profilep
 (put-assoc-equal :tls-handshake-turns 0 *fn2-tls-profile-probe*))))
(fn2-assert-owed-teeth fn2-host-tls-turn-budget-decreases)

(defconst *fn2-peer-tls-profile-probe*
 '((:peer-pull-ca-file . "/peer/anchor.pem") (:peer-pull-tls-name . "news.example.test")
   (:tls-handshakes . 2)))
(assert-event (and (fn2-tls-profilep *fn2-peer-tls-profile-probe*)
                   (equal 2 (fn2-tls-admission-capacity *fn2-peer-tls-profile-probe*))
                   (not (fn2-tls-requested-p *fn2-peer-tls-profile-probe*))))
(assert-event (not (fn2-tls-profilep '((:peer-pull-ca-file . "ca.pem")))))
(assert-event (not (fn2-tls-profilep '((:peer-pull-tls-name . "news.example.test")))))
(assert-event (not (fn2-tls-profilep
 (put-assoc-equal :peer-pull-tls-name "*.example.test" *fn2-peer-tls-profile-probe*))))
(defun fn2-peer-tls-live-connect-positive ()
 (declare (xargs :guard t))
 (let ((cap 4) (nonce 41) (physical-cap 4) (physical-nonce 41) (outboundp t)
       (kind *fn2-action-tls-start*))
  (and (equal (fn2-host-tls-role kind cap nonce physical-cap physical-nonce outboundp) :client)
       (posp cap) (posp nonce) (equal cap physical-cap) (equal nonce physical-nonce)
       (equal outboundp t) (equal kind *fn2-action-tls-start*))))
(defun fn2-peer-tls-live-connect-negative ()
 (declare (xargs :guard t))
 (let ((cap 4) (nonce 40) (physical-cap 4) (physical-nonce 41) (outboundp t)
       (kind *fn2-action-tls-start*))
  (and (equal (fn2-host-tls-role kind cap nonce physical-cap physical-nonce outboundp) :refused)
       (not (equal nonce physical-nonce)) (equal cap physical-cap)
       (equal outboundp t) (posp cap) (posp nonce) (equal kind *fn2-action-tls-start*))))
(fn2-assert-owed-teeth fn2-host-tls-client-binds-live-connect)
(assert-event (eq (fn2-host-tls-role *fn2-action-tls-start* 4 41 4 41 nil) :server))
(assert-event (eq (fn2-host-tls-role *fn2-action-receive* 4 41 4 41 t) :refused))
(assert-event (eq (fn2-host-tls-role *fn2-action-tls-start* 0 1 0 1 t) :refused))
