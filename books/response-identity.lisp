; HST-047: independent bounded serials for connection and response lifetimes.
; Runtime retains these ACL2 results; config/history/draw generations differ.
(in-package "ACL2")

(defun fn-rid-wordp (x)
  (declare (xargs :guard t))
  (and (integerp x) (<= 0 x) (< x 18446744073709551616)))

(defun fn-rid-reserve (serial)
  (declare (xargs :guard t))
  (if (and (fn-rid-wordp serial) (< serial 18446744073709551615))
      (mv :reserved (+ 1 serial))
    (mv :exhausted serial)))

(defun fn-rid-connection (cid serial)
  (declare (xargs :guard t))
  (if (not (fn-rid-wordp cid)) (mv :invalid-connection nil serial)
    (mv-let (word next) (fn-rid-reserve serial)
      (if (eq word :reserved)
          (mv :reserved (list :connection cid next) next)
        (mv word nil serial)))))

(defun fn-rid-response (connection serial)
  (declare (xargs :guard t))
  (if (not (and (true-listp connection) (equal (len connection) 3)
                (eq (car connection) :connection)
                (fn-rid-wordp (cadr connection))
                (fn-rid-wordp (caddr connection))
                (< 0 (caddr connection))))
      (mv :invalid-connection nil serial)
    (mv-let (word next) (fn-rid-reserve serial)
      (if (eq word :reserved)
          (mv :reserved (list :response (cadr connection) (caddr connection) next) next)
        (mv word nil serial)))))

(defthm fn-rid-reserve-strictly-advances-without-wrap
  (implies (equal (mv-nth 0 (fn-rid-reserve serial)) :reserved)
           (and (fn-rid-wordp (mv-nth 1 (fn-rid-reserve serial)))
                (< serial (mv-nth 1 (fn-rid-reserve serial))))))

(defthm fn-rid-connection-retains-exact-cid
  (implies (equal (mv-nth 0 (fn-rid-connection cid serial)) :reserved)
           (and (equal (cadr (mv-nth 1 (fn-rid-connection cid serial))) cid)
                (fn-rid-wordp (caddr (mv-nth 1 (fn-rid-connection cid serial)))))))

(defthm fn-rid-response-retains-connection-lifetime
  (implies (equal (mv-nth 0 (fn-rid-response connection serial)) :reserved)
           (and (equal (cadr (mv-nth 1 (fn-rid-response connection serial)))
                       (cadr connection))
                (equal (caddr (mv-nth 1 (fn-rid-response connection serial)))
                       (caddr connection))
                (fn-rid-wordp (cadddr (mv-nth 1 (fn-rid-response connection serial)))))))
