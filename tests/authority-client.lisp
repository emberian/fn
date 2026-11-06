; A test client of the served authority requests (FNCT kind 29, answered in
; kind 30; books/authority-codec.lisp's generated request and reply
; octets): frames a fixture sends and the replies it judges. Shared by
; tests/authority-served.lisp and tests/m2-cuts.lisp (Mini's world).
(in-package "ACL2")
(include-book "fnct-client")
(include-book "../books/authority-codec")

(defun fnca-codes (cs)
  (declare (xargs :verify-guards nil))
  (if (atom cs) nil (cons (char-code (car cs)) (fnca-codes (cdr cs)))))
(defun fnca-octets (s) (declare (xargs :verify-guards nil)) (fnca-codes (coerce s 'list)))
;; a kind 29 frame: VERB's request with VALUES (names as octet lists)
(defun fnca-frame (verb values)
  (declare (xargs :verify-guards nil))
  (fn2-fnct-seal *fn2-authority-request-kind* (fn2-authority-request-octets verb values)))
;; a kind 30 reply, as the list specification renders it
(defun fnca-reply (verb class reason values found-values)
  (declare (xargs :verify-guards nil))
  (fn2-fnct-seal *fn2-authority-reply-kind* (fn2-authority-reply-octets verb class reason values found-values)))
;; the (:id) codec's octets (LEB128): (mv value rest)
(defun fnca-leb (xs shift acc)
  (declare (xargs :verify-guards nil :measure (len xs)))
  (if (atom xs) (mv nil nil)
    (let ((b (nfix (car xs))))
      (if (< b 128) (mv (+ acc (* b (expt 2 shift))) (cdr xs))
        (fnca-leb (cdr xs) (+ 7 shift) (+ acc (* (- b 128) (expt 2 shift))))))))
;; a sealed frame's payload and the octets after it (header: magic 4,
;; version, kind, length 4 big-endian; trailer 32): (mv payload rest)
(defun fnca-unseal (xs)
  (declare (xargs :verify-guards nil))
  (let ((n (+ (* 16777216 (nfix (nth 6 xs))) (* 65536 (nfix (nth 7 xs))) (* 256 (nfix (nth 8 xs))) (nfix (nth 9 xs)))))
    (if (< (len xs) (+ 10 n 32)) (mv nil nil)
      (mv (take n (nthcdr 10 xs)) (nthcdr (+ 10 n 32) xs)))))
;; an accepted grant-set reply's (grant head) and the octets after it
(defun fnca-set-reply (xs)
  (declare (xargs :verify-guards nil))
  (mv-let (pl rest) (fnca-unseal xs)
    (if (not (equal (take 4 pl) (list 2 0 0 0))) (mv nil nil nil)
      (mv-let (g r1) (fnca-leb (nthcdr 4 pl) 0 0)
        (mv-let (h r2) (fnca-leb r1 0 0)
          (if (and (natp g) (natp h) (equal r2 '(0 0)))
              (mv g h rest)
            (mv nil nil nil)))))))
