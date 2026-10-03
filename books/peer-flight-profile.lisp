; Inert operator authority for the retained catchup driver. This independent
; file uses the existing big-endian catchup u64 codec; never the Lisp reader.
(in-package "ACL2")
(include-book "peer-flight-reservation")
(include-book "peer-u64-codec")

(defun fn-pfp-file-name () (declare (xargs :guard t)) "peer-flight-profile")
(defun fn-pfp-read-bound () (declare (xargs :guard t)) 53)
(defun fn-pfp-prefix () (declare (xargs :guard t)) '(70 78 80 49)) ; FNP1
(defun fn-pfp-take (n xs)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (or (zp n) (not (consp xs))) nil
   (cons (car xs) (fn-pfp-take (1- n) (cdr xs)))))
(defun fn-pfp-drop (n xs)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (or (zp n) (not (consp xs))) xs (fn-pfp-drop (1- n) (cdr xs))))
(defun fn-pfp-values (n xs)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) nil
   (cons (fn-cu-octets-value (fn-pfp-take 8 xs) 0)
         (fn-pfp-values (1- n) (fn-pfp-drop 8 xs)))))
(defthm fn-pfp-pack-keeps-list-shape
 (equal (true-listp (fn-cu-u64-octets-aux k n acc)) (true-listp acc))
 :hints (("Goal" :induct (fn-cu-u64-octets-aux k n acc)
                  :in-theory (enable fn-cu-u64-octets-aux))))
(defun fn-pfp-fields (xs)
 (declare (xargs :guard t))
 (if (consp xs)
     (append (fn-cu-u64-octets (car xs)) (fn-pfp-fields (cdr xs))) nil))
(defun fn-pfp-write (policy)
 (declare (xargs :guard t))
 (if (fn-pfr-policy-p policy) (append (fn-pfp-prefix) (fn-pfp-fields policy)) nil))
(defun fn-pfp-read (present bytes)
 (declare (xargs :guard t))
 (if (not present) nil
   (if (not (and (true-listp bytes) (equal (len bytes) 52)
                 (fn-cbor-octet-listp bytes) (equal (fn-pfp-take 4 bytes) (fn-pfp-prefix))))
       :bad
     (let ((policy (fn-pfp-values 6 (fn-pfp-drop 4 bytes))))
       (if (fn-pfr-policy-p policy) policy :bad)))))

(defun fn-pfp-refusal-line ()
 (declare (xargs :guard t))
 "Peer flight profile refused: malformed or unsupported resource allowance.")
