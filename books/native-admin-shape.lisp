;; fn: the bounded vocabulary of the native administrative command.
;
; The argv bound, the decimal parser, the plan result record and the
; fixed-width configuration record name, split out of books/native-admin.lisp
; (planning/audit-2026-09-25-twins-fanin.md packet 4).  books/native-control,
; books/native-hybrid-control and books/native-config-observation name only
; these, so a change to a verb of the plan no longer recertifies them and the
; books above them.  The definitions and theorems are the ones
; books/native-admin.lisp had, unchanged, and are enabled at export as they
; were there.

(in-package "ACL2")
(include-book "records-shape")
(include-book "acceptance-alloc")
(include-book "byte-store-txn-name")

(defconst *fn-native-admin-max-arguments* 16)
(defconst *fn-native-admin-max-argument-octets* 512)
(defconst *fn-native-admin-config-name-width* 8)
(defconst *fn-native-admin-config-name-limit* 100000000)
(defconst *fn-native-admin-config-name-suffix* '(#\. #\c #\f #\g))

(local (defthm fn-native-admin-natural-digits-characters
  (character-listp (fn-bs-txn-natural-digits n))
  :hints (("Goal" :in-theory (enable fn-bs-txn-natural-digits
                                        fn-bs-txn-natural-digits-rev
                                        fn-bs-txn-reverse)))))

(local (defthm fn-native-admin-zeroes-characters
  (character-listp (fn-bs-txn-zeroes n))
  :hints (("Goal" :induct (fn-bs-txn-zeroes n)))) )

(local (defthm fn-native-admin-config-name-chars
  (character-listp
   (append (fn-bs-txn-zeroes n) (fn-bs-txn-natural-digits generation)
           *fn-native-admin-config-name-suffix*))
  :hints (("Goal" :use ((:instance fn-native-admin-zeroes-characters (n n))
                         (:instance fn-native-admin-natural-digits-characters
                                    (n generation)))))))

(defun fn-native-admin-argvp (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (and (consp (car argv))
           (<= (len (car argv)) *fn-native-admin-max-argument-octets*)
           (fn-record-ascii-octet-listp (car argv))
           (fn-native-admin-argvp (cdr argv)))
    (null argv)))

(defun fn-native-admin-words (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (cons (fn-record-octets-string (car argv))
            (fn-native-admin-words (cdr argv)))
    nil))

(defun fn-native-admin-digit-value (char)
  (declare (xargs :guard t))
  (if (characterp char)
      (let ((digit (char-code char)))
        (if (and (<= (char-code #\0) digit) (<= digit (char-code #\9)))
            (- digit (char-code #\0))
          -1))
    -1))

(defun fn-native-admin-decimal-value-aux (chars value)
  (declare (xargs :guard t))
  (if (consp chars)
      (let ((digit (fn-native-admin-digit-value (car chars))))
        (if (<= 0 digit)
            (fn-native-admin-decimal-value-aux
             (cdr chars) (+ (* 10 (nfix value)) digit))
          -1))
    (nfix value)))

(defun fn-native-admin-decimal-value (chars)
  (declare (xargs :guard t))
  (fn-native-admin-decimal-value-aux chars 0))

(defun fn-native-admin-decimalp (text)
  (declare (xargs :guard t))
  (if (not (stringp text)) nil
    (let ((chars (coerce text 'list)))
      (and (consp chars)
           (not (and (consp (cdr chars)) (equal (car chars) #\0)))
           (<= 0 (fn-native-admin-decimal-value chars))
           (fn-record-uint32p (fn-native-admin-decimal-value chars))))))

(defun fn-native-admin-result (status reason kind name capacity peer value)
  ; `value' is the second label of a two-label delta: the policy id of
  ; `policy set SLOT VALUE' (`name' carries the slot).  Every other kind
  ; leaves it nil.
  (declare (xargs :guard t))
  (list status reason kind name capacity peer value))

(defun fn-native-admin-result-status (result)
  (declare (xargs :guard t))
  (mbe :logic (car result) :exec (fn-ag-car result)))
(defun fn-native-admin-result-reason (result)
  (declare (xargs :guard t))
  (mbe :logic (cadr result) :exec (fn-ag-car (fn-ag-cdr result))))
(defun fn-native-admin-result-kind (result)
  (declare (xargs :guard t))
  (mbe :logic (caddr result) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr result)))))
(defun fn-native-admin-result-name (result)
  (declare (xargs :guard t))
  (mbe :logic (cadddr result)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))
(defun fn-native-admin-result-capacity (result) (declare (xargs :guard t))
  (mbe :logic (car (cddddr result))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))))
(defun fn-native-admin-result-peer (result) (declare (xargs :guard t))
  (mbe :logic (cadr (cddddr result))
       :exec (fn-ag-car
              (fn-ag-cdr
               (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))))
(defun fn-native-admin-result-value (result) (declare (xargs :guard t))
  (mbe :logic (caddr (cddddr result))
       :exec (fn-ag-car
              (fn-ag-cdr
               (fn-ag-cdr
                (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))))))

; Config record names are a fixed-width namespace.  The digit renderer is the
; existing ACL2 byte-store renderer; no host formatter derives a durable name.
(defun fn-native-admin-config-name-bounded (generation)
  (declare (xargs :guard (and (natp generation)
                              (< generation *fn-native-admin-config-name-limit*))
                  :verify-guards nil))
  (coerce
   (append (fn-bs-txn-zeroes
            (nfix (- *fn-native-admin-config-name-width*
                     (len (fn-bs-txn-natural-digits generation)))))
           (fn-bs-txn-natural-digits generation)
           *fn-native-admin-config-name-suffix*)
   'string))

(verify-guards fn-native-admin-config-name-bounded
  :hints (("Goal"
           :use ((:instance fn-native-admin-config-name-chars
                            (n (nfix (- *fn-native-admin-config-name-width*
                                        (len (fn-bs-txn-natural-digits generation)))))
                            (generation generation))))))

(defun fn-native-admin-config-name (generation)
  (declare (xargs :guard t))
  (if (and (natp generation)
           (< generation *fn-native-admin-config-name-limit*))
      (fn-native-admin-config-name-bounded generation)
    nil))

(defthm fn-native-admin-config-name-of-one
  (equal (fn-native-admin-config-name 1) "00000001.cfg"))

(defthm fn-native-admin-config-name-refuses-overflow
  (equal (fn-native-admin-config-name *fn-native-admin-config-name-limit*) nil))
