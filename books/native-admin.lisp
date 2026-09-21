; fn: bounded native administrative configuration plan.
;
; This is deliberately a narrow command boundary.  It selects only the three
; durable configuration deltas that the store already owns, and it never owns
; a second group table, capacity rule, record encoder, or replay algorithm.
; Raw Lisp supplies bounded argv octets and physical observations; the record
; remains `fn-store-cfg-reconfigure' and a proposed history is checked here by
; the same logical replay/open entry used at ordinary recovery.

(in-package "ACL2")
(include-book "node-config")
(include-book "store-observed")
(include-book "byte-store-txn-name")

(defconst *fn-native-admin-max-arguments* 3)
(defconst *fn-native-admin-max-argument-octets* 512)
(defconst *fn-native-admin-config-name-width* 8)
(defconst *fn-native-admin-config-name-limit* 100000000)
(defconst *fn-native-admin-config-name-suffix* '(#\. #\c #\f #\g))

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

(defun fn-native-admin-decimal-value-aux (chars value)
  ; The plan calls this only on the character list produced from an ACL2
  ; string.  Keeping that conversion at the public parser avoids a raw host
  ; decimal parser; the generic total definition intentionally has no broader
  ; executable guard claim.
  (declare (xargs :guard t :verify-guards nil))
  (if (consp chars)
      (let ((digit (char-code (car chars))))
        (if (and (<= (char-code #\0) digit) (<= digit (char-code #\9)))
            (fn-native-admin-decimal-value-aux
             (cdr chars) (+ (* 10 value) (- digit (char-code #\0))))
          -1))
    value))

(defun fn-native-admin-decimal-value (chars)
  (declare (xargs :guard t :verify-guards nil))
  (fn-native-admin-decimal-value-aux chars 0))

(defun fn-native-admin-decimalp (text)
  (declare (xargs :guard t :verify-guards nil))
  (let ((chars (coerce text 'list)))
    (and (consp chars)
         (not (and (consp (cdr chars)) (equal (car chars) #\0)))
         (<= 0 (fn-native-admin-decimal-value chars))
         (fn-record-uint32p (fn-native-admin-decimal-value chars)))))

(defun fn-native-admin-result (status reason kind name capacity)
  (declare (xargs :guard t))
  (list status reason kind name capacity))

(defun fn-native-admin-result-status (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car result) :exec (fn-ag-car result)))
(defun fn-native-admin-result-reason (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadr result) :exec (fn-ag-car (fn-ag-cdr result))))
(defun fn-native-admin-result-kind (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (caddr result) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr result)))))
(defun fn-native-admin-result-name (result)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadddr result)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))
(defun fn-native-admin-result-capacity (result) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cddddr result))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))))

(defun fn-native-admin-plan (argv)
  "Normalize an administrative request; configuration admission stays in the store core."
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-native-admin-argvp argv))
          (< *fn-native-admin-max-arguments* (len argv)))
      (fn-native-admin-result :refused :argv nil nil nil)
    (let ((words (fn-native-admin-words argv)))
      (cond
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "create")
             (fn-record-group-namep (caddr words)))
        (fn-native-admin-result :accepted nil :create-group (caddr argv) 0))
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "retire")
             (fn-record-group-namep (caddr words)))
        (fn-native-admin-result :accepted nil :remove-group (caddr argv) 0))
       ((and (equal (len words) 2)
             (equal (car words) "capacity")
             (fn-native-admin-decimalp (cadr words)))
        (fn-native-admin-result :accepted nil :set-capacity nil
                                (fn-native-admin-decimal-value
                                 (coerce (cadr words) 'list))))
       (t (fn-native-admin-result :refused :syntax nil nil nil))))))

; Config record names are a fixed-width namespace.  The digit renderer is the
; existing ACL2 byte-store renderer; no host formatter derives a durable name.
(defun fn-native-admin-config-name (generation)
  ; The byte-store renderer's useful guard is its natural input; this public
  ; total projection performs that check in its body and makes no broader raw
  ; executable guard claim.
  (declare (xargs :guard t :verify-guards nil))
  (if (and (natp generation)
           (< generation *fn-native-admin-config-name-limit*))
      (coerce
       (append (fn-bs-txn-zeroes
                (nfix (- *fn-native-admin-config-name-width*
                         (len (fn-bs-txn-natural-digits generation)))))
               (fn-bs-txn-natural-digits generation)
               *fn-native-admin-config-name-suffix*)
       'string)
    nil))

; The physical adapter decodes exact framed records at its byte boundary, then
; calls this total logical function over those typed values.  A candidate that
; cannot replay into the same recovering state ordinary startup requires is a
; refusal before a namespace name is published.
(defun fn-native-admin-candidate-open-result (records frontier config-records)
  (declare (xargs :guard t :verify-guards nil))
  (let ((replayed (fn-cnode-config-replay config-records)))
    (if (not (equal (fn-replay-result-kind replayed) :ok))
        (list :refused :configuration)
      (let* ((cn (fn-replay-result-node replayed))
             (cfg (fn-cnode-config cn))
             (opened (fn-sn-open-observed (fn-cnode-domain cn)
                                          (fn-cfg-capacity (fn-cfg-value cfg))
                                          frontier records)))
        (if (and (fn-sn-open-okp opened)
                 (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                        :recovering))
            (list :accepted cn)
          (list :refused :history))))))

(defun fn-native-admin-candidate-openp (records frontier config-records)
  (declare (xargs :guard t :verify-guards nil))
  (equal (car (fn-native-admin-candidate-open-result records frontier config-records))
         :accepted))

(defthm fn-native-admin-config-name-of-one
  (equal (fn-native-admin-config-name 1) "00000001.cfg"))

(defthm fn-native-admin-config-name-refuses-overflow
  (equal (fn-native-admin-config-name *fn-native-admin-config-name-limit*) nil))
