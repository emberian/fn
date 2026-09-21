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
(include-book "journal-publish")

(defconst *fn-native-admin-max-arguments* 3)
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

(defun fn-native-admin-result (status reason kind name capacity)
  (declare (xargs :guard t))
  (list status reason kind name capacity))

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

(defun fn-native-admin-plan (argv)
  "Normalize an administrative request; configuration admission stays in the store core."
  (declare (xargs :guard t))
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

; The physical adapter decodes exact framed records at its byte boundary, then
; calls this total logical function over those typed values.  A candidate that
; cannot replay into the same recovering state ordinary startup requires is a
; refusal before a namespace name is published.
(defun fn-native-admin-candidate-open-result (records frontier config-records)
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
  (equal (car (fn-native-admin-candidate-open-result records frontier config-records))
         :accepted))

(defun fn-native-admin-clock-result (status reason stamp)
  (declare (xargs :guard t))
  (list status reason stamp))
(defun fn-native-admin-clock-status (result)
  (declare (xargs :guard t)) (fn-ag-car result))
(defun fn-native-admin-clock-stamp (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))

(defun fn-native-admin-clock-observation (monotonic wall)
  "The configuration-record codec, not raw Lisp, decides whether the two host
clock observations fit its schema-0 representation."
  (declare (xargs :guard t))
  (let ((stamp (fn-clock-observation monotonic wall 0 t)))
    (if (fn-cfg-stampp stamp)
        (fn-native-admin-clock-result :accepted nil stamp)
      (fn-native-admin-clock-result :refused :clock-unrepresentable nil))))

(defun fn-native-admin-publication-result (status reason generation name publication)
  (declare (xargs :guard t))
  (list status reason generation name publication))
(defun fn-native-admin-publication-status (result)
  (declare (xargs :guard t)) (fn-ag-car result))
(defun fn-native-admin-publication-reason (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr result)))
(defun fn-native-admin-publication-generation (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))
(defun fn-native-admin-publication-name (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))
(defun fn-native-admin-publication-jpub (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))

(defun fn-native-admin-name-memberp (name names)
  (declare (xargs :guard t))
  (if (consp names)
      (or (equal name (car names)) (fn-native-admin-name-memberp name (cdr names)))
    nil))

(defun fn-native-admin-append-record (records record)
  "Total, one-record extension for the candidate replay.  The byte decoder
supplies proper record lists, but this boundary remains executable for a
malformed logical value and therefore does not make an unproved LISTP claim
to Common Lisp's guarded APPEND."
  (declare (xargs :guard t))
  (if (consp records)
      (cons (car records) (fn-native-admin-append-record (cdr records) record))
    (list record)))

(defun fn-native-admin-publication-authorize
    (records frontier config-records record lock-owned observed-names)
  "Authorize this exact final configuration name once.  LOCK-OWNED and
OBSERVED-NAMES are raw physical observations.  ACL2 binds them to the record's
generation, the candidate replay/open check, the fixed filename, and the
shared immutable publication state before raw Lisp may execute an I/O action."
  (declare (xargs :guard t))
  (if (not lock-owned)
      (fn-native-admin-publication-result :refused :lock nil nil nil)
    (let ((replayed (fn-cnode-config-replay config-records)))
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-native-admin-publication-result :refused :configuration nil nil nil)
        (let* ((current (fn-cnode-config (fn-replay-result-node replayed)))
               ; Replay success supplies a configuration generation.  NFIX
               ; keeps this public executable boundary total for malformed
               ; logical inputs without changing a valid replay's generation.
               (generation (+ 1 (nfix (fn-cfg-generation current))))
               (name (fn-native-admin-config-name generation))
               (candidate (fn-native-admin-candidate-openp
                           records frontier
                           (fn-native-admin-append-record config-records record))))
          (cond ((not (fn-cfg-recordp record))
                 (fn-native-admin-publication-result :refused :record nil nil nil))
                ((or (not (equal (fn-cfg-record-sequence record)
                                 (fn-cfg-generation current)))
                     (not (equal (fn-cfg-record-generation record) generation)))
                 (fn-native-admin-publication-result :refused :generation nil nil nil))
                ((null name)
                 (fn-native-admin-publication-result :refused :generation-name nil nil nil))
                ((fn-native-admin-name-memberp name observed-names)
                 (fn-native-admin-publication-result :refused :occupied nil nil nil))
                ((not candidate)
                 (fn-native-admin-publication-result :refused :candidate nil nil nil))
                (t (fn-native-admin-publication-result
                    :accepted nil generation name (fn-jpub-initial t)))))))))

(defthm fn-native-admin-config-name-of-one
  (equal (fn-native-admin-config-name 1) "00000001.cfg"))

(defthm fn-native-admin-config-name-refuses-overflow
  (equal (fn-native-admin-config-name *fn-native-admin-config-name-limit*) nil))
