; Trusted bounded marshalling helpers for the composed store bridge.
; Stateful acceptance/recovery/completion live only in store-node-host.lisp.
; No untrusted input is read as Lisp: the process interface supplies decimal
; octets and fixed operation names after Python boundary validation.

(in-package "ACL2")

(defconst *fn-store-groups* '("fn.letters" "fn.test"))

(defconst *fn-store-capacity* 1048576)

(defconst *fn-store-max-text* 512)

(defconst *fn-store-max-payload* 32768)

(defun fn-store-text-octetsp-tail (xs)
  (if (consp xs)
      (and (fn-octetp (car xs)) (<= 33 (car xs)) (<= (car xs) 126)
           (fn-store-text-octetsp-tail (cdr xs)))
    (null xs)))

(defun fn-store-text-octetsp (xs)
  (and (consp xs)
       (<= (len xs) *fn-store-max-text*)
       (fn-octet-listp xs)
       (<= 33 (car xs)) (<= (car xs) 126)
       (fn-store-text-octetsp-tail (cdr xs))))

(defun fn-store-msgid-octetsp (xs)
  (and (fn-store-text-octetsp xs)
       (<= 3 (len xs))
       (equal (car xs) 60)
       (equal (car (last xs)) 62)))

(defun fn-store-octets->string (xs)
  (fn-record-octets-string xs))

(defun fn-store-group-code (code)
  (if (equal code 0) "fn.letters"
    (if (equal code 1) "fn.test" nil)))

(defun fn-store-groups-from-codes (codes)
  (if (consp codes)
      (let ((group (fn-store-group-code (car codes))))
        (if group
            (let ((rest (fn-store-groups-from-codes (cdr codes))))
              (if (or (equal rest :bad) (member-equal group rest))
                  :bad
                (cons group rest)))
          :bad))
    (if (null codes) nil :bad)))

(defun fn-store-decode-records (octet-records)
  (declare (xargs :mode :program))
  (if (consp octet-records)
      (let ((decoded (fn-record-decode-exact (car octet-records))))
        (if (and (consp decoded) (equal (car decoded) :ok)
                 (consp (cdr decoded)) (fn-record-p (car (cdr decoded))))
            (let ((rest (fn-store-decode-records (cdr octet-records))))
              (if (equal rest :bad) :bad (cons (car (cdr decoded)) rest)))
          :bad))
    (if (null octet-records) nil :bad)))

(defun fn-store-record-sequence (octets)
  (declare (xargs :mode :program))
  (let ((decoded (fn-record-decode-exact octets)))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (consp (cdr decoded)) (fn-record-p (car (cdr decoded))))
        (fn-record-sequence (car (cdr decoded)))
      -1)))

(defun fn-store-record-txid (octets)
  (declare (xargs :mode :program))
  (let ((decoded (fn-record-decode-exact octets)))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (consp (cdr decoded)) (fn-record-p (car (cdr decoded))))
        (fn-record-txid (car (cdr decoded)))
      -1)))

(defun fn-store-article-match (msgid payload groups node)
  (let ((article (fn-find-article msgid
                                  (fn-state-articles (fn-node-acceptance node)))))
    (if article
        (if (and (equal payload (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))
