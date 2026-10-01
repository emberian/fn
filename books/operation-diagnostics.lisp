; Fixed scalar diagnostic projection. Rendering consumes an admitted response
; octet allowance; this parameter alone is not an installation receipt.
(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-od-word (word)
 (declare (xargs :guard t))
 (case word
  (:observed '(111 98 115 101 114 118 101 100)) (:unavailable '(117 110 97 118 97 105 108 97 98 108 101))
  (:runtime-operation-unavailable '(114 117 110 116 105 109 101 45 111 112 101 114 97 116 105 111 110 45 117 110 97 118 97 105 108 97 98 108 101))
  (:response-budget-unavailable '(114 101 115 112 111 110 115 101 45 98 117 100 103 101 116 45 117 110 97 118 97 105 108 97 98 108 101))
  (:history-backing-unavailable '(104 105 115 116 111 114 121 45 98 97 99 107 105 110 103 45 117 110 97 118 97 105 108 97 98 108 101))
  (:operation-not-issued '(111 112 101 114 97 116 105 111 110 45 110 111 116 45 105 115 115 117 101 100))
  (:recovery-required '(114 101 99 111 118 101 114 121 45 114 101 113 117 105 114 101 100)) (:admitted '(97 100 109 105 116 116 101 100))
  (:reserved '(114 101 115 101 114 118 101 100)) (:produced '(112 114 111 100 117 99 101 100)) (:published '(112 117 98 108 105 115 104 101 100))
  (:promoted '(112 114 111 109 111 116 101 100)) (:uncertain '(117 110 99 101 114 116 97 105 110))
  (:released '(114 101 108 101 97 115 101 100)) (:waiting '(119 97 105 116 105 110 103)) (:yield '(121 105 101 108 100))
  (:refused '(114 101 102 117 115 101 100)) (:stale '(115 116 97 108 101)) (:stale-source '(115 116 97 108 101 45 115 111 117 114 99 101))
  (:idle '(105 100 108 101)) (:ready '(114 101 97 100 121)) (:writing '(119 114 105 116 105 110 103)) (:done '(100 111 110 101))
  (:request-budget '(114 101 113 117 101 115 116 45 98 117 100 103 101 116)) (:physical '(112 104 121 115 105 99 97 108))
  (:served '(115 101 114 118 101 100)) (:bootstrap '(98 111 111 116 115 116 114 97 112)) (:none '(110 111 110 101))
  (:writer-current '(119 114 105 116 101 114 45 99 117 114 114 101 110 116))
  (:writer-stale '(119 114 105 116 101 114 45 115 116 97 108 101))
  (:writer-source-changed '(119 114 105 116 101 114 45 115 111 117 114 99 101 45 99 104 97 110 103 101 100))
  (:offered '(111 102 102 101 114 101 100))
  (:prepared '(112 114 101 112 97 114 101 100))
  (:completed '(99 111 109 112 108 101 116 101 100))
  (:fenced '(102 101 110 99 101 100))
  (:active '(97 99 116 105 118 101))
  (:draining '(100 114 97 105 110 105 110 103))
  (:exhausted '(101 120 104 97 117 115 116 101 100))
  (:faulted '(102 97 117 108 116 101 100))
  (:article '(97 114 116 105 99 108 101))
  (:identity '(105 100 101 110 116 105 116 121))
  (:retention '(114 101 116 101 110 116 105 111 110))
  (:consumer '(99 111 110 115 117 109 101 114))
  (:topic '(116 111 112 105 99))
  (:config '(99 111 110 102 105 103))
  (:configuration '(99 111 110 102 105 103 117 114 97 116 105 111 110))
  (otherwise '(111 116 104 101 114))))

; A bounded decimal-width preflight, before allocating any digit list. Budget
; bounds work even when an observed identifier is an arbitrarily large natural.
(defun fn-od-nat-fits-p (n budget)
 (declare (xargs :guard (and (natp n) (natp budget))
                 :measure (nfix budget)))
 (and (posp budget)
      (or (< n 10) (fn-od-nat-fits-p (floor n 10) (1- budget)))))

(defun fn-od-digits (n acc)
 (declare (xargs :guard (and (natp n) (true-listp acc)) :measure (nfix n)))
 (if (zp n) acc
  (fn-od-digits (floor n 10) (cons (+ 48 (mod n 10)) acc))))
(defun fn-od-nat (n)
 (declare (xargs :guard (natp n)))
 (if (posp n) (fn-od-digits n nil) '(48)))

(defun fn-od-value (value budget)
 (declare (xargs :guard (natp budget)))
 (cond
  ((natp value)
   (if (fn-od-nat-fits-p value budget)
       (mv :rendered (fn-od-nat value)) (mv :response-budget-unavailable nil)))
  (t (let ((octets (if (null value) '(110 111 110 101) (fn-od-word value))))
       (if (<= (len octets) budget) (mv :rendered octets)
        (mv :response-budget-unavailable nil))))))

(defun fn-od-fieldsp (fields)
 (declare (xargs :guard t))
 (if (consp fields)
  (and (consp (car fields)) (true-listp (caar fields))
       (fn-od-fieldsp (cdr fields)))
  (null fields)))
(defthm fn-od-digits-true-listp
 (implies (true-listp acc) (true-listp (fn-od-digits n acc)))
 :rule-classes :type-prescription)
(defthm fn-od-value-true-listp
 (true-listp (mv-nth 1 (fn-od-value value budget)))
 :hints (("Goal" :in-theory (e/d (fn-od-value fn-od-nat) (fn-od-digits fn-od-nat-fits-p))))
 :rule-classes :type-prescription)

(defun fn-od-fields (fields budget)
 (declare (xargs :guard (and (natp budget) (fn-od-fieldsp fields))
                 :guard-hints (("Goal" :in-theory (disable fn-od-value fn-od-word fn-od-digits fn-od-nat fn-od-nat-fits-p)))))
 (if (atom fields) (mv :rendered nil)
  (let* ((field (car fields))
         (prefix (append '(32) (if (consp field) (car field) '(117 110 107 110 111 119 110)) '(61))))
   (if (> (len prefix) budget) (mv :response-budget-unavailable nil)
    (mv-let (word value)
     (fn-od-value (if (consp field) (cdr field) nil) (- budget (len prefix)))
     (if (or (not (eq word :rendered)) (> (+ (len prefix) (len value)) budget))
         (mv :response-budget-unavailable nil)
      (mv-let (next rest)
       (fn-od-fields (cdr fields) (- budget (+ (len prefix) (len value))))
       (if (eq next :rendered) (mv :rendered (append prefix value rest))
        (mv next nil)))))))))

(defthm fn-od-fields-true-listp
 (true-listp (mv-nth 1 (fn-od-fields fields budget)))
 :hints (("Goal" :induct (fn-od-fields fields budget)
                 :in-theory (disable fn-od-value)))
 :rule-classes :type-prescription)

(defun fn-od-report (availability reason phase producer epoch source publication
                     txid mode allocated turns charge0 charge1 charge2 charge3
                     charge4 fault budget)
 (declare (xargs :guard (natp budget)
                 :guard-hints (("Goal" :in-theory (disable fn-od-fields fn-od-value fn-od-digits fn-od-nat-fits-p)))))
 (let ((prefix '(111 112 101 114 97 116 105 111 110)))
  (if (< budget (+ 1 (len prefix))) (mv :response-budget-unavailable nil)
   (mv-let (word fields)
    (fn-od-fields
     (list (cons '(111 98 115 101 114 118 97 116 105 111 110) availability) (cons '(114 101 97 115 111 110) reason)
      (cons '(112 104 97 115 101) phase) (cons '(112 114 111 100 117 99 101 114) producer) (cons '(101 112 111 99 104) epoch)
      (cons '(115 111 117 114 99 101) source) (cons '(112 117 98 108 105 99 97 116 105 111 110) publication) (cons '(116 120 105 100) txid)
      (cons '(112 111 111 108 45 109 111 100 101) mode) (cons '(97 108 108 111 99 97 116 101 100) allocated) (cons '(97 99 116 105 118 101 45 116 117 114 110 115) turns)
      (cons '(104 111 108 100 48) charge0) (cons '(104 111 108 100 49) charge1) (cons '(104 111 108 100 50) charge2)
      (cons '(104 111 108 100 51) charge3) (cons '(104 111 108 100 52) charge4) (cons '(102 97 117 108 116) fault))
     (- budget (+ 1 (len prefix))))
    (if (eq word :rendered) (mv :rendered (append prefix fields '(10)))
     (mv word nil))))))

(local
 (defthm fn-od-len-append
 (equal (len (append x y)) (+ (len x) (len y)))
 :hints (("Goal" :induct (append x y)))))

(defthm fn-od-fields-within-budget
 (implies (natp budget)
  (<= (len (mv-nth 1 (fn-od-fields fields budget))) budget))
 :hints (("Goal" :induct (fn-od-fields fields budget)
                 :in-theory (disable binary-append fn-od-value fn-od-digits fn-od-nat fn-od-nat-fits-p)))
 :rule-classes nil)
(defthm fn-od-report-within-budget
 (implies (natp budget)
  (<= (len (mv-nth 1 (fn-od-report availability reason phase producer epoch source publication
       txid mode allocated turns charge0 charge1 charge2 charge3 charge4 fault budget))) budget))
 :hints (("Goal" :use ((:instance fn-od-fields-within-budget
         (budget (- budget 10))
         (fields (list (cons '(111 98 115 101 114 118 97 116 105 111 110) availability)
                       (cons '(114 101 97 115 111 110) reason)
                       (cons '(112 104 97 115 101) phase)
                       (cons '(112 114 111 100 117 99 101 114) producer)
                       (cons '(101 112 111 99 104) epoch)
                       (cons '(115 111 117 114 99 101) source)
                       (cons '(112 117 98 108 105 99 97 116 105 111 110) publication)
                       (cons '(116 120 105 100) txid)
                       (cons '(112 111 111 108 45 109 111 100 101) mode)
                       (cons '(97 108 108 111 99 97 116 101 100) allocated)
                       (cons '(97 99 116 105 118 101 45 116 117 114 110 115) turns)
                       (cons '(104 111 108 100 48) charge0)
                       (cons '(104 111 108 100 49) charge1)
                       (cons '(104 111 108 100 50) charge2)
                       (cons '(104 111 108 100 51) charge3)
                       (cons '(104 111 108 100 52) charge4)
                       (cons '(102 97 117 108 116) fault)))))
  :in-theory (e/d (fn-od-report) (fn-od-fields fn-od-value))))
 :rule-classes nil)

; Actual issued admission nonce and operation kind are scalar projections from
; the typed observer token. They never serialize a prepared operation graph.
(defun fn-od-correlated-report
 (nonce kind availability reason phase producer epoch source publication txid mode
  allocated turns charge0 charge1 charge2 charge3 charge4 fault budget)
 (declare (xargs :guard (natp budget)
  :guard-hints (("Goal" :in-theory (disable fn-od-fields fn-od-report fn-od-value fn-od-digits fn-od-nat-fits-p)))))
 (mv-let (word correlation)
  (fn-od-fields (list (cons '(97 100 109 105 115 115 105 111 110 45 110 111 110 99 101) nonce)
                      (cons '(111 112 101 114 97 116 105 111 110 45 107 105 110 100) kind)) budget)
  (if (or (not (eq word :rendered)) (> (len correlation) budget))
      (mv :response-budget-unavailable nil)
   (mv-let (word report)
    (fn-od-report availability reason phase producer epoch source publication txid mode
                  allocated turns charge0 charge1 charge2 charge3 charge4 fault (- budget (len correlation)))
    (if (eq word :rendered) (mv word (append correlation report))
     (mv word nil))))))
