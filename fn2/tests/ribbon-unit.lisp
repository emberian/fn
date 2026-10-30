; Layer C2c unit: a Ribbon filter page built through the real build, checked
; by B's checker, probed through the real probe.
(in-package "ACL2")
(include-book "../books/ribbon")

; Message-ID j: "<i" six digits "@t>".
(defun fn2-rbt-digits (n k)
 (declare (xargs :verify-guards nil :measure (nfix k)))
 (if (zp k) nil (append (fn2-rbt-digits (floor n 10) (- k 1)) (list (+ 48 (mod n 10))))))
(defun fn2-rbt-mid (j) (declare (xargs :verify-guards nil)) (append (list 60 105) (fn2-rbt-digits j 6) (list 64 116 62)))
(defun fn2-rbt-mids (i n)
 (declare (xargs :verify-guards nil :measure (nfix (- n i))))
 (if (zp (- n i)) nil (cons (fn2-rbt-mid i) (fn2-rbt-mids (+ 1 i) n))))
(defun fn2-rbt-count (x l)
 (declare (xargs :verify-guards nil))
 (if (atom l) 0 (+ (if (equal x (car l)) 1 0) (fn2-rbt-count x (cdr l)))))

(defconst *fn2-rbt-keys* (fn2-rbt-mids 0 200))
; Every key and 56 Message-IDs that are no key, among them the empty one.
(defconst *fn2-rbt-queries* (append *fn2-rbt-keys* (list nil) (fn2-rbt-mids 1000 1055)))

;; Teeth for fn2-ribbon-no-false-negative. Positive: 200 keys, every key and
;; 56 others probed; every key answers :maybe and most others :absent (the
;; filter is not the always-maybe filter). Negative: a filter built without
;; key 17 answers :absent to it.
(defun fn2-ribbon-no-false-negative-positive ()
 (declare (xargs :verify-guards nil))
 (let ((r (fn2-ribbon-image *fn2-rbt-keys* nil *fn2-rbt-queries* nil)))
  (and (fn2-ribbon-keysp *fn2-rbt-keys*) (fn2-ribbon-keysp *fn2-rbt-queries*)
       (equal (car r) :sealed) (equal (cadr r) :ok)
       (fn2-ribbon-answers-sound *fn2-rbt-keys* *fn2-rbt-queries* (caddr r))
       (equal (fn2-rbt-count :maybe (take 200 (caddr r))) 200)
       (<= 50 (fn2-rbt-count :absent (nthcdr 200 (caddr r)))))))
(defun fn2-ribbon-no-false-negative-negative ()
 (declare (xargs :verify-guards nil))
 (let ((r (fn2-ribbon-image *fn2-rbt-keys* 17 *fn2-rbt-queries* nil)))
  (and (equal (nth 17 (caddr r)) :absent)
       (not (fn2-ribbon-answers-sound *fn2-rbt-keys* *fn2-rbt-queries* (caddr r))))))
(fn2-assert-owed-teeth fn2-ribbon-no-false-negative)

;; Teeth for fn2-ribbon-mutation-refused. Positive: one flipped bit or byte
;; in B's header, the filter header, the solution bytes and the padding is
;; each refused by name, while the unmutated page is accepted. Negative: a
;; change of zero (no mutation) is accepted, so the conclusion fails.
(defun fn2-rbt-refused (offs x)
 (declare (xargs :verify-guards nil))
 (or (atom offs)
     (let ((check (cadr (fn2-ribbon-image *fn2-rbt-keys* nil nil (cons (car offs) x)))))
      (and (keywordp check) (not (equal check :ok)) (fn2-rbt-refused (cdr offs) x)))))
(defun fn2-ribbon-mutation-refused-positive ()
 (declare (xargs :verify-guards nil))
 (and (equal (cadr (fn2-ribbon-image *fn2-rbt-keys* nil nil nil)) :ok)
      (fn2-rbt-refused '(0 9 96 100 144 300 400 65535) 1)
      (fn2-rbt-refused '(2 144 50000) 128)))
(defun fn2-ribbon-mutation-refused-negative ()
 (declare (xargs :verify-guards nil))
 (equal (cadr (fn2-ribbon-image *fn2-rbt-keys* nil nil (cons 144 0))) :ok))
(fn2-assert-owed-teeth fn2-ribbon-mutation-refused)

;; Measurement (laptop, pinned as a regression): 2,000 keys, 20,000 other
;; Message-IDs. Slots 2,000 + 125 + 63 = 2,188 bytes: 8.75 bits per key
;; (8.5 as keys grow; 60,000 keys measured 8.51). No key is ever :absent;
;; the false-positive count is the measured one at r = 8 (2^-8 = 0.39%).
(defconst *fn2-rbt-measure*
 (let ((r (fn2-ribbon-image (fn2-rbt-mids 0 2000) nil (append (fn2-rbt-mids 0 2000) (fn2-rbt-mids 100000 120000)) nil)))
  (list (car r) (cadr r) (fn2-rbt-count :maybe (take 2000 (caddr r))) (fn2-rbt-count :maybe (nthcdr 2000 (caddr r))))))
(assert-event (equal (take 3 *fn2-rbt-measure*) '(:sealed :ok 2000)))
(assert-event (<= (nth 3 *fn2-rbt-measure*) 160))
(value-triple (cw "fn2-ribbon measure: ~x0 false positives in 20000~%" (nth 3 *fn2-rbt-measure*)))
