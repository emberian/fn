(in-package "ACL2")
(include-book "../../books/over-byte-full-seek-range")
(defconst *obfst-source*
 (append (fn-record-string-octets "Subject: a") '(13 10)
         (fn-record-string-octets "From: c") '(13 10)
         (fn-record-string-octets "Date: d") '(13 10)
         (fn-record-string-octets "Message-ID: <e@x>") '(13 10 13 10 122 13 10)))
(defun obfst-token ()
 (mv-let (owners pins status) (fn-rpin-step nil '(31 nil nil) '(:acquire 7))
  (declare (ignore pins status)) (fn-rpin-token 7 owners)))
(defun-nx obfst-conclusionp (s fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (let ((r (fn-obc-one s fn-arena fn-cat)))
  (equal (append (mv-nth 0 r)
                 (fn-obc-actual-old-residual (mv-nth 1 r) fn-arena fn-cat))
         (fn-obc-actual-old-residual s fn-arena fn-cat))))

; Actual begin, complete antecedent and conclusion; fixed C1/V7.
(defthm obfst-positive-cached
 (let* ((source *obfst-source*) (fn-arena (list source)) (k 1)
        (top 3) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of source) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-begin range (obfst-token))))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (nth 0 s)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (obfst-conclusionp s fn-arena fn-cat)))
 :rule-classes nil)

; Actual begin, complete antecedent and conclusion; fixed C1/V7.
(defthm obfst-positive-uncached
 (let* ((source *obfst-source*) (fn-arena (list source)) (k 1)
        (top 3) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-hf-make (len source) nil 0 nil) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-begin range (obfst-token))))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (nth 0 s)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (obfst-conclusionp s fn-arena fn-cat)))
 :rule-classes nil)

; Actual begin, complete antecedent and conclusion; fixed C1/V7.
(defthm obfst-positive-invalid
 (let* ((source '(120 13 10)) (fn-arena (list source)) (k 1)
        (top 3) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of source) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-begin range (obfst-token))))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (nth 0 s)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (obfst-conclusionp s fn-arena fn-cat)))
 :rule-classes nil)

; Actual begin, complete antecedent and conclusion; fixed C1/V7.
(defthm obfst-positive-tombstone
 (let* ((source (append *fn-rcl-magic* (make-list 137 :initial-element 0))) (fn-arena (list source)) (k 1)
        (top 3) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of source) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-begin range (obfst-token))))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (nth 0 s)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (obfst-conclusionp s fn-arena fn-cat)))
 :rule-classes nil)

; Actual begin, complete antecedent and conclusion; fixed C1/V7.
(defthm obfst-positive-hole
 (let* ((source *obfst-source*) (fn-arena (list source)) (k 2)
        (top 3) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of source) nil (list (cons "fn.test" 1)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-begin range (obfst-token))))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (nth 0 s)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (obfst-conclusionp s fn-arena fn-cat)))
 :rule-classes nil)

; Actual begin, complete antecedent and conclusion; fixed C1/V7.
(defthm obfst-positive-unsupported-zero
 (let* ((source *obfst-source*) (fn-arena (list source)) (k 0)
        (top 3) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of source) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-begin range (obfst-token))))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (nth 0 s)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (obfst-conclusionp s fn-arena fn-cat)))
 :rule-classes nil)

; Actual begin, complete antecedent and conclusion; fixed C1/V7.
(defthm obfst-positive-exhausted
 (let* ((source *obfst-source*) (fn-arena (list source)) (k 1)
        (top 0) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of source) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-begin range (obfst-token))))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (nth 0 s)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (obfst-conclusionp s fn-arena fn-cat)))
 :rule-classes nil)

; Actual begin, complete antecedent and conclusion; fixed C1/V7.
(defthm obfst-positive-advanced-owed
 (let* ((source *obfst-source*) (fn-arena (list source)) (k 1)
        (top 3) (owed nil)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of source) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-begin range (obfst-token))))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (nth 0 s)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (obfst-conclusionp s fn-arena fn-cat)))
 :rule-classes nil)

; Corrupted-state literal removal, every retained hypothesis asserted.
(defthm obfst-without-phase
 (let* ((source *obfst-source*) (fn-arena (list source)) (k 1)
        (top 3) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of source) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-make range (obfst-token) :bad nil nil 0)))
  (declare (ignorable top owed))
  (and (not (equal (nth 2 s) :seek))
       (nth 0 s)
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (not (obfst-conclusionp s fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal removal, every retained hypothesis asserted.
(defthm obfst-without-range
 (let* ((source *obfst-source*) (fn-arena (list source)) (k 1)
        (top 3) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of source) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range nil)
        (s (fn-obc-make range (obfst-token) :seek nil nil 0)))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (not (nth 0 s))
       (fn-obc-seek-cached-source-p s fn-arena fn-cat)
       (not (obfst-conclusionp s fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal removal, every retained hypothesis asserted.
(defthm obfst-without-same-source
 (let* ((source *obfst-source*) (fn-arena (list source)) (k 1)
        (top 3) (owed t)
        (row (fn-held-make 0 1 0 "<e@x>" 0 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of (append (fn-record-string-octets "Subject: other") (nthcdr 10 source))) nil (list (cons "fn.test" k)) nil))
        (fn-cat (list row))
        (range (fn-ovw-cursor "fn.test" k top 7 nil owed))
        (s (fn-obc-make range (obfst-token) :seek nil nil 0)))
  (declare (ignorable top owed))
  (and (equal (nth 2 s) :seek)
       (nth 0 s)
       (not (fn-obc-seek-cached-source-p s fn-arena fn-cat))
       (not (obfst-conclusionp s fn-arena fn-cat))))
 :rule-classes nil)
