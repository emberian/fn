; over-render-tests.lisp -- witnesses and teeth for books/over-render.lisp (Builder O, row O1).
;
; Fixture: five rows of fn.test (number 2 cross-posted to fn.other).  Rows 1, 2, 3 carry
; their overview column; row 4 is a plain row (no column: the payload-parse arm); row 5 is a
; reclaim tombstone (no line).  Every keystone's whole implication is evaluated on concrete
; cursors, leases and capacities; each hypothesis that is not a domain condition is removed
; once with the conclusion failing.

(in-package "ACL2")
(include-book "../../books/over-render")

(defconst *ovrt-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *ovrt-p1* (append (fn-record-string-octets "Subject: bb") '(13 10 13 10 66 13 10)))
(defconst *ovrt-p2* (append (fn-record-string-octets "Subject: ccc") '(13 10 13 10 67 13 10 67 13 10)))
(defconst *ovrt-p3* (append (fn-record-string-octets "Subject: plain") '(13 10 13 10 68 13 10)))
(defconst *ovrt-p4* (append *fn-rcl-magic* (make-list 137 :initial-element 0)))
(defconst *ovrt-w0* (fn-record-make 0 1 1 "<a@x>" *ovrt-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *ovrt-w1* (fn-record-make 1 2 2 "<b@x>" *ovrt-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *ovrt-w2* (fn-record-make 2 3 3 "<c@x>" *ovrt-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *ovrt-w3* (fn-record-make 3 4 4 "<d@x>" *ovrt-p3* '("fn.test") "o" "s" "e" 1 5))
(defconst *ovrt-w4* (fn-record-make 4 5 5 "<e@x>" *ovrt-p4* '("fn.test") "o" "s" "e" 1 5))

(defun ovrt-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *ovrt-a* (list *ovrt-p0* *ovrt-p1* *ovrt-p2* *ovrt-p3* *ovrt-p4*))
(defconst *ovrt-r0* (fn-cat-assign (ovrt-held *ovrt-w0* 0 nil) nil))
(defconst *ovrt-r1* (fn-cat-assign (ovrt-held *ovrt-w1* 1 nil) (list *ovrt-r0*)))
(defconst *ovrt-r2* (fn-cat-assign (ovrt-held *ovrt-w2* 2 nil) (list *ovrt-r0* *ovrt-r1*)))
(defconst *ovrt-r3* (fn-cat-assign (fn-held-plain *ovrt-w3* 3) (list *ovrt-r0* *ovrt-r1* *ovrt-r2*)))
(defconst *ovrt-r4* (fn-cat-assign (ovrt-held *ovrt-w4* 4 nil) (list *ovrt-r0* *ovrt-r1* *ovrt-r2* *ovrt-r3*)))
(defconst *ovrt-c* (list *ovrt-r0* *ovrt-r1* *ovrt-r2* *ovrt-r3* *ovrt-r4*))
(defconst *ovrt-server* '(110 102))   ; "nf"

; ---------------------------------------------------------------------------
; KO1 / KO1b: each probe, both arms, over a non-empty lease.
(defun ovrt-ko1 (group j server v fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil))
  (let ((l0 (fn-ovr-lease-list fn-ovr-lease)))
    (let* ((fn-ovr-lease (fn-ovr-put-probe group j server v fn-ovr-lease fn-arena fn-cat))
           (l2 (fn-ovr-lease-list fn-ovr-lease))
           (fn-ovr-lease (fn-ovr-lease-from-list l0 fn-ovr-lease))
           (ref (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
      (mv (list (equal l2 (append l0 ref))
                (equal (fn-ovr-probe-len group j server v fn-arena fn-cat) (len ref))
                (len ref))
          fn-ovr-lease))))

(defthm ovrt-ko1-witness
  (and (equal (car (mv-nth 0 (ovrt-ko1 "fn.test" 1 *ovrt-server* 6 '(1 2) *ovrt-a* *ovrt-c*))) t)
       (equal (cadr (mv-nth 0 (ovrt-ko1 "fn.test" 1 *ovrt-server* 6 '(1 2) *ovrt-a* *ovrt-c*))) t)
       (< 0 (caddr (mv-nth 0 (ovrt-ko1 "fn.test" 1 *ovrt-server* 6 '(1 2) *ovrt-a* *ovrt-c*))))
       ;; the cross-posted row: its Xref names both groups
       (equal (car (mv-nth 0 (ovrt-ko1 "fn.test" 2 *ovrt-server* 6 nil *ovrt-a* *ovrt-c*))) t)
       (equal (cadr (mv-nth 0 (ovrt-ko1 "fn.test" 2 *ovrt-server* 6 nil *ovrt-a* *ovrt-c*))) t)
       (equal (car (mv-nth 0 (ovrt-ko1 "fn.other" 1 *ovrt-server* 6 nil *ovrt-a* *ovrt-c*))) t)
       ;; the plain row: the payload-parse arm, a line nonetheless
       (not (fn-scol-facts (fn-scat-available-article "fn.test" 4 6 *ovrt-a* *ovrt-c*) *ovrt-c*))
       (equal (car (mv-nth 0 (ovrt-ko1 "fn.test" 4 *ovrt-server* 6 '(9) *ovrt-a* *ovrt-c*))) t)
       (< 0 (caddr (mv-nth 0 (ovrt-ko1 "fn.test" 4 *ovrt-server* 6 '(9) *ovrt-a* *ovrt-c*))))
       ;; the tombstone: no line, the lease unchanged
       (equal (mv-nth 0 (ovrt-ko1 "fn.test" 5 *ovrt-server* 6 '(9) *ovrt-a* *ovrt-c*)) '(t t 0))
       ;; no server name: the plain reader's arm
       (equal (car (mv-nth 0 (ovrt-ko1 "fn.test" 3 nil 6 nil *ovrt-a* *ovrt-c*))) t)
       (< 0 (caddr (mv-nth 0 (ovrt-ko1 "fn.test" 3 nil 6 nil *ovrt-a* *ovrt-c*))))
       ;; past the group's high, and invisible at view 2
       (equal (mv-nth 0 (ovrt-ko1 "fn.test" 9 *ovrt-server* 6 nil *ovrt-a* *ovrt-c*)) '(t t 0))
       (equal (mv-nth 0 (ovrt-ko1 "fn.test" 3 *ovrt-server* 2 nil *ovrt-a* *ovrt-c*)) '(t t 0)))
  :rule-classes nil)

; Teeth for KO1's (true-listp lease): over an improper lease the written octets differ.
(defthm ovrt-ko1-improper-lease-teeth
  (not (car (mv-nth 0 (ovrt-ko1 "fn.test" 5 *ovrt-server* 6 '(1 . 2) *ovrt-a* *ovrt-c*))))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; KO2-KO5 over every capacity 0..400 at several cursors; KO6/KO7 over the runs.
(defun ovrt-step0 (cur n fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (mv-let (o nx) (fn-ovw-step cur n fn-arena fn-cat) (declare (ignore nx)) o))
(defun ovrt-step1 (cur n fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (mv-let (o nx) (fn-ovw-step cur n fn-arena fn-cat) (declare (ignore o)) nx))

(defun ovrt-ko-at (cur w cap fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil))
  (let ((lease (fn-ovr-lease-list fn-ovr-lease)))
    (mv-let (n next fn-ovr-lease) (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)
      (let* ((lease2 (fn-ovr-lease-list fn-ovr-lease))
             (fn-ovr-lease (fn-ovr-lease-from-list lease fn-ovr-lease))
             (room (- (nfix cap) (len lease)))
             (wmax (+ 1 (- (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w) (nfix (nth 1 cur)))))
             (ko2 (if (posp n)
                      (and (equal lease2 (append lease (ovrt-step0 cur n fn-arena fn-cat)))
                           (equal next (ovrt-step1 cur n fn-arena fn-cat)))
                    (and (equal lease2 lease) (equal next cur))))
             (ko3 (implies (<= (len lease) (nfix cap)) (<= (len lease2) (nfix cap))))
             (ko4 (<= n (if (posp w) w 1)))
             (ko5a (implies (and (<= (len lease) (nfix cap)) (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                                 (<= (len (ovrt-step0 cur 1 fn-arena fn-cat)) room))
                            (posp n)))
             (ko5b (implies (and (posp n) (< n wmax))
                            (< room (len (ovrt-step0 cur (+ 1 n) fn-arena fn-cat))))))
        (mv (list ko2 ko3 ko4 ko5a ko5b n) fn-ovr-lease)))))

(defun ovrt-all-true (xs) (if (consp xs) (and (car xs) (ovrt-all-true (cdr xs))) t))

; Failures over caps 0..CAP for one cursor, and the count of cases that took >= 1 number.
(defun ovrt-sweep (cur w cap fn-ovr-lease fn-arena fn-cat fails took)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil :measure (nfix cap)))
  (mv-let (r fn-ovr-lease) (ovrt-ko-at cur w cap fn-ovr-lease fn-arena fn-cat)
    (let ((fails (if (ovrt-all-true (take 5 r)) fails (cons (list cap r) fails)))
          (took (if (posp (nth 5 r)) (+ 1 took) took)))
      (if (zp cap) (mv fails took fn-ovr-lease)
        (ovrt-sweep cur w (- cap 1) fn-ovr-lease fn-arena fn-cat fails took)))))

(defun ovrt-run-sweep (cur w cap fn-ovr-lease fn-arena fn-cat fails oks)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil :measure (nfix cap)))
  (mv-let (okp octets fn-ovr-lease) (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)
    (let ((fails (if (implies okp (equal octets (fn-ovw-run cur w fn-arena fn-cat))) fails (cons cap fails)))
          (oks (if okp (+ 1 oks) oks)))
      (if (zp cap) (mv fails oks fn-ovr-lease)
        (ovrt-run-sweep cur w (- cap 1) fn-ovr-lease fn-arena fn-cat fails oks)))))
(defun ovrt-max-probe (group k top server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (<= k (nfix top)))
      (max (fn-ovr-probe-len group k server v fn-arena fn-cat)
           (ovrt-max-probe group (+ 1 k) top server v fn-arena fn-cat))
    0))
(defun ovrt-ko7-sweep (cur w cap hi fn-ovr-lease fn-arena fn-cat fails)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil :measure (nfix (- (+ 1 (nfix hi)) (nfix cap)))))
  (mv-let (okp octets fn-ovr-lease) (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)
    (declare (ignore octets))
    (let ((fails (if okp fails (cons cap fails))))
      (if (and (natp cap) (< cap (nfix hi)))
          (ovrt-ko7-sweep cur w (+ 1 cap) hi fn-ovr-lease fn-arena fn-cat fails)
        (mv fails fn-ovr-lease)))))
(defmacro ovrt-ko7 (cur w)
  `(let* ((c ,cur)
          (l (ovrt-max-probe (nth 0 c) (nfix (nth 1 c)) (nfix (nth 2 c)) (nth 6 c) (nfix (nth 3 c)) *ovrt-a* *ovrt-c*)))
     (and (posp l)
          (equal (mv-nth 0 (ovrt-ko7-sweep c ,w (+ l (fn-ovr-frame-max)) 500 nil *ovrt-a* *ovrt-c* nil)) nil)
          ;; removal of the cap hypothesis: a lease below one line stalls
          (not (mv-nth 0 (fn-ovr-run c ,w (- l 1) nil *ovrt-a* *ovrt-c*))))))
(defun ovrt-session (group) (fn-nntp-make-session t group nil t))
(defmacro ovrt-start (group token legacyp server)
  `(mv-nth 1 (fn-ovw-start (ovrt-session ,group) 6 (fn-record-string-octets ,token) ,legacyp ,server *ovrt-c*)))
(defmacro ovrt-ok (cur w lease)
  `(and (equal (mv-nth 0 (ovrt-sweep ,cur ,w 400 ,lease *ovrt-a* *ovrt-c* nil 0)) nil)
        (equal (mv-nth 0 (ovrt-run-sweep ,cur ,w 400 ,lease *ovrt-a* *ovrt-c* nil 0)) nil)))

(defthm ovrt-ko2-ko6-witness
  (and (ovrt-ok (ovrt-start "fn.test" "1-10" nil *ovrt-server*) 1 nil)
       (ovrt-ok (ovrt-start "fn.test" "1-10" nil *ovrt-server*) 3 '(1 2 3))
       (ovrt-ok (ovrt-start "fn.test" "1-10" t *ovrt-server*) 7 nil)
       (ovrt-ok (ovrt-start "fn.test" "1-10" nil nil) 2 nil)
       (ovrt-ok (ovrt-start "fn.test" "3-" nil *ovrt-server*) 2 nil)
       (ovrt-ok (ovrt-start "fn.other" "1-10" nil *ovrt-server*) 2 nil)
       (ovrt-ok (ovrt-start "fn.test" "7-9" nil nil) 2 nil)
       (ovrt-ok (ovrt-start "fn.test" "7-9" t nil) 2 '(1 2 3))
       (ovrt-ok (fn-ovw-cursor "fn.test" 4 5 6 nil t *ovrt-server*) 1 nil))
  :rule-classes nil)

; The antecedents are met: most capacities take a number and complete the run.
(defthm ovrt-ko5-ko6-satisfied
  (and (< 250 (mv-nth 1 (ovrt-sweep (ovrt-start "fn.test" "1-10" nil *ovrt-server*) 3 400 nil *ovrt-a* *ovrt-c* nil 0)))
       (< 250 (mv-nth 1 (ovrt-run-sweep (ovrt-start "fn.test" "1-10" nil *ovrt-server*) 3 400 nil *ovrt-a* *ovrt-c* nil 0))))
  :rule-classes nil)

; KO7 from L + framing up to 500, and the removal of its capacity hypothesis: L - 1 stalls.
(defthm ovrt-ko7-witness
  (and (ovrt-ko7 (ovrt-start "fn.test" "1-10" nil *ovrt-server*) 1)
       (ovrt-ko7 (ovrt-start "fn.test" "1-10" t nil) 3)
       (ovrt-ko7 (ovrt-start "fn.test" "2-" nil *ovrt-server*) 7))
  :rule-classes nil)

; Removal of the header-cursor hypothesis (KO5, KO7): a header cursor takes no number
; although its one-number window fits, and its run stalls.
(defthm ovrt-header-cursor-teeth
  (let ((c (fn-ovw-hdr-cursor "fn.test" 1 3 6 t (list 0 0 "subject" nil))))
    (and (equal (mv-nth 0 (ovrt-ko-at c 2 400 nil *ovrt-a* *ovrt-c*)) (list t t t nil t 0))
         (not (mv-nth 0 (fn-ovr-run c 2 400 nil *ovrt-a* *ovrt-c*)))))
  :rule-classes nil)

; Removal of the server-octets hypothesis (KO5, KO7): a server name that is not an octet
; list takes no number, and its run stalls.
(defthm ovrt-server-octets-teeth
  (let ((c (fn-ovw-cursor "fn.test" 1 5 6 nil t '(300))))
    (and (equal (nth 3 (mv-nth 0 (ovrt-ko-at c 2 400 nil *ovrt-a* *ovrt-c*))) nil)
         (not (mv-nth 0 (fn-ovr-run c 2 400 nil *ovrt-a* *ovrt-c*)))))
  :rule-classes nil)

; Mutation (KO5's maximality is tight): one octet less than the two-number window takes one.
(defthm ovrt-largest-tight
  (let* ((c (ovrt-start "fn.test" "1-10" nil *ovrt-server*))
         (two (len (ovrt-step0 c 2 *ovrt-a* *ovrt-c*))))
    (and (equal (mv-nth 0 (fn-ovr-quantum c 5 two nil *ovrt-a* *ovrt-c*)) 2)
         (equal (mv-nth 0 (fn-ovr-quantum c 5 (- two 1) nil *ovrt-a* *ovrt-c*)) 1)))
  :rule-classes nil)

; Removal of the fixnum-capacity hypothesis (KO5, KO7): a capacity of 2^59 takes no number
; although every window fits, and its run stalls.
(defthm ovrt-cap-fixnum-teeth
  (let ((c (ovrt-start "fn.test" "1-10" nil *ovrt-server*)))
    (and (equal (mv-nth 0 (fn-ovr-quantum c 5 (expt 2 59) nil *ovrt-a* *ovrt-c*)) 0)
         (equal (mv-nth 0 (fn-ovr-quantum c 5 (- (expt 2 59) 1) nil *ovrt-a* *ovrt-c*)) 5)
         (not (mv-nth 0 (fn-ovr-run c 5 (expt 2 59) nil *ovrt-a* *ovrt-c*)))))
  :rule-classes nil)

; An empty range (K past TOP: OVER 5-3, and a low bound past the group's last article) is
; one quantum that writes the close: KO2's window of one, and the run completes (KO6, KO7).
(defthm ovrt-empty-range-witness
  (let ((c1 (ovrt-start "fn.test" "5-3" nil *ovrt-server*))
        (c2 (ovrt-start "fn.test" "9-12" t nil))
        (c3 '("g" 5 3 0 nil t nil)))
    (and (< (nfix (nth 2 c1)) (nfix (nth 1 c1)))
         (ovrt-ok c1 1 nil) (ovrt-ok c2 3 '(1 2)) (ovrt-ok c3 1 nil)
         (equal (mv-nth 0 (fn-ovr-quantum c1 1 100 nil *ovrt-a* *ovrt-c*)) 1)
         (mv-nth 0 (fn-ovr-run c1 1 100 nil *ovrt-a* *ovrt-c*))
         (mv-nth 0 (fn-ovr-run c3 1 100 nil *ovrt-a* *ovrt-c*))
         (equal (mv-nth 1 (fn-ovr-run c2 3 100 nil *ovrt-a* *ovrt-c*))
                (fn-ovw-run c2 3 *ovrt-a* *ovrt-c*))))
  :rule-classes nil)
