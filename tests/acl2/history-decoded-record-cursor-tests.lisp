(in-package "ACL2")
(include-book "../../books/history-decoded-record-cursor")

(defun fn-hrcur-test-nil-tick-values (c)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v next) (fn-hrcur-nil-tick c) (list v next)))
(defun fn-hrcur-test-nil-supply-values (c position byte)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v next) (fn-hrcur-nil-supply c position byte) (list v next)))

(defun fn-hrcur-test-nil-run (fuel c pool)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (list :yield c)
    (mv-let (v next) (fn-hrcur-nil-tick c)
      (if (and (consp v) (eq (car v) :need-byte))
          (mv-let (sv supplied) (fn-hrcur-nil-supply next (cadr v) (nth (cadr v) pool))
            (if (eq sv :continue) (fn-hrcur-test-nil-run (1- fuel) supplied pool)
              (list sv supplied)))
        (list v next)))))

(defun fn-hrcur-test-nil-supply-conclusion (c position byte pool)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v next) (fn-hrcur-nil-supply c position byte)
    (and (equal v :continue) (fn-hrcur-nil-invariantp next pool))))

(defun fn-hrcur-test-nil-tick-conclusion (c pool)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v next) (fn-hrcur-nil-tick c)
    (and (fn-hrcur-nil-invariantp next pool)
         (implies (equal v '(:done :nil))
                  (fn-hrcur-nil-model (fn-hrcur-field 1 c) (fn-hrcur-field 2 c)
                                     (fn-hrcur-field 3 c) pool))
         (implies (equal v '(:done :not-nil))
                  (not (fn-hrcur-nil-model (fn-hrcur-field 1 c) (fn-hrcur-field 2 c)
                                          (fn-hrcur-field 3 c) pool))))))

; Complete initialization antecedent/result; both NIL packages, yield/resume.
(assert-event
 (let* ((pool '(9 78 73 76 9))
        (c (fn-hrcur-nil-begin 1 1 3 '(:epoch :pass :row) :lease))
        (first (fn-hrcur-test-nil-run 2 c pool))
        (second (fn-hrcur-test-nil-run 2 (cadr first) pool)))
   (and (member-equal 1 '(0 1 2)) (natp 1) (natp 3)
        (< (+ 1 3) *fn-hrcur-u64-bound*)
        (fn-scc-octet-listp pool) (<= (+ 1 3) (len pool))
        (fn-hrcur-nil-invariantp c pool)
        (eq (car first) :yield) (equal (car second) '(:done :nil))
        (fn-hrcur-nil-invariantp (cadr second) pool)
        (equal (fn-hrcur-field 5 (cadr second)) '(:epoch :pass :row))
        (equal (fn-hrcur-field 6 (cadr second)) :lease))))
(assert-event
 (let* ((pool '(78 73 76)) (c (fn-hrcur-nil-begin 2 0 3 :capture :lease)))
   (and (fn-hrcur-nil-invariantp c pool)
        (equal (car (fn-hrcur-test-nil-run 4 c pool)) '(:done :nil)))))
(assert-event
 (let* ((pool '(78 73 76)) (c (fn-hrcur-nil-begin 0 0 3 :capture :lease)))
   (and (fn-hrcur-nil-invariantp c pool)
        (equal (car (fn-hrcur-test-nil-run 1 c pool)) '(:done :not-nil)))))
(assert-event
 (let* ((pool '(78 73 76 88)) (c (fn-hrcur-nil-begin 1 0 4 :capture :lease)))
   (and (fn-hrcur-nil-invariantp c pool)
        (equal (car (fn-hrcur-test-nil-run 1 c pool)) '(:done :not-nil)))))
(assert-event
 (let* ((pool '(78 73 88)) (c (fn-hrcur-nil-begin 1 0 3 :capture :lease)))
   (and (fn-hrcur-nil-invariantp c pool)
        (equal (car (fn-hrcur-test-nil-run 4 c pool)) '(:done :not-nil)))))

; Full supply theorem antecedent/conclusion at every matched byte.
(assert-event
 (let ((c '(:check 1 0 3 1 :capture :lease)) (pool '(78 73 76)))
   (and (fn-hrcur-nil-invariantp c pool) (eq (fn-hrcur-field 0 c) :check)
        (equal 1 (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
        (equal 73 (nth 1 pool))
        (fn-hrcur-test-nil-supply-conclusion c 1 73 pool))))

; Supply invariant removal: earlier byte does not match carried prefix.
(assert-event
 (let ((c '(:check 1 0 3 1 :capture :lease)) (pool '(88 73 76)))
   (and (not (fn-hrcur-nil-invariantp c pool)) (eq (fn-hrcur-field 0 c) :check)
        (equal 1 (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
        (equal 73 (nth 1 pool))
        (not (fn-hrcur-test-nil-supply-conclusion c 1 73 pool)))))
; Supply phase removal: valid terminal state has no outstanding request.
(assert-event
 (let ((c '(:nil 1 0 3 3 :capture :lease)) (pool '(78 73 76 0)))
   (and (fn-hrcur-nil-invariantp c pool) (not (eq (fn-hrcur-field 0 c) :check))
        (equal 3 (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
        (equal 0 (nth 3 pool))
        (not (fn-hrcur-test-nil-supply-conclusion c 3 0 pool)))))
; Supply expected-position removal; response is correct at its other position.
(assert-event
 (let ((c '(:check 1 0 3 0 :capture :lease)) (pool '(78 73 76)))
   (and (fn-hrcur-nil-invariantp c pool) (eq (fn-hrcur-field 0 c) :check)
        (not (equal 1 (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c))))
        (equal 73 (nth 1 pool))
        (not (fn-hrcur-test-nil-supply-conclusion c 1 73 pool)))))
; Supply byte attribution removal: a wrong octet falsely selects non-NIL.
(assert-event
 (let ((c '(:check 1 0 3 1 :capture :lease)) (pool '(78 73 76)))
   (and (fn-hrcur-nil-invariantp c pool) (eq (fn-hrcur-field 0 c) :check)
        (equal 1 (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
        (not (equal 88 (nth 1 pool)))
        (not (fn-hrcur-test-nil-supply-conclusion c 1 88 pool)))))

; Tick theorem full antecedent/conclusion and its sole invariant removal.
(assert-event
 (let ((c '(:nil 1 0 3 3 :capture :lease)) (pool '(78 73 76)))
   (and (fn-hrcur-nil-invariantp c pool) (fn-hrcur-test-nil-tick-conclusion c pool))))
(assert-event
 (let ((c '(:nil 1 0 3 3 :capture :lease)) (pool '(78 73 88)))
   (and (not (fn-hrcur-nil-invariantp c pool))
        (not (fn-hrcur-test-nil-tick-conclusion c pool)))))

; Stale position refuses unchanged, including replay after one supply.
(assert-event
 (let* ((c (fn-hrcur-nil-begin 1 0 3 :capture :lease))
        (next (cadr (fn-hrcur-test-nil-supply-values c 0 78))))
   (and (not (equal 0 (+ (fn-hrcur-field 2 next) (fn-hrcur-field 4 next))))
        (equal (fn-hrcur-test-nil-supply-values next 0 78)
               (list '(:refused :nil-response) next))
        (equal (cadr (fn-hrcur-test-nil-tick-values next)) next))))

; Actual decoded NIL tail: canonical row becomes one opaque octet list.
(defthm fn-hrcur-test-nil-tail-canonical-collapse
  (and (member-equal 1 '(0 1 2)) (fn-scc-octet-listp '(78 73 76))
       (natp 0) (natp 3) (<= (+ 0 3) (len '(78 73 76)))
       (equal (fn-hrcur-nil-model 1 0 3 '(78 73 76))
              (equal (fn-hdc-abstract (fn-hdc-span 4 1 0 3) '(78 73 76)) nil))
       (equal (fn-scc-encode
                (fn-hdc-abstract
                  (fn-hdc-pair (fn-hdc-atom 65) (fn-hdc-span 4 1 0 3)) '(78 73 76)))
              (fn-scc-encode '(65))))
  :hints (("Goal" :in-theory (enable fn-hrcur-nil-model fn-hdc-span fn-hdc-atom
                                    fn-hdc-pair fn-hdc-abstract fn-scc-intern))))

(defun fn-hrcur-test-nil-progress-conclusion (c position byte)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v next) (fn-hrcur-nil-supply c position byte)
    (declare (ignore v))
    (< (fn-hrcur-nil-work next) (fn-hrcur-nil-work c))))

(assert-event
 (let ((c '(:check 1 0 3 1 :capture :lease)) (position 1) (byte 73))
   (and (fn-hrcur-nil-shapep c) (eq (fn-hrcur-field 0 c) :check)
        (< (fn-hrcur-field 4 c) 3)
        (equal position (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
        (fn-scc-octetp byte) (fn-hrcur-test-nil-progress-conclusion c position byte))))

; Productive-work hypothesis removal: shape/package.
(assert-event
 (let ((c '(:check 3 0 3 1 :capture :lease)) (position 1) (byte 73))
   (and (not (fn-hrcur-nil-shapep c))
        (eq (fn-hrcur-field 0 c) :check)
        (< (fn-hrcur-field 4 c) 3)
        (equal position (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
        (fn-scc-octetp byte)
        (not (fn-hrcur-test-nil-progress-conclusion c position byte)))))

; Productive-work hypothesis removal: outstanding check phase.
(assert-event
 (let ((c '(:nil 1 0 3 1 :capture :lease)) (position 1) (byte 73))
   (and (fn-hrcur-nil-shapep c)
        (not (eq (fn-hrcur-field 0 c) :check))
        (< (fn-hrcur-field 4 c) 3)
        (equal position (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
        (fn-scc-octetp byte)
        (not (fn-hrcur-test-nil-progress-conclusion c position byte)))))

; Productive-work hypothesis removal: remaining index.
(assert-event
 (let ((c '(:check 1 0 3 3 :capture :lease)) (position 3) (byte 73))
   (and (fn-hrcur-nil-shapep c)
        (eq (fn-hrcur-field 0 c) :check)
        (not (< (fn-hrcur-field 4 c) 3))
        (equal position (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
        (fn-scc-octetp byte)
        (not (fn-hrcur-test-nil-progress-conclusion c position byte)))))

; Productive-work hypothesis removal: position.
(assert-event
 (let ((c '(:check 1 0 3 1 :capture :lease)) (position 2) (byte 73))
   (and (fn-hrcur-nil-shapep c)
        (eq (fn-hrcur-field 0 c) :check)
        (< (fn-hrcur-field 4 c) 3)
        (not (equal position (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c))))
        (fn-scc-octetp byte)
        (not (fn-hrcur-test-nil-progress-conclusion c position byte)))))

; Productive-work hypothesis removal: octet.
(assert-event
 (let ((c '(:check 1 0 3 1 :capture :lease)) (position 1) (byte 300))
   (and (fn-hrcur-nil-shapep c)
        (eq (fn-hrcur-field 0 c) :check)
        (< (fn-hrcur-field 4 c) 3)
        (equal position (+ (fn-hrcur-field 2 c) (fn-hrcur-field 4 c)))
        (not (fn-scc-octetp byte))
        (not (fn-hrcur-test-nil-progress-conclusion c position byte)))))

; Unconditional tick/supply capture and lease preservation, including refusal.
(assert-event
 (let* ((c '(:check 1 0 3 1 (:epoch :pass :row) (:lease ticket)))
        (tick-next (cadr (fn-hrcur-test-nil-tick-values c)))
        (supply-next (cadr (fn-hrcur-test-nil-supply-values c 1 73))))
   (and (equal (fn-hrcur-field 5 tick-next) (fn-hrcur-field 5 c))
        (equal (fn-hrcur-field 6 tick-next) (fn-hrcur-field 6 c))
        (equal (fn-hrcur-field 5 supply-next) (fn-hrcur-field 5 c))
        (equal (fn-hrcur-field 6 supply-next) (fn-hrcur-field 6 c)))))

; Initialization hypothesis-removal witnesses; the u64 sum removal would need
; a pool of at least 2^64 octets and is not represented by a finite fixture.
(assert-event
 (let ((pkg 3) (offset 0) (count 3) (pool '(78 73 76)))
   (and (not (member-equal pkg '(0 1 2))) (natp offset) (natp count)
        (< (+ offset count) *fn-hrcur-u64-bound*) (fn-scc-octet-listp pool)
        (<= (+ offset count) (len pool))
        (not (fn-hrcur-nil-invariantp (fn-hrcur-nil-begin pkg offset count :capture :lease) pool)))))
(assert-event
 (let ((pkg 1) (offset -1) (count 3) (pool '(78 73 76)))
   (and (member-equal pkg '(0 1 2)) (not (natp offset)) (natp count)
        (< (+ offset count) *fn-hrcur-u64-bound*) (fn-scc-octet-listp pool)
        (<= (+ offset count) (len pool))
        (not (fn-hrcur-nil-invariantp (fn-hrcur-nil-begin pkg offset count :capture :lease) pool)))))
(assert-event
 (let ((pkg 1) (offset 0) (count -1) (pool '(78 73 76)))
   (and (member-equal pkg '(0 1 2)) (natp offset) (not (natp count))
        (< (+ offset count) *fn-hrcur-u64-bound*) (fn-scc-octet-listp pool)
        (<= (+ offset count) (len pool))
        (not (fn-hrcur-nil-invariantp (fn-hrcur-nil-begin pkg offset count :capture :lease) pool)))))
(assert-event
 (let ((pkg 1) (offset 0) (count 3) (pool '(78 73 300)))
   (and (member-equal pkg '(0 1 2)) (natp offset) (natp count)
        (< (+ offset count) *fn-hrcur-u64-bound*) (not (fn-scc-octet-listp pool))
        (<= (+ offset count) (len pool))
        (not (fn-hrcur-nil-invariantp (fn-hrcur-nil-begin pkg offset count :capture :lease) pool)))))
(assert-event
 (let ((pkg 1) (offset 0) (count 3) (pool '(78 73)))
   (and (member-equal pkg '(0 1 2)) (natp offset) (natp count)
        (< (+ offset count) *fn-hrcur-u64-bound*) (fn-scc-octet-listp pool)
        (not (<= (+ offset count) (len pool)))
        (not (fn-hrcur-nil-invariantp (fn-hrcur-nil-begin pkg offset count :capture :lease) pool)))))
