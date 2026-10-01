; Incremental nested statement-item decode. Source byte strings are borrowed,
; never copied. The caller retains the ORIGINALctx/source until consumption.
(in-package "ACL2")
(include-book "cbor")
(include-book "statement-results")

; All calls use literal state indices <=18. No source traversal is hidden here.
(defun fn-sic-at (i x)
 (declare (xargs :guard (natp i)))
 (if (zp i) (fn-cbor-ag-car x) (fn-sic-at (1- i) (fn-cbor-ag-cdr x))))
(defun fn-sic-put (i v x)
 (declare (xargs :guard (natp i)))
 (if (zp i) (cons v (fn-cbor-ag-cdr x))
  (cons (fn-cbor-ag-car x) (fn-sic-put (1- i) v (fn-cbor-ag-cdr x)))))

; phase/source/tail/pos/outer-left/item-budget/items-left/bad-octet/
; major/additional/argument-left/argument/byte-start/byte-count/byte-left/
; borrowed-content/reversed-items/ordered-items/result.
(defun fn-sic-begin (fuel octets outer-budget item-budget)
 (declare (xargs :guard (and (natp fuel) (natp outer-budget) (natp item-budget))))
 (list :preflight octets octets 0 outer-budget item-budget fuel nil
       nil 0 0 0 0 0 0 nil nil nil :pending))
(defun fn-sic-begin-legacy (fuel octets)
 (declare (xargs :guard (natp fuel)))
 (fn-sic-begin fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))
(defun fn-sic-finish (result c)
 (declare (xargs :guard t))
 (fn-sic-put 0 :done (fn-sic-put 18 result c)))
(defun fn-sic-error (code c)
 (declare (xargs :guard t))
 (fn-sic-finish (fn-stmt-error code) c))
(defun fn-sic-push (item c)
 (declare (xargs :guard t))
 (fn-sic-put 0 :head (fn-sic-put 16 (cons item (fn-sic-at 16 c)) c)))
(defun fn-sic-argument-start (major additional c)
 (declare (xargs :guard (natp additional)))
 (let ((d (fn-sic-put 8 major (fn-sic-put 9 additional c))))
  (cond ((< additional 24)
         (fn-sic-put 0 :argument-check (fn-sic-put 11 additional d)))
        ((or (equal additional 24) (equal additional 25) (equal additional 26))
         (fn-sic-put 0 :argument
          (fn-sic-put 10 (cond ((equal additional 24) 1) ((equal additional 25) 2) (t 4))
           (fn-sic-put 11 0 d))))
        (t (fn-sic-error :unsupported d)))))

; One step examines at most one borrowed source cons, or one result link.
; Preflight carries invalid-byte status but finishes :limit first, exactly as
; the original at-most check before whole-input octet validation does.
(defun fn-sic-step (c)
 (declare (xargs :guard t))
 (let* ((phase (fn-sic-at 0 c)) (tail (fn-sic-at 2 c))
        (pos (nfix (fn-sic-at 3 c))))
  (cond
   ((equal phase :done) c)
   ((equal phase :preflight)
    (if (consp tail)
     (if (zp (nfix (fn-sic-at 4 c))) (fn-sic-error :limit c)
      (fn-sic-put 2 (cdr tail)
       (fn-sic-put 3 (+ 1 pos)
        (fn-sic-put 4 (1- (nfix (fn-sic-at 4 c)))
         (fn-sic-put 7 (or (fn-sic-at 7 c) (not (fn-cbor-octetp (car tail)))) c)))))
     (if (or (fn-sic-at 7 c) tail) (fn-sic-error :malformed c)
      (fn-sic-put 0 :head (fn-sic-put 2 (fn-sic-at 1 c) (fn-sic-put 3 0 c))))))
   ((equal phase :head)
    (if (not (consp tail)) (fn-sic-put 0 :reverse c)
     (if (zp (nfix (fn-sic-at 6 c))) (fn-sic-error :too-many-items c)
      (let* ((head (car tail))
             (d (fn-sic-put 2 (cdr tail) (fn-sic-put 3 (+ 1 pos)
                 (fn-sic-put 6 (1- (nfix (fn-sic-at 6 c))) c)))))
       (cond ((and (natp head) (< head 32)) (fn-sic-argument-start :uint head d))
             ((and (natp head) (< 63 head) (< head 96)) (fn-sic-argument-start :bytes (- head 64) d))
             (t (fn-sic-error :unsupported d)))))))
   ((equal phase :argument)
    (if (not (consp tail)) (fn-sic-error :truncated c)
     (let* ((left (nfix (fn-sic-at 10 c)))
            (d (fn-sic-put 2 (cdr tail) (fn-sic-put 3 (+ 1 pos)
                (fn-sic-put 10 (nfix (1- left))
                 (fn-sic-put 11 (+ (* 256 (nfix (fn-sic-at 11 c))) (nfix (car tail))) c))))))
      (if (<= left 1) (fn-sic-put 0 :argument-check d) d))))
   ((equal phase :argument-check)
    (let ((argument (nfix (fn-sic-at 11 c))))
     (if (not (fn-cbor-canonical-argumentp (nfix (fn-sic-at 9 c)) argument))
      (fn-sic-error :noncanonical c)
      (if (equal (fn-sic-at 8 c) :uint) (fn-sic-push (cons :uint argument) c)
       (if (< (nfix (fn-sic-at 5 c)) argument) (fn-sic-error :limit c)
        (fn-sic-put 0 :bytes (fn-sic-put 12 pos (fn-sic-put 13 argument
         (fn-sic-put 14 argument (fn-sic-put 15 tail c))))))))))
   ((equal phase :bytes)
    (if (zp (nfix (fn-sic-at 14 c)))
     (fn-sic-push (list :bytes (nfix (fn-sic-at 12 c))
                   (nfix (fn-sic-at 13 c)) (fn-sic-at 15 c)) c)
     (if (not (consp tail)) (fn-sic-error :truncated c)
      (fn-sic-put 2 (cdr tail) (fn-sic-put 3 (+ 1 pos)
       (fn-sic-put 14 (1- (nfix (fn-sic-at 14 c))) c))))))
   ((equal phase :reverse)
    (let ((items (fn-sic-at 16 c)))
     (if (consp items)
      (fn-sic-put 16 (cdr items) (fn-sic-put 17 (cons (car items) (fn-sic-at 17 c)) c))
      (fn-sic-finish (fn-stmt-ok (fn-sic-at 17 c)) c))))
   (t (fn-sic-error :malformed c)))))
(defun fn-sic-result (c)
 (declare (xargs :guard t))
 (if (equal (fn-sic-at 0 c) :done) (fn-sic-at 18 c) :pending))

; Positive allocation/read cost is fixed per step; exhaustion yields the SAME
; continuation. Nothing treats a depleted scheduling quantum as a decode error.
(defun fn-sic-run (quantum c)
 (declare (xargs :guard (natp quantum) :measure (nfix quantum)))
 (if (or (zp quantum) (equal (fn-sic-at 0 c) :done)) c
  (fn-sic-run (1- quantum) (fn-sic-step c))))

(in-theory (disable fn-sic-at fn-sic-put fn-sic-begin fn-sic-begin-legacy
 fn-sic-finish fn-sic-error fn-sic-push fn-sic-argument-start fn-sic-step
 fn-sic-result fn-sic-run))
