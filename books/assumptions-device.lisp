; The storage device, as the commit keystone sees it: a log of what the host
; handed the device and what the device answered, crash images over it, and
; A-FENCE-PERSISTS, the one assumed fact about which images a crash leaves.
; Lists only: the log is written by books/commit-durable-all.lisp's
; environment run, never by the served core.
(in-package "ACL2")

; LOG ENTRIES, in the order the host performed them:
;   (:take SLOT GEN KIND OFFSET FUA OCTETS)  the device received operation
;       (SLOT GEN) of action KIND for storage OFFSET; OCTETS are the payload
;       it carries (a write's, a send's; nil otherwise)
;   (:result SLOT GEN EVKIND OUTCOME COUNT)  the core accepted the device's
;       terminal answer for (SLOT GEN)
(defconst *fn2-dev-write-kind* 6)        ; *fn2-action-write*
(defconst *fn2-dev-fence-kind* 7)        ; *fn2-action-fence*
(defconst *fn2-dev-write-result* 6)      ; *fn2-event-write-result*
(defconst *fn2-dev-fence-result* 7)      ; *fn2-event-fence-result*
(defconst *fn2-dev-done* 0)              ; *fn2-outcome-done*

(defun fn2-dev-field (i e)
  (declare (xargs :guard (natp i)))
  (if (true-listp e) (nth i e) nil))
(defun fn2-dev-takep (e)
  (declare (xargs :guard t))
  (and (true-listp e) (equal (len e) 7) (eq (car e) :take)))
(defun fn2-dev-resultp (e)
  (declare (xargs :guard t))
  (and (true-listp e) (equal (len e) 6) (eq (car e) :result)))
(defun fn2-dev-take-writep (e)
  (declare (xargs :guard t))
  (and (fn2-dev-takep e) (equal (nth 3 e) *fn2-dev-write-kind*)
       (natp (nth 4 e)) (true-listp (nth 6 e))))

; The first answer for (SLOT GEN) in LOG, as the tail starting at it.
(defun fn2-dev-answer (slot gen log)
  (declare (xargs :guard t))
  (cond ((atom log) nil)
        ((and (fn2-dev-resultp (car log))
              (equal (nth 1 (car log)) slot) (equal (nth 2 (car log)) gen))
         log)
        (t (fn2-dev-answer slot gen (cdr log)))))

; A successful answer of EVKIND moving COUNT octets (COUNT nil: any).
(defun fn2-dev-done-answer-p (tail evkind count)
  (declare (xargs :guard t))
  (and (consp tail) (fn2-dev-resultp (car tail))
       (equal (nth 3 (car tail)) evkind)
       (equal (nth 4 (car tail)) *fn2-dev-done*)
       (or (not count) (equal (nth 5 (car tail)) count))))

; Some fence taken in LOG whose first answer is a successful fence result.
(defun fn2-dev-fence-after-p (log)
  (declare (xargs :guard t))
  (if (atom log) nil
    (or (and (fn2-dev-takep (car log))
             (equal (nth 3 (car log)) *fn2-dev-fence-kind*)
             (fn2-dev-done-answer-p
              (fn2-dev-answer (nth 1 (car log)) (nth 2 (car log)) (cdr log))
              *fn2-dev-fence-result* nil))
        (fn2-dev-fence-after-p (cdr log)))))

; Entry W of LOG is a write the device acknowledged as done in full, and
; either it was a FUA write, or a fence taken after that answer succeeded.
(defun fn2-dev-fenced-write-p (w log)
  (declare (xargs :guard t))
  (and (natp w) (true-listp log) (< w (len log))
       (let ((e (nth w log)))
         (and (fn2-dev-take-writep e)
              (let ((answer (fn2-dev-answer (nth 1 e) (nth 2 e) (nthcdr (+ 1 w) log))))
                (and (fn2-dev-done-answer-p answer *fn2-dev-write-result* (len (nth 6 e)))
                     (or (equal (nth 5 e) 1)
                         (fn2-dev-fence-after-p (cdr answer)))))))))

; IMAGES. Any object is an image: a list of segments (OFFSET . OCTETS),
; the first segment covering an address giving its octet; an address no
; segment covers reads 0. Every byte assignment is some image.
(defun fn2-dev-byte (x)
  (declare (xargs :guard t))
  (if (unsigned-byte-p 8 x) x 0))
(defun fn2-dev-covers-p (seg a)
  (declare (xargs :guard t))
  (and (consp seg) (natp (car seg)) (true-listp (cdr seg)) (natp a)
       (<= (car seg) a) (< a (+ (car seg) (len (cdr seg))))))
(defun fn2-dev-image-byte (image a)
  (declare (xargs :guard t))
  (cond ((atom image) 0)
        ((fn2-dev-covers-p (car image) a)
         (fn2-dev-byte (nth (- a (caar image)) (cdar image))))
        (t (fn2-dev-image-byte (cdr image) a))))
(defun fn2-dev-image-octets (image a n)
  (declare (xargs :guard (and (natp a) (natp n))))
  (if (zp n) nil
    (cons (fn2-dev-image-byte image a) (fn2-dev-image-octets image (+ 1 a) (- n 1)))))

; The segment a write take puts on the medium.
(defun fn2-dev-segment (e)
  (declare (xargs :guard t))
  (cons (nfix (fn2-dev-field 4 e)) (true-list-fix (fn2-dev-field 6 e))))

; Some write take in ENTRIES with no answer in PRIOR (not resolved before the
; write in question was handed over) carries BYTE at address A.
(defun fn2-dev-overwrites-p (a byte entries prior)
  (declare (xargs :guard t))
  (if (atom entries) nil
    (or (let ((e (car entries)))
          (and (fn2-dev-take-writep e)
               (not (fn2-dev-answer (nth 1 e) (nth 2 e) prior))
               (fn2-dev-covers-p (fn2-dev-segment e) a)
               (equal (fn2-dev-byte (nth (- a (nth 4 e)) (nth 6 e))) byte)))
        (fn2-dev-overwrites-p a byte (cdr entries) prior))))

; Address A (inside write W's range) of IMAGE holds W's octet, or the octet
; of a write that may land after W: one taken later, or one taken earlier
; that was still unanswered when W was taken.
(defun fn2-dev-byte-kept-p (a w log image)
  (declare (xargs :guard (and (natp a) (natp w) (true-listp log))))
  (let* ((e (nth w log)) (byte (fn2-dev-image-byte image a)))
    (or (equal byte (fn2-dev-byte (nth (nfix (- a (nfix (fn2-dev-field 4 e))))
                                       (true-list-fix (fn2-dev-field 6 e)))))
        (fn2-dev-overwrites-p a byte (take w log) (take w log))
        (fn2-dev-overwrites-p a byte (nthcdr (+ 1 w) log) nil))))
(defun fn2-dev-range-kept-p (a n w log image)
  (declare (xargs :guard (and (natp a) (natp n) (natp w) (true-listp log))
                  :measure (nfix n)))
  (if (zp n) t
    (and (fn2-dev-byte-kept-p a w log image)
         (fn2-dev-range-kept-p (+ 1 a) (- n 1) w log image))))
(defun fn2-dev-image-keeps-p (w log image)
  (declare (xargs :guard t))
  (and (natp w) (true-listp log)
       (let ((e (nth w log)))
         (fn2-dev-range-kept-p (nfix (fn2-dev-field 4 e)) (len (fn2-dev-field 6 e)) w log image))))

; The device whose every taken write reached the medium in take order.
(defun fn2-dev-taken-image (log)
  (declare (xargs :guard t))
  (if (atom log) nil
    (if (fn2-dev-take-writep (car log))
        (append (fn2-dev-taken-image (cdr log)) (list (fn2-dev-segment (car log))))
      (fn2-dev-taken-image (cdr log)))))

;; The witness: every write take is kept by the taken-order image.
(local (defthm fn2-dev-true-list-fix-id
  (implies (true-listp x) (equal (true-list-fix x) x))))
(local (defun fn2-dev-image-covers-p (image a)
  (if (atom image) nil
    (or (fn2-dev-covers-p (car image) a) (fn2-dev-image-covers-p (cdr image) a)))))
(local (defthm fn2-dev-image-byte-append
  (equal (fn2-dev-image-byte (append x y) a)
         (if (fn2-dev-image-covers-p x a) (fn2-dev-image-byte x a) (fn2-dev-image-byte y a)))))
(local (defthm fn2-dev-taken-image-append
  (equal (fn2-dev-taken-image (append x y))
         (append (fn2-dev-taken-image y) (fn2-dev-taken-image x)))))
(local (defthm fn2-dev-image-covers-append
  (equal (fn2-dev-image-covers-p (append x y) a)
         (or (fn2-dev-image-covers-p x a) (fn2-dev-image-covers-p y a)))))
(local (defthm fn2-dev-later-overwrites
  (implies (fn2-dev-image-covers-p (fn2-dev-taken-image entries) a)
           (fn2-dev-overwrites-p a (fn2-dev-image-byte (fn2-dev-taken-image entries) a) entries nil))))
(local (defthm fn2-dev-taken-image-split
  (implies (and (natp w) (< w (len log)) (fn2-dev-take-writep (nth w log)))
           (equal (fn2-dev-taken-image log)
                  (append (fn2-dev-taken-image (nthcdr (+ 1 w) log))
                          (list (fn2-dev-segment (nth w log)))
                          (fn2-dev-taken-image (take w log)))))
  :hints (("Goal" :use ((:instance fn2-dev-taken-image-append (x (take w log)) (y (nthcdr w log))))
           :in-theory (disable fn2-dev-taken-image-append fn2-dev-segment fn2-dev-take-writep)))))
(local (defthm fn2-dev-taken-image-byte-kept
  (implies (and (natp w) (< w (len log)) (fn2-dev-take-writep (nth w log))
                (fn2-dev-covers-p (fn2-dev-segment (nth w log)) a))
           (fn2-dev-byte-kept-p a w log (fn2-dev-taken-image log)))
  :hints (("Goal" :in-theory (disable fn2-dev-taken-image fn2-dev-overwrites-p)))))
(local (defthm fn2-dev-taken-image-range-kept
  (implies (and (natp w) (< w (len log)) (fn2-dev-take-writep (nth w log)) (natp a)
                (<= (nth 4 (nth w log)) a)
                (<= (+ a n) (+ (nth 4 (nth w log)) (len (nth 6 (nth w log))))))
           (fn2-dev-range-kept-p a n w log (fn2-dev-taken-image log)))
  :hints (("Goal" :induct (fn2-dev-range-kept-p a n w log (fn2-dev-taken-image log))
           :in-theory (disable fn2-dev-byte-kept-p fn2-dev-taken-image fn2-dev-taken-image-split)))))
(local (defthm fn2-dev-taken-image-keeps-every-write
  (implies (and (natp w) (true-listp log) (< w (len log)) (fn2-dev-take-writep (nth w log)))
           (fn2-dev-image-keeps-p w log (fn2-dev-taken-image log)))
  :hints (("Goal" :in-theory (disable fn2-dev-range-kept-p fn2-dev-taken-image fn2-dev-taken-image-split)))))

; A-FENCE-PERSISTS (the one assumption about the environment). A write the
; device answered done in full, made durable by its FUA or by a successful
; fence taken after that answer, is in every crash image, byte by byte,
; unless a write that may land after it replaced the byte. Unfenced writes
; may be lost, torn or reordered; nothing is promised about any other byte.
; CHOICE selects the image.
(encapsulate
 (((fn2-a-crash-image * *) => *))
 (local (defun fn2-a-crash-image (log choice)
          (declare (ignore choice)) (fn2-dev-taken-image log)))
 (defthm fn2-a-fence-persists
   (implies (fn2-dev-fenced-write-p w log)
            (fn2-dev-image-keeps-p w log (fn2-a-crash-image log choice)))
   :rule-classes nil
   :hints (("Goal" :use fn2-dev-taken-image-keeps-every-write
            :in-theory (disable fn2-dev-taken-image-keeps-every-write fn2-dev-image-keeps-p
                                fn2-dev-taken-image fn2-dev-take-writep)))))

;; LOG EXTENSION. A fenced write stays fenced as the log grows: the
;; invariant toward FN2-COMMIT-ACK-IMPLIES-RECOVERABLE carries durability
;; facts across every step through this one lemma.
(local (defthm fn2-dev-nthcdr-append
  (implies (<= (nfix n) (len x))
           (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))))
(local (defthm fn2-dev-nth-append-low
  (implies (< (nfix n) (len x)) (equal (nth n (append x y)) (nth n x)))))
(local (defthm fn2-dev-cdr-append
  (implies (consp x) (equal (cdr (append x y)) (append (cdr x) y)))))
(local (defthm fn2-dev-len-append (equal (len (append x y)) (+ (len x) (len y)))))
(local (defthm fn2-dev-done-answer-nil (not (fn2-dev-done-answer-p nil evkind count))))
(local (defthm fn2-dev-done-answer-append
  (implies (consp tail)
           (equal (fn2-dev-done-answer-p (append tail y) evkind count)
                  (fn2-dev-done-answer-p tail evkind count)))))
(defthm fn2-dev-answer-append
  (equal (fn2-dev-answer slot gen (append x y))
         (if (fn2-dev-answer slot gen x)
             (append (fn2-dev-answer slot gen x) y)
           (fn2-dev-answer slot gen y))))
(defthm fn2-dev-fence-after-append
  (implies (fn2-dev-fence-after-p x) (fn2-dev-fence-after-p (append x y))))
(defthm fn2-dev-fenced-write-extends
  (implies (and (fn2-dev-fenced-write-p w log) (true-listp more))
           (fn2-dev-fenced-write-p w (append log more)))
  :hints (("Goal" :in-theory (disable fn2-dev-take-writep fn2-dev-done-answer-p fn2-dev-answer
                                      fn2-dev-fence-after-p binary-append nthcdr nth len))))

; A fenced write at storage OFFSET carrying OCTETS, from entry W on.
(defun fn2-dev-fenced-at-from (w offset octets log)
  (declare (xargs :guard (natp w) :measure (nfix (- (len log) (nfix w)))))
  (cond ((not (and (natp w) (true-listp log) (< w (len log)))) nil)
        ((and (fn2-dev-fenced-write-p w log)
              (equal (nth 4 (nth w log)) offset) (equal (nth 6 (nth w log)) octets))
         t)
        (t (fn2-dev-fenced-at-from (+ 1 w) offset octets log))))
(defthm fn2-dev-fenced-at-extends
  (implies (and (fn2-dev-fenced-at-from w offset octets log) (true-listp more))
           (fn2-dev-fenced-at-from w offset octets (append log more)))
  :hints (("Goal" :induct (fn2-dev-fenced-at-from w offset octets log)
           :in-theory (disable fn2-dev-fenced-write-p nth len binary-append))))
; Some fenced write at storage OFFSET (any octets), from entry W on.
(defun fn2-dev-fenced-offset-from (w offset log)
  (declare (xargs :guard (natp w) :measure (nfix (- (len log) (nfix w)))))
  (cond ((not (and (natp w) (true-listp log) (< w (len log)))) nil)
        ((and (fn2-dev-fenced-write-p w log) (equal (nth 4 (nth w log)) offset)) t)
        (t (fn2-dev-fenced-offset-from (+ 1 w) offset log))))
(defthm fn2-dev-fenced-offset-extends
  (implies (and (fn2-dev-fenced-offset-from w offset log) (true-listp more))
           (fn2-dev-fenced-offset-from w offset (append log more)))
  :hints (("Goal" :induct (fn2-dev-fenced-offset-from w offset log)
           :in-theory (disable fn2-dev-fenced-write-p nth len binary-append))))
