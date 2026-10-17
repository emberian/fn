; Catchup article framing in bounded windows. The controller retains no line.
; Receive removes one leading dot; replay adds it. CRLF is preserved exactly.
(in-package "ACL2")
(include-book "peer-pull")

(defun fn-csp-framer (lines receivep)
  (declare (xargs :guard t))
  (list t nil nil (nfix lines) (if receivep t nil)))

(defun fn-csp-framerp (f)
  (declare (xargs :guard t))
  (and (true-listp f) (equal (len f) 5)
       (booleanp (fn-pull-at 0 f)) (booleanp (fn-pull-at 1 f))
       (booleanp (fn-pull-at 2 f)) (natp (fn-pull-at 3 f))
       (booleanp (fn-pull-at 4 f))
       (not (and (fn-pull-at 0 f) (fn-pull-at 1 f)))))

(defun fn-csp-framer-step (f byte)
  ; (word emitted next). A pending CR is one scalar, not a retained line.
  ; A :record-end consumes this byte, while :done/:refused consume none.
  (declare (xargs :guard t))
  (let* ((bolp (fn-pull-at 0 f)) (crp (fn-pull-at 1 f))
         (dotp (fn-pull-at 2 f)) (lines (nfix (fn-pull-at 3 f)))
         (receivep (fn-pull-at 4 f)))
    (cond
     ((zp lines) (list :done nil f))
     ((not (and (natp byte) (< byte 256))) (list :refused nil f))
     ((and crp (equal byte 10))
      (if (and receivep dotp)
          (list :refused nil f) ; a terminator inside an advertised record
        (list (if (equal lines 1) :record-end :next) '(13 10)
              (list t nil nil (1- lines) receivep))))
     (t
      (let ((prefix (if crp '(13) nil)))
        (cond
         ((equal byte 13)
          (list :next prefix (list nil t (and dotp (not crp)) lines receivep)))
         ((and bolp receivep (equal byte 46))
          (list :next prefix (list nil nil t lines receivep)))
         (t (list :next
                  (append prefix (if (and bolp (not receivep) (equal byte 46))
                                     '(46 46) (list byte)))
                  (list nil nil nil lines receivep)))))))))

(defun fn-csp-framer-window-aux (f input fuel out count used)
  (declare (xargs :guard (and (natp fuel) (true-listp out)
                              (natp count) (natp used))
                  :measure (nfix fuel) :verify-guards nil))
  (cond
   ((or (zp fuel) (<= 512 count))
    (list :yield f (revappend out nil) input used))
   ((atom input) (list :need f (revappend out nil) nil used))
   (t
    (let* ((step (fn-csp-framer-step f (car input)))
           (word (fn-pull-at 0 step))
           (emitted (fn-pull-list (fn-pull-at 1 step)))
           (next (fn-pull-at 2 step))
           (new-count (+ count (len emitted))))
      (cond
       ((member-eq word '(:done :refused))
        (list word f (revappend out nil) input used))
       ((< 512 new-count)
        (list :yield f (revappend out nil) input used))
       ((eq word :record-end)
        (list :record-end next (revappend out emitted) (cdr input) (1+ used)))
       (t (fn-csp-framer-window-aux
           next (cdr input) (1- fuel) (revappend emitted out)
           new-count (1+ used))))))))

(verify-guards fn-csp-framer-window-aux)

(defun fn-csp-framer-window (f input)
  ; Physical chunk ceiling is a scheduling/allocation quantum. The returned
  ; input tail and exact next framer resume, including a CR across windows.
  (declare (xargs :guard t))
  (if (or (not (fn-cbor-at-mostp input 512))
          (not (fn-cbor-octet-listp input)))
      (list :refused f nil input 0)
    (fn-csp-framer-window-aux f input 512 nil 0 0)))

(defun fn-csp-append-admit (used limit emission)
  ; Offset is the actual signed native off_t domain. Refusal precedes write
  ; and leaves the spool cursor unchanged. Limits are independently funded.
  (declare (xargs :guard t))
  (if (and (natp used) (natp limit) (< limit (expt 2 63))
           (fn-cbor-at-mostp emission 512) (fn-cbor-octet-listp emission)
           (<= (+ used (len emission)) limit))
      (list :write used (+ used (len emission)))
    (list :refused used used)))

(defthm fn-csp-framer-step-output-bounded
  (implies (fn-csp-framerp f)
           (<= (len (fn-pull-at 1 (fn-csp-framer-step f byte))) 2))
  :hints (("Goal" :in-theory (enable fn-csp-framer-step fn-csp-framerp fn-pull-at))))

(defthm fn-csp-framer-step-preserves-framer
  (implies (fn-csp-framerp f)
           (fn-csp-framerp (fn-pull-at 2 (fn-csp-framer-step f byte))))
  :hints (("Goal" :in-theory (enable fn-csp-framer-step fn-csp-framerp fn-pull-at))))

(defthm fn-csp-append-refusal-preserves-offset
  (implies (eq (car (fn-csp-append-admit used limit emission)) :refused)
           (equal (caddr (fn-csp-append-admit used limit emission)) used)))

(in-theory (disable fn-csp-framer-step fn-csp-framer-window
                    fn-csp-append-admit))

; -----------------------------------------------------------------------------
; No silent truncation (PRF claimed below): the window accounts for every octet.
; The reference is one framer step per octet; a window is a resumable prefix.

(defun fn-csp-framer-emit (f bytes)
  ; Logical reference: the octets the framer emits for BYTES, one step each.
  (declare (xargs :guard t))
  (if (atom bytes) nil
    (let ((step (fn-csp-framer-step f (car bytes))))
      (append (fn-pull-list (fn-pull-at 1 step))
              (fn-csp-framer-emit (fn-pull-at 2 step) (cdr bytes))))))

(defun fn-csp-framer-after (f bytes)
  (declare (xargs :guard t))
  (if (atom bytes) f
    (fn-csp-framer-after (fn-pull-at 2 (fn-csp-framer-step f (car bytes))) (cdr bytes))))

(local (defthm fn-csp-revappend-of-revappend
  (equal (revappend (revappend a b) c) (revappend b (append a c)))))

(defun fn-csp-framer-consumed (f input fuel count)
  ; How many input octets one window consumes (mirrors the window loop).
  (declare (xargs :guard (and (natp fuel) (natp count)) :measure (nfix fuel)
                  :verify-guards nil))
  (cond
   ((or (zp fuel) (<= 512 count) (atom input)) 0)
   (t
    (let* ((step (fn-csp-framer-step f (car input)))
           (word (fn-pull-at 0 step))
           (new-count (+ count (len (fn-pull-list (fn-pull-at 1 step))))))
      (cond ((member-eq word '(:done :refused)) 0)
            ((< 512 new-count) 0)
            ((eq word :record-end) 1)
            (t (+ 1 (fn-csp-framer-consumed (fn-pull-at 2 step) (cdr input)
                                            (1- fuel) new-count))))))))

(local (defthm fn-csp-framer-aux-accounts
  (implies (and (natp used) (true-listp input))
           (let* ((w (fn-csp-framer-window-aux f input fuel out count used))
                  (k (fn-csp-framer-consumed f input fuel count)))
             (and (equal (nth 4 w) (+ used k))
                  (equal (nth 3 w) (nthcdr k input))
                  (equal (nth 2 w) (revappend out (fn-csp-framer-emit f (take k input))))
                  (equal (nth 1 w) (fn-csp-framer-after f (take k input))))))
  :hints (("Goal" :induct (fn-csp-framer-window-aux f input fuel out count used)
                  :in-theory (enable fn-csp-framer-window-aux)))))

(local (defthm fn-csp-framer-consumed-bounded
  (<= (fn-csp-framer-consumed f input fuel count) (len input))
  :rule-classes :linear))

(local (defthm fn-csp-octet-list-true-listp
  (implies (fn-cbor-octet-listp x) (true-listp x))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(defthm fn-csp-framer-window-accounts-for-every-octet
  ; KEYSTONE (no silent truncation). A window consumes a prefix of INPUT and
  ; returns exactly the rest; what it emits is the per-octet framer output of
  ; that prefix and its next framer is the state after it. Nothing read is
  ; dropped, so chained windows frame the whole record stream.
  (let* ((w (fn-csp-framer-window f input))
         (used (nth 4 w)))
    (and (natp used)
         (<= used (len input))
         (equal (nth 3 w) (nthcdr used input))
         (equal (nth 2 w) (fn-csp-framer-emit f (take used input)))
         (equal (nth 1 w) (fn-csp-framer-after f (take used input)))))
  :hints (("Goal" :in-theory (enable fn-csp-framer-window)
                  :use ((:instance fn-csp-framer-aux-accounts
                                   (fuel 512) (out nil) (count 0) (used 0))))))
