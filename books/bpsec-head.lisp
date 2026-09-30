; Bounded deterministic CBOR head cursor for RFC 9172 section 3.6 ASBs.
; This is a grammar primitive, not a generic CBOR decoder or a security gate.
(in-package "ACL2")
(include-book "bpsec-model")

; At most eight argument octets are accumulated as a uint64 integer.  No
; field body, input window or raw ASB is retained in this cursor.
(defun fn-bps-head-start ()
  (declare (xargs :guard t))
  (list :bps-head :initial 0 0 0 0))

(defun fn-bps-head-width (ai)
  (declare (xargs :guard t))
  (cond ((equal ai 24) 1) ((equal ai 25) 2)
        ((equal ai 26) 4) ((equal ai 27) 8) (t 0)))

(defun fn-bps-head-minimum (ai)
  (declare (xargs :guard t))
  (cond ((equal ai 24) 24) ((equal ai 25) 256)
        ((equal ai 26) 65536) ((equal ai 27) 4294967296) (t 0)))

(defun fn-bps-headp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6) (eq (car x) :bps-head)
       (member-equal (fn-bps-field 1 x) '(:initial :argument :ready :refused :unsupported))
       (natp (fn-bps-field 2 x)) (< (fn-bps-field 2 x) 8)
       (natp (fn-bps-field 3 x)) (< (fn-bps-field 3 x) 32)
       (natp (fn-bps-field 4 x)) (<= (fn-bps-field 4 x) 8)
       (fn-bps-uintp (fn-bps-field 5 x))))

(defun fn-bps-head-feed (head octet)
  (declare (xargs :guard t))
  (let* ((phase (fn-bps-field 1 head))
         (major (fn-bps-field 2 head)) (ai (fn-bps-field 3 head))
         (remaining (fn-bps-field 4 head)) (value (fn-bps-field 5 head)))
    (cond
     ((not (and (fn-bps-headp head) (fn-cbor-octetp octet)))
      (list :refused :invalid-head-cursor head))
     ((eq phase :initial)
      (let ((m (floor octet 32)) (a (mod octet 32)))
        (cond ((<= 28 a)
               (list :refused :indefinite-or-reserved-head
                     (list :bps-head :refused m a 0 0)))
              ((not (member-equal m '(0 2 3 4)))
               (list :unsupported :cbor-major-type
                     (list :bps-head :unsupported m a 0 0)))
              ((< a 24)
               (list :ready (list m a) (list :bps-head :ready m a 0 a)))
              (t (list :more nil
                       (list :bps-head :argument m a (fn-bps-head-width a) 0))))))
     ((eq phase :argument)
      (if (or (zp remaining) (not (member-equal ai '(24 25 26 27))))
          (list :refused :invalid-head-cursor head)
        (let ((v (+ (* 256 value) octet)))
          (cond ((< *fn-bpc-max-uint* v) (list :refused :head-overflow head))
                ((< 1 remaining)
                 (list :more nil (list :bps-head :argument major ai (1- remaining) v)))
                ((< v (fn-bps-head-minimum ai))
                 (list :refused :nonminimal-head
                       (list :bps-head :refused major ai 0 v)))
                (t (list :ready (list major v)
                         (list :bps-head :ready major ai 0 v)))))))
     (t (list :refused :terminal-head-cursor head)))))

; A scheduling unit consumes one octet.  A completed head leaves the rest of
; the window untouched.  Input absence and quantum exhaustion stay distinct.
; Result: (status detail cursor exact-consumed-prefix-length rest-of-window).
(defun fn-bps-head-drive (head octets quantum)
  (declare (xargs :guard t :measure (nfix quantum)))
  (cond ((zp (nfix quantum)) (list :more nil head 0 octets))
        ((not (consp octets)) (list :need-input nil head 0 octets))
        (t (let* ((one (fn-bps-head-feed head (car octets)))
                  (status (fn-bps-field 0 one))
                  (next (fn-bps-field 2 one)))
             (if (not (eq status :more))
                 (list status (fn-bps-field 1 one) next 1 (cdr octets))
               (let ((tail (fn-bps-head-drive next (cdr octets) (1- (nfix quantum)))))
                 (list (fn-bps-field 0 tail) (fn-bps-field 1 tail)
                       (fn-bps-field 2 tail) (1+ (nfix (fn-bps-field 3 tail)))
                       (fn-bps-field 4 tail))))))))

(defthm fn-bps-head-drive-consumes-at-most-quantum
  (<= (fn-bps-field 3 (fn-bps-head-drive head octets quantum)) (nfix quantum))
  :hints (("Goal" :induct (fn-bps-head-drive head octets quantum)
           :in-theory (enable fn-bps-head-drive fn-bps-field))))

(defthm fn-bps-head-drive-consumes-at-most-window
  (<= (fn-bps-field 3 (fn-bps-head-drive head octets quantum)) (len octets))
  :hints (("Goal" :induct (fn-bps-head-drive head octets quantum)
           :in-theory (enable fn-bps-head-drive fn-bps-field))))

(defthm fn-bps-head-drive-rest-is-exact-unconsumed-suffix
  (equal (fn-bps-field 4 (fn-bps-head-drive head octets quantum))
         (nthcdr (fn-bps-field 3 (fn-bps-head-drive head octets quantum)) octets))
  :hints (("Goal" :induct (fn-bps-head-drive head octets quantum)
           :in-theory (enable fn-bps-head-drive fn-bps-field))))

; Literal teeth: an interrupted nine-octet head resumes without truncation;
; a nonminimal uint and an indefinite array are refused before interpretation.
(assert-event
 (let* ((a (fn-bps-head-drive (fn-bps-head-start) '(27 0 0 0 1 0 0 0 0 99) 3))
        (b (fn-bps-head-drive (fn-bps-field 2 a) (fn-bps-field 4 a) 8)))
   (and (equal (fn-bps-field 0 a) :more) (equal (fn-bps-field 3 a) 3)
        (equal (fn-bps-field 0 b) :ready) (equal (fn-bps-field 1 b) '(0 4294967296))
        (equal (fn-bps-field 3 b) 6) (equal (fn-bps-field 4 b) '(99)))))
(assert-event
 (equal (fn-bps-field 0 (fn-bps-head-drive (fn-bps-head-start) '(24 23) 2)) :refused))
(assert-event
 (equal (fn-bps-field 1 (fn-bps-head-drive (fn-bps-head-start) '(159) 1))
        :indefinite-or-reserved-head))
