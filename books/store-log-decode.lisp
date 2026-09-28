; fn: the record log's executable scan, fn-lg-decode (D27: the served path
; uses a concrete representation).
;
; The host reads the segment once into a string S (one character per octet,
; host/native/io.lisp fnn-octets-string) and calls fn-lg-decode.  The scan
; walks S by index: per entry it reads the header's ten octets and then the
; entry's declared range (fn-lgd-range: the one range read, an octet list
; of at most the frame's length, which the payload bound MAX limits), opens
; it with the frame codec and steps past its padding.  Nothing converts the
; whole segment to a list.  It answers (mv RECORDS CONSUMED LAST): the
; records (every record of an entry: one, or a packed chunk's), the
; frontier and the last trailer, which are the logical scan's
; three answers:
;
;   fn-lg-decode-is-the-scan   for every S (no hypothesis),
;       (fn-lg-decode s prev unit max)
;     = (mv (car (fn-lg-scan (fn-lgd-octets s) prev unit max))
;           (cdr (fn-lg-scan (fn-lgd-octets s) prev unit max))
;           (fn-lg-scan-last (fn-lgd-octets s) prev unit max))
;
; with fn-lgd-octets the string's character codes, the logical model.  The
; loop is tail-recursive (the records accumulate reversed and are reversed
; once), so a long segment costs no stack.  The frame codec's helpers the
; loop calls (fn-lg-declared-len, fn-lg-entry-okp, fn-lg-slice-records,
; fn-lg-trailer: guards not verified in books/store-log.lisp) run through
; ec-call on octet lists of one entry; the SHA-256 digest of the frame's
; open dominates each step.
(in-package "ACL2")

(include-book "store-log-crash")

(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The logical model of a string, and the range read.

(defun fn-lgd-codes (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars)) (fn-lgd-codes (cdr chars)))
    nil))

(defun fn-lgd-octets (s)
  (declare (xargs :guard (stringp s)))
  (fn-lgd-codes (coerce s 'list)))

; The octets S[POS, POS + K) consed in front of ACC, built from the end
; (tail-recursive).
(defun fn-lgd-range-acc (s pos k acc)
  (declare (xargs :guard (and (stringp s) (natp pos) (natp k) (<= (+ pos k) (length s)))))
  (if (zp k)
      acc
    (fn-lgd-range-acc s pos (1- k) (cons (char-code (char s (+ pos k -1))) acc))))

(defun fn-lgd-range (s pos n)
  (declare (xargs :guard (and (stringp s) (natp pos) (natp n) (<= (+ pos n) (length s)))))
  (fn-lgd-range-acc s pos n nil))

; -----------------------------------------------------------------------------
; The loop.

(defthm fn-lgd-declared-len-bound-rewrite
  (implies (fn-lg-declared-len octets)
           (and (natp (fn-lg-declared-len octets))
                (<= *fn-frame-overhead-octets* (fn-lg-declared-len octets))))
  :hints (("Goal" :in-theory (disable fn-cbor-u32-from fn-bs-take))))

; The length the header at POS declares: the header's ten octets (or the
; octets left, when fewer) read and decided by the codec.
(defun fn-lgd-declared-at (s pos)
  (declare (xargs :guard (and (stringp s) (natp pos) (<= pos (length s)))))
  (ec-call (fn-lg-declared-len
            (fn-lgd-range s pos (min *fn-frame-header-octets* (- (length s) pos))))))

(defthm fn-lgd-declared-at-natp
  (implies (fn-lgd-declared-at s pos)
           (and (natp (fn-lgd-declared-at s pos))
                (<= *fn-frame-overhead-octets* (fn-lgd-declared-at s pos))))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-lgd-declared-at s pos)))
                 (:rewrite :corollary (implies (fn-lgd-declared-at s pos)
                                               (natp (fn-lgd-declared-at s pos))))
                 (:linear :corollary (implies (fn-lgd-declared-at s pos)
                                              (<= *fn-frame-overhead-octets*
                                                  (fn-lgd-declared-at s pos)))))
  :hints (("Goal" :in-theory (disable fn-lg-declared-len fn-lgd-range))))

(defun fn-lgd-loop (s pos prev unit max acc)
  (declare (xargs :guard (and (stringp s) (natp pos) (<= pos (length s)) (true-listp acc))
                  :measure (nfix (- (length s) (nfix pos)))
                  :hints (("Goal" :in-theory (disable fn-lgd-declared-at fn-lg-entry-okp
                                                      fn-lg-pad-len fn-lgd-range)))))
  (if (not (mbt (and (stringp s) (natp pos) (<= pos (length s)))))
      (mv (revappend acc nil) 0 prev)
    (let* ((avail (- (length s) pos))
           (n (fn-lgd-declared-at s pos)))
      (if (not (and n (<= n avail)))
          (mv (revappend acc nil) pos prev)
        (let ((slice (fn-lgd-range s pos n)))
          (if (not (ec-call (fn-lg-entry-okp slice prev max)))
              (mv (revappend acc nil) pos prev)
            (let ((step (+ n (fn-lg-pad-len n unit)))
                  (records (ec-call (fn-lg-slice-records slice max)))
                  (last (ec-call (fn-lg-trailer slice))))
              (if (< (+ pos step) (length s))
                  (fn-lgd-loop s (+ pos step) last unit max (revappend records acc))
                (mv (revappend (revappend records acc) nil) (+ pos step) last)))))))))

(defun fn-lg-decode (s prev unit max)
  (declare (xargs :guard (stringp s)))
  (fn-lgd-loop s 0 prev unit max nil))

; -----------------------------------------------------------------------------
; The range read is a slice of the model.

(local
 (defthm fn-lgd-len-codes
   (equal (len (fn-lgd-codes x)) (len x))))

(local
 (defthm fn-lgd-nth-codes
   (implies (< (nfix i) (len x))
            (equal (nth i (fn-lgd-codes x)) (char-code (nth i x))))))

(local
 (defthm fn-lgd-len-octets
   (implies (stringp s) (equal (len (fn-lgd-octets s)) (length s)))))

(local
 (defthm fn-lgd-take-snoc
   (implies (and (natp k) (< k (len x)))
            (equal (fn-bs-take (1+ k) x)
                   (append (fn-bs-take k x) (list (nth k x)))))
   :hints (("Goal" :induct (fn-bs-take k x)))))

(local
 (defthm fn-lgd-nth-nthcdr
   (equal (nth i (nthcdr j x)) (nth (+ (nfix i) (nfix j)) x))))

(local
 (defthm fn-lgd-range-acc-is-take
   (implies (and (stringp s) (natp pos) (natp k) (<= (+ pos k) (length s)))
            (equal (fn-lgd-range-acc s pos k acc)
                   (append (fn-bs-take k (nthcdr pos (fn-lgd-octets s))) acc)))
   :hints (("Goal" :induct (fn-lgd-range-acc s pos k acc)
            :in-theory (disable fn-lgd-take-snoc))
           ("Subgoal *1/2"
            :use ((:instance fn-lgd-take-snoc (k (1- k))
                             (x (nthcdr pos (fn-lgd-octets s)))))))))

(defthm fn-lgd-range-is-take
  (implies (and (stringp s) (natp pos) (natp n) (<= (+ pos n) (length s)))
           (equal (fn-lgd-range s pos n) (fn-bs-take n (nthcdr pos (fn-lgd-octets s))))))

; The header's ten octets decide the declared length.
(local
 (defthm fn-lgd-take-of-take
   (implies (<= (nfix m) (nfix n))
            (equal (fn-bs-take m (fn-bs-take n x)) (fn-bs-take m x)))))

(local
 (defun fn-lgd-kn-ind (k n x)
   (if (or (zp k) (zp n)) (list k n x) (fn-lgd-kn-ind (1- k) (1- n) (cdr x)))))

(local
 (defthm fn-lgd-nthcdr-of-take-shift
   (implies (<= (nfix k) (nfix n))
            (equal (nthcdr k (fn-bs-take n x))
                   (fn-bs-take (- (nfix n) (nfix k)) (nthcdr k x))))
   :hints (("Goal" :induct (fn-lgd-kn-ind k n x)))))

(local
 (defthm fn-lgd-nthcdr-of-take
   (implies (<= (+ (nfix k) (nfix m)) (nfix n))
            (equal (fn-bs-take m (nthcdr k (fn-bs-take n x)))
                   (fn-bs-take m (nthcdr k x))))))

(defthm fn-lgd-declared-len-of-header
  (equal (fn-lg-declared-len (fn-bs-take (min *fn-frame-header-octets* (len x)) x))
         (fn-lg-declared-len x))
  :hints (("Goal" :in-theory (disable fn-cbor-u32-from))))

(defthm fn-lgd-codes-octets
  (fn-cbor-octet-listp (fn-lgd-codes x)))

; -----------------------------------------------------------------------------
; The loop is the scan.

(defthm fn-lgd-header-at
  (implies (and (stringp s) (natp pos) (<= pos (length s)))
           (equal (fn-lgd-declared-at s pos)
                  (fn-lg-declared-len (nthcdr pos (fn-lgd-octets s)))))
  :hints (("Goal" :in-theory (disable fn-lg-declared-len fn-lgd-declared-len-of-header)
           :use ((:instance fn-lgd-declared-len-of-header (x (nthcdr pos (fn-lgd-octets s))))))))

(defthm fn-lgd-nthcdr-past-end
  (implies (and (stringp s) (<= (length s) (nfix k)))
           (atom (nthcdr k (fn-lgd-octets s)))))

(defthm fn-lgd-slice-at
  (implies (and (stringp s) (natp pos) (<= pos (length s))
                (fn-lg-declared-len (nthcdr pos (fn-lgd-octets s)))
                (<= (fn-lg-declared-len (nthcdr pos (fn-lgd-octets s))) (- (length s) pos)))
           (equal (fn-lgd-range s pos (fn-lg-declared-len (nthcdr pos (fn-lgd-octets s))))
                  (fn-lg-slice (nthcdr pos (fn-lgd-octets s)))))
  :hints (("Goal" :in-theory (disable fn-lg-declared-len))))

(defthm fn-lgd-slice-when-short
  (implies (not (and (fn-lg-declared-len x) (<= (fn-lg-declared-len x) (len x))))
           (equal (fn-lg-slice x) nil)))

(defthm fn-lgd-scan-last-of-atom
  (implies (atom x) (equal (fn-lg-scan-last x prev unit max) prev)))

(defthm fn-lgd-revappend-revappend
  (equal (revappend (revappend r acc) y) (revappend acc (append r y))))

(defthm fn-lgd-loop-is-the-scan
  (implies (and (stringp s) (natp pos) (<= pos (length s)) (true-listp acc))
           (equal (fn-lgd-loop s pos prev unit max acc)
                  (let ((x (nthcdr pos (fn-lgd-octets s))))
                    (mv (revappend acc (car (fn-lg-scan x prev unit max)))
                        (+ pos (cdr (fn-lg-scan x prev unit max)))
                        (fn-lg-scan-last x prev unit max)))))
  :hints (("Goal" :induct (fn-lgd-loop s pos prev unit max acc)
           :expand ((fn-lg-scan (nthcdr pos (fn-lgd-octets s)) prev unit max)
                    (fn-lg-scan-last (nthcdr pos (fn-lgd-octets s)) prev unit max))
           :in-theory (disable fn-lg-declared-len fn-lg-entry-okp fn-lg-slice-records
                               fn-lg-trailer fn-lg-pad-len fn-lgd-range fn-lg-scan
                               fn-lg-scan-last fn-lg-slice fn-lgd-octets length
                               fn-lgd-declared-at
                               fn-lgd-range-is-take fn-lgd-declared-len-of-header))))

; No hypothesis: a non-string reads as the empty model (its coerce is nil)
; and the loop's guard branch answers the empty history.
(defthm fn-lg-decode-is-the-scan
  (equal (fn-lg-decode s prev unit max)
         (mv (car (fn-lg-scan (fn-lgd-octets s) prev unit max))
             (cdr (fn-lg-scan (fn-lgd-octets s) prev unit max))
             (fn-lg-scan-last (fn-lgd-octets s) prev unit max)))
  :hints (("Goal" :cases ((stringp s)))))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:rewrite fn-lgd-slice-when-short)))
