; Witnesses and teeth for books/store-log (the record log prototype).
;
; Every ground frame here is built by a function call inside an
; assert-event, never a defconst: the trailer is fn-frame-digest, which
; evaluates only under the SHA-256 attachment (books/frame-trailer through
; crypto-attach), and a defconst is evaluated without it (the marker
; candidates' tests record the same rule).
;
; The torn variants are the byte model's own: each is the content inode 0
; of fn-bs-crash on the one-inode store with the one pending write, under
; explicit admissible choices (fn-bs-crash-choicesp asserted), so each IS a
; witness of fn-bs-torn-variantp (the defun-sk's existential, not
; executable, is shown by exhibiting the choices).  The third disjunct of
; fn-lg-scan-of-torn-entry, the forgery, has no witness: exhibiting one is
; exhibiting a SHA-256 collision, which is what A-CRYPTO-TRAILER says the
; campaign never sees.
(in-package "ACL2")
(include-book "../../books/store-log")
(include-book "../../books/frame-trailer")

; Two records and a unit of 4 octets.
(defun slt-r1 () (declare (xargs :guard t)) '(1 2 3))
(defun slt-r2 () (declare (xargs :guard t)) '(4 5 6 7 8 9 10))
(defun slt-unit () (declare (xargs :guard t)) 4)
(defun slt-max () (declare (xargs :guard t)) 4096)
(defun slt-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)

; -----------------------------------------------------------------------------
; Keystone 1, the reachable witness: a log of two chained entries scans to
; exactly its two records and its length; the padding is a natural and the
; entry's length is its frame's plus the padding.

(assert-event
 (let* ((log (fn-lg-log (list (slt-r1) (slt-r2)) (slt-genesis) (slt-unit)))
        (scan (fn-lg-scan log (slt-genesis) (slt-unit) (slt-max))))
   (and (fn-frame-digestp (slt-genesis))
        (fn-lg-recordsp (list (slt-r1) (slt-r2)) (slt-max))
        (equal scan (cons (list (slt-r1) (slt-r2)) (len log)))
        ; the first entry: 42 octets of frame overhead, 32 of chain, 3 of
        ; record, padded from 77 to 80
        (equal (len (fn-lg-frame (slt-genesis) (slt-r1))) 77)
        (equal (fn-lg-pad-len 77 (slt-unit)) 3)
        (equal (len (fn-lg-entry (slt-genesis) (slt-r1) (slt-unit))) 80)
        (equal (mod (len log) (slt-unit)) 0))))

; The frontier after an append is the end: appending a third entry at the
; log's last trailer reads back three.
(assert-event
 (let* ((records (list (slt-r1) (slt-r2)))
        (log (fn-lg-log records (slt-genesis) (slt-unit)))
        (r3 '(11 12))
        (entry (fn-lg-entry (fn-lg-last-trailer records (slt-genesis)) r3 (slt-unit)))
        (scan (fn-lg-scan (append log entry) (slt-genesis) (slt-unit) (slt-max))))
   (equal scan (cons (list (slt-r1) (slt-r2) r3) (+ (len log) (len entry))))))

; Hypothesis removal, keystone 1.  (fn-frame-digestp prev) removed: a
; two-octet predecessor is not a chain field, the payload's first 32 octets
; are not it, and the scan reads nothing.  Every retained hypothesis holds.
; (The entry's guard asks for a digest, so the witness is evaluated with
; guard checking off: the logical functions are what the theorem is about.)
(with-guard-checking-event
 :none
 (assert-event
  (let* ((prev '(1 2))
         (log (fn-lg-log (list (slt-r1) (slt-r2)) prev (slt-unit))))
    (and (not (fn-frame-digestp prev))
         (fn-lg-recordsp (list (slt-r1) (slt-r2)) (slt-max))
         (not (equal (fn-lg-scan log prev (slt-unit) (slt-max))
                     (cons (list (slt-r1) (slt-r2)) (len log))))))))
; (fn-lg-recordsp records max) removed: a record past the payload bound is
; refused by the frame decoder (:limit), so the scan reads nothing.
(assert-event
 (let* ((big (make-list 100 :initial-element 7))
        (max 64)
        (log (fn-lg-log (list big) (slt-genesis) (slt-unit))))
   (and (fn-frame-digestp (slt-genesis))
        (not (fn-lg-recordsp (list big) max))
        (not (equal (fn-lg-scan log (slt-genesis) (slt-unit) max)
                    (cons (list big) (len log)))))))

; -----------------------------------------------------------------------------
; Keystone 2: torn variants of one appended entry, as crash images.

; The one-inode store with the one pending write of ENTRY at offset 0.
(defun slt-store (entry unit)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make unit (list (cons 0 nil)) nil (list (list :write 0 0 entry)) 1))
; The content inode 0 holds after the crash under CHOICES.
(defun slt-torn (entry unit choices)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (assoc-equal 0 (fn-bs-inodes (fn-bs-crash (slt-store entry unit) choices)))))
; One selector per write unit: the same selector for every unit but the
; i-th, which gets SEL.
(defun slt-selectors (count i sel other)
  (declare (xargs :guard (natp count)))
  (if (zp count) nil
    (cons (if (equal i 0) sel other)
          (slt-selectors (1- count) (1- (nfix i)) sel other))))
(defun slt-choices (entry unit i sel other)
  (declare (xargs :guard t :verify-guards nil))
  (list (slt-selectors (fn-bs-unit-count 0 (len entry) unit) i sel other)))

(defun slt-entry () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-entry (slt-genesis) (slt-r1) (slt-unit)))
(defun slt-scan (octets) (declare (xargs :guard t :verify-guards nil))
  (fn-lg-scan octets (slt-genesis) (slt-unit) (slt-max)))

; The entry spans 20 units of 4 octets; its frame ends in unit 19 with 3
; octets of padding.
(assert-event (equal (fn-bs-unit-count 0 (len (slt-entry)) (slt-unit)) 20))

; (a) the last unit did not land: the frame is cut short, the scan reads
;     nothing, the frontier stays.
(assert-event
 (let ((choices (slt-choices (slt-entry) (slt-unit) 19 :old :new)))
   (and (fn-bs-crash-choicesp choices (list (list :write 0 0 (slt-entry))) (slt-unit))
        (equal (len (slt-torn (slt-entry) (slt-unit) choices)) 76)
        (equal (slt-scan (slt-torn (slt-entry) (slt-unit) choices)) (cons nil 0)))))
; (b) the first unit landed as zeros: no magic, nothing read.
(assert-event
 (let ((choices (slt-choices (slt-entry) (slt-unit) 0 :zero :new)))
   (and (fn-bs-crash-choicesp choices (list (list :write 0 0 (slt-entry))) (slt-unit))
        (equal (len (slt-torn (slt-entry) (slt-unit) choices)) 80)
        (equal (slt-scan (slt-torn (slt-entry) (slt-unit) choices)) (cons nil 0)))))
; (c) a middle unit garbled: the trailer does not validate, nothing read.
(assert-event
 (let ((choices (slt-choices (slt-entry) (slt-unit) 10 '(:garble 255 255 255 255) :new)))
   (and (fn-bs-crash-choicesp choices (list (list :write 0 0 (slt-entry))) (slt-unit))
        (equal (slt-scan (slt-torn (slt-entry) (slt-unit) choices)) (cons nil 0)))))
; (d) every unit landed: the exact write, the one record, the frontier past it.
(assert-event
 (let ((choices (slt-choices (slt-entry) (slt-unit) 0 :new :new)))
   (and (fn-bs-crash-choicesp choices (list (list :write 0 0 (slt-entry))) (slt-unit))
        (equal (slt-torn (slt-entry) (slt-unit) choices) (slt-entry))
        (equal (slt-scan (slt-torn (slt-entry) (slt-unit) choices))
               (cons (list (slt-r1)) 80)))))
; (e) the last unit garbled so that the frame's last octet is kept and the
;     padding is not: the frame validates, the record is read, the padding
;     is skipped by alignment and never parsed.
(assert-event
 (let* ((last-unit (nthcdr 76 (slt-entry)))       ; the frame's last octet then 3 zeros
        (garbled (cons (car last-unit) '(9 9 9)))
        (choices (slt-choices (slt-entry) (slt-unit) 19 (cons :garble garbled) :new))
        (torn (slt-torn (slt-entry) (slt-unit) choices)))
   (and (fn-bs-crash-choicesp choices (list (list :write 0 0 (slt-entry))) (slt-unit))
        (not (equal torn (slt-entry)))
        (equal (fn-bs-take 77 torn) (fn-lg-frame (slt-genesis) (slt-r1)))
        (equal (slt-scan torn) (cons (list (slt-r1)) 80)))))
; (f) nothing landed: the empty history.
(assert-event
 (equal (slt-scan (slt-torn (slt-entry) (slt-unit) (list nil))) (cons nil 0)))

; A stale entry beyond a torn tail: a complete valid entry whose chain names
; another predecessor is not read (the scan stops before it), whatever its
; record says.
(assert-event
 (let* ((stale (fn-lg-entry (fn-lg-trailer (fn-lg-frame (slt-genesis) (slt-r2)))
                            '(99) (slt-unit)))
        (log (fn-lg-log (list (slt-r1)) (slt-genesis) (slt-unit))))
   (equal (slt-scan (append log stale)) (cons (list (slt-r1)) (len log)))))

; -----------------------------------------------------------------------------
; Hypothesis removal, keystone 2: the torn-variant hypothesis.  Octets that
; are NOT a torn variant of the entry can hold the entry and more: the scan
; reads two records, which is none of the three disjuncts.
(assert-event
 (let* ((two (fn-lg-log (list (slt-r1) (slt-r2)) (slt-genesis) (slt-unit)))
        (scan (slt-scan two)))
   (and (fn-frame-digestp (slt-genesis))
        (fn-lg-recordp (slt-r1) (slt-max))
        (< (len (slt-entry)) (len two))         ; so not a torn variant (fn-lg-torn-variant-len)
        (not (equal scan (cons nil 0)))
        (not (equal scan (cons (list (slt-r1)) (len (slt-entry)))))
        (not (fn-lg-forgeryp two (slt-genesis) (slt-max) (fn-lg-frame (slt-genesis) (slt-r1)))))))
