; Witnesses and teeth for books/store-log-txid (T5: the durable txids
; strictly increase along the scan and the recovered NEXT-TXID exceeds them).
;
; Records are the codec's own encodings (fn-record-encode-impl of a
; fn-record-make), so fn-lgt-txid reads them through the host's decoder.
; Crash images are fn-bs-crash under explicit choices with
; fn-bs-crash-choicesp asserted.  fn-lg-platform-tears-p evaluates only on an
; image whose every entry is exact (its other branch is the constrained
; fn-assume-crash-tearp): the positive witness is the all-landed image.
(in-package "ACL2")
(include-book "../../books/store-log-txid")
(include-book "../../books/frame-trailer")
; The record codec seam's attachment: the log's txid reads the record through
; fn-record-decode-exact (books/store-log-txid.lisp).
(include-book "../../books/codec-attach")

(defun slt-unit () (declare (xargs :guard t)) 4)
(defun slt-max () (declare (xargs :guard t)) 4096)
(defun slt-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun slt-r (txid)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-encode-impl
   (fn-record-make txid txid 1 "<t@example.invalid>" '(72 105) '("fn.test")
                   "o" "s" "e" 4 5)))

(defun slt-bs (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (slt-unit) (list (cons 0 content)) nil pending 1))
(defun slt-write (bs offset octets)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r bs1) (fn-bs-write bs 0 offset octets :ok) (declare (ignore r)) bs1))
(defun slt-fsync (bs)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r bs1) (fn-bs-fsync-file bs 0 :ok) (declare (ignore r)) bs1))

; Prepare each record through PREP (the checked fn-lgt-prepare, or the
; kernel's unchecked one for a mutation witness).
(defun slt-prepare-all (ks records checkedp)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom records) ks
    (slt-prepare-all (if checkedp (fn-lgt-prepare ks (car records))
                       (fn-lgk-prepare ks (car records)))
                     (cdr records) checkedp)))

; Append: the kernel's append and the one write of its octets.
(defun slt-append (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((extent (len (fn-bs-durable-content bs 0)))
         (ks1 (fn-lgk-append ks (slt-unit) extent)))
    (cons (slt-write bs (fn-lgk-frontier ks) (fn-lgk-append-octets ks (slt-unit))) ks1)))

; The recovered empty segment of 1024 preallocated octets, then a committed
; batch (txids 1 2), then a batch in flight (txids 3 4).
(defun slt-ks0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover (fn-bs-zeros 1024) (slt-genesis) (slt-unit) (slt-max) 1))
(defun slt-committed (checkedp)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((ks (slt-prepare-all (slt-ks0) (list (slt-r 1) (slt-r 2)) checkedp))
         (a (slt-append (slt-bs (fn-bs-zeros 1024) nil) ks)))
    (cons (slt-fsync (car a)) (fn-lgk-fence (cdr a) (slt-unit)))))
(defun slt-inflight (records checkedp)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((c (slt-committed t))
         (ks (slt-prepare-all (cdr c) records checkedp)))
    (slt-append (car c) ks)))

(defun slt-sels (count)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil (cons :new (slt-sels (1- count)))))
(defun slt-all-landed (bs)
  (declare (xargs :guard t :verify-guards nil))
  (list (slt-sels (floor (len (nth 3 (car (fn-bs-pending bs)))) (slt-unit)))))

(defun slt-recovered (image)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover (fn-bs-durable-content image 0) (slt-genesis) (slt-unit) (slt-max) 0))

(defun slt-txids (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom records) nil (cons (fn-lgt-txid (car records)) (slt-txids (cdr records)))))

; -----------------------------------------------------------------------------
; T5, the reachable witness: the batch (3 4) in flight after the committed
; (1 2), the all-landed crash image; every hypothesis of
; fn-lg-txids-strictly-increase holds and the recovered kernel reads
; txids (1 2 3 4) with NEXT-TXID 5.
(assert-event
 (let* ((a (slt-inflight (list (slt-r 3) (slt-r 4)) t)) (bs (car a)) (ks (cdr a))
        (choices (slt-all-landed bs))
        (image (fn-bs-crash bs choices))
        (k2 (slt-recovered image)))
   (and (fn-lgk-relp bs ks 0 (slt-genesis) (slt-max))
        (fn-lgt-okp ks)
        (consp (fn-lgk-inflight ks))
        (fn-bs-crash-choicesp choices (fn-bs-pending bs) (slt-unit))
        (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image 0))
                                (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
        (fn-lgt-okp k2)
        (equal (slt-txids (fn-lgk-committed k2)) '(1 2 3 4))
        (equal (fn-lgk-next-txid k2) 5))))

; The allocation rule: after recovery at NEXT-TXID 5 a stale txid (2) and a
; future one (9) are refused (the state unchanged); 5 is admitted.
(assert-event
 (let* ((a (slt-inflight (list (slt-r 3) (slt-r 4)) t))
        (image (fn-bs-crash (car a) (slt-all-landed (car a))))
        (k2 (slt-recovered image)))
   (and (equal (fn-lgt-prepare k2 (slt-r 2)) k2)
        (equal (fn-lgt-prepare k2 (slt-r 9)) k2)
        (equal (fn-lgk-batch (fn-lgt-prepare k2 (slt-r 5))) (list (slt-r 5)))
        (fn-lgt-okp (fn-lgt-prepare k2 (slt-r 5))))))

; Hypothesis removal: fn-lgt-okp.  A MUTATION witness (the kernel's unchecked
; prepare admits txids 4 then 3): R holds, the batch is in flight, the image
; is an admissible all-landed crash with exact entries, the invariant fails,
; and the recovered kernel reads (1 2 4 3): not strictly increasing.
(assert-event
 (let* ((a (slt-inflight (list (slt-r 4) (slt-r 3)) nil)) (bs (car a)) (ks (cdr a))
        (choices (slt-all-landed bs))
        (image (fn-bs-crash bs choices))
        (k2 (slt-recovered image)))
   (and (fn-lgk-relp bs ks 0 (slt-genesis) (slt-max))
        (not (fn-lgt-okp ks))
        (consp (fn-lgk-inflight ks))
        (fn-bs-crash-choicesp choices (fn-bs-pending bs) (slt-unit))
        (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image 0))
                                (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
        (equal (slt-txids (fn-lgk-committed k2)) '(1 2 4 3))
        (not (fn-lgt-okp k2)))))

; Hypothesis removal: fn-lgk-relp.  A CORRUPTED-STATE witness: the kernel of
; the good run (okp, (3 4) in flight) over a store whose durable log is
; (9 1), not the kernel's (1 2).  The image of the pending write scans to
; (9 1) (the batch does not chain after it): not increasing.
(assert-event
 (let* ((a (slt-inflight (list (slt-r 3) (slt-r 4)) t)) (ks (cdr a))
        (bad (append (fn-lg-log (list (slt-r 9) (slt-r 1)) (slt-genesis) (slt-unit))
                     (fn-bs-zeros 1024)))
        (bad (fn-bs-take 1024 bad))
        (bs (slt-bs bad (fn-bs-pending (car a))))
        (choices (slt-all-landed bs))
        (image (fn-bs-crash bs choices))
        (k2 (slt-recovered image)))
   (and (not (fn-lgk-relp bs ks 0 (slt-genesis) (slt-max)))
        (fn-lgt-okp ks)
        (consp (fn-lgk-inflight ks))
        (fn-bs-crash-choicesp choices (fn-bs-pending bs) (slt-unit))
        (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image 0))
                                (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
        (equal (slt-txids (fn-lgk-committed k2)) '(9 1))
        (not (fn-lgt-okp k2)))))

; Hypothesis removal: fn-bs-crash-imagep.  The good related state and a
; store that is not one of its crash images: its content holds the batch's
; entries exactly and then one more chained entry (txid 2) past the pending
; write's range [F, F + |W|), where every crash image keeps the durable
; octets (zeros) -- the model's crash changes only the octets a pending
; operation writes.  Its recovered kernel reads (1 2 3 4 2).
(assert-event
 (let* ((a (slt-inflight (list (slt-r 3) (slt-r 4)) t)) (bs (car a)) (ks (cdr a))
        ; the committed chunk (1 2), the batch's chunk (3 4), then one more
        ; chained entry (2): the layout the appends write (PKT-749)
        (t12 (fn-lg-last-trailer (list (slt-r 1) (slt-r 2)) (slt-genesis)))
        (t34 (fn-lg-last-trailer (list (slt-r 3) (slt-r 4)) t12))
        (content (fn-bs-take 1024 (append (fn-lg-log (list (slt-r 1) (slt-r 2)) (slt-genesis) (slt-unit))
                                           (fn-lg-log (list (slt-r 3) (slt-r 4)) t12 (slt-unit))
                                           (fn-lg-log (list (slt-r 2)) t34 (slt-unit))
                                           (fn-bs-zeros 1024))))
        (image (slt-bs content nil))
        (end (+ (fn-lgk-frontier ks)
                (len (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (slt-unit)))))
        (k2 (slt-recovered image)))
   (and (fn-lgk-relp bs ks 0 (slt-genesis) (slt-max))
        (fn-lgt-okp ks)
        (consp (fn-lgk-inflight ks))
        (not (equal (nthcdr end (fn-bs-durable-content image 0))
                    (nthcdr end (fn-bs-durable-content bs 0))))
        (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image 0))
                                (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
        (equal (slt-txids (fn-lgk-committed k2)) '(1 2 3 4 2))
        (not (fn-lgt-okp k2)))))
