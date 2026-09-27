; Witnesses and teeth for books/store-log-kernel and books/store-log-recover
; (the record log's kernel, R, T3 and R's establishment by P-LOG-RECOVER).
;
; Ground frames are built inside assert-event (the trailer is fn-frame-digest,
; evaluated under the SHA-256 attachment of books/frame-trailer), never in a
; defconst.  Crash images are the byte model's own: fn-bs-crash under
; explicit choices with fn-bs-crash-choicesp asserted, so each is a witness
; of fn-bs-crash-imagep.
;
; fn-assume-log-sole-pending-writer is a constrained function (the owner's
; obligation) and does not evaluate; every witness asserts its constraint's
; consequent instead, (not (fn-bs-ops-not-for-ino pending ino)), which is
; the local witness's definition.
(in-package "ACL2")
(include-book "../../books/store-log-recover")
(include-book "../../books/frame-trailer")

(defun slk-unit () (declare (xargs :guard t)) 4)
(defun slk-max () (declare (xargs :guard t)) 4096)
(defun slk-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun slk-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))

; The one-inode store over CONTENT with PENDING.
(defun slk-store (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (slk-unit) (list (cons 0 content)) nil pending 1))

; The store after a write or an fsync that returned :ok (the executable
; face of the theorems' (mv-nth 1 ...)).
(defun slk-write (bs ino offset octets)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r bs1) (fn-bs-write bs ino offset octets :ok) (declare (ignore r)) bs1))
(defun slk-fsync (bs ino)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r bs1) (fn-bs-fsync-file bs ino :ok) (declare (ignore r)) bs1))

; P-LOG-RECOVER as the theorem states it: the kernel of the scan, the tail
; zeroed by one write, one fence.
(defun slk-recover-ks (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-recover (fn-bs-durable-content bs 0) (slk-genesis) (fn-bs-unit bs) (slk-max) 1))
(defun slk-recover-bs (bs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((c (fn-bs-durable-content bs 0))
         (f (fn-lgk-frontier (slk-recover-ks bs)))
         (bs1 (slk-write bs 0 f (fn-bs-zeros (- (len c) f)))))
    (slk-fsync bs1 0)))

; The durable content after a crash: a two-record log, then a torn unit of
; garbage, then two zero units of the preallocated extent.
(defun slk-content ()
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (slk-r 1) (slk-r 2)) (slk-genesis) (slk-unit))
          '(9 9 9 9 0 0 0 0 0 0 0 0)))

; -----------------------------------------------------------------------------
; T3, the reachable witness: the scan consumes the two entries (not the
; garbage), the frontier is aligned, and the content cut there scans the same.
(assert-event
 (let* ((c (slk-content)) (scan (fn-lg-scan c (slk-genesis) (slk-unit) (slk-max)))
        (f (cdr scan)))
   (and (posp (slk-unit)) (true-listp c) (equal (mod (len c) (slk-unit)) 0)
        (equal (car scan) (list (slk-r 1) (slk-r 2)))
        (equal f (- (len c) 12))
        (<= f (len c)) (equal (mod f (slk-unit)) 0)
        (equal (fn-lg-scan (fn-bs-take f c) (slk-genesis) (slk-unit) (slk-max)) scan)
        (equal (fn-lg-scan-last (fn-bs-take f c) (slk-genesis) (slk-unit) (slk-max))
               (fn-lg-scan-last c (slk-genesis) (slk-unit) (slk-max))))))

; T3, hypothesis removal: (mod (len c) unit) = 0 removed.  Content of 2
; octets past a whole entry at unit 4: the scan's frontier is aligned and
; within, but a content whose length is not a multiple of the unit is not a
; content R accepts (fn-lgk-content-okp asks for it) -- T3's conclusion
; (<= f (len c)) needs the alignment: a content whose last entry's padding
; runs past its end.
(assert-event
 (let* ((whole (fn-lg-log (list (slk-r 1)) (slk-genesis) (slk-unit)))
        (c (fn-bs-take (- (len whole) 2) whole))  ; the padding cut short
        (frame-len (len (fn-lg-frame (slk-genesis) (list (slk-r 1)))))
        (scan (fn-lg-scan c (slk-genesis) (slk-unit) (slk-max))))
   (and (posp (slk-unit)) (true-listp c)
        (not (equal (mod (len c) (slk-unit)) 0))
        (<= frame-len (len c))
        (equal (car scan) (list (slk-r 1)))
        (not (<= (cdr scan) (len c))))))

; -----------------------------------------------------------------------------
; R established (fn-lgk-recover-establishes-relation), the reachable
; witness: every hypothesis, then R, the frontier, the records and the
; zeroed tail.
(assert-event
 (let* ((bs (slk-store (slk-content) nil))
        (c (fn-bs-durable-content bs 0))
        (ks (slk-recover-ks bs)) (bs2 (slk-recover-bs bs)))
   (and (posp (fn-bs-unit bs)) (assoc-equal 0 (fn-bs-inodes bs))
        (true-listp c) (equal (mod (len c) (fn-bs-unit bs)) 0)
        (fn-frame-digestp (slk-genesis))
        (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) 0))
        (not (fn-bs-ops-for-ino (fn-bs-pending bs) 0))
        (fn-lgk-relp bs2 ks 0 (slk-genesis) (slk-max))
        (equal (fn-lgk-committed ks) (list (slk-r 1) (slk-r 2)))
        (equal (fn-bs-durable-content bs2 0)
               (append (fn-bs-take (fn-lgk-frontier ks) c) (fn-bs-zeros 12)))
        (not (fn-bs-pending bs2)))))

; Hypothesis removal: the log's own write pending at recovery (removed:
; (not (fn-bs-ops-for-ino pending ino))).  The fence lands it too: the
; first unit is overwritten and R fails.  Every other hypothesis holds.
(assert-event
 (let* ((bs (slk-store (slk-content) (list (list :write 0 0 '(1 1 1 1)))))
        (c (fn-bs-durable-content bs 0)))
   (and (posp (fn-bs-unit bs)) (assoc-equal 0 (fn-bs-inodes bs))
        (true-listp c) (equal (mod (len c) (fn-bs-unit bs)) 0)
        (fn-frame-digestp (slk-genesis))
        (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) 0))
        (fn-bs-ops-for-ino (fn-bs-pending bs) 0)
        (not (fn-lgk-relp (slk-recover-bs bs) (slk-recover-ks bs) 0 (slk-genesis) (slk-max))))))

; Hypothesis removal: another inode's write pending (removed: the owner's
; obligation fn-assume-log-sole-pending-writer).  The fence of the segment
; does not drain it, so the pending list is not R's.
(assert-event
 (let* ((bs (fn-bs-make (slk-unit) (list (cons 0 (slk-content)) (cons 1 nil)) nil
                        (list (list :write 1 0 '(5 5 5 5))) 2))
        (c (fn-bs-durable-content bs 0)))
   (and (posp (fn-bs-unit bs)) (assoc-equal 0 (fn-bs-inodes bs))
        (true-listp c) (equal (mod (len c) (fn-bs-unit bs)) 0)
        (fn-frame-digestp (slk-genesis))
        (fn-bs-ops-not-for-ino (fn-bs-pending bs) 0)
        (not (fn-bs-ops-for-ino (fn-bs-pending bs) 0))
        (not (fn-lgk-relp (slk-recover-bs bs) (slk-recover-ks bs) 0 (slk-genesis) (slk-max))))))

; Hypothesis removal: the content not a whole number of units.
(assert-event
 (let* ((bs (slk-store (append (slk-content) '(0 0)) nil))
        (c (fn-bs-durable-content bs 0)))
   (and (posp (fn-bs-unit bs)) (assoc-equal 0 (fn-bs-inodes bs))
        (true-listp c) (not (equal (mod (len c) (fn-bs-unit bs)) 0))
        (fn-frame-digestp (slk-genesis))
        (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) 0))
        (not (fn-bs-ops-for-ino (fn-bs-pending bs) 0))
        (not (fn-lgk-relp (slk-recover-bs bs) (slk-recover-ks bs) 0 (slk-genesis) (slk-max))))))

; Hypothesis removal: the genesis not a digest.  The scan reads nothing
; (no entry chains to it) and ends on the genesis, which R refuses as LAST.
(with-guard-checking-event
 :none
 (assert-event
  (let* ((bs (slk-store (slk-content) nil))
         (c (fn-bs-durable-content bs 0))
         (g '(1 2))
         (ks (fn-lgk-recover c g (slk-unit) (slk-max) 1))
         (f (fn-lgk-frontier ks))
         (bs2 (slk-fsync
                         (slk-write bs 0 f (fn-bs-zeros (- (len c) f)))
                         0)))
    (and (posp (fn-bs-unit bs)) (assoc-equal 0 (fn-bs-inodes bs))
         (true-listp c) (equal (mod (len c) (fn-bs-unit bs)) 0)
         (not (fn-frame-digestp g))
         (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) 0))
         (not (fn-bs-ops-for-ino (fn-bs-pending bs) 0))
         (not (fn-lgk-relp bs2 ks 0 g (slk-max)))))))

; Hypothesis removal: the segment not in the inode table.  The write is
; refused (EBADF) and R, which names the inode, fails.
(assert-event
 (let* ((bs (fn-bs-make (slk-unit) (list (cons 1 (slk-content))) nil nil 2)))
   (and (posp (fn-bs-unit bs)) (not (assoc-equal 0 (fn-bs-inodes bs)))
        (fn-frame-digestp (slk-genesis))
        (not (fn-lgk-relp (slk-recover-bs bs) (slk-recover-ks bs) 0 (slk-genesis) (slk-max))))))

; -----------------------------------------------------------------------------
; The served sequence from the recovered state: prepare three records,
; append (one write of the batch's chained entries at the frontier), a
; crash of that write, the fence, the finishes.  R holds at every step.

(defun slk-batch () (declare (xargs :guard t)) (list (slk-r 3) (slk-r 4) (slk-r 5)))
(defun slk-ks0 () (declare (xargs :guard t :verify-guards nil))
  (slk-recover-ks (slk-store (slk-content) nil)))
(defun slk-bs0 () (declare (xargs :guard t :verify-guards nil))
  (slk-recover-bs (slk-store (slk-content) nil)))
(defun slk-ks-prepared () (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-prepare (fn-lgk-prepare (fn-lgk-prepare (slk-ks0) (slk-r 3)) (slk-r 4)) (slk-r 5)))

; The preallocated extent must hold the batch: extend the segment by zeros
; first (the host's fnn-log-open-segment preallocates; here 512 octets).
(defun slk-bs-extended () (declare (xargs :guard t :verify-guards nil))
  (let ((bs (slk-bs0)))
    (fn-bs-make (fn-bs-unit bs)
                (list (cons 0 (append (fn-bs-durable-content bs 0) (fn-bs-zeros 512))))
                nil nil 1)))

(defun slk-appended-bs () (declare (xargs :guard t :verify-guards nil))
  (let ((bs (slk-bs-extended)) (ks (slk-ks-prepared)))
    (slk-write bs 0 (fn-lgk-frontier ks)
                           (fn-lgk-append-octets ks (fn-bs-unit bs)))))
(defun slk-appended-ks () (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-append (slk-ks-prepared) (slk-unit)
                 (len (fn-bs-durable-content (slk-bs-extended) 0))))

(assert-event
 (and (fn-lgk-relp (slk-bs-extended) (slk-ks0) 0 (slk-genesis) (slk-max))
      (fn-lgk-relp (slk-bs-extended) (slk-ks-prepared) 0 (slk-genesis) (slk-max))
      (equal (fn-lgk-batch (slk-ks-prepared)) (slk-batch))
      (fn-lgk-fitsp (slk-ks-prepared) (slk-unit) (len (fn-bs-durable-content (slk-bs-extended) 0)))
      (fn-lgk-relp (slk-appended-bs) (slk-appended-ks) 0 (slk-genesis) (slk-max))
      (equal (fn-lgk-inflight (slk-appended-ks)) (slk-batch))))

; Append, hypothesis removal: the batch does not fit the extent (removed:
; fn-lgk-fitsp).  Without the extension the write runs past the zeroed
; tail; the append is refused by the kernel (the state unchanged), so the
; written store and the kernel are not related.
(assert-event
 (let* ((bs (slk-bs0)) (ks (slk-ks-prepared))
        (bs1 (slk-write bs 0 (fn-lgk-frontier ks)
                                    (fn-lgk-append-octets ks (fn-bs-unit bs)))))
   (and (fn-lgk-relp bs ks 0 (slk-genesis) (slk-max))
        (not (consp (fn-lgk-inflight ks)))
        (not (equal (fn-lgk-phase ks) :fault))
        (not (fn-lgk-fitsp ks (fn-bs-unit bs) (len (fn-bs-durable-content bs 0))))
        (not (fn-lgk-relp bs1 (fn-lgk-append ks (fn-bs-unit bs) (len (fn-bs-durable-content bs 0)))
                          0 (slk-genesis) (slk-max))))))

; T2 lifted (fn-lgk-crash-of-related-state-is-a-prefix): crash images of the
; appended state, each an explicit admissible choice of fn-bs-crash.  The
; batch's log spans U units and, since PKT-749, is ONE packed entry (three
; records): the prefix T2 allows is all or nothing.  The selectors: every
; unit landed; nothing landed; only the first unit landed; one unit zeroed
; and the rest landed.
(defun slk-sels (count k sel other)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil
    (cons (if (and (integerp k) (< 0 k)) sel other)
          (slk-sels (1- count) (1- (ifix k)) sel other))))
(defun slk-image-scan (choices)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-scan (fn-bs-durable-content (fn-bs-crash (slk-appended-bs) choices) 0)
              (slk-genesis) (slk-unit) (slk-max)))
(defun slk-verdictp (choices)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ks (slk-appended-ks)))
    (and (fn-bs-crash-choicesp choices (fn-bs-pending (slk-appended-bs)) (slk-unit))
         (fn-lg-crash-verdictp (slk-image-scan choices) (fn-lgk-committed ks)
                               (fn-lgk-frontier ks) (fn-lgk-inflight ks)
                               (fn-lgk-last ks) (slk-unit)))))

(assert-event
 (let* ((ks (slk-appended-ks))
        (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (slk-unit)))
        (units (floor (len w) (slk-unit)))
        (e1 1))
   (and (consp (fn-lgk-inflight ks))
        ; one entry for the whole batch
        (equal (len w) (len (fn-lg-entry (fn-lgk-last ks) (slk-batch) (slk-unit))))
        ; all landed: COMMITTED ++ the whole batch
        (slk-verdictp (list (slk-sels units units :new :new)))
        (equal (car (slk-image-scan (list (slk-sels units units :new :new))))
               (append (list (slk-r 1) (slk-r 2)) (slk-batch)))
        ; nothing landed: COMMITTED
        (slk-verdictp (list (slk-sels units 0 :new :old)))
        (equal (car (slk-image-scan (list (slk-sels units 0 :new :old))))
               (list (slk-r 1) (slk-r 2)))
        ; only the first unit landed: COMMITTED (the batch is not read in part)
        (slk-verdictp (list (slk-sels units e1 :new :old)))
        (equal (car (slk-image-scan (list (slk-sels units e1 :new :old))))
               (list (slk-r 1) (slk-r 2)))
        ; the second unit zeroed, the rest landed: COMMITTED
        (slk-verdictp (list (append (slk-sels e1 e1 :new :new) (list :zero)
                                    (slk-sels (- units (+ e1 1)) (- units (+ e1 1)) :new :new))))
        (equal (car (slk-image-scan (list (append (slk-sels e1 e1 :new :new) (list :zero)
                                                  (slk-sels (- units (+ e1 1)) (- units (+ e1 1))
                                                            :new :new)))))
               (list (slk-r 1) (slk-r 2))))))

; Fence, finish: R after the barrier; every record committed; the finishes
; acknowledge in order and never past COMMITTED.
(assert-event
 (let* ((bs (slk-fsync (slk-appended-bs) 0))
        (ks (fn-lgk-fence (slk-appended-ks) (slk-unit)))
        (k3 (fn-lgk-finish-one (fn-lgk-finish-one (fn-lgk-finish-one ks)))))
   (and (fn-lgk-relp bs ks 0 (slk-genesis) (slk-max))
        (equal (fn-lgk-committed ks) (append (list (slk-r 1) (slk-r 2)) (slk-batch)))
        (fn-lgk-relp bs k3 0 (slk-genesis) (slk-max))
        (equal (fn-lgk-acked k3) 5)
        (equal (fn-lgk-acked (fn-lgk-finish-one k3)) 5)
        ; the recovered durable content scans to the committed records
        (equal (car (fn-lg-scan (fn-bs-durable-content bs 0) (slk-genesis) (slk-unit) (slk-max)))
               (fn-lgk-committed ks)))))
