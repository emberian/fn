; Witnesses and teeth for books/store-log-programs (the log's programs and
; runner) and the hypothesis-removal witnesses of T2,
; fn-lg-batch-crash-is-a-prefix (books/store-log-crash.lisp).
;
; Crash images are fn-bs-crash under explicit choices with
; fn-bs-crash-choicesp asserted.  fn-assume-log-sole-pending-writer is
; constrained; a witness asserts its constraint's consequent instead.
(in-package "ACL2")
(include-book "../../books/store-log-programs")
(include-book "../../books/frame-trailer")

(defun slp-unit () (declare (xargs :guard t)) 4)
(defun slp-max () (declare (xargs :guard t)) 4096)
(defun slp-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun slp-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))
(defun slp-bs (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (slp-unit) (list (cons 0 content)) nil pending 1))
(defun slp-log (records prev)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log records prev (slp-unit)))
(defun slp-sels (count sel)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil (cons sel (slp-sels (1- count) sel))))
(defun slp-landed (ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops) nil
    (cons (slp-sels (floor (len (nth 3 (car ops))) (slp-unit)) :new)
          (slp-landed (cdr ops)))))
(defun slp-last-state (run)
  (declare (xargs :guard t :verify-guards nil))
  (car (last run)))

; The recovered empty segment of 1024 preallocated octets with a batch of
; two prepared.
(defun slp-ks0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover (fn-bs-zeros 1024) (slp-genesis) (slp-unit) (slp-max) 1))
(defun slp-ks-prepared ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-prepare (fn-lgk-prepare (slp-ks0) (slp-r 1)) (slp-r 2)))
(defun slp-bs0 () (declare (xargs :guard t :verify-guards nil)) (slp-bs (fn-bs-zeros 1024) nil))
(defun slp-appended ()
  (declare (xargs :guard t :verify-guards nil))
  (slp-last-state (fn-lg-run (slp-bs0) (slp-ks-prepared) (fn-lg-append-program) nil 0)))

; -----------------------------------------------------------------------------
; The append program.

; Reachable: R before, R at log-written, the batch in flight.
(assert-event
 (let* ((bs (slp-bs0)) (ks (slp-ks-prepared))
        (run (fn-lg-run bs ks (fn-lg-append-program) nil 0)))
   (and (fn-lgk-relp bs ks 0 (slp-genesis) (slp-max))
        (not (consp (fn-lgk-inflight ks)))
        (not (equal (fn-lgk-phase ks) :fault))
        (fn-lgk-fitsp ks (fn-bs-unit bs) (len (fn-bs-durable-content bs 0)))
        (fn-lg-all-relp run 0 (slp-genesis) (slp-max))
        (equal (len run) 2)
        (equal (fn-lgk-inflight (cdr (slp-last-state run))) (list (slp-r 1) (slp-r 2)))
        (equal (cdr (slp-last-state run))
               (fn-lgk-append ks (fn-bs-unit bs) (len (fn-bs-durable-content bs 0)))))))

; A second append while the batch is in flight is refused; the state is
; kept (fn-lg-append-program-appends with its no-batch-in-flight hypothesis
; removed: R, not faulted and the fit hold; the run has one state, not two).
(assert-event
 (let* ((a (slp-appended))
        (ks (fn-lgk-prepare (cdr a) (slp-r 3)))
        (run (fn-lg-run (car a) ks (fn-lg-append-program) nil 0)))
   (and (fn-lgk-relp (car a) ks 0 (slp-genesis) (slp-max))
        (consp (fn-lgk-inflight ks))
        (not (equal (fn-lgk-phase ks) :fault))
        (fn-lgk-fitsp ks (slp-unit) (len (fn-bs-durable-content (car a) 0)))
        (equal run (list (cons (car a) ks)))
        (not (equal (len run) 2)))))

; Hypothesis removal (fn-lg-append-program-keeps-the-relation, R): a
; CORRUPTED-STATE witness.  The kernel says (r9) is committed; the segment
; is zeros.  The run's state is not related.
(assert-event
 (let* ((bs (slp-bs0))
        (ks (fn-lgk-make (list (slp-r 9)) (slp-genesis) 0 1 (list (slp-r 1)) nil 0 :ready))
        (run (fn-lg-run bs ks (fn-lg-append-program) nil 0)))
   (and (not (fn-lgk-relp bs ks 0 (slp-genesis) (slp-max)))
        (not (fn-lg-all-relp run 0 (slp-genesis) (slp-max))))))

; Hypothesis removal (fn-lg-append-program-appends): each of its three
; admission hypotheses removed, R kept: the run is the one refused state,
; not the kernel's append.
(assert-event
 (let* ((bs (slp-bs0)) (ks (slp-ks-prepared))
        (faulted (fn-lgk-fence-failed ks))
        (small (slp-bs (fn-bs-zeros 8) nil))
        (ks-small (fn-lgk-prepare (fn-lgk-prepare
                                   (fn-lgt-recover (fn-bs-zeros 8) (slp-genesis) (slp-unit)
                                                   (slp-max) 1)
                                   (slp-r 1)) (slp-r 2))))
   (and ; the fault
        (fn-lgk-relp bs faulted 0 (slp-genesis) (slp-max))
        (equal (fn-lgk-phase faulted) :fault)
        (not (consp (fn-lgk-inflight faulted)))
        (fn-lgk-fitsp faulted (slp-unit) 1024)
        (equal (len (fn-lg-run bs faulted (fn-lg-append-program) nil 0)) 1)
        ; the fit: an 8-octet extent
        (fn-lgk-relp small ks-small 0 (slp-genesis) (slp-max))
        (not (consp (fn-lgk-inflight ks-small)))
        (not (equal (fn-lgk-phase ks-small) :fault))
        (not (fn-lgk-fitsp ks-small (slp-unit) 8))
        (equal (fn-lg-run small ks-small (fn-lg-append-program) nil 0)
               (list (cons small ks-small)))
        (not (consp (fn-lgk-inflight (cdr (slp-last-state
                                            (fn-lg-run small ks-small (fn-lg-append-program)
                                                       nil 0)))))))))

; -----------------------------------------------------------------------------
; The fence program.

(assert-event
 (let* ((a (slp-appended))
        (run (fn-lg-run (car a) (cdr a) (fn-lg-fence-program) nil 0))
        (f (slp-last-state run)))
   (and (fn-lgk-relp (car a) (cdr a) 0 (slp-genesis) (slp-max))
        (fn-lg-all-relp run 0 (slp-genesis) (slp-max))
        (equal (fn-lgk-committed (cdr f)) (list (slp-r 1) (slp-r 2)))
        (equal (fn-bs-pending (car f)) nil)
        (equal (car (fn-lg-scan (fn-bs-durable-content (car f) 0) (slp-genesis) (slp-unit)
                                (slp-max)))
               (list (slp-r 1) (slp-r 2))))))

; Hypothesis removal (R): the batch in flight but its write never issued (the
; store's pending list empty).  After the fence the kernel says committed,
; the segment is zeros: not related.
(assert-event
 (let* ((a (slp-appended))
        (bs (slp-bs0))
        (run (fn-lg-run bs (cdr a) (fn-lg-fence-program) nil 0)))
   (and (not (fn-lgk-relp bs (cdr a) 0 (slp-genesis) (slp-max)))
        (not (fn-lg-all-relp run 0 (slp-genesis) (slp-max))))))

; -----------------------------------------------------------------------------
; The recovery program.  The durable content: two records, a torn unit of
; garbage, two zero units.

(defun slp-content ()
  (declare (xargs :guard t :verify-guards nil))
  (append (slp-log (list (slp-r 1) (slp-r 2)) (slp-genesis)) '(9 9 9 9 0 0 0 0 0 0 0 0)))

(defun slp-recovered-relp (bs genesis)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((ks (fn-lg-recovered-kernel bs 0 genesis (slp-max) 0))
         (run (fn-lg-run bs ks (fn-lg-recover-program) nil 0))
         (final (slp-last-state run)))
    (and (equal (len run) 4)
         (fn-lgk-relp (car final) (cdr final) 0 genesis (slp-max)))))

; The retained hypotheses, asserted in every witness.
(defun slp-recover-hyps (bs genesis)
  (declare (xargs :guard t :verify-guards nil))
  (list (posp (fn-bs-unit bs)) (and (assoc-equal 0 (fn-bs-inodes bs)) t)
        (true-listp (fn-bs-durable-content bs 0))
        (equal (mod (len (fn-bs-durable-content bs 0)) (fn-bs-unit bs)) 0)
        (fn-frame-digestp genesis)
        (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) 0))
        (not (fn-bs-ops-for-ino (fn-bs-pending bs) 0))))

(assert-event
 (let* ((bs (slp-bs (slp-content) nil))
        (ks (fn-lg-recovered-kernel bs 0 (slp-genesis) (slp-max) 0)))
   (and (equal (slp-recover-hyps bs (slp-genesis)) '(t t t t t t t))
        (slp-recovered-relp bs (slp-genesis))
        (equal (fn-lgk-committed ks) (list (slp-r 1) (slp-r 2)))
        (equal (fn-lgk-frontier ks) (- (len (slp-content)) 12)))))

; Removal: the log's own write pending (the 7th hypothesis false).
(assert-event
 (let ((bs (slp-bs (slp-content) (list (list :write 0 (len (slp-content)) '(1 2 3 4))))))
   (and (equal (slp-recover-hyps bs (slp-genesis)) '(t t t t t t nil))
        (not (slp-recovered-relp bs (slp-genesis))))))

; Removal: another inode's write pending (the owner's obligation false).
(assert-event
 (let ((bs (fn-bs-make (slp-unit) (list (cons 0 (slp-content)) (cons 1 '(0 0 0 0))) nil
                       (list (list :write 1 0 '(5 5 5 5))) 2)))
   (and (equal (slp-recover-hyps bs (slp-genesis)) '(t t t t t nil t))
        (not (slp-recovered-relp bs (slp-genesis))))))

; Removal: not whole units (two octets more).
(assert-event
 (let ((bs (slp-bs (append (slp-content) '(0 0)) nil)))
   (and (equal (slp-recover-hyps bs (slp-genesis)) '(t t t nil t t t))
        (not (slp-recovered-relp bs (slp-genesis))))))

; Removal: a genesis that is not a digest.
(assert-event
 (let ((bs (slp-bs (slp-content) nil)))
   (and (equal (slp-recover-hyps bs '(1 2)) '(t t t t nil t t))
        (not (slp-recovered-relp bs '(1 2))))))

; Removal: the segment's inode absent.
(assert-event
 (let ((bs (fn-bs-make (slp-unit) (list (cons 1 (slp-content))) nil nil 2)))
   (and (equal (slp-recover-hyps bs (slp-genesis)) '(t nil t t t t t))
        (not (slp-recovered-relp bs (slp-genesis))))))

; -----------------------------------------------------------------------------
; T2 (fn-lg-batch-crash-is-a-prefix), hypothesis-removal witnesses.  The
; store: durable D = the log of (r1 r2) from genesis, Z = 256 zero octets,
; the one pending write of the batch (r3 r4) at (len D), chained from the
; trailer LAST of D; the all-landed image.  Each witness checks every
; retained hypothesis, the removed one false, and the conclusion false.

(defun slp-t2-hyps (s d z committed last batch image)
  (declare (xargs :guard t :verify-guards nil))
  (let ((unit (fn-bs-unit s)))
    (list (posp unit)
          (and (natp (floor (len d) unit)) (equal (len d) (* (floor (len d) unit) unit)))
          (true-listp d)
          (equal (fn-lg-scan d (slp-genesis) unit (slp-max)) (cons committed (len d)))
          (equal (fn-lg-scan-last d (slp-genesis) unit (slp-max)) last)
          (fn-frame-digestp last)
          (fn-lg-recordsp batch (slp-max))
          (fn-lg-zerosp z)
          (<= (len (fn-lg-log batch last unit)) (len z))
          (equal (fn-bs-durable-content s 0) (append d z))
          (equal (fn-bs-pending s) (list (list :write 0 (len d) (fn-lg-log batch last unit))))
          (and (fn-bs-crash-choicesp (slp-landed (fn-bs-pending s)) (fn-bs-pending s) unit)
               (equal image (fn-bs-crash s (slp-landed (fn-bs-pending s))))))))

(defun slp-t2-conclusion (s d committed last batch image)
  (declare (xargs :guard t :verify-guards nil))
  (let ((content (fn-bs-durable-content image 0)) (unit (fn-bs-unit s)))
    (or (fn-lg-crash-verdictp (fn-lg-scan content (slp-genesis) unit (slp-max))
                              committed (len d) batch last unit)
        (fn-lg-forgery-in (nthcdr (len d) content) batch last unit (slp-max)))))

(defun slp-d () (declare (xargs :guard t :verify-guards nil))
  (slp-log (list (slp-r 1) (slp-r 2)) (slp-genesis)))
(defun slp-last () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-scan-last (slp-d) (slp-genesis) (slp-unit) (slp-max)))
(defun slp-batch () (declare (xargs :guard t :verify-guards nil)) (list (slp-r 3) (slp-r 4)))
(defun slp-w () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (slp-batch) (slp-last) (slp-unit)))

; The reachable witness: every hypothesis, and the image scans to
; (r1 r2 r3 r4).
(assert-event
 (let* ((z (fn-bs-zeros 256))
        (s (slp-bs (append (slp-d) z) (list (list :write 0 (len (slp-d)) (slp-w)))))
        (image (fn-bs-crash s (slp-landed (fn-bs-pending s)))))
   (and (equal (slp-t2-hyps s (slp-d) z (list (slp-r 1) (slp-r 2)) (slp-last) (slp-batch) image)
               '(t t t t t t t t t t t t))
        (slp-t2-conclusion s (slp-d) (list (slp-r 1) (slp-r 2)) (slp-last) (slp-batch) image)
        (equal (car (fn-lg-scan (fn-bs-durable-content image 0) (slp-genesis) (slp-unit)
                                (slp-max)))
               (list (slp-r 1) (slp-r 2) (slp-r 3) (slp-r 4))))))

; Removal: the scan of D is COMMITTED (claimed (r1), D holds (r1 r2)).
(assert-event
 (let* ((z (fn-bs-zeros 256))
        (s (slp-bs (append (slp-d) z) (list (list :write 0 (len (slp-d)) (slp-w)))))
        (image (fn-bs-crash s (slp-landed (fn-bs-pending s)))))
   (and (equal (slp-t2-hyps s (slp-d) z (list (slp-r 1)) (slp-last) (slp-batch) image)
               '(t t t nil t t t t t t t t))
        (not (slp-t2-conclusion s (slp-d) (list (slp-r 1)) (slp-last) (slp-batch) image)))))

; Removal: Z all zeros.  Past the batch's extent Z holds an entry (r9)
; chained after the batch: the image scans to (r1 r2 r3 r4 r9).
(assert-event
 (let* ((after (fn-lg-last-trailer (slp-batch) (slp-last)))
        (tail (slp-log (list (slp-r 9)) after))
        (z (append (fn-bs-zeros (len (slp-w))) tail (fn-bs-zeros 64)))
        (s (slp-bs (append (slp-d) z) (list (list :write 0 (len (slp-d)) (slp-w)))))
        (image (fn-bs-crash s (slp-landed (fn-bs-pending s)))))
   (and (equal (slp-t2-hyps s (slp-d) z (list (slp-r 1) (slp-r 2)) (slp-last) (slp-batch) image)
               '(t t t t t t t nil t t t t))
        (not (slp-t2-conclusion s (slp-d) (list (slp-r 1) (slp-r 2)) (slp-last) (slp-batch)
                                image)))))

; Removal: the pending list is exactly the batch's write.  A second pending
; write lands the chained entry (r9) after the batch.
(assert-event
 (let* ((z (fn-bs-zeros 256))
        (after (fn-lg-last-trailer (slp-batch) (slp-last)))
        (extra (list :write 0 (+ (len (slp-d)) (len (slp-w))) (slp-log (list (slp-r 9)) after)))
        (s (slp-bs (append (slp-d) z) (list (list :write 0 (len (slp-d)) (slp-w)) extra)))
        (image (fn-bs-crash s (slp-landed (fn-bs-pending s)))))
   (and (equal (butlast (slp-t2-hyps s (slp-d) z (list (slp-r 1) (slp-r 2)) (slp-last)
                                     (slp-batch) image) 2)
               '(t t t t t t t t t t))
        (not (equal (fn-bs-pending s)
                    (list (list :write 0 (len (slp-d)) (slp-w)))))
        (fn-bs-crash-choicesp (slp-landed (fn-bs-pending s)) (fn-bs-pending s) (slp-unit))
        (not (slp-t2-conclusion s (slp-d) (list (slp-r 1) (slp-r 2)) (slp-last) (slp-batch)
                                image)))))

; Removal: IMAGE a crash image.  A store holding the batch and then (r9)
; past the pending write's range, where every crash image keeps Z's zeros.
(assert-event
 (let* ((z (fn-bs-zeros 256))
        (s (slp-bs (append (slp-d) z) (list (list :write 0 (len (slp-d)) (slp-w)))))
        (after (fn-lg-last-trailer (slp-batch) (slp-last)))
        (content (fn-bs-take (+ (len (slp-d)) 256)
                             (append (slp-d) (slp-w) (slp-log (list (slp-r 9)) after)
                                     (fn-bs-zeros 256))))
        (image (slp-bs content nil))
        (end (+ (len (slp-d)) (len (slp-w)))))
   (and (equal (butlast (slp-t2-hyps s (slp-d) z (list (slp-r 1) (slp-r 2)) (slp-last)
                                     (slp-batch) image) 1)
               '(t t t t t t t t t t t))
        (not (equal (nthcdr end (fn-bs-durable-content image 0))
                    (nthcdr end (fn-bs-durable-content s 0))))
        (not (slp-t2-conclusion s (slp-d) (list (slp-r 1) (slp-r 2)) (slp-last) (slp-batch)
                                image)))))

; -----------------------------------------------------------------------------
; The host's open kernel (fn-lg-open-kernel-is-the-recovered-kernel, no
; hypothesis): the segment read as a string decodes to the recovered kernel.
(defun slp-chars (codes)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp codes) (cons (code-char (car codes)) (slp-chars (cdr codes))) nil))

(assert-event
 (let* ((codes (append (slp-log (list (slp-r 1) (slp-r 2)) (slp-genesis)) (fn-bs-zeros 8)))
        (s (coerce (slp-chars codes) 'string))
        (ks (fn-lg-open-kernel s (slp-genesis) (slp-unit) (slp-max) 1)))
   (and (equal (fn-lgd-octets s) codes)
        (equal ks (fn-lgt-recover codes (slp-genesis) (slp-unit) (slp-max) 1))
        (equal (fn-lgk-committed ks) (list (slp-r 1) (slp-r 2)))
        (equal (mv-list 2 (fn-lg-recover-tail ks (len codes)))
               (list (- (len codes) 8) 8)))))

; The workload record carries its txid through the codec.
(assert-event
 (and (equal (fn-lgt-txid (fn-lg-workload-record 7 16)) 7)
      (fn-lg-extent-okp 8192 4096)
      (not (fn-lg-extent-okp 8190 4096))))
