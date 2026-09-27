; owner-batch-tests.lisp -- teeth for books/owner-batch.lisp (PRF-249, PRF-250, PRF-251).
;
; The served sequence from a recovered log: recover, take three members (three
; connections), append, fence, finish each in order; the layer aligned with the
; kernel and R held at every step.  Then the crash images (T1), the failed
; barrier (T7), the catalog's two-member batch against the sequential token
; protocol (T4), the bounds and the sole-pending-writer discharge, each with a
; reachable witness asserting the retained hypotheses and the conclusion, and
; a ground witness per removed hypothesis where one is constructible (the
; platform-tear hypothesis of T1/T7 is the A-CRYPTO-TRAILER assumption: a
; constrained function, not evaluable; the kernel's tests exhibit the tears).

(in-package "ACL2")
(include-book "../../books/owner-batch")
(include-book "../../books/frame-trailer")
(include-book "std/testing/must-fail" :dir :system)

(defun owb-unit () (declare (xargs :guard t)) 4)
(defun owb-max () (declare (xargs :guard t)) 4096)
(defun owb-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun owb-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))

(defun owb-store (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (owb-unit) (list (cons 0 content)) nil pending 1))
(defun owb-write (bs ino offset octets)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r bs1) (fn-bs-write bs ino offset octets :ok) (declare (ignore r)) bs1))
(defun owb-fsync (bs ino)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r bs1) (fn-bs-fsync-file bs ino :ok) (declare (ignore r)) bs1))
; The word fn-owb-finish-member offers (nil when it offers none).
(defun owb-word (st)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (w st1) (fn-owb-finish-member st) (declare (ignore st1)) w))

; A two-record log, a torn unit, two zero units: the content a crash left.
(defun owb-content ()
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (owb-r 1) (owb-r 2)) (owb-genesis) (owb-unit))
          '(9 9 9 9 0 0 0 0 0 0 0 0)))

; P-LOG-RECOVER: the layer of the scan; the store's tail zeroed and fenced.
(defun owb-st0 () (declare (xargs :guard t :verify-guards nil))
  (fn-owb-recover (owb-content) (owb-genesis) (owb-unit) (owb-max) 3))
(defun owb-bs0 () (declare (xargs :guard t :verify-guards nil))
  (let* ((bs (owb-store (owb-content) nil))
         (c (fn-bs-durable-content bs 0))
         (f (fn-lgk-frontier (fn-owb-ks (owb-st0)))))
    (owb-fsync (owb-write bs 0 f (fn-bs-zeros (- (len c) f))) 0)))
; The segment preallocated (fnn-log-open-segment): 512 more zero octets.
(defun owb-ext-bs () (declare (xargs :guard t :verify-guards nil))
  (let ((bs (owb-bs0)))
    (fn-bs-make (fn-bs-unit bs)
                (list (cons 0 (append (fn-bs-durable-content bs 0) (fn-bs-zeros 512))))
                nil nil 1)))
(defun owb-extent () (declare (xargs :guard t :verify-guards nil))
  (len (fn-bs-durable-content (owb-ext-bs) 0)))

; The sole-pending-writer discharge, reachable: the store before recovery has
; nothing pending; R is established.
(assert-event
 (let ((bs (owb-store (owb-content) nil)))
   (and (fn-owb-sole-pending-writer bs 0)
        (not (fn-bs-ops-for-ino (fn-bs-pending bs) 0))
        (fn-lgk-relp (owb-bs0) (fn-owb-ks (owb-st0)) 0 (owb-genesis) (owb-max))
        (fn-lgk-relp (owb-ext-bs) (fn-owb-ks (owb-st0)) 0 (owb-genesis) (owb-max))
        (fn-owb-alignedp (owb-st0))
        (equal (fn-owb-records (fn-owb-acked (owb-st0))) (list (owb-r 1) (owb-r 2)))
        (null (fn-owb-waiting (owb-st0))) (null (fn-owb-members (owb-st0))))))

; Hypothesis removal: another inode's write pending at recovery (removed:
; fn-owb-sole-pending-writer).  The segment's fence does not drain it; R fails.
(assert-event
 (let* ((bs (fn-bs-make (owb-unit) (list (cons 0 (owb-content)) (cons 1 nil)) nil
                        (list (list :write 1 0 '(5 5 5 5))) 2))
        (c (fn-bs-durable-content bs 0))
        (ks (fn-owb-ks (owb-st0))) (f (fn-lgk-frontier ks))
        (bs2 (owb-fsync (owb-write bs 0 f (fn-bs-zeros (- (len c) f))) 0)))
   (and (posp (fn-bs-unit bs)) (assoc-equal 0 (fn-bs-inodes bs))
        (true-listp c) (equal (mod (len c) (fn-bs-unit bs)) 0)
        (fn-frame-digestp (owb-genesis))
        (not (fn-bs-ops-for-ino (fn-bs-pending bs) 0))
        (not (fn-owb-sole-pending-writer bs 0))
        (not (fn-lgk-relp bs2 ks 0 (owb-genesis) (owb-max))))))

; -----------------------------------------------------------------------------
; The served sequence: three connections' members taken into one batch.

(defun owb-bmax () (declare (xargs :guard t)) 64)
(defun owb-omax () (declare (xargs :guard t)) 512)
(defun owb-st1 () (declare (xargs :guard t :verify-guards nil))
  (fn-owb-take (owb-st0) 10 '(3 . 2) (owb-r 3) (owb-unit) (owb-bmax) (owb-omax)))
(defun owb-st2 () (declare (xargs :guard t :verify-guards nil))
  (fn-owb-take (owb-st1) 11 '(4 . 3) (owb-r 4) (owb-unit) (owb-bmax) (owb-omax)))
(defun owb-st3 () (declare (xargs :guard t :verify-guards nil))
  (fn-owb-take (owb-st2) 12 '(5 . 4) (owb-r 5) (owb-unit) (owb-bmax) (owb-omax)))
(defun owb-batch () (declare (xargs :guard t)) (list (owb-r 3) (owb-r 4) (owb-r 5)))

(assert-event
 (and (fn-owb-alignedp (owb-st1)) (fn-owb-alignedp (owb-st2)) (fn-owb-alignedp (owb-st3))
      (fn-owb-boundedp (owb-st3) (owb-unit) (owb-bmax) (owb-omax))
      (equal (fn-lgk-batch (fn-owb-ks (owb-st3))) (owb-batch))
      (equal (fn-owb-records (fn-owb-members (owb-st3))) (owb-batch))
      (equal (fn-owb-member-id (car (fn-owb-members (owb-st3)))) 10)
      (equal (fn-owb-member-token (cadr (fn-owb-members (owb-st3)))) '(4 . 3))
      ; every prepared state is R-related to the preallocated segment
      (fn-lgk-relp (owb-ext-bs) (fn-owb-ks (owb-st1)) 0 (owb-genesis) (owb-max))
      (fn-lgk-relp (owb-ext-bs) (fn-owb-ks (owb-st3)) 0 (owb-genesis) (owb-max))
      ; the kernel consumed three txids
      (equal (fn-lgk-next-txid (fn-owb-ks (owb-st3))) 6)))

; The bounds (fn-owb-batch-within-bounds), reachable: at bmax 2 the third take
; is refused with the layer unchanged; at omax exactly the two entries'
; octets, likewise.
(assert-event
 (let ((two (fn-owb-batch-octets (fn-lgk-batch (fn-owb-ks (owb-st2))) (owb-unit))))
   (and (fn-owb-boundedp (owb-st2) (owb-unit) 2 (owb-omax))
        (not (< (len (fn-owb-members (owb-st2))) 2))
        (equal (fn-owb-take (owb-st2) 12 '(5 . 4) (owb-r 5) (owb-unit) 2 (owb-omax)) (owb-st2))
        (fn-owb-boundedp (owb-st2) (owb-unit) (owb-bmax) two)
        (not (<= (fn-owb-batch-octets (append (fn-lgk-batch (fn-owb-ks (owb-st2))) (list (owb-r 5)))
                                      (owb-unit))
                 two))
        (equal (fn-owb-take (owb-st2) 12 '(5 . 4) (owb-r 5) (owb-unit) (owb-bmax) two) (owb-st2))
        ; and below both bounds the take is admitted
        (not (equal (owb-st3) (owb-st2))))))

; Hypothesis removal (bounds): a layer NOT bounded at the given bounds (its
; batch already holds three members against bmax 2) is not made bounded by
; a refused take; boundedp fails before and after.
(assert-event
 (and (not (fn-owb-boundedp (owb-st3) (owb-unit) 2 (owb-omax)))
      (not (fn-owb-boundedp (fn-owb-take (owb-st3) 13 '(6 . 5) (owb-r 6) (owb-unit) 2 (owb-omax))
                            (owb-unit) 2 (owb-omax)))))

; Append (the batch in flight), the store's write, the fence, the finishes.
(defun owb-st4 () (declare (xargs :guard t :verify-guards nil))
  (fn-owb-append (owb-st3) (owb-unit) (owb-extent)))
(defun owb-bs4 () (declare (xargs :guard t :verify-guards nil))
  (let ((ks (fn-owb-ks (owb-st3))))
    (owb-write (owb-ext-bs) 0 (fn-lgk-frontier ks) (fn-lgk-append-octets ks (owb-unit)))))
(defun owb-st5 () (declare (xargs :guard t :verify-guards nil))
  (fn-owb-fence (owb-st4) (owb-unit)))
(defun owb-bs5 () (declare (xargs :guard t :verify-guards nil))
  (owb-fsync (owb-bs4) 0))

(assert-event
 (and (fn-owb-append-enabledp (owb-st3) (owb-unit) (owb-extent))
      (fn-owb-alignedp (owb-st4)) (fn-owb-alignedp (owb-st5))
      (fn-lgk-relp (owb-bs4) (fn-owb-ks (owb-st4)) 0 (owb-genesis) (owb-max))
      (fn-lgk-relp (owb-bs5) (fn-owb-ks (owb-st5)) 0 (owb-genesis) (owb-max))
      (equal (fn-owb-records (fn-owb-inflight (owb-st4))) (owb-batch))
      (null (fn-owb-members (owb-st4)))
      (equal (fn-owb-records (fn-owb-waiting (owb-st5))) (owb-batch))
      (null (fn-owb-inflight (owb-st5)))
      (equal (fn-lgk-committed (fn-owb-ks (owb-st5)))
             (append (list (owb-r 1) (owb-r 2)) (owb-batch)))
      ; nothing acknowledged before the fence: no finish is offered in flight
      ; (WAITING is empty at st4), and none is offered while the open batch
      ; is unappended (st3)
      (equal (owb-word (owb-st4)) nil)
      (equal (owb-word (owb-st3)) nil)))

; The finishes, in order, each after the barrier; then nothing more.
(assert-event
 (mv-let (w1 st6) (fn-owb-finish-member (owb-st5))
   (mv-let (w2 st7) (fn-owb-finish-member st6)
     (mv-let (w3 st8) (fn-owb-finish-member st7)
       (mv-let (w4 st9) (fn-owb-finish-member st8)
         (and (equal w1 '(10 . :durable)) (equal w2 '(11 . :durable)) (equal w3 '(12 . :durable))
              (equal w4 nil) (equal st9 st8)
              (fn-owb-alignedp st6) (fn-owb-alignedp st7) (fn-owb-alignedp st8)
              (fn-lgk-relp (owb-bs5) (fn-owb-ks st8) 0 (owb-genesis) (owb-max))
              (equal (fn-owb-records (fn-owb-acked st8))
                     (append (list (owb-r 1) (owb-r 2)) (owb-batch)))
              (equal (fn-lgk-acked (fn-owb-ks st8)) 5)))))))

; -----------------------------------------------------------------------------
; T1, reachable.  After the fence nothing is pending: the one admissible
; image is the store itself, and every acknowledged member's record is in its
; scan.  With the batch in flight (st4/bs4), the two anonymous acknowledged
; members (r1, r2) are in the scan of each of three admissible images: all
; units landed, none landed, the first entry's landed.

(defun owb-sels (count k sel other)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil
    (cons (if (and (integerp k) (< 0 k)) sel other)
          (owb-sels (1- count) (1- (ifix k)) sel other))))
(defun owb-units () (declare (xargs :guard t :verify-guards nil))
  (let ((ks (fn-owb-ks (owb-st4))))
    (floor (len (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (owb-unit))) (owb-unit))))
(defun owb-e1 () (declare (xargs :guard t :verify-guards nil))
  (floor (len (fn-lg-entry (fn-lgk-last (fn-owb-ks (owb-st4))) (owb-r 3) (owb-unit))) (owb-unit)))
(defun owb-choice (k) (declare (xargs :guard t :verify-guards nil))
  (list (owb-sels (owb-units) k :new :old)))
(defun owb-image-scan (bs choices) (declare (xargs :guard t :verify-guards nil))
  (car (fn-lg-scan (fn-bs-durable-content (fn-bs-crash bs choices) 0)
                   (owb-genesis) (owb-unit) (owb-max))))

(assert-event
 (mv-let (w1 st6) (fn-owb-finish-member (owb-st5))
   (declare (ignore w1))
   (let ((m (car (last (fn-owb-acked st6)))))
     (and (fn-owb-alignedp st6)
          (fn-lgk-relp (owb-bs5) (fn-owb-ks st6) 0 (owb-genesis) (owb-max))
          (member-equal m (fn-owb-acked st6))
          (equal (fn-owb-member-record m) (owb-r 3))
          (not (consp (fn-lgk-inflight (fn-owb-ks st6))))
          (fn-bs-crash-choicesp nil (fn-bs-pending (owb-bs5)) (owb-unit))
          (equal (fn-bs-crash (owb-bs5) nil) (owb-bs5))
          (member-equal (owb-r 3) (owb-image-scan (owb-bs5) nil))))))

(assert-event
 (let ((st (owb-st4)) (bs (owb-bs4)))
   (and (fn-owb-alignedp st)
        (fn-lgk-relp bs (fn-owb-ks st) 0 (owb-genesis) (owb-max))
        (consp (fn-lgk-inflight (fn-owb-ks st)))
        (equal (fn-owb-records (fn-owb-acked st)) (list (owb-r 1) (owb-r 2)))
        (fn-bs-crash-choicesp (owb-choice (owb-units)) (fn-bs-pending bs) (owb-unit))
        (fn-bs-crash-choicesp (owb-choice 0) (fn-bs-pending bs) (owb-unit))
        (fn-bs-crash-choicesp (owb-choice (owb-e1)) (fn-bs-pending bs) (owb-unit))
        (equal (owb-image-scan bs (owb-choice (owb-units)))
               (append (list (owb-r 1) (owb-r 2)) (owb-batch)))
        (equal (owb-image-scan bs (owb-choice 0)) (list (owb-r 1) (owb-r 2)))
        (equal (owb-image-scan bs (owb-choice (owb-e1))) (list (owb-r 1) (owb-r 2) (owb-r 3)))
        (member-equal (owb-r 1) (owb-image-scan bs (owb-choice 0)))
        (member-equal (owb-r 2) (owb-image-scan bs (owb-choice (owb-e1)))))))

; T1, hypothesis removal: alignment (a layer whose ACKED names a record the
; kernel never committed): R and the image hold, the record is not in the scan.
(assert-event
 (let* ((st (owb-st5))
        (bad (fn-owb-make (fn-owb-ks st) nil nil (fn-owb-waiting st)
                          (append (fn-owb-acked st) (list (fn-owb-member 99 '(9 . 9) (owb-r 9))))))
        (m (fn-owb-member 99 '(9 . 9) (owb-r 9))))
   (and (not (fn-owb-alignedp bad))
        (fn-lgk-relp (owb-bs5) (fn-owb-ks bad) 0 (owb-genesis) (owb-max))
        (member-equal m (fn-owb-acked bad))
        (equal (fn-bs-crash (owb-bs5) nil) (owb-bs5))
        (not (member-equal (fn-owb-member-record m) (owb-image-scan (owb-bs5) nil))))))

; T1, hypothesis removal: R (a store unrelated to the kernel: an empty
; segment): the layer is aligned, the image is the store, the record is absent.
(assert-event
 (let* ((st (owb-st5)) (bs (owb-store (fn-bs-zeros 64) nil))
        (m (car (fn-owb-acked st))))
   (and (fn-owb-alignedp st)
        (not (fn-lgk-relp bs (fn-owb-ks st) 0 (owb-genesis) (owb-max)))
        (member-equal m (fn-owb-acked st))
        (equal (fn-bs-crash bs nil) bs)
        (not (member-equal (fn-owb-member-record m) (owb-image-scan bs nil))))))

; T1, hypothesis removal: the crash image (an image that is not the crash of
; the store: nothing is pending at bs5, so its one admissible image is bs5
; itself; the empty segment is not it, and the record is absent from it).
(assert-event
 (let* ((st (owb-st5)) (bs (owb-bs5)) (other (owb-store (fn-bs-zeros 64) nil))
        (m (car (fn-owb-acked st))))
   (and (fn-owb-alignedp st)
        (fn-lgk-relp bs (fn-owb-ks st) 0 (owb-genesis) (owb-max))
        (member-equal m (fn-owb-acked st))
        (null (fn-bs-pending bs))
        (equal (fn-bs-crash bs nil) bs)
        (not (equal other bs))
        (not (member-equal (fn-owb-member-record m)
                           (car (fn-lg-scan (fn-bs-durable-content other 0)
                                            (owb-genesis) (owb-unit) (owb-max))))))))

; -----------------------------------------------------------------------------
; T7, reachable.  The barrier fails with the first entry's units landed: the
; kernel faults, every member in flight is :uncertain, nothing is
; acknowledged, and the recovered kernel holds (r1 r2 r3).

; The store a failed fsync of the segment leaves.
(defun owb-eio-of (bs choices) (declare (xargs :guard t :verify-guards nil))
  (mv-let (r bs1) (fn-bs-fsync-file bs 0 (cons :eio choices)) (declare (ignore r)) bs1))
(defun owb-eio-bs (choices) (declare (xargs :guard t :verify-guards nil))
  (owb-eio-of (owb-bs4) choices))
(defun owb-eio-ks (choices) (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-recover (fn-bs-durable-content (owb-eio-bs choices) 0) (owb-genesis) (owb-unit) (owb-max) 9))

(assert-event
 (let* ((st (owb-st4)) (bs (owb-bs4)) (st1 (fn-owb-fence-failed st))
        (choices (owb-choice (owb-e1))))
   (and (fn-owb-alignedp st)
        (fn-lgk-relp bs (fn-owb-ks st) 0 (owb-genesis) (owb-max))
        (consp (fn-lgk-inflight (fn-owb-ks st)))
        (fn-bs-crash-choicesp choices (fn-bs-pending bs) (owb-unit))
        (equal (fn-lgk-phase (fn-owb-ks st1)) :fault)
        (equal (fn-owb-fault-words st1) '((10 . :uncertain) (11 . :uncertain) (12 . :uncertain)))
        (equal (owb-word st1) nil)
        ; the store the failed fsync left is the crash image of the selection
        (equal (owb-eio-bs choices) (fn-bs-crash bs choices))
        (null (fn-bs-pending (owb-eio-bs choices)))
        (equal (fn-lgk-committed (owb-eio-ks choices)) (list (owb-r 1) (owb-r 2) (owb-r 3)))
        (fn-lg-prefixp (nthcdr 2 (fn-lgk-committed (owb-eio-ks choices))) (owb-batch))
        ; the other selections: everything landed, nothing landed
        (equal (fn-lgk-committed (owb-eio-ks (owb-choice (owb-units))))
               (append (list (owb-r 1) (owb-r 2)) (owb-batch)))
        (equal (fn-lgk-committed (owb-eio-ks (owb-choice 0))) (list (owb-r 1) (owb-r 2)))
        ; a take after the fault is refused: nothing enters a faulted kernel
        (equal (fn-owb-take st1 13 '(6 . 5) (owb-r 6) (owb-unit) (owb-bmax) (owb-omax)) st1))))

; T7, hypothesis removal: R (the kernel of an unrelated store).  The failed
; fence of a store holding nothing leaves nothing; the recovered kernel's
; records are not the committed records followed by anything.
(assert-event
 (let* ((st (owb-st4)) (bs (owb-store (fn-bs-zeros 64) (fn-bs-pending (owb-bs4)))))
   (and (fn-owb-alignedp st)
        (consp (fn-lgk-inflight (fn-owb-ks st)))
        (not (fn-lgk-relp bs (fn-owb-ks st) 0 (owb-genesis) (owb-max)))
        (let ((ks2 (fn-lgk-recover
                    (fn-bs-durable-content (owb-eio-of bs (owb-choice 0)) 0)
                    (owb-genesis) (owb-unit) (owb-max) 9)))
          (not (equal (fn-lgk-committed ks2)
                      (append (fn-lgk-committed (fn-owb-ks st))
                              (nthcdr 2 (fn-lgk-committed ks2)))))))))

; T7's "a batch in flight" is scope, not load: with nothing in flight the
; failed fence selects nothing and the conclusion holds as well (the
; weakened theorem is not proved here; recorded).
(assert-event
 (let* ((st (owb-st0)) (bs (owb-bs0)) (st1 (fn-owb-fence-failed st)))
   (and (not (consp (fn-lgk-inflight (fn-owb-ks st))))
        (equal (fn-lgk-phase (fn-owb-ks st1)) :fault)
        (equal (fn-owb-fault-words st1) nil)
        (equal (fn-lgk-committed
                (fn-lgk-recover (fn-bs-durable-content (owb-eio-of bs nil) 0)
                                (owb-genesis) (owb-unit) (owb-max) 9))
               (list (owb-r 1) (owb-r 2))))))

; -----------------------------------------------------------------------------
; T4 over the catalog: two members as a batch against the sequential protocol.

(defconst *owbt-art*
  (append (fn-record-string-octets "Subject: b") '(13 10 13 10)
          (fn-record-string-octets "body") '(13 10)))
(defun owbt-w (seq txid msgid)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-make seq txid 0 msgid *owbt-art* '("fn.test") "o" "s" "e" 1 5))
(defconst *owbt-w1* (owbt-w 0 1 "<a@x>"))
(defconst *owbt-w2* (owbt-w 1 2 "<b@x>"))
(assert-event (and (fn-record-p *owbt-w1*) (fn-record-p *owbt-w2*) (fn-prin-keyringp nil)))

(defun owbt-run-in (fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (pc1 fn-arena)
      (fn-owb-cat-prepare *owbt-w1* :p1 :r1 fn-octets nil 0 0 fn-arena fn-cat)
      (mv-let (pc2 fn-arena)
        (fn-owb-cat-prepare *owbt-w2* :p2 :r2 fn-octets nil 0 1 fn-arena fn-cat)
        (mv-let (b1 b2 fn-cat)
          (fn-owb-complete-two pc1 pc2 fn-cat)
          (let ((batch (list b1 b2 (fn-cat-count fn-cat) (fn-arena-count fn-arena)
                             (fn-held-wire-of (fn-cat-at 0 fn-cat) fn-arena)
                             (fn-held-wire-of (fn-cat-at 1 fn-cat) fn-arena)
                             (fn-pc-token pc1) (fn-pc-token pc2))))
            (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
              (mv-let (q1 fn-arena)
                (fn-cat-prepare *owbt-w1* :p1 :r1 fn-octets nil 0 nil fn-arena fn-cat)
                (mv-let (s1 p1 fn-cat)
                  (fn-cat-complete (fn-pc-token q1) q1 fn-cat)
                  (mv-let (q2 fn-arena)
                    (fn-cat-prepare *owbt-w2* :p2 :r2 fn-octets nil 0 p1 fn-arena fn-cat)
                    (mv-let (s2 p2 fn-cat)
                      (fn-cat-complete (fn-pc-token q2) q2 fn-cat)
                      (declare (ignore p2))
                      (let ((sequential (list s1 s2 (fn-cat-count fn-cat) (fn-arena-count fn-arena)
                                              (fn-held-wire-of (fn-cat-at 0 fn-cat) fn-arena)
                                              (fn-held-wire-of (fn-cat-at 1 fn-cat) fn-arena)
                                              (fn-pc-token q1) (fn-pc-token q2))))
                        ; hypothesis removal: the second member minted with
                        ; AHEAD 0, as if nothing were in the batch
                        (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
                          (mv-let (x1 fn-arena)
                            (fn-owb-cat-prepare *owbt-w1* :p1 :r1 fn-octets nil 0 0 fn-arena fn-cat)
                            (mv-let (x2 fn-arena)
                              (fn-owb-cat-prepare *owbt-w2* :p2 :r2 fn-octets nil 0 0 fn-arena fn-cat)
                              (mv-let (c1 c2 fn-cat)
                                (fn-owb-complete-two x1 x2 fn-cat)
                                (mv (list batch sequential
                                          (list (car c1) c2 (fn-cat-count fn-cat)
                                                (fn-pc-expected x2)))
                                    fn-arena fn-cat fn-octets)))))))))))))))))

(defun owbt-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (with-local-stobj fn-octets
    (mv-let (result fn-arena fn-cat fn-octets)
      (let ((fn-octets (fn-octets-from-list *owbt-art* fn-octets)))
        (owbt-run-in fn-octets fn-arena fn-cat))
      (mv result fn-arena fn-cat))))

(defun owbt-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (owbt-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; T4, reachable: the batch and the sequential protocol agree in every
; component (deltas, count, arena, rows, tokens); the count advanced by two.
; Hypothesis removal: the second token minted AHEAD 0 has EXPECTED 0 where
; the count is 1 after the first complete, and is refused :expected-mismatch.
(assert-event
 (let* ((r (owbt-exec)) (batch (first r)) (sequential (second r)) (wrong (third r)))
   (and (equal batch sequential)
        (equal (car (first batch)) :article) (equal (car (second batch)) :article)
        (equal (third batch) 2)
        (equal (seventh batch) '(1 . 0)) (equal (eighth batch) '(2 . 1))
        (equal (first wrong) :article)
        (equal (second wrong) '(:expected-mismatch))
        (equal (third wrong) 1)
        (equal (fourth wrong) 0))))
