; Teeth for books/recovery-refinement (lane recovery-refinement, 2026-10-01):
; the keystone fn-rr-recovery-refines-a-prefix-with-every-acknowledged-record
; on a ground two-record log, a third record in flight, at the cuts of the
; append and the fence under explicit crash choices, with the image medium
; instantiated by a ground one (the medium that caches the records: the
; encapsulate's witness shape, made executable here); then the MUTATION (a
; recovery that drops an acknowledged record is refused by the theorem: the
; image is no admissible crash image, and the conclusion fails on it) and
; one witness per removed hypothesis.
;
; Crash images are fn-bs-crash under explicit choices with
; fn-bs-crash-choicesp asserted (fn-bs-crash-imagep is a defun-sk and is
; not executable).  The fixture is the one of
; tests/acl2/store-log-durable-tests.lisp (lgut-), re-made here under its
; own prefix so this book includes no test book.
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/recovery-refinement")
(include-book "../../books/frame-trailer")

(defun rrt-unit () (declare (xargs :guard t)) 4)
(defun rrt-max () (declare (xargs :guard t)) 4096)
(defun rrt-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun rrt-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))
(defun rrt-store (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (rrt-unit) (list (cons 0 content)) nil pending 1))
(defun rrt-sels (count sel)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil (cons sel (rrt-sels (1- count) sel))))
(defun rrt-units-of (octets)
  (declare (xargs :guard t :verify-guards nil))
  (floor (len octets) (rrt-unit)))

; The segment a crash left: two records logged, a torn unit, zeros, then the
; preallocated extent; P-LOG-RECOVER from it gives the related state.
(defun rrt-content ()
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (rrt-r 1) (rrt-r 2)) (rrt-genesis) (rrt-unit))
          '(9 9 9 9 0 0 0 0 0 0 0 0)
          (fn-bs-zeros 512)))
(defun rrt-ks0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-recover (rrt-content) (rrt-genesis) (rrt-unit) (rrt-max) 3))
(defun rrt-recover-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (rrt-store (rrt-content) nil) (rrt-ks0) (fn-lg-recover-program) nil 0))
(defun rrt-bs0 () (declare (xargs :guard t :verify-guards nil)) (car (car (last (rrt-recover-run)))))
; A third record prepared and appended: the batch in flight.
(defun rrt-ks1 () (declare (xargs :guard t :verify-guards nil)) (fn-lgk-prepare (rrt-ks0) (rrt-r 3)))
(defun rrt-append-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (rrt-bs0) (rrt-ks1) (fn-lg-append-program) nil 0))
(defun rrt-appended () (declare (xargs :guard t :verify-guards nil)) (car (last (rrt-append-run))))
(defun rrt-batch-units ()
  (declare (xargs :guard t :verify-guards nil))
  (rrt-units-of (nth 3 (car (fn-bs-pending (car (rrt-appended)))))))
(defun rrt-fence-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (car (rrt-appended)) (cdr (rrt-appended)) (fn-lg-fence-program) nil 0))

; Reachable: the recovered kernel holds r1 r2 acknowledged (the recovery
; acknowledges every scanned record), is related to the fenced store, and
; the append reaches log-written with r3 in flight.
(assert-event
 (and (fn-lgk-relp (rrt-bs0) (rrt-ks0) 0 (rrt-genesis) (rrt-max))
      (equal (fn-lgk-committed (rrt-ks0)) (list (rrt-r 1) (rrt-r 2)))
      (equal (fn-lgk-acked (rrt-ks0)) 2)
      (fn-lgk-relp (rrt-bs0) (rrt-ks1) 0 (rrt-genesis) (rrt-max))
      (equal (len (rrt-append-run)) 2)
      (fn-lgk-relp (car (rrt-appended)) (cdr (rrt-appended)) 0 (rrt-genesis) (rrt-max))
      (equal (fn-lgk-inflight (cdr (rrt-appended))) (list (rrt-r 3)))
      (equal (len (rrt-fence-run)) 2)))

; -----------------------------------------------------------------------------
; The log's half on the ground, at log-written under every per-unit tear
; and at log-fenced: the recovered records are a tree-sequence member and
; hold the acknowledged r1 and r2.

(defun rrt-recovered (pair choices)
  (declare (xargs :guard t :verify-guards nil))
  (fn-rr-recovered-records (fn-bs-crash (car pair) choices) 0 (rrt-genesis) (rrt-unit) (rrt-max) 0))
(defun rrt-member-p (pair choices)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-crash-choicesp choices (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
       (fn-rr-tree-sequence-memberp (rrt-recovered pair choices)
                                    (fn-lgk-committed (cdr pair)) (fn-lgk-inflight (cdr pair)))
       (member-equal (rrt-r 1) (rrt-recovered pair choices))
       (member-equal (rrt-r 2) (rrt-recovered pair choices))))

(assert-event
 (let ((w (rrt-appended)))
   (and (rrt-member-p w (list (rrt-sels (rrt-batch-units) :new)))   ; the batch landed whole: r1 r2 r3
        (equal (rrt-recovered w (list (rrt-sels (rrt-batch-units) :new)))
               (list (rrt-r 1) (rrt-r 2) (rrt-r 3)))
        (rrt-member-p w (list nil))                                   ; not at all: r1 r2
        (equal (rrt-recovered w (list nil)) (list (rrt-r 1) (rrt-r 2)))
        (rrt-member-p w (list (list :new)))                           ; its first unit only
        (rrt-member-p w (list (list :new :old :new)))                 ; a hole
        (rrt-member-p w (list (list :zero :new)))                     ; zero-filled
        (rrt-member-p (nth 1 (rrt-fence-run)) nil)                    ; log-fenced: nothing pending
        (equal (rrt-recovered (nth 1 (rrt-fence-run)) nil)
               (list (rrt-r 1) (rrt-r 2) (rrt-r 3))))))

; -----------------------------------------------------------------------------
; The medium's half on the ground: a medium that caches the records (the
; encapsulate's witness, executable), instantiated into fn-rr-open.

(defun rrt-capture (configs records) (declare (xargs :guard t) (ignore configs)) records)
(defun rrt-full-open (configs frontier records)
  (declare (xargs :guard t))
  (list :opened configs frontier records))
(defun rrt-open (ckpt configs frontier suffix)
  (declare (xargs :guard t :verify-guards nil))
  (rrt-full-open configs frontier (append ckpt suffix)))
(defun rrt-select (status s count k)
  (declare (xargs :guard t))
  (if (and (equal status :ok) (natp s) (natp count) (<= s count)
           (natp k) (<= (- count s) k))
      (list :checkpoint s)
    (list :full-replay)))
(defun rrt-composed-open (status s ckpt configs frontier records k)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car (rrt-select status s (len records) k)) :checkpoint)
      (rrt-open ckpt configs frontier (nthcdr s records))
    (rrt-full-open configs frontier records)))
; The ground open always succeeds and holds the records it opened.
(defun rrt-open-okp (st) (declare (xargs :guard t :verify-guards nil)) (equal (car st) :opened))
(defun rrt-holds (st r) (declare (xargs :guard t :verify-guards nil)) (member-equal r (nth 3 st)))

; The medium's theorem, instantiated: the ground medium meets the interface
; (its three constraints discharged, the holding one included).
(defthm rrt-open-is-the-full-open-of-the-recovered-records
  (implies (equal ckpt (rrt-capture configs (take s records)))
           (equal (rrt-composed-open status s ckpt configs frontier records k)
                  (rrt-full-open configs frontier records)))
  :hints (("Goal"
           :use ((:functional-instance
                  fn-rr-open-is-the-full-open-of-the-recovered-records
                  (fn-rr-medium-capture rrt-capture)
                  (fn-rr-medium-open rrt-open)
                  (fn-rr-medium-full-open rrt-full-open)
                  (fn-rr-medium-select rrt-select)
                  (fn-rr-medium-open-okp rrt-open-okp)
                  (fn-rr-medium-holds rrt-holds)
                  (fn-rr-open rrt-composed-open)))
           :in-theory (enable rrt-composed-open rrt-select rrt-open rrt-capture
                              rrt-full-open rrt-open-okp rrt-holds))))

; The keystone itself over the ground medium: the literal theorem with the
; medium's five functions instantiated (the Codex review of 2d1b10ed7, F4:
; the positive witness below asserts THIS theorem's antecedent and
; conclusion, not a paraphrase).
(defthm rrt-keystone
  (let ((recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (fn-bs-crash-imagep bs image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
                  (natp s)
                  (<= s (len (fn-lgk-committed ks)))
                  (equal ckpt (rrt-capture configs (take s (fn-lgk-committed ks)))))
             (and (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks)
                                               (fn-lgk-inflight ks))
                  (equal (rrt-composed-open status s ckpt configs frontier recovered k)
                         (rrt-full-open configs frontier recovered))
                  (implies (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                           (and (member-equal r recovered)
                                (implies (rrt-open-okp
                                          (rrt-composed-open status s ckpt configs frontier
                                                             recovered k))
                                         (rrt-holds
                                          (rrt-composed-open status s ckpt configs frontier
                                                             recovered k)
                                          r)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:functional-instance
                  fn-rr-recovery-refines-a-prefix-with-every-acknowledged-record
                  (fn-rr-medium-capture rrt-capture)
                  (fn-rr-medium-open rrt-open)
                  (fn-rr-medium-full-open rrt-full-open)
                  (fn-rr-medium-select rrt-select)
                  (fn-rr-medium-open-okp rrt-open-okp)
                  (fn-rr-medium-holds rrt-holds)
                  (fn-rr-open rrt-composed-open)))
           :in-theory (enable rrt-composed-open rrt-select rrt-open rrt-capture
                              rrt-full-open rrt-open-okp rrt-holds))))

; Evaluated on the ground: an image bound at S = 0, 1, 2 (within K = 4),
; past K (K = 0: the full replay), and an absent image, each the full open
; of the recovered r1 r2 r3.
(assert-event
 (let* ((rec (rrt-recovered (rrt-appended) (list (rrt-sels (rrt-batch-units) :new))))
        (full (rrt-full-open nil 9 rec)))
   (and (equal (rrt-composed-open :ok 0 (rrt-capture nil (take 0 rec)) nil 9 rec 4) full)
        (equal (rrt-composed-open :ok 1 (rrt-capture nil (take 1 rec)) nil 9 rec 4) full)
        (equal (rrt-composed-open :ok 2 (rrt-capture nil (take 2 rec)) nil 9 rec 4) full)
        (equal (car (rrt-select :ok 2 (len rec) 4)) :checkpoint)
        (equal (rrt-composed-open :ok 1 (rrt-capture nil (take 1 rec)) nil 9 rec 0) full)
        (equal (car (rrt-select :ok 1 (len rec) 0)) :full-replay)
        (equal (rrt-composed-open :absent 0 nil nil 9 rec 4) full))))

; -----------------------------------------------------------------------------
; The reachable positive witness of rrt-keystone, complete antecedent and
; conclusion, at two crash points: log-written with the batch landed whole
; (the exact tear: fn-lg-platform-tears-p evaluates through its exact arm
; and the empty batch, reaching no constrained call) and log-fenced
; (nothing in flight).  The image is fn-bs-crash under choices asserted
; admissible (fn-bs-crash-imagep's executable form).  At a non-exact tear
; the premise is A-CRYPTO-TRAILER's constrained consequent and cannot be
; evaluated: its applicability is the assumption's own tooth
; (tests/acl2/assumptions-tests.lisp), and the local witness of
; fn-assume-crash-tearp admits only the exact tear (the open item F4 of the
; Codex review, recorded in specs/recovery-refinement.md section 6).
(defun rrt-full-witness-p (pair choices s r)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((bs (car pair)) (ks (cdr pair))
         (image (fn-bs-crash bs choices))
         (recovered (fn-rr-recovered-records image 0 (rrt-genesis) (fn-bs-unit bs) (rrt-max) 0))
         (ckpt (rrt-capture nil (take s (fn-lgk-committed ks))))
         (opened (rrt-composed-open :ok s ckpt nil 9 recovered 4)))
    (and ; the antecedent
         (fn-lgk-relp bs ks 0 (rrt-genesis) (rrt-max))
         (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
         (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image 0))
                                 (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
         (natp s) (<= s (len (fn-lgk-committed ks)))
         (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
         ; the conclusion
         (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks) (fn-lgk-inflight ks))
         (equal opened (rrt-full-open nil 9 recovered))
         (member-equal r recovered)
         (rrt-open-okp opened)
         (rrt-holds opened r))))
(assert-event
 (and (rrt-full-witness-p (rrt-appended) (list (rrt-sels (rrt-batch-units) :new)) 1 (rrt-r 1))
      (rrt-full-witness-p (rrt-appended) (list (rrt-sels (rrt-batch-units) :new)) 2 (rrt-r 2))
      (rrt-full-witness-p (nth 1 (rrt-fence-run)) nil 2 (rrt-r 2))
      (rrt-full-witness-p (nth 1 (rrt-fence-run)) nil 0 (rrt-r 1))))

; -----------------------------------------------------------------------------
; MUTATION: a recovery that drops an acknowledged record.  The image whose
; segment is zeroed from r2's entry on is NOT an admissible crash image of
; the related state (the segment is fenced there: every admissible image
; holds its durable content, fn-bs-crash-keeps-fenced-content), and on it
; the keystone's conclusion fails: r2 (acknowledged) is not recovered.

(defun rrt-r1-only-octets ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (rrt-r 1)) (rrt-genesis) (rrt-unit)))
(defun rrt-dropped-image ()
  (declare (xargs :guard t :verify-guards nil))
  (rrt-store (append (rrt-r1-only-octets)
                     (fn-bs-zeros (- (len (fn-bs-durable-content (rrt-bs0) 0))
                                     (len (rrt-r1-only-octets)))))
             nil))
(assert-event
 (and (fn-bs-fencedp (rrt-bs0) 0)
      (not (equal (fn-bs-durable-content (rrt-dropped-image) 0)
                  (fn-bs-durable-content (rrt-bs0) 0)))
      (equal (fn-rr-recovered-records (rrt-dropped-image) 0 (rrt-genesis) (rrt-unit) (rrt-max) 0)
             (list (rrt-r 1)))
      (member-equal (rrt-r 2) (take (fn-lgk-acked (rrt-ks0)) (fn-lgk-committed (rrt-ks0))))))
(must-fail-checked
 (defthm rrt-dropping-an-acknowledged-record
   (member-equal (rrt-r 2)
                 (fn-rr-recovered-records (rrt-dropped-image) 0 (rrt-genesis) (rrt-unit) (rrt-max) 0))))
(must-fail-checked
 (defthm rrt-dropped-image-is-a-tree-sequence-member
   (fn-rr-tree-sequence-memberp
    (fn-rr-recovered-records (rrt-dropped-image) 0 (rrt-genesis) (rrt-unit) (rrt-max) 0)
    (fn-lgk-committed (rrt-ks0)) (fn-lgk-inflight (rrt-ks0)))))

; -----------------------------------------------------------------------------
; Hypothesis removal.

; The binding: an image bound to the capture of a NON-prefix (r2 r1) at
; S = 2 opens to the full open of r2 r1 r3, not of the recovered r1 r2 r3.
(must-fail-checked
 (defthm rrt-without-the-binding
   (let* ((rec (list (rrt-r 1) (rrt-r 2) (rrt-r 3))))
     (equal (rrt-composed-open :ok 2 (rrt-capture nil (list (rrt-r 2) (rrt-r 1))) nil 9 rec 4)
            (rrt-full-open nil 9 rec)))))

; The relation R alone: the store at log-written with a SECOND pending
; write to the segment, the log of r4 chained after r3's entry and placed
; after it, while the kernel holds r3 alone in flight.  It is unrelated
; (R's pending conjunct: the segment's write is not the only pending
; operation; the lifted relation of books/recovery-refinement-concurrent
; fails the same way, two writes to the segment), and every other
; hypothesis is kept: the choices are admissible, the trailer premise
; evaluates true on the image where both land whole (r3's entry is exact
; and the batch is then exhausted, so no constrained call is reached), S
; and the binding are the witness's own.  That image recovers r1 r2 r3 r4:
; no tree-sequence member over COMMITTED and INFLIGHT = (r3).  (A single
; write of r4 in r3's place, or of r3 r4 in one entry, would also falsify
; the trailer premise: two hypotheses removed, the Codex review's F3.)
(defun rrt-wrong-batch ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((bs (car (rrt-appended)))
         (ks (cdr (rrt-appended)))
         (w (car (fn-bs-pending bs)))
         (prev4 (fn-lg-scan-last (nth 3 w) (fn-lgk-last ks) (rrt-unit) (rrt-max))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (list w
                      (list :write 0 (+ (nth 2 w) (len (nth 3 w)))
                            (fn-lg-log (list (rrt-r 4)) prev4 (rrt-unit))))
                (fn-bs-next-ino bs))))
(defun rrt-wrong-choices ()
  (declare (xargs :guard t :verify-guards nil))
  (list (rrt-sels (rrt-units-of (nth 3 (car (fn-bs-pending (rrt-wrong-batch))))) :new)
        (rrt-sels (rrt-units-of (nth 3 (cadr (fn-bs-pending (rrt-wrong-batch))))) :new)))
(defun rrt-wrong-image ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-crash (rrt-wrong-batch) (rrt-wrong-choices)))
(defun rrt-wrong-recovered ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-rr-recovered-records (rrt-wrong-image) 0 (rrt-genesis) (rrt-unit) (rrt-max) 0))
(assert-event
 (let ((ks (cdr (rrt-appended))))
   (and ; the omitted hypothesis fails
        (not (fn-lgk-relp (rrt-wrong-batch) ks 0 (rrt-genesis) (rrt-max)))
        ; every retained hypothesis holds
        (fn-bs-crash-choicesp (rrt-wrong-choices) (fn-bs-pending (rrt-wrong-batch)) (rrt-unit))
        (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content (rrt-wrong-image) 0))
                                (fn-lgk-inflight ks) (fn-lgk-last ks) (rrt-unit))
        (<= 2 (len (fn-lgk-committed ks)))
        ; the conclusion fails
        (equal (rrt-wrong-recovered) (list (rrt-r 1) (rrt-r 2) (rrt-r 3) (rrt-r 4)))
        (not (fn-rr-tree-sequence-memberp (rrt-wrong-recovered)
                                          (fn-lgk-committed ks) (fn-lgk-inflight ks))))))
(must-fail-checked
 (defthm rrt-without-the-relation
   (fn-rr-tree-sequence-memberp (rrt-wrong-recovered)
                                (fn-lgk-committed (cdr (rrt-appended)))
                                (fn-lgk-inflight (cdr (rrt-appended))))))

; A-CRYPTO-TRAILER's premise (fn-lg-platform-tears-p) is a constrained
; function's consequent; without it the in-flight theorem keeps the forgery
; disjunct (fn-lgk-crash-of-related-state-is-a-prefix), and no ground tear
; forges under the model's own trailer: the per-unit tears above all
; satisfy the conclusion.  The witness that the premise is needed is the
; assumption's own (tests/acl2/assumptions-tests.lisp).

; -----------------------------------------------------------------------------
; The checkpoint program's crash points
; (fn-rr-checkpoint-crash-point-recovers-committed-under-old-or-new): the
; publish program from the recovered, quiet store (no old image), every
; one of its ten states, under the lose-everything choice and the
; land-everything choice: the segment recovers r1 r2 and the image is the
; old (absent) or the new one.

(defun rrt-scp-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-run (rrt-bs0) (rrt-ks0) (fn-bs-scp-program ".stage-1" '(1 2 3)) nil nil 0))
(defun rrt-scp-ok-p (i choices)
  (declare (xargs :guard t :verify-guards nil))
  (let ((image (fn-bs-crash (car (nth i (rrt-scp-run))) choices)))
    (and (equal (fn-rr-recovered-records image 0 (rrt-genesis) (rrt-unit) (rrt-max) 0)
                (list (rrt-r 1) (rrt-r 2)))
         (fn-bs-scp-old-or-newp image (rrt-bs0) nil '(1 2 3)))))
(defun rrt-scp-all-ok-p (i)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp i) t
    (and (rrt-scp-ok-p (1- i) nil)
         (rrt-scp-ok-p (1- i) (list :apply (list :new) :apply :apply))
         (rrt-scp-all-ok-p (1- i)))))
(assert-event
 (and (fn-bs-scp-inputp (rrt-bs0) ".stage-1" nil)
      (not (consp (fn-lgk-inflight (rrt-ks0))))
      (< 0 (fn-bs-next-ino (rrt-bs0)))
      (equal (len (rrt-scp-run)) 10)
      (rrt-scp-all-ok-p 10)
      ; the new image lands at the durable cut under the land-everything choice
      (equal (fn-bs-durable-entry (fn-bs-crash (car (nth 9 (rrt-scp-run)))
                                               (list :apply (list :new) :apply :apply))
                                  :root "store-checkpoint.fnsc")
             (fn-bs-next-ino (rrt-bs0)))))
