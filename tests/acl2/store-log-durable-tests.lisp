; Teeth for books/store-log-durable (lane byte-model, row Q3b): the keystone
; fn-lgu-acknowledged-article-is-recoverable-at-every-crash-point and its
; recovery half, on a ground two-record log, at every cut of every program
; the host runs, under explicit crash choices; then one witness per removed
; hypothesis.
;
; Crash images are fn-bs-crash under explicit choices with
; fn-bs-crash-choicesp asserted (fn-bs-crash-imagep is a defun-sk and is
; not executable); fn-assume-log-sole-pending-writer is constrained, so a
; witness asserts its constraint's consequent instead.
(in-package "ACL2")
(include-book "../../books/store-log-durable")
(include-book "../../books/frame-trailer")

(defun lgut-unit () (declare (xargs :guard t)) 4)
(defun lgut-max () (declare (xargs :guard t)) 4096)
(defun lgut-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun lgut-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))
(defun lgut-store (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (lgut-unit) (list (cons 0 content)) nil pending 1))
(defun lgut-sels (count sel)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil (cons sel (lgut-sels (1- count) sel))))
(defun lgut-units-of (octets)
  (declare (xargs :guard t :verify-guards nil))
  (floor (len octets) (lgut-unit)))
; The recovered kernel of an image's segment: what the next open holds.
(defun lgut-open (image)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image 0)
                                    (lgut-genesis) (lgut-unit) (lgut-max) 0)))
; The keystone's conclusion on the image the choices leave.
(defun lgut-recovered-p (m pair choices)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-crash-choicesp choices (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
       (member-equal (fn-owb-member-record m)
                     (lgut-open (fn-bs-crash (car pair) choices)))))

; The segment a crash left: two records logged, a torn unit, zeros, then the
; preallocated extent.
(defun lgut-content ()
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (lgut-r 1) (lgut-r 2)) (lgut-genesis) (lgut-unit))
          '(9 9 9 9 0 0 0 0 0 0 0 0)
          (fn-bs-zeros 512)))
(defun lgut-bs-raw () (declare (xargs :guard t :verify-guards nil)) (lgut-store (lgut-content) nil))
; P-LOG-RECOVER: the recovered layer (every scanned record an acknowledged
; anonymous member), the run, the fenced store at log-recovered.
(defun lgut-st0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-owb-recover (lgut-content) (lgut-genesis) (lgut-unit) (lgut-max) 3))
(defun lgut-ks0 () (declare (xargs :guard t :verify-guards nil)) (fn-owb-ks (lgut-st0)))
(defun lgut-recover-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (lgut-bs-raw) (lgut-ks0) (fn-lg-recover-program) nil 0))
(defun lgut-bs0 () (declare (xargs :guard t :verify-guards nil)) (car (car (last (lgut-recover-run)))))
(defun lgut-m1 () (declare (xargs :guard t :verify-guards nil)) (car (fn-owb-acked (lgut-st0))))
(defun lgut-m2 () (declare (xargs :guard t :verify-guards nil)) (cadr (fn-owb-acked (lgut-st0))))

; Reachable: the recovered layer is aligned, related to the fenced store,
; and holds the two records as acknowledged members.
(assert-event
 (and (fn-owb-alignedp (lgut-st0))
      (fn-lgk-relp (lgut-bs0) (lgut-ks0) 0 (lgut-genesis) (lgut-max))
      (equal (fn-lgk-committed (lgut-ks0)) (list (lgut-r 1) (lgut-r 2)))
      (equal (fn-owb-member-record (lgut-m1)) (lgut-r 1))
      (equal (fn-owb-member-record (lgut-m2)) (lgut-r 2))
      (equal (len (lgut-recover-run)) 4)))

; -----------------------------------------------------------------------------
; The recovery half: every cut of P-LOG-RECOVER from the raw store, the
; zeroing write torn four ways at log-truncated, nothing pending at
; log-recovered.

(defun lgut-recover-pair (i) (declare (xargs :guard t :verify-guards nil)) (nth i (lgut-recover-run)))
(defun lgut-tail-units ()
  (declare (xargs :guard t :verify-guards nil))
  (lgut-units-of (nth 3 (car (fn-bs-pending (car (lgut-recover-pair 0)))))))

(assert-event
 (and (not (fn-bs-ops-for-ino (fn-bs-pending (lgut-bs-raw)) 0))
      (not (fn-bs-ops-not-for-ino (fn-bs-pending (lgut-bs-raw)) 0))
      (consp (fn-bs-pending (car (lgut-recover-pair 0))))
      (null (fn-bs-pending (car (lgut-recover-pair 2))))
      ; log-truncated: all landed, none, the first unit only, a hole
      (lgut-recovered-p (lgut-m1) (lgut-recover-pair 0) (list (lgut-sels (lgut-tail-units) :new)))
      (lgut-recovered-p (lgut-m2) (lgut-recover-pair 0) (list (lgut-sels (lgut-tail-units) :new)))
      (lgut-recovered-p (lgut-m1) (lgut-recover-pair 0) (list nil))
      (lgut-recovered-p (lgut-m1) (lgut-recover-pair 1) (list (list :new)))
      (lgut-recovered-p (lgut-m2) (lgut-recover-pair 1) (list (list :old :new :old)))
      ; log-recovered: nothing pending, the image is the store
      (lgut-recovered-p (lgut-m1) (lgut-recover-pair 2) nil)
      (lgut-recovered-p (lgut-m2) (lgut-recover-pair 3) nil)))

; -----------------------------------------------------------------------------
; The served programs from the recovered state: a third record prepared,
; the append, the fence (:ok and failed), the extension.

(defun lgut-ks1 () (declare (xargs :guard t :verify-guards nil)) (fn-lgk-prepare (lgut-ks0) (lgut-r 3)))
(defun lgut-m3 () (declare (xargs :guard t :verify-guards nil)) (fn-owb-member 9 :t9 (lgut-r 3)))
; The layer with the third record open: aligned over ks1.
(defun lgut-st1 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-owb-make (lgut-ks1) (list (lgut-m3)) nil nil (fn-owb-acked (lgut-st0))))
(defun lgut-append-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (lgut-bs0) (lgut-ks1) (fn-lg-append-program) nil 0))
(defun lgut-appended () (declare (xargs :guard t :verify-guards nil)) (car (last (lgut-append-run))))
(defun lgut-batch-units ()
  (declare (xargs :guard t :verify-guards nil))
  (lgut-units-of (nth 3 (car (fn-bs-pending (car (lgut-appended)))))))
(defun lgut-fence-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (car (lgut-appended)) (cdr (lgut-appended)) (fn-lg-fence-program) nil 0))
(defun lgut-failed-outcome (choices) (declare (xargs :guard t)) (cons :eio choices))
(defun lgut-failed-fence-run (choices)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (car (lgut-appended)) (cdr (lgut-appended)) (fn-lg-fence-program)
             (list (lgut-failed-outcome choices)) 0))
(defun lgut-next ()
  (declare (xargs :guard t :verify-guards nil))
  (+ (len (fn-bs-durable-content (lgut-bs0) 0)) 512))
(defun lgut-extend-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-extend-run (lgut-bs0) (lgut-ks0) (fn-lg-extend-program (lgut-next)) nil 0))

; Reachable: the layer with the third record is aligned and related; the
; append reaches log-written with the batch in flight; every cut of the
; append, the fence and the extension is a crash point of the keystone.
(assert-event
 (and (fn-owb-alignedp (lgut-st1))
      (fn-lgk-relp (lgut-bs0) (lgut-ks1) 0 (lgut-genesis) (lgut-max))
      (equal (len (lgut-append-run)) 2)
      (equal (fn-lgk-inflight (cdr (lgut-appended))) (list (lgut-r 3)))
      (equal (len (lgut-fence-run)) 2)
      (equal (len (lgut-failed-fence-run (list nil))) 1)
      (equal (len (lgut-extend-run)) 4)
      (fn-lgu-crash-point-p (nth 0 (lgut-append-run)) (lgut-bs0) (lgut-ks1) nil 0 0 (lgut-genesis) (lgut-max))
      (fn-lgu-crash-point-p (nth 1 (lgut-append-run)) (lgut-bs0) (lgut-ks1) nil 0 0 (lgut-genesis) (lgut-max))
      (fn-lgu-crash-point-p (nth 1 (lgut-fence-run)) (car (lgut-appended)) (cdr (lgut-appended))
                            nil 0 0 (lgut-genesis) (lgut-max))
      (fn-lgu-crash-point-p (nth 0 (lgut-failed-fence-run (list (list :new))))
                            (car (lgut-appended)) (cdr (lgut-appended))
                            (lgut-failed-outcome (list (list :new))) 0 0 (lgut-genesis) (lgut-max))
      (fn-lgu-crash-point-p (nth 0 (lgut-extend-run)) (lgut-bs0) (lgut-ks0) nil (lgut-next) 0
                            (lgut-genesis) (lgut-max))
      (fn-lgu-crash-point-p (nth 3 (lgut-extend-run)) (lgut-bs0) (lgut-ks0) nil (lgut-next) 0
                            (lgut-genesis) (lgut-max))))

; The keystone at every served cut: the acknowledged records r1 and r2
; are held by the open of every image.  log-written: the batch's write
; landed whole, not at all, its first unit only, with a hole; log-fenced:
; nothing pending; the failed barrier under each selection: the store it
; leaves has nothing pending (its one image is itself); log-extended: the
; zeros landed whole, not at all, torn; log-extent-fenced.
(assert-event
 (let ((w (lgut-appended)) (x0 (nth 0 (lgut-extend-run))) (x3 (nth 3 (lgut-extend-run))))
   (and (lgut-recovered-p (lgut-m1) w (list (lgut-sels (lgut-batch-units) :new)))
        (lgut-recovered-p (lgut-m2) w (list (lgut-sels (lgut-batch-units) :new)))
        (lgut-recovered-p (lgut-m1) w (list nil))
        (lgut-recovered-p (lgut-m2) w (list (list :new)))
        (lgut-recovered-p (lgut-m1) w (list (list :new :old :new)))
        (lgut-recovered-p (lgut-m1) (nth 1 (lgut-fence-run)) nil)
        (lgut-recovered-p (lgut-m2) (nth 1 (lgut-fence-run)) nil)
        (lgut-recovered-p (lgut-m1) (nth 0 (lgut-failed-fence-run (list (lgut-sels (lgut-batch-units) :new)))) nil)
        (lgut-recovered-p (lgut-m2) (nth 0 (lgut-failed-fence-run (list nil))) nil)
        (lgut-recovered-p (lgut-m1) (nth 0 (lgut-failed-fence-run (list (list :old :new)))) nil)
        (lgut-recovered-p (lgut-m1) x0 (list (lgut-sels 128 :new)))
        (lgut-recovered-p (lgut-m2) x0 (list nil))
        (lgut-recovered-p (lgut-m1) x0 (list (list :new :old :new)))
        (lgut-recovered-p (lgut-m2) x3 nil))))

; T7 on the ground: after the failed barrier the kernel is faulted and the
; open holds the committed records then a prefix of the batch: the whole
; batch when its write landed, nothing of it when nothing landed.
(assert-event
 (let ((all (nth 0 (lgut-failed-fence-run (list (lgut-sels (lgut-batch-units) :new)))))
       (none (nth 0 (lgut-failed-fence-run (list nil)))))
   (and (equal (fn-lgk-phase (cdr all)) :fault)
        (equal (lgut-open (car all)) (list (lgut-r 1) (lgut-r 2) (lgut-r 3)))
        (equal (lgut-open (car none)) (list (lgut-r 1) (lgut-r 2))))))

; -----------------------------------------------------------------------------
; Hypothesis removal, one witness each.  Every retained hypothesis is
; asserted, the omitted one is asserted false, and the conclusion false.

; (member-equal m (fn-owb-acked st)) removed: the third record is a member
; of the layer, not acknowledged; at log-written with nothing landed the
; open does not hold it.
(assert-event
 (let ((pair (lgut-appended)))
   (and (fn-owb-alignedp (lgut-st1))
        (fn-lgu-crash-point-p pair (lgut-bs0) (lgut-ks1) nil 0 0 (lgut-genesis) (lgut-max))
        (fn-bs-crash-choicesp (list nil) (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
        (member-equal (lgut-m3) (fn-owb-members (lgut-st1)))
        (not (member-equal (lgut-m3) (fn-owb-acked (lgut-st1))))
        (not (member-equal (fn-owb-member-record (lgut-m3))
                           (lgut-open (fn-bs-crash (car pair) (list nil))))))))

; fn-lgu-crash-point-p removed (its relation R): a CORRUPTED-STATE witness.
; The kernel says (r9) is committed; the segment holds r1 and r2.  The
; layer acknowledges r9; the state is not related, the append's cut is no
; crash point, and the open does not hold r9.
(defun lgut-bad-ks ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-make (list (lgut-r 9)) (lgut-genesis) 0 1 nil nil 1 :ready))
(defun lgut-bad-st ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-owb-make (lgut-bad-ks) nil nil nil (fn-owb-anonymous (list (lgut-r 9)))))
(assert-event
 (let* ((m (car (fn-owb-acked (lgut-bad-st))))
        (pair (car (last (fn-lg-run (lgut-bs0) (lgut-bad-ks) (fn-lg-append-program) nil 0)))))
   (and (fn-owb-alignedp (lgut-bad-st))
        (member-equal m (fn-owb-acked (lgut-bad-st)))
        (fn-bs-crash-choicesp nil (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
        (not (fn-lgk-relp (lgut-bs0) (lgut-bad-ks) 0 (lgut-genesis) (lgut-max)))
        (not (fn-lgu-crash-point-p pair (lgut-bs0) (lgut-bad-ks) nil 0 0 (lgut-genesis) (lgut-max)))
        (not (member-equal (fn-owb-member-record m) (lgut-open (fn-bs-crash (car pair) nil)))))))

; fn-lgu-crash-point-p removed (the cut): a MUTATION witness.  A state that
; is no cut of any program (the segment wiped to zeros) with the related
; layer: not a crash point, and the open holds nothing.
(assert-event
 (let ((pair (cons (lgut-store (fn-bs-zeros (len (lgut-content))) nil) (lgut-ks0))))
   (and (fn-owb-alignedp (lgut-st0))
        (member-equal (lgut-m1) (fn-owb-acked (lgut-st0)))
        (fn-bs-crash-choicesp nil (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
        (not (fn-lgu-crash-point-p pair (lgut-bs0) (lgut-ks0) nil 0 0 (lgut-genesis) (lgut-max)))
        (not (member-equal (fn-owb-member-record (lgut-m1)) (lgut-open (fn-bs-crash (car pair) nil)))))))

; The image's admissibility removed: an "image" no crash of the appended
; state leaves (its segment wiped), with the retained hypotheses: the open
; holds nothing.  (fn-bs-crash-imagep is not executable; the witness shows
; the wiped store differs from every image of the sample choices.)
(assert-event
 (let* ((pair (lgut-appended))
        (wiped (lgut-store (fn-bs-zeros (len (fn-bs-durable-content (car pair) 0))) nil)))
   (and (fn-owb-alignedp (lgut-st1))
        (member-equal (lgut-m1) (fn-owb-acked (lgut-st1)))
        (fn-lgu-crash-point-p pair (lgut-bs0) (lgut-ks1) nil 0 0 (lgut-genesis) (lgut-max))
        (not (equal wiped (fn-bs-crash (car pair) (list nil))))
        (not (equal wiped (fn-bs-crash (car pair) (list (lgut-sels (lgut-batch-units) :new)))))
        (not (member-equal (fn-owb-member-record (lgut-m1)) (lgut-open wiped))))))

; The recovery half's (member-equal r committed) removed: a record the scan
; did not read (r3, never logged) is not in the open of any recovery cut's
; image; the retained hypotheses hold.
(assert-event
 (let ((pair (lgut-recover-pair 0)))
   (and (not (fn-bs-ops-for-ino (fn-bs-pending (lgut-bs-raw)) 0))
        (not (fn-bs-ops-not-for-ino (fn-bs-pending (lgut-bs-raw)) 0))
        (fn-bs-crash-choicesp (list nil) (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
        (not (member-equal (lgut-r 3) (fn-lgk-committed (lgut-ks0))))
        (not (member-equal (lgut-r 3) (lgut-open (fn-bs-crash (car pair) (list nil))))))))
