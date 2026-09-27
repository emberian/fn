; Witnesses and teeth for books/store-log-extend.lisp (lane log-2): the
; segment's extension step.  Crash images are fn-bs-crash under explicit
; choices with fn-bs-crash-choicesp asserted (the keystone's
; fn-bs-crash-imagep is its existential).
(in-package "ACL2")
(include-book "../../books/store-log-extend")
(include-book "../../books/store-log-txid")
(include-book "../../books/frame-trailer")

(defun sle-unit () (declare (xargs :guard t)) 4)
(defun sle-max () (declare (xargs :guard t)) 4096)
(defun sle-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun sle-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))
(defun sle-bs (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (sle-unit) (list (cons 0 content)) nil pending 1))
(defun sle-sels (count sel)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil (cons sel (sle-sels (1- count) sel))))
(defun sle-content (bs) (declare (xargs :guard t :verify-guards nil)) (fn-bs-durable-content bs 0))

; One committed record, then 200 zeros: a resting segment (frontier < end).
(defun sle-log1 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (sle-r 1)) (sle-genesis) (sle-unit)))
(defun sle-c () (declare (xargs :guard t :verify-guards nil))
  (append (sle-log1) (fn-bs-zeros 200)))
(defun sle-ks () (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover (sle-c) (sle-genesis) (sle-unit) (sle-max) 2))
(defun sle-bs0 () (declare (xargs :guard t :verify-guards nil)) (sle-bs (sle-c) nil))
(defun sle-next () (declare (xargs :guard t :verify-guards nil)) (+ (len (sle-c)) 12))

; The keystone's conclusion, as a predicate over one image.
(defun sle-crash-okp (bs ks image)
  (declare (xargs :guard t :verify-guards nil))
  (let ((content (fn-bs-durable-content image 0))
        (c (fn-bs-durable-content bs 0)))
    (and (equal (fn-lg-scan content (sle-genesis) (sle-unit) (sle-max))
                (cons (fn-lgk-committed ks) (fn-lgk-frontier ks)))
         (equal (fn-lg-scan-last content (sle-genesis) (sle-unit) (sle-max)) (fn-lgk-last ks))
         (true-listp content)
         (equal (mod (len content) (sle-unit)) 0)
         (equal (fn-bs-take (len c) content) c))))

; The antecedent, every hypothesis but the crash image.
(defun sle-hyps (bs ks next)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-lgk-relp bs ks 0 (sle-genesis) (sle-max))
       (not (consp (fn-lgk-inflight ks)))
       (equal (mod next (fn-bs-unit bs)) 0)
       (<= (+ (fn-lgk-frontier ks) *fn-frame-magic-octets*) (len (fn-bs-durable-content bs 0)))))

; -----------------------------------------------------------------------------
; fn-lg-extend-program-keeps-the-relation: a reachable positive witness.
(assert-event (fn-lgk-relp (sle-bs0) (sle-ks) 0 (sle-genesis) (sle-max)))
(assert-event (equal (fn-lgk-committed (sle-ks)) (list (sle-r 1))))
(assert-event (< (fn-lgk-frontier (sle-ks)) (len (sle-c))))
(assert-event
 (let* ((run (fn-lg-extend-run (sle-bs0) (sle-ks) (fn-lg-extend-program (sle-next)) nil 0))
        (final (car (last run))))
   (and (equal (len run) 4)
        (equal (cdr final) (sle-ks))
        (fn-lgk-relp (car final) (sle-ks) 0 (sle-genesis) (sle-max))
        (equal (len (sle-content (car final))) (sle-next))
        (null (fn-bs-pending (car final))))))
; Tooth (< len next): a target below the segment's end writes nothing and
; the length conclusion fails.
(with-guard-checking-event
 :none
 (assert-event
 (let* ((run (fn-lg-extend-run (sle-bs0) (sle-ks) (fn-lg-extend-program 8) nil 0))
        (final (car (last run))))
   (and (fn-lgk-relp (sle-bs0) (sle-ks) 0 (sle-genesis) (sle-max))
        (not (< (len (sle-c)) 8))
        (not (equal (len (sle-content (car final))) 8))))))

; -----------------------------------------------------------------------------
; fn-lg-extension-written-crash-reads-the-committed-records: positive
; witnesses (every unit landed; landed, zeroed and garbled mixed).
(defun sle-written () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-extension-written-state (sle-bs0) 0 (sle-next)))
(defun sle-garble () (declare (xargs :guard t)) '(:garble 70 76 71 49))
(assert-event (sle-hyps (sle-bs0) (sle-ks) (sle-next)))
(assert-event (equal (len (fn-bs-pending (sle-written))) 1))
(assert-event
 (let ((ch (list (sle-sels 3 :new))))
   (and (fn-bs-crash-choicesp ch (fn-bs-pending (sle-written)) (sle-unit))
        (sle-crash-okp (sle-bs0) (sle-ks) (fn-bs-crash (sle-written) ch))
        (equal (len (sle-content (fn-bs-crash (sle-written) ch))) (sle-next)))))
(assert-event
 (let ((ch (list (list :old (sle-garble) :new))))
   (and (fn-bs-crash-choicesp ch (fn-bs-pending (sle-written)) (sle-unit))
        (sle-crash-okp (sle-bs0) (sle-ks) (fn-bs-crash (sle-written) ch))
        (not (equal (sle-content (fn-bs-crash (sle-written) ch))
                    (append (sle-c) (fn-bs-zeros 12)))))))

; Tooth (relation): the same store read by a kernel that claims nothing
; committed (the kernel of an empty segment): every other hypothesis holds
; and the image reads a record the kernel does not hold.
(defun sle-ks-empty () (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover (fn-bs-zeros 16) (sle-genesis) (sle-unit) (sle-max) 1))
(assert-event
 (let* ((w (fn-lg-extension-written-state (sle-bs0) 0 (sle-next)))
        (ch (list (sle-sels 3 :new))))
   (and (not (fn-lgk-relp (sle-bs0) (sle-ks-empty) 0 (sle-genesis) (sle-max)))
        (not (consp (fn-lgk-inflight (sle-ks-empty))))
        (<= (+ (fn-lgk-frontier (sle-ks-empty)) *fn-frame-magic-octets*) (len (sle-c)))
        (fn-bs-crash-choicesp ch (fn-bs-pending w) (sle-unit))
        (not (sle-crash-okp (sle-bs0) (sle-ks-empty) (fn-bs-crash w ch))))))

; Tooth (at rest): a batch in flight.  R holds with its write pending; an
; image that lands it reads past the committed records.
(defun sle-ks-flight () (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-append (fn-lgk-prepare (sle-ks) (sle-r 2)) (sle-unit) (len (sle-c))))
(defun sle-bs-flight () (declare (xargs :guard t :verify-guards nil))
  (sle-bs (sle-c) (list (list :write 0 (fn-lgk-frontier (sle-ks))
                              (fn-lg-log (list (sle-r 2)) (fn-lgk-last (sle-ks)) (sle-unit))))))
(assert-event
 (let* ((w (fn-lg-extension-written-state (sle-bs-flight) 0 (sle-next)))
        (ch (list (sle-sels (floor (len (fn-lg-log (list (sle-r 2)) (fn-lgk-last (sle-ks)) (sle-unit)))
                                   (sle-unit))
                            :new)
                  (sle-sels 3 :new))))
   (and (fn-lgk-relp (sle-bs-flight) (sle-ks-flight) 0 (sle-genesis) (sle-max))
        (consp (fn-lgk-inflight (sle-ks-flight)))
        (fn-bs-crash-choicesp ch (fn-bs-pending w) (sle-unit))
        (not (sle-crash-okp (sle-bs-flight) (sle-ks-flight) (fn-bs-crash w ch))))))

; Tooth (whole units): a target that is not a whole number of units leaves
; an image that is not.
(assert-event
 (let* ((next (+ (len (sle-c)) 6))
        (w (fn-lg-extension-written-state (sle-bs0) 0 next))
        (ch (list (sle-sels 2 :new))))
   (and (fn-lgk-relp (sle-bs0) (sle-ks) 0 (sle-genesis) (sle-max))
        (not (equal (mod next (sle-unit)) 0))
        (fn-bs-crash-choicesp ch (fn-bs-pending w) (sle-unit))
        (not (sle-crash-okp (sle-bs0) (sle-ks) (fn-bs-crash w ch))))))

; Tooth (zeros past the frontier): a FULL segment (the frontier at its end)
; whose extension's first units are garbled into the next chained entry:
; the image reads a record never committed.  The host's spare unit
; (fn-olr-extension-needed-p) is what excludes this.
(defun sle-bs-full () (declare (xargs :guard t :verify-guards nil)) (sle-bs (sle-log1) nil))
(defun sle-ks-full () (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover (sle-log1) (sle-genesis) (sle-unit) (sle-max) 2))
(defun sle-forged () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (sle-r 2)) (fn-lgk-last (sle-ks-full)) (sle-unit)))
(defun sle-forge-sels (w n) (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (zp n) nil (cons (cons :garble (fn-bs-take (sle-unit) w)) (sle-forge-sels (nthcdr (sle-unit) w) (1- n)))))
(assert-event
 (let* ((next (+ (len (sle-log1)) (len (sle-forged))))
        (w (fn-lg-extension-written-state (sle-bs-full) 0 next))
        (ch (list (sle-forge-sels (sle-forged) (floor (len (sle-forged)) (sle-unit))))))
   (and (fn-lgk-relp (sle-bs-full) (sle-ks-full) 0 (sle-genesis) (sle-max))
        (equal (mod next (sle-unit)) 0)
        (not (<= (+ (fn-lgk-frontier (sle-ks-full)) *fn-frame-magic-octets*) (len (sle-log1))))
        (fn-bs-crash-choicesp ch (fn-bs-pending w) (sle-unit))
        (not (sle-crash-okp (sle-bs-full) (sle-ks-full) (fn-bs-crash w ch))))))

; -----------------------------------------------------------------------------
; fn-olr-extension-target-is-an-extent: the host's rule at the default unit.
(assert-event (fn-olr-extension-needed-p 1044480 8192 1048576 4096))
(assert-event (not (fn-olr-extension-needed-p 1024 8192 1048576 4096)))
(assert-event (equal (fn-olr-extension-target 1044480 8192 1048576 4096) 2097152))
(assert-event (equal (fn-olr-extension-target 0 (* 3 1048576) 1048576 4096) 3149824))
; Tooth (whole-unit extent): an extent of 3 at unit 4 doubles to 6, not a
; whole number of units.
(assert-event (and (posp 4) (not (equal (mod 3 4) 0))
                   (not (equal (mod (fn-olr-extension-target 0 0 3 4) 4) 0))))
; Tooth (a positive unit): at unit 0 the target is not a multiple of it.
(with-guard-checking-event
 :none
 (assert-event (and (equal (mod 4096 0) 4096)
                    (not (equal (mod (fn-olr-extension-target 0 0 4096 0) 0) 0)))))
