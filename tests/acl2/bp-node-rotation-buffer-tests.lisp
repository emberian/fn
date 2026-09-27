; Teeth for books/bp-node-rotation-buffer.lisp (lane bp-checkpoint-open):
; the kind-19 checkpoint read from the octet buffer by index, executed on a
; live `fn-octets-bp' against the list decoder `fn-bpnr-checkpoint-decode'.
(in-package "ACL2")
(include-book "../../books/bp-node-rotation-buffer")

; The host-called entry and the index decoder run compiled.
(assert-event (eq (symbol-class 'fn-bpnrb-selection-plan (w state))
                  :common-lisp-compliant))
(assert-event (eq (symbol-class 'fn-bpnrb-checkpoint-decode (w state))
                  :common-lisp-compliant))
(assert-event (eq (symbol-class 'fn-bpnrb-dec (w state)) :common-lisp-compliant))

; A checkpoint whose held rows exercise every tag of the tree codec: nil,
; t, a keyword, an ACL2 and a COMMON-LISP symbol, a natural, a negative
; integer, a string, a character, an octet list and nested pairs.
(defconst *bpnrbt-held*
  (list (list :row 1 "held" #\c -7 '(1 2 3 255 0) 'fn-bpnr-dec 'car nil t)
        (list :row 2 (cons 4000 '(9 9 9)) "" (cons :k (cons 5 nil)))))
(defconst *bpnrbt-ck*
  (fn-bpnr-checkpoint 3 *bpnrbt-held* '((:handoff 1)) '(2 . 7) 11 1311))
(defconst *bpnrbt-budget* (fn-bpnr-depth-budget 4))
; The file ends in fn-frame-trailer, a constrained digest whose executable
; attachment ACL2 ignores while it evaluates a defconst: every value built
; from a file is a zero-argument function (the pattern of
; bp-node-counterexamples-tests).
(defun bpnrbt-file ()
  (declare (xargs :verify-guards nil))
  (fn-bpnr-checkpoint-octets *bpnrbt-ck* *bpnrbt-budget*))
(assert-event (and (fn-bpnr-checkpointp *bpnrbt-ck*) (consp (bpnrbt-file))))

; Damaged files: one payload octet changed, the last trailer octet dropped,
; one octet appended, the header alone, nothing.
(defun bpnrbt-damaged ()
  (declare (xargs :verify-guards nil))
  (let ((file (bpnrbt-file)))
    (list (update-nth 20 (mod (+ 1 (nth 20 file)) 256) file)
          (take (1- (len file)) file)
          (append file '(0))
          (take 14 file)
          nil)))

; Each file into the live buffer, the host's plan, and the list model's.
(defun bpnrbt-plans (files present fn-octets-bp)
  (declare (xargs :stobjs fn-octets-bp :verify-guards nil))
  (if (atom files)
      (mv nil fn-octets-bp)
    (let ((fn-octets-bp (fn-octets-bp-from-list (car files) fn-octets-bp)))
      (let ((pair (list (fn-bpnrb-selection-plan present *bpnrbt-budget* fn-octets-bp)
                        (fn-bpnr-selection-plan present (car files) *bpnrbt-budget*))))
        (mv-let (rest fn-octets-bp)
          (bpnrbt-plans (cdr files) present fn-octets-bp)
          (mv (cons pair rest) fn-octets-bp))))))

(defun bpnrbt-exec (files present)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets-bp
    (mv-let (result fn-octets-bp)
      (bpnrbt-plans files present fn-octets-bp)
      result)))

; KEYSTONE witness (fn-bpnrb-checkpoint-decode-is-decode, through the entry
; fn-bpnrb-selection-plan-is-selection-plan): the well-formed file decodes
; on the buffer to exactly the checkpoint written, as the list decoder
; decodes it; each damaged file is refused by both.
(assert-event
 (equal (bpnrbt-exec (cons (bpnrbt-file) (bpnrbt-damaged)) t)
        (list (list (list :selected *bpnrbt-ck*) (list :selected *bpnrbt-ck*))
              (list '(:damaged) '(:damaged))
              (list '(:damaged) '(:damaged))
              (list '(:damaged) '(:damaged))
              (list '(:damaged) '(:damaged))
              (list '(:damaged) '(:damaged)))))

; No selection file: (:none) whatever the buffer holds.
(assert-event
 (equal (bpnrbt-exec (list (bpnrbt-file)) nil)
        (list (list '(:none) '(:none)))))

; The budget binds on the buffer as on the list: a depth budget below the
; value's depth refuses the file both ways.
(defun bpnrbt-shallow (fn-octets-bp)
  (declare (xargs :stobjs fn-octets-bp :verify-guards nil))
  (let ((fn-octets-bp (fn-octets-bp-from-list (bpnrbt-file) fn-octets-bp)))
    (mv (list (fn-bpnrb-checkpoint-decode 3 fn-octets-bp)
              (fn-bpnr-checkpoint-decode (bpnrbt-file) 3)
              (fn-bpnrb-checkpoint-decode *bpnrbt-budget* fn-octets-bp))
        fn-octets-bp)))
(defun bpnrbt-shallow-exec ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets-bp
    (mv-let (result fn-octets-bp) (bpnrbt-shallow fn-octets-bp) result)))
(assert-event (equal (bpnrbt-shallow-exec) (list nil nil *bpnrbt-ck*)))

; The bounded-step machine (fn-bpnrb-mrun-all-of-dec-goal,
; fn-bpnrb-mrun-all-of-mrun): quanta of at most 5 steps and 16 octets,
; resumed from their exact continuations, reach the whole run's answer,
; which is the recursive decoder's value over the payload.
(defun bpnrbt-quanta (n i e goals vals fn-octets-bp)
  (declare (xargs :stobjs fn-octets-bp :verify-guards nil :measure (nfix n)))
  (if (or (zp n) (atom goals))
      (mv i goals vals)
    (mv-let (ok i2 goals2 vals2) (fn-bpnrb-mrun 5 16 i e goals vals fn-octets-bp)
      (if (not ok)
          (mv :refused nil nil)
        (bpnrbt-quanta (1- n) i2 e goals2 vals2 fn-octets-bp)))))

(defun bpnrbt-machine (fn-octets-bp)
  (declare (xargs :stobjs fn-octets-bp :verify-guards nil))
  (let* ((fn-octets-bp (fn-octets-bp-from-list (bpnrbt-file) fn-octets-bp))
         (e (fn-bpnrb-frame-end (fn-octets-bp-len fn-octets-bp) *bpnrbt-budget*
                                fn-octets-bp)))
    (mv-let (i goals vals)
      (bpnrbt-quanta 100000 14 e (list *bpnrbt-budget*) nil fn-octets-bp)
      (mv-let (ok i-all vals-all)
        (fn-bpnrb-mrun-all 14 e (list *bpnrbt-budget*) nil fn-octets-bp)
        (mv (list (equal i e) goals (equal vals (list *bpnrbt-ck*))
                  ok (equal i-all e) (equal vals-all vals))
            fn-octets-bp)))))

(defun bpnrbt-machine-exec ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets-bp
    (mv-let (result fn-octets-bp) (bpnrbt-machine fn-octets-bp) result)))

(assert-event (equal (bpnrbt-machine-exec) (list t nil t t t t)))
