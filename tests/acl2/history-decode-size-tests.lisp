(in-package "ACL2")
(include-book "../../books/history-decode-size")

(defun hdszt-run (bytes s sizes prefix usable)
  (if (consp bytes)
      (mv-let (s sizes prefix usable) (fn-hds-feed (car bytes) s sizes prefix usable)
        (hdszt-run (cdr bytes) s sizes prefix usable))
    (list s sizes prefix usable)))

(defun hdszt-decode (bytes)
  (mv-let (s sizes prefix usable) (fn-hds-begin 0 (len bytes) 17 23)
    (hdszt-run bytes s sizes prefix usable)))

(defun hdszt-exact (bytes value)
  (let* ((r (hdszt-decode bytes)) (s (car r)) (sizes (cadr r)))
    (and (eq (car s) :done) (nth 3 r) (consp sizes) (null (cdr sizes))
         (equal (car sizes) (fn-scs-summary value))
         (equal (nth 8 s) (len bytes))
         (equal (nth 10 s) 17) (equal (nth 11 s) 23))))

(assert-event
 (and (eq (symbol-class 'fn-hds-begin (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hds-feed (w state)) :common-lisp-compliant)))

; Nonempty tree, shared subtrees, all scalar shapes and canonical octet collapse.
(defconst *hdszt-tree*
  '(0 "<a@x>" 255 ("fn.test") :hstxa (1 2 3) "" #\A -256 nil))
(assert-event (hdszt-exact (fn-scc-encode *hdszt-tree*) *hdszt-tree*))

; Accepted nonminimal integer spelling must use the decoded value's width.
(assert-event (hdszt-exact '(1 2 7 0) 7))
; Both accepted NIL aliases collapse to the NIL opcode; keyword :NIL does not.
(assert-event (hdszt-exact '(4 1 1 3 78 73 76) nil))
(assert-event (hdszt-exact '(4 2 1 3 78 73 76) nil))
(assert-event (hdszt-exact '(4 0 1 3 78 73 76) :nil))
; Same length / one differing byte must not accidentally take the NIL size.
(assert-event (hdszt-exact '(4 1 1 3 78 73 77) 'nim))
; The decoder accepts zero OP6, whose canonical representation is NIL.
(assert-event (hdszt-exact '(6 0) nil))
; Uncompressed pair input is recomputed to the canonical octet-list size.
(assert-event (hdszt-exact '(1 1 1 1 1 2 0 5 5) '(1 2)))
(assert-event (hdszt-exact '(3 0) ""))

; Actual malformed stream refuses, never exposes a usable reserve.
(assert-event
 (let ((r (hdszt-decode '(5))))
   (and (eq (car (car r)) :refused) (not (nth 3 r)))))
; A corrupted size stack loses usability even though parser bytes are valid.
(assert-event
 (let* ((bytes '(1 1 1 0 5))
        (s (car (hdszt-run '(1 1 1 0) (fn-hdc-begin 0 5 17 23) nil nil t)))
        (r (mv-list 4 (fn-hds-feed 5 s nil nil t))))
   (and (equal (nth 0 r) (fn-hdc-feed 5 s))
        (eq (car (nth 0 r)) :done) (not (nth 3 r))
        (equal (len bytes) 5))))
; Once unusable, later input cannot silently bless the stale carry.
(assert-event
 (let* ((s (fn-hdc-begin 0 1 17 23))
        (r (mv-list 4 (fn-hds-feed 0 s '((999 nil nil)) nil nil))))
   (and (not nil) (not (nth 3 r))
        (equal (nth 0 r) (fn-hdc-feed 0 s)))))
