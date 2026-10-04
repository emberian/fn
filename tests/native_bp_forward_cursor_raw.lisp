;;; The retained loop's :forward turn, before and after PRF-1311, counted.
;;; Real repository forms: fn-bpnp-forward-plan(-rows, -loop) and
;;; fn-bpsched-forward-entry (the turn the host made until this slice), and
;;; fn-bpfc-scan/turn/run (the turn it makes now), read from books/ and
;;; evaluated in a plain SBCL with their :exec bodies.  The route decision
;;; fn-bprt-outbound-choice and the destination reader fn-bpnp-held-dest are
;;; replaced by a counting double over synthetic held rows (slot 11 next
;;; hop, 12 status, 14 deleted, 15 the double's destination); the count of
;;; route decisions per turn is the quantity measured, and both turns read
;;; the same double.  No host code, no native endpoint.
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(declaim (declaration xargs))
(defmacro defconst (name value) `(defparameter ,name ,value))
(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun posp (x) (and (integerp x) (< 0 x)))
(defun zp (x) (or (not (integerp x)) (<= x 0)))
(defun nfix (x) (if (natp x) x 0))
(defun fix-true-list (x) (if (consp x) (cons (car x) (fix-true-list (cdr x))) nil))
(defun true-listp (x) (if (consp x) (true-listp (cdr x)) (null x)))
(defun len (x) (if (consp x) (+ 1 (len (cdr x))) 0))
(defun member-equal (x l) (member x l :test #'equal))
(defun fn-bpp-dtn-sspp (x) (declare (ignore x)) nil)
(defun selected-forms (path names)
 (with-open-file (in path)
  (loop for form = (read in nil :eof) until (eq form :eof)
   when (and (consp form) (member (car form) '(defun defconst))
             (member (second form) names)) collect form)))
(defun load-forms (path names)
 (let ((forms (selected-forms path names)))
  (assert (= (length forms) (length names)) () "~a: wanted ~a, read ~a" path names
          (mapcar #'second forms))
  (dolist (form forms) (eval form))))
(load-forms "books/cbor.lisp" '(fn-cbor-ag-car))
(load-forms "books/acceptance-alloc.lisp" '(fn-ag-car))
(load-forms "books/rev-onto.lisp" '(fn-ag-rev-onto))
(load-forms "books/bp-node-machine.lisp" '(fn-bpn-nth))
(load-forms "books/bp-route.lisp" '(fn-bprt-nth))
(load-forms "books/bp-primary-cbor.lisp" '(*fn-bpc-max-uint*))
(load-forms "books/bp-primary.lisp" '(fn-bpp-eidp))
(load-forms "books/bp-node-forward-plan.lisp"
 '(fn-bpnp-forward-plan-rows-loop fn-bpnp-forward-plan-rows fn-bpnp-forward-plan))
(load-forms "books/bp-session-scheduler.lisp" '(fn-bpsched-forward-entry))
(load-forms "books/bp-forward-cursor.lisp"
 '(fn-bpfc-scan fn-bpfc-cursor fn-bpfc-pos fn-bpfc-seen fn-bpfc-initial
   fn-bpfc-ordered fn-bpfc-turn fn-bpfc-run))
;;; The double: a destination is routed to the hop named by its row.
(defvar *decisions* 0)
(defun fn-bpnp-held-dest (h) (fn-bpn-nth 15 h))
(defun fn-bprt-outbound-choice (dest table)
 (incf *decisions*)
 (let ((route (assoc dest table :test #'equal)))
  (if route (list :hop (second route) (third route) (fourth route)) (list :no-route))))
(defconstant +quantum+ 64)             ; host/native/bp-node.lisp +fnn-bpnode-forward-quantum+
(defun peer (n) (list :ipn n 0))
(defun row (hop dest)
 (append (make-list 11) (list (peer hop) '(:forward-pending) nil nil dest)))
(defparameter *table* '(("dest-a" "a" "ipn:1.0" 4556) ("dest-b" "b" "ipn:2.0" 4557)))
;;; HELD is newest first; DESTS is given oldest first.
(defun held (pairs) (reverse (loop for (hop dest) in pairs collect (row hop dest))))
(defun old-turn (held busy)
 (let ((*decisions* 0))
  (let ((entry (fn-bpsched-forward-entry (fn-bpnp-forward-plan held *table*) busy)))
   (values entry *decisions*))))
(defun new-turn (cursor held busy)
 (let ((*decisions* 0))
  (let ((answer (fn-bpfc-turn (or cursor (fn-bpfc-initial)) held *table* busy +quantum+)))
   (values answer *decisions*))))
(defun new-sweep (held busy)
 "Turns until a non-yield; answers the final answer, the turn count and the largest per-turn count."
 (loop with cursor = nil with turns = 0 with most = 0
       do (multiple-value-bind (answer n) (new-turn cursor held busy)
           (incf turns) (setq most (max most n))
           (if (eq (first answer) :yield) (setq cursor (second answer))
             (return (values answer turns most))))))
;;; 1. 2,000 forward-pending rows, the oldest routed to free peer 1.
(let ((held (held (cons '(1 "dest-a") (loop repeat 1999 collect '(2 "dest-b"))))))
 (multiple-value-bind (old-entry old-n) (old-turn held nil)
  (multiple-value-bind (answer new-n) (new-turn nil held nil)
   (assert (= old-n 2000))
   (assert (eq (first answer) :entry))
   (assert (equal (second answer) old-entry))
   (assert (equal old-entry (list (peer 1) "a" "ipn:1.0" 4556)))
   (assert (= new-n 1))
   (format t "turn with a startable head: old ~d route decisions, new ~d, same entry~%" old-n new-n))))
;;; 2. 1,999 rows to busy peer 1, the youngest to free peer 2: the plan's
;;; choice is peer 2; the cursor reaches it over ceiling(2000/64) turns.
(let ((held (held (append (loop repeat 1999 collect '(1 "dest-a")) (list '(2 "dest-b")))))
      (busy (list (peer 1))))
 (multiple-value-bind (old-entry old-n) (old-turn held busy)
  (multiple-value-bind (answer new-n) (new-turn nil held busy)
   (assert (= old-n 2000))
   (assert (eq (first answer) :yield))
   (assert (= new-n +quantum+))
   (multiple-value-bind (final turns most) (new-sweep held busy)
    (assert (eq (first final) :entry))
    (assert (equal (second final) old-entry))
    (assert (equal old-entry (list (peer 2) "b" "ipn:2.0" 4557)))
    (assert (= turns (ceiling 2000 +quantum+)))
    (assert (<= most +quantum+))
    ;; the logical run with fuel (len held) is the same answer (K2)
    (assert (equal (fn-bpfc-run (fn-bpfc-initial) held *table* busy +quantum+ (length held)) final))
    (format t "busy head: old turn ~d decisions; new turn ~d, sweep ~d turns of <= ~d, same entry~%"
            old-n new-n turns most)))))
;;; 3. Both peers busy: the plan chooses nothing; the sweep drains.
(let ((held (held (loop for i below 2000 collect (if (evenp i) '(1 "dest-a") '(2 "dest-b")))))
      (busy (list (peer 1) (peer 2))))
 (multiple-value-bind (old-entry old-n) (old-turn held busy)
  (multiple-value-bind (final turns most) (new-sweep held busy)
   (assert (null old-entry)) (assert (= old-n 2000))
   (assert (equal final '(:drained)))
   (assert (<= most +quantum+))
   (format t "all busy: old turn ~d decisions, nil; new sweep ~d turns of <= ~d, drained~%"
           old-n turns most))))
(format t "PASS forward cursor: a :forward turn makes at most 64 route decisions where the plan made 2000, and chooses the plan's entry~%")
