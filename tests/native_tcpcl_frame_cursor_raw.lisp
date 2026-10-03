;;; Actual native retained input consumer and ACL2 cursor; codec/publication
;;; observations are recorded, never acceptance or protocol oracle claims.
(load "tests/native_tcpcl_retained_turn_raw.lisp")
(in-package "ACL2")
(defvar *decoded* nil)
(defun fnn-core (name &rest args)
 (case name
  ((fn-tcim-turn fn-tcf-at fn-tcf-begin fn-tcf-contactp fn-tcf-byte fn-tcf-span) (apply name args))
  (fn-tcl-max-message 200000)
  (fn-tcl-host-segment-mru 100000)
  (fn-tcl-host-phase (first args))
  (fn-tcl-host-input-probe
   ;; Only segment extension probe is reachable in these cases. Record the
   ;; exact prefix and refuse its deliberately malformed extension item.
   (not (equal (second args) '(1 3 0 0 0 0 0 0 0 7 0 0 0 1 255))))
  (fn-tcl-host-drive
   (push (second args) *decoded*)
   (list (if (equal (second args) '(1 3 0 0 0 0 0 0 0 7 0 0 0 1 255))
             :closed (first args)) nil nil))
  (otherwise (error "Unexpected frame core call ~s" name))))
(defun frame-drain (conn)
 (loop while (fnn-tclc-source-more conn) repeat 100000 do
  (let* ((v (fnn-tclc-input-vector conn)) (off (fnn-tclc-input-offset conn)))
   (fnn-tcl-input-turn conn nil 100)
   (when (eq v (fnn-tclc-input-vector conn))
    (assert (<= (- (fnn-tclc-input-offset conn) off) 4096))))))
;;; 65536 data octets in one-octet physical reads. No increasing carry, no
;;; speculative codec call. Only the exact completed frame is decoded once.
(let* ((conn (make-fnn-tcl-conn :session :established))
       (header '(1 0 0 0 0 0 0 0 0 7 0 0 0 0 0 1 0 0))
       (wire (append header (loop for i below 65536 collect (mod i 256))))
       (*decoded* nil))
 (loop for byte in wire for i from 0 do
  (fnn-tcl-input-turn conn (vector byte) 100)
  (frame-drain conn)
  (assert (null (fnn-tclc-carry conn)))
  (unless (= i (1- (length wire))) (assert (null *decoded*))))
 (assert (equal *decoded* (list wire)))
 (assert (zerop (svref (fnn-tclc-input-buffer conn) 1))))
;;; Coalesced frames retain the original incoming vector until every exact
;;; frame has been dispatched. The incomplete suffix survives the next read.
(let ((conn (make-fnn-tcl-conn :session :established)) (*decoded* nil))
 (fnn-tcl-input-turn conn #(4 4 2 0 0 0) 100)
 (frame-drain conn)
 (assert (equal (reverse *decoded*) '((4) (4))))
 (assert (= (svref (fnn-tclc-input-buffer conn) 1) 4))
 (fnn-tcl-input-turn conn (make-array 14 :initial-element 0) 100)
 (frame-drain conn)
 (assert (= (length *decoded*) 3))
 (assert (= (length (first *decoded*)) 18)))
;;; Bad extension prefix reaches the existing codec before waiting for a
;;; data length/body the peer never supplies.
(let ((conn (make-fnn-tcl-conn :session :established)) (*decoded* nil))
 (fnn-tcl-input-turn conn #(1 3 0 0 0 0 0 0 0 7 0 0 0 1 255) 100)
 (frame-drain conn)
 (assert (eq (fnn-tclc-session conn) :closed))
 (assert (= (length *decoded*) 1)))
;;; A declared payload above negotiated MRU reaches the codec at its header,
;;; without reserving/copying the peer's claimed size.
(let ((conn (make-fnn-tcl-conn :session :established)) (*decoded* nil))
 (fnn-tcl-input-turn conn #(1 0 0 0 0 0 0 0 0 7 0 0 0 0 0 2 0 0) 100)
 (frame-drain conn)
 (assert (= (length *decoded*) 1))
 (assert (= (length (first *decoded*)) 18)))
(format t "PASS actual retained framing: 65536 one-byte reads/one decode, coalesced frames/partial suffix, extension and MRU prefix refusal.~%")
