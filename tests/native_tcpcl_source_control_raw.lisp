;;; Actual retained driver + ACL2 control function; recording socket/encoder.
(load "tests/native_bp_received_source_raw.lisp")
(in-package "ACL2")
(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)
(defconstant *fn-clock-max* 18446744073709551615)
(dolist (path '("books/tcpcl-records.lisp" "books/tcpcl-session.lisp" "books/clock.lisp" "books/tcpcl-source-control.lisp"))
 (with-open-file (stream path)
  (loop for form = (read stream nil :eof) until (eq form :eof) do
   (when (and (consp form) (eq (first form) 'defun)
    (member (second form) '(fn-tcl-session-role fn-tcl-session-phase fn-tcl-session-local fn-tcl-session-tls
     fn-tcl-session-peer fn-tcl-session-negotiated fn-tcl-session-inbound fn-tcl-session-outbound
     fn-tcl-session-next-xfer-id fn-tcl-session-last-rx fn-tcl-session-last-tx fn-tcl-session-term
     fn-tcl-make-session fn-tcl-negotiated-keepalive fn-tcl-make-negotiated fn-tcl-make-keepalive
     fn-tcl-next fn-tcl-transferringp fn-clock-timep fn-tclsctl-turn)))
    (eval (cons 'defun (cons (second form) (cons (third form)
     (remove-if (lambda (x) (and (consp x) (eq (car x) 'declare))) (cdddr form))))))))))
(defvar *source-control-recording-core* (symbol-function 'fnn-core))
(defun fnn-core (name &rest args)
 (case name
  ((fn-tclsctl-turn fn-tcrt-action fn-tcrt-write-end fn-tcrt-read-limit fn-tcrt-write-deadline fn-tcrt-contact-deadline fn-tcrt-contact-timeout-p fn-tcrt-init-deadline fn-tcrt-init-timeout-p) (apply name args))
  (fn-tcl-host-phase (fn-tcl-session-phase (first args)))
  (fn-tcl-host-encode (assert (equal (first args) (fn-tcl-make-keepalive))) '(4))
  (otherwise (apply *source-control-recording-core* name args))))
(let* ((bank (test-bank))
       (conn (make-fnn-tcl-conn :fd 9 :retained t
        :session (fn-tcl-make-session :passive :established nil nil nil
                  (fn-tcl-make-negotiated 1 1000 1000 nil '(100)) nil nil 1 9 0 nil)))
       (grant (test-grant bank 2 :incoming :socket conn))
       (root (list (make-list 1000 :initial-element 65)))
       (ack '(:xfer-ack 3 7 1000)) (*now* 1000) (*writes* nil) (*flushes* 0) (*calls* nil)
       (*fnn-tcl-source-turn* (lambda (c token) (fnn-bp-session-source-turn grant c token))))
 (setf (fnn-tclc-source-pending conn) t (fnn-tclc-source-root conn) root
       (fnn-tclc-source-id conn) 7 (fnn-tclc-held conn) (list ack)
       (fnn-tclc-source-token conn) (second (fnn-bp-session-source-start grant conn 7 root 1000 1000)))
 (assert (eq (fnn-tcl-turn conn) :work)) ; control encode
 (assert (fnn-tclc-tx-data conn))
 (let ((*wait-write* t) (*now* 2000))
  (assert (eq (fnn-tcl-turn conn) :wait))
  (assert (null (fnn-tclc-tx-messages conn)))) ; no duplicate control behind held write
 (assert (eq (fnn-tcl-turn conn) :work)) ; actual one-octet physical return
 (assert (equal *writes* '(4)))
 (assert (eq (fnn-tcl-turn conn) :work)) ; actual private source cursor resumes
 (assert (plusp (fnn-bpsrx-offset (fnn-tclc-source-token conn))))
 (assert (eq (fnn-tclc-source-root conn) root)) (assert (equal (fnn-tclc-held conn) (list ack)))
 (assert (= (fn-tcl-session-last-rx (fnn-tclc-session conn)) 9))
 (assert (zerop *flushes*)) (assert (= (hash-table-count (fnn-bpsb-held bank)) 1)))
(format t "PASS actual retained source control: independent KEEPALIVE writes, held END ACK/root untouched, no queued duplicate while physical write waits, bounded source resumes.~%")

;;; Exact shipped apply/flush: the passive admission gate runs before any
;;; event/source installation. Admission answer is recorded here; its actual
;;; ACL2 producer has separate accepted/channel/EID/malformed literal teeth.
(with-open-file (stream "host/native/tcpcl.lisp")
 (loop for form = (read stream nil :eof) until (eq form :eof) do
  (when (and (consp form) (eq (first form) 'defun)
             (member (second form) '(fnn-tcl-apply fnn-tcl-flush))) (eval form))))
(defun fnn-tcl-log-events (&rest args) (declare (ignore args)))
(defvar *admission-recording-core* (symbol-function 'fnn-core))
(defun fnn-core (name &rest args)
 (case name
  (fn-tcl-host-event-digests nil)
  (otherwise (apply *admission-recording-core* name args))))
(dolist (admitted '(nil t))
 (let* ((calls 0)
        (session (fn-tcl-make-session :passive :established nil nil nil
                  (fn-tcl-make-negotiated 1 1000 1000 nil '(100)) nil nil 1 9 0 nil))
        (conn (make-fnn-tcl-conn :retained t :session :contact :held '(:old-ack)
               :session-admit (lambda (c) (declare (ignore c)) (incf calls)
                 (if admitted '(:admitted :peer 7) '(:refused :eid-mismatch)))))
        (*fnn-tcl-source-start* (lambda (&rest args) (declare (ignore args))
                               (error "refused channel reached source issuer"))))
  (fnn-tcl-apply conn
   (list session
     (if admitted '((:send (:keepalive)))
       '((:send (:sess-init)) (:bundle-segments-received 1 (:root) 100))) nil))
  (assert (= calls 1))
  (if admitted
   (progn (assert (not (fnn-tclc-broken conn)))
          (assert (equal (fnn-tclc-tx-messages conn) '(:old-ack (:keepalive)))))
   (progn (assert (fnn-tclc-broken conn))
          (assert (eq (fnn-tclc-outcome conn) :refused))
          (assert (null (fnn-tclc-source-pending conn)))
          (assert (null (fnn-tclc-held conn)))
          (assert (null (fnn-tclc-tx-messages conn)))))))
(format t "PASS actual passive session admission precedes frame events/source issuer; refusal is connection-local, no ACK/publication released.~%")
