;;; Actual retained driver + ACL2 control function; recording socket/encoder.
(load "tests/native_bp_received_source_raw.lisp")
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-bp-observation (wall wall-error)
  (declare (ignorable wall wall-error))
  (harness-stub-reached 'fnn-bp-observation "host/native/bp.lisp"))
(defun fnn-bpnode-budgeted (event)
  (declare (ignorable event))
  (harness-stub-reached 'fnn-bpnode-budgeted "host/native/bp-node.lisp"))
(defun fnn-bpnode-forward-result (bp sent session-id result wall wall-error)
  (declare (ignorable bp sent session-id result wall wall-error))
  (harness-stub-reached 'fnn-bpnode-forward-result "host/native/bp-node.lisp"))
(defun fnn-bpnode-pause-at-durable-cut (selector marker)
  (declare (ignorable selector marker))
  (harness-stub-reached 'fnn-bpnode-pause-at-durable-cut "host/native/bp-node.lisp"))
(defun fnn-bps-drive-effects (service effects)
  (declare (ignorable service effects))
  (harness-stub-reached 'fnn-bps-drive-effects "host/native/bp-service.lisp"))
(defun fnn-bps-foundation-step (service event)
  (declare (ignorable service event))
  (harness-stub-reached 'fnn-bps-foundation-step "host/native/bp-service.lisp"))
(defun fnn-graceful-close (fd)
  (declare (ignorable fd))
  (harness-stub-reached 'fnn-graceful-close "host/native/io.lisp"))
(defun fnn-refuse (control &rest args)
  (declare (ignorable control args))
  (harness-stub-reached 'fnn-refuse "host/native/io.lisp"))
(defun fnn-tcl-params (node-id peer keepalive segment-mru transfer-mru)
  (declare (ignorable node-id peer keepalive segment-mru transfer-mru))
  (harness-stub-reached 'fnn-tcl-params "host/native/tcpcl.lisp"))
(defun fnn-tcl-stage (conn xfer-id octets)
  (declare (ignorable conn xfer-id octets))
  (harness-stub-reached 'fnn-tcl-stage "host/native/tcpcl.lisp"))
(defun fnn-tcl-summary (conn)
  (declare (ignorable conn))
  (harness-stub-reached 'fnn-tcl-summary "host/native/tcpcl.lisp"))
;;; ---- derived stubs: END ----
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
     fn-tcl-next fn-tcl-transferringp fn-clock-timep fn-tclsctl-turn fn-tclsctl-control-header-p fn-tclsctl-source-action)))
    (eval (cons 'defun (cons (second form) (cons (third form)
     (remove-if (lambda (x) (and (consp x) (eq (car x) 'declare))) (cdddr form))))))))))
(defvar *source-control-recording-core* (symbol-function 'fnn-core))
(defun fnn-core (name &rest args)
 (case name
  ((fn-tclsctl-source-action fn-tclsctl-turn fn-tcrt-action fn-tcrt-write-end fn-tcrt-read-limit fn-tcrt-write-deadline fn-tcrt-contact-deadline fn-tcrt-contact-timeout-p fn-tcrt-init-deadline fn-tcrt-init-timeout-p) (apply name args))
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

(defun true-listp (x) (typep x 'list))
(defun len (x) (length x))
(dolist (path '("books/tcpcl-records.lisp" "books/tcpcl-octets.lisp" "books/tcpcl-delivery.lisp"))
 (with-open-file (stream path)
  (loop for form = (read stream nil :eof) until (eq form :eof) do
   (when (and (consp form) (eq (first form) 'defun)
    (member (second form) '(fn-tcl-xfer-ack-shapep fn-tcl-xfer-ack-flags
      fn-tcl-xfer-ack-xfer-id fn-tcl-flag-end fn-tcl-held-prior-messagep
      fn-tcl-held-final-ackp fn-tcl-delivery-plan fn-tcl-delivery-plan-status
      fn-tcl-delivery-plan-messages fn-tcl-delivery-plan-detail fn-tcl-delivery-plan-progress-p)))
    (eval (cons 'defun (cons (second form) (cons (third form)
     (remove-if (lambda (x) (and (consp x) (eq (car x) 'declare))) (cdddr form))))))))))

;;; Exact bounded read/framing/private source consumers. Wire decoder is
;;; recorded for one KEEPALIVE; its original fn-tcl-step transition is actual.
(dolist (path '("books/tcpcl-records.lisp" "books/tcpcl-session.lisp"))
 (with-open-file (stream path)
  (loop for form = (read stream nil :eof) until (eq form :eof) do
   (when (and (consp form) (eq (first form) 'defun)
     (member (second form) '(fn-tcl-msg-kind fn-tcl-make-result fn-tcl-result-session
       fn-tcl-result-events fn-tcl-result-unconsumed fn-tcl-touch-rx fn-tcl-step fn-tcl-settle)))
    (eval (cons 'defun (cons (second form) (cons (third form)
     (remove-if (lambda (x) (and (consp x) (eq (car x) 'declare))) (cdddr form))))))))))
(defvar *held-input-recording-core* (symbol-function 'fnn-core))
(defvar *received-controls* 0)
(defun fnn-core (name &rest args)
 (case name
  ((fn-tcl-delivery-plan fn-tcl-delivery-plan-status fn-tcl-delivery-plan-messages
    fn-tcl-delivery-plan-detail fn-tcl-delivery-plan-progress-p) (apply name args))
  ((fn-tcf-at fn-tcf-begin fn-tcf-contactp fn-tcf-byte fn-tcf-span) (apply name args))
  (fn-tcl-max-message 200000)
  (fn-tcl-host-segment-mru 1000)
  (fn-tcl-host-input-probe nil)
  (fn-tcl-host-source-drive
   (assert (equal (second args) '(4))) (incf *received-controls*)
   (let ((r (fn-tcl-step (first args) (fn-tcl-make-keepalive) (third args))))
    (list (fn-tcl-result-session r) (fn-tcl-result-events r) (fn-tcl-result-unconsumed r))))
  (otherwise (apply *held-input-recording-core* name args))))
(dolist (lost '(nil t))
(let* ((bank (test-bank))
       (conn (make-fnn-tcl-conn :retained t :fd 9
        :session (fn-tcl-make-session :passive :established nil nil nil
                  (fn-tcl-make-negotiated 0 1000 1000 nil '(100)) nil nil 1 9 0 nil)))
       (grant (test-grant bank 2 :incoming :socket conn))
       (root (list (make-list 1000 :initial-element 65)))
       (ack '(:xfer-ack 3 7 1000))
       (*now* 100) (*incoming* #(4 1)) (*calls* nil) (*received-controls* 0) (*publications* 0)
       (*fnn-tcl-source-start* (lambda (c id chain count)
        (fnn-bp-session-source-start grant c id chain count 1000)))
       (*fnn-tcl-source-turn* (lambda (c token) (fnn-bp-session-source-turn grant c token)))
       (*fnn-tcl-deliver* (lambda (c id bytes)
        (declare (ignore c id)) (assert (= (length bytes) 1000))
        (incf *publications*) '(:accepted nil))))
 (fnn-tcl-act conn (list (list :send ack) (list :bundle-segments-received 7 root 1000)))
 (loop repeat 20 until (plusp *received-controls*) do (fnn-tcl-turn conn))
 (assert (= *received-controls* 1)) (assert (zerop *publications*))
 (assert (fnn-tclc-source-pending conn)) (assert (eq (fnn-tclc-source-root conn) root))
 (assert (equal (fnn-tclc-held conn) (list ack)))
 (assert (= (fn-tcl-session-last-rx (fnn-tclc-session conn)) 100))
 (let ((vector (fnn-tclc-input-vector conn)) (offset (fnn-tclc-input-offset conn))
       (reads (count :read *calls*)))
  (assert (= (aref vector offset) 1))
  (loop repeat 5 do (fnn-tcl-turn conn))
  (assert (eq (fnn-tclc-input-vector conn) vector))
  (assert (= (fnn-tclc-input-offset conn) offset))
  (assert (= (count :read *calls*) reads)))
 (when lost (fnn-tcl-turn-lost conn))
 (loop repeat 100 while (fnn-tclc-source-pending conn) do (fnn-tcl-turn conn))
 (assert (= *publications* 1))
 (if lost
  (progn
   (assert (null (fnn-tclc-tx-messages conn)))
   (assert (eq (fnn-tcl-turn conn) :done))
   (fnn-bp-session-close bank grant)
   (fnn-bp-session-release-context bank grant)
   (assert (zerop (hash-table-count (fnn-bpsb-held bank)))))
  (assert (equal (fnn-tclc-tx-messages conn) (list ack))))))
(format t "PASS held-source incoming KEEPALIVE updates actual reception before publication; next XFER prefix stays in one vector, no extra read/issuer; EOF drains source.~%")
