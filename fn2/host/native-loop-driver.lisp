;;; The native loop acceptance driver (fn2/tests/native-loop.lsp). Test-only.
(in-package "ACL2")

(defun fn2-nl-transcripts ()
  "conn-unit's fixture octets, each with three chunkings: whole, 1-octet, and 7s."
  (loop for f in *fn2-cu-fixtures*
        for octets = (nth 1 f)
        append (list (list (nth 0 f) octets nil)
                     (list (nth 0 f) octets (make-list (length octets) :initial-element 1))
                     (list (nth 0 f) octets (make-list (ceiling (length octets) 7) :initial-element 7)))))

(defun fn2-nl-run-set (transcripts trace-capacity)
  "One node, these clients one after another. Values: client views, trace, stop reason."
  (let ((host (fn2-n-make-host *fn2-nl-profile* :trace-capacity trace-capacity)) (views nil))
    (unwind-protect
         (progn
           (dolist (tr transcripts)
             (let ((c (fn2-nc-connect host)))
               (fn2-nc-sync host c nil :openp t)
               (fn2-nc-send host c (nth 1 tr) (nth 2 tr))
               (fn2-nc-close host c)
               (push (fn2-nc-view c) views)
               (sb-bsd-sockets:socket-close (fn2-nc-socket c))))
           (let ((reason (fn2-n-stop host)))
             (values (reverse views) (fn2-n-trace-list host) reason)))
      (fn2-n-destroy host))))

(defun fn2-nl-wire-gap-p (v verdict)
  "D's WIRE gap, reported through main (A5r, 2026-10-30): the node answers an unterminated
line of 511+ octets with 501 and closes; a client that stops at EOF leaves WIRE an
unterminated tail, which it calls :unasked-reply. Named and counted, never silent."
  (let ((sent (nth 1 v)))
    (and (equal verdict '(:fail :unasked-reply 0)) (nth 3 v)
         (not (search '(13 10) sent)) (<= 511 (length sent)))))
(defvar *fn2-nl-wire-gaps* 0)
(defun fn2-nl-wire (views)
  (loop for v in views
        for verdict = (fn2-wire-check (nth 1 v) (nth 2 v) (nth 3 v))
        if (and (not (eq verdict :pass)) (fn2-nl-wire-gap-p v verdict)) do (incf *fn2-nl-wire-gaps*)
        else unless (eq verdict :pass) collect (list (nth 0 v) verdict)))

(defun fn2-nl-mutate (trace pred fn)
  "TRACE with the first entry satisfying PRED replaced by (FN entry); nil if none."
  (let ((at (position-if pred trace)))
    (and at (append (subseq trace 0 at) (list (funcall fn (nth at trace))) (nthcdr (1+ at) trace)))))
(defun fn2-nl-post-of (kind trace)
  "A predicate true of the first :post (count > 0) whose op, by the latest take of its slot, is of KIND."
  (let ((latest (make-hash-table)) (target nil))
    (dolist (e trace)
      (case (car e)
        (:take (setf (gethash (nth 1 e) latest) (nth 3 e)))
        (:post (when (and (null target) (eql (gethash (nth 2 e) latest) kind) (plusp (nth 7 e)))
                 (setf target e)))))
    (lambda (e) (eq e target))))

(defun fn2-nl-controls (trace views)
  "ENVELOPE's controls: each breaks one premise and must be refused with its word."
  (let* ((recv (fn2-nl-post-of *fn2-action-receive* trace))
         (send (fn2-nl-post-of *fn2-action-send* trace))
         (accepts (loop for e in trace when (and (eq (car e) :post) (eql (nth 4 e) *fn2-event-accept-result*)) collect e))
         (first-accept (first accepts))
         (cases
          (list
           (list :take-descriptor
                 (fn2-nl-mutate trace (lambda (e) (eq (car e) :take)) (lambda (e) (let ((e (copy-list e))) (setf (nth 9 e) (1+ (nth 9 e))) e))))
           (list :post-unacknowledged
                 (fn2-nl-mutate trace recv (lambda (e) (let ((e (copy-list e))) (setf (nth 2 e) 7 (nth 3 e) 99999) e))))
           (list :post-not-allowed
                 (fn2-nl-mutate trace recv (lambda (e) (let ((e (copy-list e))) (setf (nth 7 e) 100000) e))))
           (list :accept-capability-reused
                 (and (second accepts)
                      (fn2-nl-mutate trace (lambda (e) (eq e (second accepts)))
                                     (lambda (e) (let ((e (copy-list e))) (setf (nth 8 e) (nth 8 first-accept) (nth 9 e) (nth 9 first-accept)) e)))))
           (list :release-unauthorized
                 (let ((at (position-if send trace)))
                   (and at (let ((e (nth at trace)))
                             (append (subseq trace 0 (1+ at))
                                     (list (list :post 1 (nth 2 e) (nth 3 e) *fn2-event-borrow-released* *fn2-outcome-done*
                                                 *fn2-reason-none* 0 0 0 *fn2-peer-family-none* '(0 0 0 0 0) nil))
                                     (nthcdr (1+ at) trace))))))
           ;; The case of the first command letter: the same reply (NNTP keywords
           ;; are case-insensitive), so only the input check can catch it.
           (list :receive-not-client
                 (fn2-nl-mutate trace recv (lambda (e) (let ((e (copy-list e)) (o (copy-list (nth 12 e))))
                                                         (setf (car o) (logxor 32 (car o)) (nth 12 e) o) e))))
           (list :send-bytes
                 (fn2-nl-mutate trace send (lambda (e) (let ((e (copy-list e)) (o (copy-list (nth 12 e))))
                                                         (setf (car o) (logxor 1 (car o)) (nth 12 e) o) e))))))
         (ok t))
    (dolist (c cases ok)
      (let* ((mutant (second c))
             (v (and mutant (funcall (if (eq (first c) :receive-not-client) #'fn2-envelope-check-inputs #'fn2-envelope-check) mutant (mapcar #'identity views) *fn2-nl-profile*)))
             (word (if (consp v) (car v) v)))
        (format t "ENVELOPE CONTROL ~a: ~s~%" (first c) v)
        (unless (and mutant (eq word (first c))) (setf ok nil))))))

(defun fn2-nl-write-evidence (trace views)
  (with-open-file (out "fn2/tests/evidence/native-envelope-trace.lisp" :direction :output :if-exists :supersede)
    (with-standard-io-syntax
      (let ((*print-pretty* nil) (*package* (find-package "ACL2")))
        (format out "; Written by fn2/tests/native-loop.lsp (A5r): a native boundary trace of~%; conn-unit's first fixtures over loopback TCP, and the clients' views.~%(in-package \"ACL2\")~%")
        (format out "(defconst *fn2-native-trace* '~s)~%" trace)
        (format out "(defconst *fn2-native-clients* '~s)~%" views)))))

(defun fn2-nl-main ()
  (let* ((all (fn2-nl-transcripts)) (ok t))
    ;; Evidence set (DATE-free, for the refinement keystone's teeth): idle,
    ;; pipelined, unknown-then-quit whole and pipelined in 1-octet chunks.
    (multiple-value-bind (views trace reason) (fn2-nl-run-set (loop for i in '(0 3 9 4) collect (nth i all)) 400000)
      (let ((wire (fn2-nl-wire views)) (env (fn2-envelope-check trace views *fn2-nl-profile*)))
        (format t "NATIVE EVIDENCE SET: clients=~d trace=~d stop=~d wire=~s envelope=~s~%" (length views) (length trace) reason wire env)
        (unless (and (null wire) (eq env :pass)) (setf ok nil))
        (fn2-nl-write-evidence trace views)
        (unless (fn2-nl-controls trace views) (setf ok nil))))
    (multiple-value-bind (views trace reason) (fn2-nl-run-set all 4000000)
      (let ((wire (fn2-nl-wire views)) (env (fn2-envelope-check trace views *fn2-nl-profile*)))
        (loop for w in wire do (let ((v (find (car w) views :key #'car)) (tr (nth (position (car w) views :key #'car) all)))
                                 (format t "WIRE REFUSED ~a chunks=~a: sent=~s~% received=~s~% closed=~s~%"
                                         (nth 0 tr) (length (nth 2 tr)) (map 'string #'code-char (nth 1 v))
                                         (map 'string #'code-char (nth 2 v)) (nth 3 v))))
        (format t "NATIVE ALL FIXTURES: clients=~d trace=~d stop=~d wire=~s envelope=~s~%" (length views) (length trace) reason wire env)
        (unless (and (null wire) (eq env :pass)) (setf ok nil))))
    (format t "WIRE-GAP-UNTERMINATED-OVERLONG ~d (D's WIRE gap, reported)~%" *fn2-nl-wire-gaps*)
    (format t "NATIVE LOOP ~a~%" (if ok "PASS" "FAIL"))
    (finish-output)
    ok))
