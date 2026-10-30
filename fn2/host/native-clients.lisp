;;; A5r test clients for the native loop, in the node's own process (layer
;;; doc 4.1.4-4.1.5): real loopback TCP clients driven between loop
;;; iterations, with the session's barrier (sync to quiescence, then read
;;; the node's cumulative output count). Raw SBCL; test-only.
(in-package "ACL2")
(require :sb-bsd-sockets)

(defstruct fn2-nc socket (port 0) (sent nil) (received nil) (closed nil) (total 0))

(defun fn2-nc-connect (host)
  (let ((s (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
    (sb-bsd-sockets:socket-connect s #(127 0 0 1) (fn2-nhost-listen-port host))
    (setf (sb-bsd-sockets:non-blocking-mode s) t)
    (make-fn2-nc :socket s :port (nth-value 1 (sb-bsd-sockets:socket-name s)))))

(defun fn2-nc-drain (c)
  "Read whatever is queued; note EOF."
  (let ((buf (make-array 4096 :element-type '(unsigned-byte 8))))
    (loop
      (multiple-value-bind (b n)
          (handler-case (sb-bsd-sockets:socket-receive (fn2-nc-socket c) buf nil)
            (sb-bsd-sockets:interrupted-error () (values nil 0)))
        (cond ((null b) (return))
              ((zerop n) (setf (fn2-nc-closed c) t) (return))
              (t (setf (fn2-nc-received c) (append (fn2-nc-received c) (coerce (subseq buf 0 n) 'list)))))))))

(defun fn2-nc-sync (host c eof &key (limit 200000))
  "Iterate the node until it answers the sync for C; then read to its output count."
  (setf (fn2-nhost-sync host) (list (fn2-nc-port c) (length (fn2-nc-sent c)) (if eof 1 0)))
  (let ((out nil))
    (loop repeat limit
          while (fn2-nhost-sync host)
          do (fn2-nc-drain c)
             (let ((*standard-output* (make-broadcast-stream)))
               (fn2-n-iteration host)))
    (when (fn2-nhost-sync host) (error "fn2 native test: no quiescence for port ~d" (fn2-nc-port c)))
    ;; The quiet marker's OUT: the node's cumulative Send octets on that capability.
    (let ((found (fn2-n-cap-by-port host (fn2-nc-port c))))
      (setf out (if found (fn2-ncap-tx (cdr found)) 0))
      (loop repeat 100000
            until (and (>= (length (fn2-nc-received c)) out)
                       (or (not (and found (fn2-ncap-closed (cdr found)))) (fn2-nc-closed c)))
            do (fn2-nc-drain c))
      (unless (>= (length (fn2-nc-received c)) out)
        (error "fn2 native test: port ~d read ~d of ~d octets" (fn2-nc-port c) (length (fn2-nc-received c)) out)))))

(defun fn2-nc-send (host c octets chunks)
  "OCTETS cut at CHUNKS (the rest one chunk), each a delivery barrier."
  (loop while octets
        do (let* ((k (if (and chunks (plusp (car chunks))) (min (car chunks) (length octets)) (length octets)))
                  (piece (subseq octets 0 k)))
             (setf octets (nthcdr k octets) chunks (cdr chunks))
             (unless (fn2-nc-closed c)
               (handler-case
                   (sb-bsd-sockets:socket-send (fn2-nc-socket c) (coerce piece '(vector (unsigned-byte 8))) nil)
                 (error () nil))
               (setf (fn2-nc-sent c) (append (fn2-nc-sent c) piece))
               (fn2-nc-sync host c nil)))))

(defun fn2-nc-close (host c)
  (fn2-nc-drain c)
  (unless (fn2-nc-closed c)
    (handler-case (sb-bsd-sockets:socket-shutdown (fn2-nc-socket c) :direction :output) (error () nil)))
  (fn2-nc-sync host c t)
  (fn2-nc-drain c))

(defun fn2-nc-view (c)
  "The client's view for ENVELOPE and WIRE: (port sent received closed)."
  (list (fn2-nc-port c) (fn2-nc-sent c) (fn2-nc-received c) (fn2-nc-closed c)))

(defun fn2-n-stop (host)
  (setf (fn2-nhost-stop host) t)
  (loop repeat 1000 until (eq (fn2-n-iteration host) :stop))
  (fn2-host-stop-reason (fn2-nhost-core host)))
