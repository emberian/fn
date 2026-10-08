;;; W2 owner-process contention, loaded before acl2::sbcl-restart; no image change.
;;; FN_LOAD_LOCKS=<path>: cumulative epoch_us name=count:wait_us rows, every 1 s.
;;; Names are percent-encoded UTF-8; equal names aggregate distinct mutex objects.
;;; Without the environment variable no wrapper, counters or thread are installed.
;;;
;;; Like 2026-10-07-w7/w7hook.lisp, intercept SB-THREAD::MUTEX-WAIT: an
;;; uncontended WITH-MUTEX grab is an inline CAS and contributes zero waits.
;;; Count and elapsed monotonic microseconds are charged when a contended call
;;; finishes (including timeout/unwind); not hold time, CPU time, or ARTICLE-only
;;; time. All owner threads, including the background poster, contribute.
;;; CONDITION-WAIT is deliberately not wrapped: its sleep is not mutex contention;
;;; any contended reacquisition that calls MUTEX-WAIT is counted once here.
;;; Counters are independently atomic words, not a transactional pair snapshot.
;;; An immutable alist is published by CAS; hot counters use ATOMIC-INCF, no
;;; instrumentation mutex. The dynamic guard excludes recursive instrumentation
;;; and the dump thread's own I/O locks. Names appear on their first contention.
;;;
;;; Names in this tree (the target image may differ):
;;; - owner.lisp: fnn-owner-install constructs :lock "fn owner/store" (near 1643),
;;;   reached by (fnn-owner-service-lock service).
;;; - extent.lisp:70: *fnn-extent-lock*, "fn extent realizer".
;;; - io.lisp:1041: *fnn-owner-log-mutex*, "fn service log";
;;;   io.lisp:7305: fnn-log lock slot, "fn log kernel".
;;; There is NO separate ACL2 dispatch mutex in this source: io.lisp:1532
;;; fnn-call -> raw-trap.lisp fnn-raw-dispatch-apply uses a per-thread extent.
;;; raw-trap.lisp explicitly describes lock-free dispatch (near line 27).
;;; Do not mistake the owner's capture mutex for a global dispatch lock.
(in-package "ACL2")
(sb-ext:defglobal *w2-lock-entries* nil)
(defvar *w2-lock-hook-active* nil)

(defun w2-lock-epoch-us ()
  (multiple-value-bind (s us) (sb-ext:get-time-of-day) (+ (* s 1000000) us)))

(defun w2-lock-name (name)
  (with-output-to-string (s)
    (loop for octet across (sb-ext:string-to-octets name :external-format :utf-8)
          do (if (or (<= 65 octet 90) (<= 97 octet 122) (<= 48 octet 57)
                     (member octet '(45 46 95 126)))
                 (write-char (code-char octet) s)
                 (format s "%~2,'0X" octet)))))

(defun w2-lock-counts (mutex)
  (let ((name (or (sb-thread:mutex-name mutex) "<unnamed>")))
    (loop
      (let* ((old *w2-lock-entries*) (entry (assoc name old :test #'equal)))
        (when entry (return (cdr entry)))
        (let* ((counts (make-array 2 :element-type 'sb-ext:word :initial-element 0))
               (new (acons name counts old)))
          (when (eq old (sb-ext:compare-and-swap *w2-lock-entries* old new))
            (return counts)))))))

(let ((path (sb-ext:posix-getenv "FN_LOAD_LOCKS")))
  (when (and path (plusp (length path)))
    (let ((log (open path :direction :output :if-exists :supersede)))
      (sb-int:encapsulate 'sb-thread::mutex-wait 'w2-lock-wait
        (lambda (f &rest args)
          (if *w2-lock-hook-active*
              (apply f args)
              (let* ((*w2-lock-hook-active* t)
                     (mutex (find-if (lambda (x) (typep x 'sb-thread:mutex)) args)))
                (if (null mutex)
                    (apply f args)
                    (let ((counts (w2-lock-counts mutex))
                          (start (get-internal-real-time)))
                      (declare (type (simple-array sb-ext:word (2)) counts))
                      (unwind-protect (apply f args)
                        (sb-ext:atomic-incf (aref counts 1)
                          (round (* 1000000 (- (get-internal-real-time) start))
                                 internal-time-units-per-second))
                        (sb-ext:atomic-incf (aref counts 0) 1))))))))
      (sb-thread:make-thread
       (lambda ()
         (let ((*w2-lock-hook-active* t))
           (loop
             (format log "~d" (w2-lock-epoch-us))
             (dolist (entry *w2-lock-entries*)
               (format log " ~a=~d:~d" (w2-lock-name (car entry))
                       (aref (cdr entry) 0) (aref (cdr entry) 1)))
             (terpri log)
             (finish-output log)
             (sleep 1))))
       :name "fn-load-locks"))))
