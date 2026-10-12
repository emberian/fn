;;; Call counters for a profiling image (FN_PROF_HOOK=this file; lane
;;; spans-newnews, 2026-10-11).  FN_COUNT_OUT=P: every function whose name
;;; starts with one of FN_COUNT_PREFIXES (colon separated, upper case; the
;;; *1* twins too) is wrapped by sb-int:encapsulate with a call counter.
;;; Every 5 s, when a count moved, the nonzero counts are appended to P.log
;;; with the seconds since start.  FN_COUNT_TRIGGER=NAME: the first call of
;;; NAME starts sb-sprof (cpu, all threads) and FN_COUNT_PROF_S seconds later
;;; (default 30) its flat and graph reports go to P.prof.txt.
;;; Optional FN_COUNT_SNAPSHOT=P: write a token line to P.request, then
;;; await P.snapshot with that token, all counters (including zero), and
;;; END.  Requests are polled at 10 ms; the normal log still runs at 5 s.
(in-package "ACL2")
(require :sb-sprof)

(defvar *fnc-counts* (make-hash-table :test 'eq :synchronized t))
(defvar *fnc-trigger* nil)
(defvar *fnc-triggered* nil)

(defun fnc-split (s)
  (let ((out nil) (start 0))
    (loop for i from 0 to (length s)
          do (when (or (= i (length s)) (char= (char s i) #\:))
               (when (> i start) (push (subseq s start i) out))
               (setq start (1+ i))))
    (nreverse out)))

(defun fnc-wrap (sym)
  (when (and (fboundp sym) (not (macro-function sym)) (not (special-operator-p sym))
             (not (sb-int:encapsulated-p sym 'fnc-count)))
    (setf (gethash sym *fnc-counts*) 0)
    (let ((trig (eq sym *fnc-trigger*)))
      (sb-int:encapsulate
       sym 'fnc-count
       (lambda (f &rest args)
         (sb-ext:with-locked-hash-table (*fnc-counts*)
           (incf (gethash sym *fnc-counts* 0)))
         (when (and trig (not *fnc-triggered*))
           (setq *fnc-triggered* (get-internal-real-time))
           (sb-sprof:reset)
           (sb-sprof:start-profiling :mode :cpu :threads :all :sample-interval 0.002
                                     :max-samples 2000000))
         (apply f args))))))

(defun fnc-snapshot (prefix last-token)
  (let ((request (concatenate 'string prefix ".request")))
    (when (probe-file request)
      (let ((token (with-open-file (s request) (read-line s nil nil))))
        (when (and token (not (equal token last-token)))
          (let ((counts nil))
            (sb-ext:with-locked-hash-table (*fnc-counts*)
              (maphash (lambda (sym n) (push (cons sym n) counts)) *fnc-counts*))
            (with-open-file (s (concatenate 'string prefix ".snapshot")
                               :direction :output :if-exists :supersede
                               :if-does-not-exist :create)
              (format s "~a~%" token)
              (dolist (e counts)
                (format s "~a::~a ~d~%" (package-name (symbol-package (car e)))
                        (symbol-name (car e)) (cdr e)))
              (format s "END~%"))
            (return-from fnc-snapshot token))))))
  last-token)

(let ((out (sb-ext:posix-getenv "FN_COUNT_OUT"))
      (snapshot (sb-ext:posix-getenv "FN_COUNT_SNAPSHOT"))
      (prefixes (fnc-split (or (sb-ext:posix-getenv "FN_COUNT_PREFIXES") "")))
      (trigger (sb-ext:posix-getenv "FN_COUNT_TRIGGER"))
      (prof-s (let ((v (sb-ext:posix-getenv "FN_COUNT_PROF_S")))
                (if (and v (plusp (length v))) (parse-integer v) 30))))
  (when (and out (plusp (length out)))
    (when (and trigger (plusp (length trigger)))
      (setq *fnc-trigger* (intern trigger "ACL2")))
    (dolist (pkg (list (find-package "ACL2") (find-package "ACL2_*1*_ACL2")))
      (when pkg
        (do-symbols (s pkg)
          (when (and (eq (symbol-package s) pkg)
                     (some (lambda (p) (and (>= (length (symbol-name s)) (length p))
                                            (string= p (symbol-name s) :end2 (length p))))
                           prefixes))
            (fnc-wrap s)))))
    (with-open-file (s (concatenate 'string out ".log") :direction :output
                       :if-exists :append :if-does-not-exist :create)
      (format s "wrapped ~d functions~%" (hash-table-count *fnc-counts*)))
    (let ((t0 (get-internal-real-time)))
      (sb-thread:make-thread
       (lambda ()
         (let ((last nil) (reported nil) (last-token nil)
               (next-log (+ (get-internal-real-time) (* 5 internal-time-units-per-second))))
           (loop
             (sleep (if (and snapshot (plusp (length snapshot))) 0.01 5))
             (when (and snapshot (plusp (length snapshot)))
               (setq last-token (fnc-snapshot snapshot last-token)))
             (when (>= (get-internal-real-time) next-log)
               (setq next-log (+ (get-internal-real-time) (* 5 internal-time-units-per-second)))
               (when (and *fnc-triggered* (not reported)
                          (> (- (get-internal-real-time) *fnc-triggered*)
                             (* prof-s internal-time-units-per-second)))
                 (setq reported t)
                 (sb-sprof:stop-profiling)
                 (with-open-file (s (concatenate 'string out ".prof.txt") :direction :output
                                    :if-exists :supersede)
                   (sb-sprof:report :type :flat :stream s :max 80)
                   (sb-sprof:report :type :graph :stream s :max 60)))
               (let ((now nil))
                 (sb-ext:with-locked-hash-table (*fnc-counts*)
                   (maphash (lambda (k v) (when (plusp v) (push (cons k v) now))) *fnc-counts*))
                 (setq now (sort now #'> :key #'cdr))
                 (unless (equal now last)
                   (setq last now)
                   (with-open-file (s (concatenate 'string out ".log") :direction :output
                                      :if-exists :append :if-does-not-exist :create)
                     (format s "~&t=~,1f~%" (/ (- (get-internal-real-time) t0)
                                               (float internal-time-units-per-second)))
                     (dolist (e now) (format s "  ~a ~d~%" (car e) (cdr e))))))))))
       :name "fn-count-dump"))))
