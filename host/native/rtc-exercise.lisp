;;; The runtime contract's multi-instance exercise (RUNTIME-MODEL section 9
;;; item 1), developer images only:
;;;
;;;   fn rtc-exercise run [VARIANT]
;;;
;;; The script is the book's (books/runtime-contract-echo.lisp
;;; `fn-rce-exercise'): host completions over two interleaved connections,
;;; which completions the host delivers and which input it lands first;
;;; The book supplies the seven-field configuration and reserves three fixed
;;; buffers per connection. VARIANT 0 is the script; 1-4 inject a host fault the
;;; checks must report.  The run is the extracted
;;; executable layer `fn-rcl-x-step*' over the abstract stobj `fn-rtc-st',
;;; the one array-backed pool; one line per step, the step's observation:
;;; (i kind actions refused invariant stability match).  The exit is ok when
;;; every step kept the invariant and the outstanding :out octets and no
;;; unmatched completion changed the state; else fault.  The host only calls
;;; the book through `fnn-call' and prints: the script, the landing, the step
;;; and every check are the book's.
(in-package "ACL2")

(defvar *fnn-rtc-st* nil)

(defun fnn-live-rtc-st ()
  (or *fnn-rtc-st*
      (setq *fnn-rtc-st*
            (or (cdr (assoc 'fn-rtc-st (user-stobj-alist *the-live-state*)))
                (fnn-fault "the runtime contract stobj is not in this image")))))

(defun fnn-rtc-observation-sound-p (obs)
  (and (eq (nth 4 obs) :invp)
       (eq (nth 5 obs) :stable)
       (not (eq (nth 6 obs) :unmatched-changed))))

(defun fnn-command-rtc-exercise (command args)
  "Developer CLI: rtc-exercise run [VARIANT]."
  (unless (fnn-developer-image-p)
    (error 'fnn-usage-error
           :message "rtc-exercise is available only in the developer image"))
  (unless (and (string= command "run") (<= (length args) 1))
    (error 'fnn-usage-error :message "rtc-exercise run [VARIANT]"))
  (let* ((variant (if args
                      (handler-case (parse-integer (first args))
                        (error () (error 'fnn-usage-error :message "rtc-exercise VARIANT must be an integer")))
                    0))
         (result (fnn-call 'fn-rce-exercise variant (fnn-live-rtc-st)))
         (obs (second result)))
    (let ((*print-case* :downcase)
          (*print-pretty* nil)
          (*print-base* 10)
          (*print-radix* nil))
      (dolist (o obs)
        (fnn-out "~s" o)))
    (if (every #'fnn-rtc-observation-sound-p obs)
        +fnn-exit-ok+
      +fnn-exit-fault+)))

(fnn-register-verb "rtc-exercise" #'fnn-command-rtc-exercise)
