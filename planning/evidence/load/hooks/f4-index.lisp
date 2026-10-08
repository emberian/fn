;;; F4 private developer-image observer. No key leaves the process.
;;; REQUEST: "serial tags start count" or "serial health", decimal integers.
;;; RESPONSE: serial, numeric rows, done (or "error <text>"). No Lisp reader on request data.
;;; Read-buffer-fill runs under the owner mutex, before served lookup. That
;;; boundary works even when STAT uses the event trie rather than the catalog.
;;; Only exported, owner-level functions are used: the key is (fn-owner-mpx-key state)
;;; (host/owner-host.lisp:2509), the health is (fn-cat-index-health key fn-cat) as the live
;;; status line computes it (host/native-live-status-host.lisp:149), a tag is
;;; (fn-mlh-tag msgid key) (books/msgid-linear-exec.lisp:91). Reaching into the catalog's
;;; concrete fields faulted twice on train 45 (fn-cat is an abstract stobj over a paged one).
;;; An observer error is written to the response and never stops the owner.
(in-package "ACL2")
(defvar *fnl-f4-last* 0)
(defun fnl-f4-words (line)
  (loop for start = 0 then (1+ end)
        for end = (position #\Space line :start start)
        collect (subseq line start end)
        while end))
(defun fnl-f4-observe (request response)
  (when (probe-file request)
    (let* ((line (with-open-file (s request) (read-line s nil "")))
           (words (fnl-f4-words line))
           (serial (parse-integer (first words))))
      (when (> serial *fnl-f4-last*)
        (let* ((cat (fnn-live-cat))
               (key (funcall 'fn-owner-mpx-key *the-live-state*)))
          (with-open-file (s response :direction :output :if-exists :supersede
                                      :if-does-not-exist :create)
            (format s "~d~%" serial)
            (cond
              ((and (= (length words) 2) (string= (second words) "health"))
               (format s "~{~d~^ ~}~%" (funcall 'fnl-f4-health key cat)))
              ((and (= (length words) 4) (string= (second words) "tags"))
               (let ((start (parse-integer (third words)))
                     (count (parse-integer (fourth words))))
                 ;; Finite experiment batch, not a store/admission limit.
                 (unless (and (<= 0 start) (<= 1 count 4096))
                   (error "F4 bad candidate batch"))
                 (loop for i from start below (+ start count)
                       do (format s "~d ~d~%" i
                                  (funcall 'fn-mlh-tag (format nil "<f4-~d@fn.test>" i) key)))))
              (t (error "F4 unknown observer request")))
            (format s "done~%")
            (finish-output s))
          (setq *fnl-f4-last* serial))))))
(let ((request (sb-ext:posix-getenv "FN_LOAD_F4_REQUEST"))
      (response (sb-ext:posix-getenv "FN_LOAD_F4_RESPONSE")))
  (when request
    (unless response (error "F4 requires response path"))
    (dolist (sym '(fnn-owner-read-buffer-fill fnn-live-cat fn-owner-mpx-key fn-mlh-tag))
      (unless (fboundp sym) (error "F4 missing observer function ~a" sym)))
    ;; fn-cat-index-health is an abstract-stobj export, a MACRO in the image (f4c-t45):
    ;; expand it once here, as the host's own call sites do at compile time.
    (setf (symbol-function 'fnl-f4-health)
          (compile nil '(lambda (key fn-cat) (fn-cat-index-health key fn-cat))))
    (sb-int:encapsulate 'fnn-owner-read-buffer-fill 'fn-load-f4
      (lambda (original &rest args)
        (handler-case (fnl-f4-observe request response)
          (error (e)
            (ignore-errors
             (with-open-file (s response :direction :output :if-exists :supersede
                                         :if-does-not-exist :create)
               (format s "error ~a~%" (remove #\Newline (princ-to-string e)))))))
        (apply original args)))))
