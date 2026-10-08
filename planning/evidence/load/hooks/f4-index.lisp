;;; F4 private developer-image observer. No key leaves the process.
;;; REQUEST: "serial tags start count" or "serial health", decimal integers.
;;; RESPONSE: serial, numeric rows, done. No Lisp reader on request data.
;;; Read-buffer-fill runs under the owner mutex, before served lookup. That
;;; boundary works even when STAT uses the event trie rather than the catalog.
(in-package "ACL2")
(defvar *fnl-f4-last* 0)
(defun fnl-f4-words (line)
  (loop for start = 0 then (1+ end)
        for end = (position #\Space line :start start)
        collect (subseq line start end)
        while end))
(let ((request (sb-ext:posix-getenv "FN_LOAD_F4_REQUEST"))
      (response (sb-ext:posix-getenv "FN_LOAD_F4_RESPONSE")))
  (when request
    (unless response (error "F4 requires response path"))
    (dolist (sym '(fnn-owner-read-buffer-fill fnn-live-cat fn-cat$c-mpx
                   fn-mlh-key-octets fn-mlh-tag-of fn-cat$c-index-health
                   fn-cat$c-rows-below-count fn-mlh-build-health))
      (unless (fboundp sym) (error "F4 missing observer function ~a" sym)))
    (sb-int:encapsulate 'fnn-owner-read-buffer-fill 'fn-load-f4
      (lambda (original &rest args)
        (when (probe-file request)
          (let* ((line (with-open-file (s request) (read-line s nil "")))
                 (words (fnl-f4-words line))
                 (serial (parse-integer (first words))))
            (when (> serial *fnl-f4-last*)
              (let* ((cat (fnn-live-cat))
                     (table (funcall 'fn-cat$c-mpx cat)))
                (with-open-file (s response :direction :output :if-exists :supersede
                                            :if-does-not-exist :create)
                  (format s "~d~%" serial)
                  (cond
                    ((and (= (length words) 2) (string= (second words) "health"))
                     (let* ((key (funcall 'fn-mlh-key-octets table))
                            (live (funcall 'fn-cat$c-index-health key cat))
                            (rebuilt (funcall 'fn-mlh-build-health key
                                              (funcall 'fn-cat$c-rows-below-count cat))))
                       (unless (equal live rebuilt) (error "F4 live/rebuilt health mismatch"))
                       (format s "~{~d~^ ~}~%" rebuilt)))
                    ((and (= (length words) 4) (string= (second words) "tags"))
                     (let ((start (parse-integer (third words)))
                           (count (parse-integer (fourth words))))
                       ;; Finite experiment batch, not a store/admission limit.
                       (unless (and (<= 0 start) (<= 1 count 4096))
                         (error "F4 bad candidate batch"))
                       (loop for i from start below (+ start count)
                             do (format s "~d ~d~%" i
                                        (funcall 'fn-mlh-tag-of (format nil "<f4-~d@fn.test>" i) table)))))
                    (t (error "F4 unknown observer request")))
                  (format s "done~%")
                  (finish-output s))
                (setq *fnl-f4-last* serial)))))
        (apply original args)))))
