;;; Link the ECL export into one executable (c:build-program): the objects of
;;; build-ecl.lisp plus the portable harness (serial, replay, host-port) and a
;;; main that replays RF_TRACE or idles (RF_MODE=idle).
(defvar *out* (ext:getenv "RF_FASL"))
(defvar *here* (ext:getenv "RF_HERE"))
(load (concatenate 'string *here* "out/00-packages.lisp"))
(compile-file (concatenate 'string *here* "out/00-packages.lisp") :output-file (concatenate 'string *out* "packages.o") :system-p t)
(defvar *objs* (with-open-file (in (concatenate 'string *out* "objects.txt"))
                 (loop for l = (read-line in nil) while l collect l)))
;; the harness needs the export loaded to compile against
(dolist (o *objs*) (load (concatenate 'string (subseq o 0 (- (length o) 2)) ".fas")))
(defun obj (name)
  (let ((o (concatenate 'string *out* name ".o")))
    ;; the .fas first: ECL links a .fas from an .o of the same name and deletes it
    (load (compile-file (concatenate 'string *here* name ".lisp") :output-file (concatenate 'string *out* name ".fas")))
    (compile-file (concatenate 'string *here* name ".lisp") :output-file o :system-p t)
    o))
(defvar *harness* (mapcar #'obj '("serial" "replay" "host-port" "ecl-main")))
(c:build-program (concatenate 'string *out* "fn-rf")
                 :lisp-files (append (list (concatenate 'string *out* "packages.o")) *objs* *harness*)
                 :epilogue-code '(cl-user::rf-main))
(ext:quit 0)
