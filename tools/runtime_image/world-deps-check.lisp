; tools/runtime_image/world-deps-check.lisp -- the qualification-time check of
; a stripped image's world reads against its build-derived dependency set
; (gpt-6's wave-5 review s.4; HST-025).  Loaded into a STRIPPED image's core
; before (acl2::sbcl-restart), never part of a release:
;
;   IMAGE's runtime ... --no-userinit --load world-deps-check.lisp
;       --eval (acl2::sbcl-restart) --disable-debugger --end-toplevel-options --fn ARGS
;
; FN_WORLD_DEPS names IMAGE.world-deps (host/native/strip-world.lisp
; fnn-write-world-deps, version 1).  At load the check first proves the file
; describes this image: every (symbol . property) pair the live world holds is
; a K line, and every K line is held (else it stops the process, exit 70).
; Then every read through fgetprop and sgetprop (the functions every
; getprop/getpropc/global-val reaches in raw Lisp) is classified once:
;
;   kept     in the set: answered as the full image answers;
;   ABSENT   no value in the full image either (not a K or O line): the
;            default the full image also returns; recorded, not a failure;
;   OMITTED  an O line: the full image had a value the strip removed; the
;            stripped image answers differently.  A FAILURE.
;
; Each pair's first read is appended to FN_WORLD_DEPS_OUT.<pid> as `KEPT S P',
; `ABSENT S P <- CALLER' or `OMITTED S P <- CALLER'; a summary line `SUMMARY kept=N absent=A omitted=O' is rewritten at
; exit.  FN_WORLD_DEPS_DROP="S P" (a K line's pair) deliberately removes that
; property from the live world before start and re-files it as omitted: the
; mutation witness that the check catches a required property the strip
; dropped.
(in-package "ACL2")

(defvar *wdc-kept* (make-hash-table :test 'equal))
(defvar *wdc-omitted* (make-hash-table :test 'equal))
(defvar *wdc-seen* (make-hash-table :test 'equal))
(defvar *wdc-lock* (sb-thread:make-mutex :name "world-deps-check"))
(defvar *wdc-counts* (list 0 0 0))
(defvar *wdc-out* nil)

(defun wdc-die (fmt &rest args)
  (format *error-output* "~&world-deps-check: ~?~%" fmt args)
  (finish-output *error-output*)
  (sb-ext:exit :code 70 :abort t))

(defun wdc-load (path)
  (with-open-file (s path :external-format :utf-8)
    (let ((head (read-line s nil)))
      (unless (equal head "fn-world-deps 1")
        (wdc-die "~a is not a version-1 dependency set: ~s" path head)))
    (loop for line = (read-line s nil)
          while line
          do (cond ((and (> (length line) 2) (string= "K " line :end2 2))
                    (setf (gethash (subseq line 2) *wdc-kept*) t))
                   ((and (> (length line) 2) (string= "O " line :end2 2))
                    (setf (gethash (subseq line 2) *wdc-omitted*) t))))))

(defun wdc-live-pairs ()
  "Every (symbol . property) pair with a current value in the live world."
  (let ((key *current-acl2-world-key*) (seen (make-hash-table :test 'eq)) (pairs nil))
    (dolist (trip (w *the-live-state*))
      (let ((s (car trip)))
        (unless (gethash s seen)
          (setf (gethash s seen) t)
          (dolist (entry (get s key))
            (let ((stack (cdr entry)))
              (when (and (consp stack) (not (eq (car stack) *acl2-property-unbound*)))
                (push (cons s (car entry)) pairs)))))))
    pairs))

(defun wdc-drop (text)
  "Remove TEXT's pair (`S P', a K line) from the live world; file it as omitted."
  (unless (gethash text *wdc-kept*)
    (wdc-die "FN_WORLD_DEPS_DROP ~s is not in the dependency set" text))
  (let* ((space (position #\Space text))
         (sym (let ((*package* (find-package "ACL2"))) (read-from-string text t nil :end space)))
         (prop (let ((*package* (find-package "ACL2"))) (read-from-string text t nil :start (1+ space))))
         (key *current-acl2-world-key*))
    (setf (get sym key) (remove prop (get sym key) :key #'car))
    (remhash text *wdc-kept*)
    (setf (gethash text *wdc-omitted*) t)
    (wdc-write (format nil "DROPPED ~a" text))))

(defun wdc-write (line)
  (when *wdc-out*
    (ignore-errors
     (with-open-file (s (format nil "~a.~d" *wdc-out* (sb-posix:getpid))
                        :direction :output :if-exists :append :if-does-not-exist :create)
       (write-line line s)))))

(defun wdc-caller ()
  (let ((found nil) (depth 0))
    (ignore-errors
     (sb-debug:map-backtrace
      (lambda (frame)
        (incf depth)
        (unless (or found (> depth 40))
          (let* ((name (sb-di:debug-fun-name (sb-di:frame-debug-fun frame)))
                 (n (cond ((symbolp name) (symbol-name name))
                          ((and (consp name) (symbolp (car (last name))))
                           (symbol-name (car (last name))))))) 
            (when (and n (not (member n '("WDC-NOTE" "WDC-CALLER" "FGETPROP" "SGETPROP")
                                      :test #'string=))
                       (not (search "ENCAPSULAT" n)) (not (search "LAMBDA" n))
                       (let ((sym (if (consp name) (car (last name)) name)))
                         (and (symbolp sym) (symbol-package sym)
                              (not (eql 0 (search "SB-" (package-name (symbol-package sym))))))))
              (setq found n)))))))
    (or found "?")))

(defun wdc-note (sym prop)
  (let ((pair (cons sym prop)))
    (unless (gethash pair *wdc-seen*)
      (sb-thread:with-recursive-lock (*wdc-lock*)
        (unless (gethash pair *wdc-seen*)
          (let* ((text (fnn-world-key-string sym prop))
                 (class (cond ((gethash text *wdc-kept*) :kept)
                              ((gethash text *wdc-omitted*) :omitted)
                              (t :absent))))
            (setf (gethash pair *wdc-seen*) class)
            (case class
              (:kept (incf (first *wdc-counts*))
               (wdc-write (format nil "KEPT ~a" text)))
              (:absent (incf (second *wdc-counts*))
               (wdc-write (format nil "ABSENT ~a <- ~a" text (wdc-caller))))
              (:omitted (incf (third *wdc-counts*))
               (wdc-write (format nil "OMITTED ~a <- ~a" text (wdc-caller)))))))))))

(defun wdc-summary ()
  (wdc-write (format nil "SUMMARY kept=~d absent=~d omitted=~d"
                     (first *wdc-counts*) (second *wdc-counts*) (third *wdc-counts*))))

(let ((path (sb-ext:posix-getenv "FN_WORLD_DEPS")))
  (unless path (wdc-die "set FN_WORLD_DEPS to the image's .world-deps"))
  (setq *wdc-out* (sb-ext:posix-getenv "FN_WORLD_DEPS_OUT"))
  (wdc-load path)
  ;; The file describes this image: the live pairs are exactly the K lines.
  (let ((live (wdc-live-pairs)) (held (make-hash-table :test 'equal)))
    (dolist (pair live)
      (let ((text (fnn-world-key-string (car pair) (cdr pair))))
        (setf (gethash text held) t)
        (unless (gethash text *wdc-kept*)
          (wdc-die "the live world holds ~a, which the dependency set does not list" text))))
    (maphash (lambda (text v) (declare (ignore v))
               (unless (gethash text held)
                 (wdc-die "the dependency set lists ~a, which the live world lacks" text)))
             *wdc-kept*)
    (wdc-write (format nil "LOADED kept=~d omitted=~d (the kept pairs match the image)"
                       (hash-table-count *wdc-kept*) (hash-table-count *wdc-omitted*))))
  (let ((drop (sb-ext:posix-getenv "FN_WORLD_DEPS_DROP")))
    (when (and drop (plusp (length drop))) (wdc-drop drop)))
  (push #'wdc-summary sb-ext:*exit-hooks*)
  (sb-int:encapsulate 'fgetprop 'world-deps-check
    (lambda (f sym prop &rest more) (wdc-note sym prop) (apply f sym prop more)))
  (sb-int:encapsulate 'sgetprop 'world-deps-check
    (lambda (f sym prop &rest more) (wdc-note sym prop) (apply f sym prop more))))
