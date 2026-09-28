; tools/runtime_image/world-deps-check.lisp -- the qualification-time check of
; a stripped image's world reads against its build-derived dependency set
; (gpt-6's wave-5 review s.4; HST-025).  Loaded into a STRIPPED image's core
; before (acl2::sbcl-restart), never part of a release:
;
;   IMAGE's runtime ... --no-userinit --load world-deps-check.lisp
;       --eval (acl2::sbcl-restart) --disable-debugger --end-toplevel-options --fn ARGS
;
; FN_WORLD_DEPS names IMAGE.world-deps (host/native/strip-world.lisp
; fnn-write-world-deps, version 2).  At load the check first proves the file
; describes this image: every (symbol . property) pair the live world holds is
; a K line, every K line is held, and every S line's item (the prover state
; fnn-strip-prover-state replaced, lane image-strip) holds its trap (else it
; stops the process, exit 70).  At exit it writes `STRIPPED intact=N
; rebuilt=M', naming each S item no longer holding its trap as `REBUILT KIND
; NAME' (something rebuilt prover state the image was saved without).  Every
; ACL2 function whose source reads that state (the census in
; *wdc-prover-state-readers*: ACL2 8.7's every definition naming the global
; enabled structure, an enabled array or a type-set table, and ens's own
; callers' funnel, ens) is traced: its first call is written `PROVER-READ FN
; <- CALLER', a failure (the served program never calls the prover).  ACL2's
; system code is compiled at safety 0, so a use of a trap there is not
; guaranteed to signal; the trace is the check, the trap the backstop in code
; compiled with safety.
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
; dropped.  FN_WORLD_DEPS_USE=ens or type-set-table makes a prover read of a
; stripped item before start (the global enabled structure's array name;
; aref2 of the type-set table): the witness that such a read fails loudly,
; naming the item.  It writes `TRAPPED <the error>' (or `UNTRAPPED') and exits
; 72.
(in-package "ACL2")

(defvar *wdc-kept* (make-hash-table :test 'equal))
(defvar *wdc-omitted* (make-hash-table :test 'equal))
(defvar *wdc-seen* (make-hash-table :test 'equal))
(defvar *wdc-lock* (sb-thread:make-mutex :name "world-deps-check"))
(defvar *wdc-counts* (list 0 0 0))
(defvar *wdc-out* nil)
(defvar *wdc-stripped* nil)

(defun wdc-die (fmt &rest args)
  (format *error-output* "~&world-deps-check: ~?~%" fmt args)
  (finish-output *error-output*)
  (sb-ext:exit :code 70 :abort t))

(defun wdc-load (path)
  (with-open-file (s path :external-format :utf-8)
    (let ((head (read-line s nil)))
      (unless (equal head "fn-world-deps 2")
        (wdc-die "~a is not a version-2 dependency set: ~s" path head)))
    (loop for line = (read-line s nil)
          while line
          do (cond ((and (> (length line) 2) (string= "K " line :end2 2))
                    (setf (gethash (subseq line 2) *wdc-kept*) t))
                   ((and (> (length line) 2) (string= "O " line :end2 2))
                    (setf (gethash (subseq line 2) *wdc-omitted*) t))
                   ((and (> (length line) 2) (string= "S " line :end2 2))
                    (with-input-from-string (in line :start 2)
                      (let* ((*package* (find-package "ACL2"))
                             (kind (read in)) (name (read in)))
                        (push (cons kind name) *wdc-stripped*))))))))

(defun wdc-use (what)
  "The trace and the trap together.  ens is traced (PROVER-READ) and returns
the trap; the uses below are compiled with safety, so each signals a type
error naming the item.  (ACL2's own code is compiled at safety 0: the same
use there gave a memory fault at #x0 on 2026-09-28, loud but unnamed and not
guaranteed, which is why the trace is the check.)"
  (let ((result
          (handler-case
              (locally (declare (optimize (safety 3)))
                (cond ((equal what "ens")
                       (car (the t (ens *the-live-state*))))
                      ((equal what "type-set-table")
                       (car (the t (symbol-value '*type-set-binary-+-table*))))
                      (t (wdc-die "FN_WORLD_DEPS_USE ~s is neither ens nor type-set-table" what))))
            (error (c)
              (wdc-write (substitute #\Space #\Newline
                                     (format nil "TRAPPED ~a: ~a" (type-of c) c)))
              (sb-ext:exit :code 72 :abort t)))))
    (wdc-write (format nil "UNTRAPPED ~s" result))
    (sb-ext:exit :code 72 :abort t)))

(defvar *wdc-finished* nil)

(defun wdc-finish ()
  "The exit reports, once: the host leaves through fnn-exit, an
(sb-ext:exit :abort t) that runs no exit hook, so the check reports from
fnn-exit's encapsulation as well as from the exit hooks."
  (unless *wdc-finished*
    (setq *wdc-finished* t)
    (wdc-stripped-report)
    (wdc-summary)))

(defun wdc-stripped-report ()
  (let ((rebuilt (remove-if (lambda (item) (fnn-stripped-item-trapped-p (car item) (cdr item)))
                            *wdc-stripped*)))
    (dolist (item rebuilt)
      (wdc-write (fnn-with-world-key-printing
                  (format nil "REBUILT ~s ~s" (car item) (cdr item)))))
    (wdc-write (format nil "STRIPPED intact=~d rebuilt=~d"
                       (- (length *wdc-stripped*) (length rebuilt)) (length rebuilt)))))

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
    (unless *wdc-stripped*
      (wdc-die "the dependency set lists no stripped prover state"))
    (dolist (item *wdc-stripped*)
      (unless (fnn-stripped-item-trapped-p (car item) (cdr item))
        (wdc-die "the dependency set lists ~s ~s as stripped; the image holds it"
                 (car item) (cdr item))))
    (wdc-write (format nil "LOADED kept=~d omitted=~d stripped=~d (the kept pairs and the stripped items match the image)"
                       (hash-table-count *wdc-kept*) (hash-table-count *wdc-omitted*)
                       (length *wdc-stripped*))))
  (let ((drop (sb-ext:posix-getenv "FN_WORLD_DEPS_DROP")))
    (when (and drop (plusp (length drop))) (wdc-drop drop)))
  (wdc-trace-prover-readers)
  (let ((use (sb-ext:posix-getenv "FN_WORLD_DEPS_USE")))
    (when (and use (plusp (length use))) (wdc-use use)))
  (push #'wdc-finish sb-ext:*exit-hooks*)
  (when (fboundp 'fnn-exit)
    (sb-int:encapsulate 'fnn-exit 'world-deps-check
      (lambda (f &rest args) (ignore-errors (wdc-finish)) (apply f args))))
  (sb-int:encapsulate 'fgetprop 'world-deps-check
    (lambda (f sym prop &rest more) (wdc-note sym prop) (apply f sym prop more)))
  (sb-int:encapsulate 'sgetprop 'world-deps-check
    (lambda (f sym prop &rest more) (wdc-note sym prop) (apply f sym prop more))))
