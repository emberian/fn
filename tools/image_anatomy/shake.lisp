; tools/image_anatomy/shake.lisp -- tree-shake a native image (lane
; image-anatomy, 2026-09-26).  Loaded by derive.sh into the production core
; before ACL2 starts; the core is then saved again.  An EXPERIMENT: the
; shaken image is never a release.
;
; 1. Roots: every ACL2-package function (raw and *1*) whose name is a token
;    of the host sources (IA_SHAKE_TOKENS, one per line: host/native/*.lisp
;    and the ld'ed host/*.lisp wrappers); ACL2's start (sbcl-restart, lp,
;    our-abort); every function a special variable of any package names or
;    holds (attachments, hooks, state globals naming functions).
; 2. Closure: callees by sb-introspect:find-function-callees (SBCL 2.6 calls
;    through linkage cells, not code constants), plus fbound symbols among a
;    code component's constants (funcall/apply of a quoted name).
; 3. fmakunbound every other function and macro of the ACL2 and community
;    book packages (never SBCL's or COMMON-LISP's).
; 4. When IA_SHAKE_WORLD is set, reduce the logical world to the (symbol
;    property) pairs listed in that file plus the execution properties of
;    every kept function, each at its current value only.
; 5. Optionally (IA_SHAKE_CHANNELS) drop closed ACL2 input channels' data.
; Prints IA-SHAKE lines.
(in-package "ACL2")
(require :sb-introspect)

(defun ia-shake-package-p (p)
  (let ((n (package-name p)))
    (not (or (eql 0 (search "SB-" n))
             (member n '("COMMON-LISP" "KEYWORD" "COMMON-LISP-USER") :test #'equal)))))

(defvar *ia-fn->name* (make-hash-table :test 'eq))
(defvar *ia-kept* (make-hash-table :test 'eq))       ; function object -> t
(defvar *ia-work* nil)

(defun ia-index-functions ()
  (let ((n 0))
    (dolist (p (list-all-packages))
      (when (ia-shake-package-p p)
        (do-symbols (s p)
          (when (and (eq (symbol-package s) p) (fboundp s) (not (special-operator-p s)))
            (incf n)
            (let ((f (or (macro-function s) (symbol-function s))))
              (setf (gethash f *ia-fn->name*) s))))))
    n))

(defun ia-root-fn (f)
  (when (and (functionp f) (not (gethash f *ia-kept*)))
    (setf (gethash f *ia-kept*) t)
    (push f *ia-work*)))

(defun ia-root-symbol (s)
  (when (and (symbolp s) (fboundp s) (not (macro-function s)) (not (special-operator-p s)))
    (ia-root-fn (symbol-function s))))

(defun ia-code-of (f)
  (ignore-errors (sb-kernel:fun-code-header (sb-kernel:%fun-fun f))))

(defun ia-closure ()
  (loop while *ia-work* do
    (let ((f (pop *ia-work*)))
      (dolist (g (ignore-errors (sb-introspect:find-function-callees f)))
        (ia-root-fn g))
      (let ((code (ia-code-of f)))
        (when code
          (ignore-errors
           (sb-introspect::map-code-constants
            code (lambda (c)
                   (cond ((symbolp c) (ia-root-symbol c))
                         ((functionp c) (ia-root-fn c)))))))))))

(defun ia-read-lines (path)
  (with-open-file (in path)
    (loop for l = (read-line in nil) while l collect l)))

(defun ia-roots ()
  (let ((tokens 0))
    (dolist (tok (ia-read-lines (sb-ext:posix-getenv "IA_SHAKE_TOKENS")))
      (let ((name (string-upcase tok)))
        (dolist (pkg '("ACL2" "ACL2_*1*_ACL2"))
          (let ((s (find-symbol name pkg)))
            (when (and s (fboundp s)) (incf tokens) (ia-root-symbol s))))))
    (dolist (s (if (sb-ext:posix-getenv "IA_SHAKE_NO_LP")
                   '(sbcl-restart acl2-default-restart fn-native-entry)
                   '(sbcl-restart acl2-default-restart lp our-abort fn-native-entry)))
      (ia-root-symbol s))
    ; Functions named or held by special variables of every package.
    (let ((held 0))
      (dolist (p (list-all-packages))
        (do-symbols (v p)
          (when (and (eq (symbol-package v) p) (boundp v)
                     (not (constantp v)))
            (let ((val (symbol-value v)))
              (cond ((and (symbolp val) val (fboundp val)
                          (symbol-package val) (ia-shake-package-p (symbol-package val)))
                     (incf held) (ia-root-symbol val))
                    ((functionp val) (incf held) (ia-root-fn val)))))))
      (format t "~&IA-SHAKE roots tokens=~d held-by-variables=~d~%" tokens held))))

(defun ia-shake-functions ()
  (let ((removed 0) (macros 0) (kept 0))
    (dolist (p (list-all-packages))
      (when (ia-shake-package-p p)
        (do-symbols (s p)
          (when (and (eq (symbol-package s) p) (fboundp s) (not (special-operator-p s))
                     (not (eql 0 (search "IA-" (symbol-name s)))))
            (cond ((macro-function s) (incf macros) (fmakunbound s))
                  ((gethash (symbol-function s) *ia-kept*) (incf kept))
                  (t (incf removed) (fmakunbound s)))))))
    (format t "~&IA-SHAKE functions kept=~d removed=~d macros-removed=~d~%" kept removed macros)))

; The execution properties of a kept function (ACL2 8.7's *1* wrapper,
; oneify-cltl-code, and the guard-violation path).
(defparameter *ia-exec-props*
  '(symbol-class stobjs-in stobjs-out formals invariant-risk absstobj-info stobj
    stobj-function attachment predefined constrainedp guard))

(defun ia-strip-world (pairs-file)
  (let* ((key *current-acl2-world-key*)
         (wrld (w *the-live-state*))
         (pairs (make-hash-table :test 'equal))
         (keep (make-hash-table :test 'equal))
         (syms (make-hash-table :test 'eq))
         (new nil))
    (with-open-file (in pairs-file)
      (let ((*package* (find-package "ACL2")))
        (loop for sym = (read in nil :eof) until (eq sym :eof)
              do (let ((prop (read in)))
                   (setf (gethash (cons sym prop) pairs) t)))))
    (dolist (tr wrld)
      (let ((k (cons (car tr) (cadr tr))))
        (setf (gethash (car tr) syms) t)
        (when (and (not (gethash k keep))
                   (or (gethash k pairs)
                       (and (member (cadr tr) *ia-exec-props*)
                            (fboundp (car tr))
                            (gethash (symbol-function (car tr)) *ia-kept*))))
          (setf (gethash k keep) t)
          (push tr new))))
    (setq new (nreverse new))
    (maphash (lambda (s v) (declare (ignore v))
               (setf (get s key)
                     (loop for e in (get s key)
                           when (and (consp e) (gethash (cons s (car e)) keep) (consp (cdr e)))
                             collect (list (car e) (cadr e)))))
             syms)
    (setf (symbol-value 'ACL2_GLOBAL_ACL2::CURRENT-ACL2-WORLD) new)
    (let ((pair (get 'current-acl2-world 'acl2-world-pair)))
      (when (consp pair) (setf (car pair) new)))
    (dolist (g '(ACL2_GLOBAL_ACL2::UNDONE-WORLDS-KILL-RING
                 ACL2_GLOBAL_ACL2::LAST-MAKE-EVENT-EXPANSION
                 ACL2_GLOBAL_ACL2::ACL2-WORLD-ALIST
                 ACL2_GLOBAL_ACL2::SAVED-OUTPUT-REVERSED))
      (when (boundp g) (setf (symbol-value g) nil)))
    (format t "~&IA-SHAKE world triples=~d kept=~d pairs-listed=~d~%"
            (length wrld) (length new) (hash-table-count pairs))))

; Build residue a node never reads (IA_SHAKE_EXTRA): the channel symbols of
; every file ACL2 opened while the image was built, ACL2's own xdoc text, and
; the hons space's build-sized tables.
(defun ia-shake-extra ()
  (let ((channels 0))
    (let ((p (find-package "ACL2-INPUT-CHANNEL")))
      (do-symbols (s p)
        (when (and (eq (symbol-package s) p) (> (length (symbol-name s)) 0)
                   (char= (char (symbol-name s) 0) #\/))
          (incf channels)
          (setf (symbol-plist s) nil)
          (unintern s p))))
    (format t "~&IA-SHAKE channels-uninterned=~d~%" channels))
  (sb-kernel:%set-symbol-global-value '*acl2-system-documentation* nil)
  ; defconst's raw value kept for redundancy checks of a re-submitted event.
  (let ((n 0))
    (dolist (p (list-all-packages))
      (when (ia-shake-package-p p)
        (do-symbols (s p)
          (when (and (eq (symbol-package s) p) (get s 'redundant-raw-lisp-discriminator))
            (incf n) (remprop s 'redundant-raw-lisp-discriminator)))))
    (format t "~&IA-SHAKE discriminators-removed=~d~%" n))
  ; ACL2 re-creates the default hons space on first use when it is nil.
  (setq *default-hs* nil))

(defun ia-shake-main ()
  (let ((*print-pretty* nil))
    (sb-ext:gc :full t)
    (format t "~&IA-SHAKE before dynamic-usage=~d~%" (sb-kernel:dynamic-usage))
    (format t "~&IA-SHAKE indexed=~d~%" (ia-index-functions))
    (ia-roots)
    (ia-closure)
    (format t "~&IA-SHAKE closure=~d~%" (hash-table-count *ia-kept*))
    (let ((out (sb-ext:posix-getenv "IA_SHAKE_KEPT_OUT")))
      (when out
        (with-open-file (s out :direction :output :if-exists :supersede)
          (maphash (lambda (f v) (declare (ignore v))
                     (let ((n (gethash f *ia-fn->name*)))
                       (when n (format s "~s~%" n))))
                   *ia-kept*))))
    (ia-shake-functions)
    (let ((pairs (sb-ext:posix-getenv "IA_SHAKE_WORLD")))
      (when (and pairs (> (length pairs) 0)) (ia-strip-world pairs)))
    (let ((extra (sb-ext:posix-getenv "IA_SHAKE_EXTRA")))
      (when (and extra (> (length extra) 0)) (ia-shake-extra)))
    (clrhash *ia-fn->name*) (clrhash *ia-kept*)
    (sb-ext:gc :full t)
    (format t "~&IA-SHAKE after dynamic-usage=~d~%" (sb-kernel:dynamic-usage))))
