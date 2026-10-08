;;; tools/extract/forms-export.lisp -- the extractor's emitter and checker
;;; (X1/X2, lane extract-forms).  Raw Lisp, loaded into the extraction world
;;; image after :q:
;;;
;;;   (load "tools/extract/forms-export.lisp")
;;;   (xt-fe-export TOKENS OUT-DIR ACL2-SRC-DIR CLRUNTIME-PATH WORLD-KEY)
;;;   (lp)  ; then xt-core-export, handed (@ xt-fe-tables): see below
;;;   (xt-verify-defs OUT-DIR ACL2-SRC-DIR CLRUNTIME-PATH WORLD-KEY)
;;;
;;; For every function f the host's closure reaches, the core compiles exactly
;;; the forms ACL2 itself installed, where the world holds them:
;;;   raw  -- the def of f's cltl-command `defuns' (or its defstobj raw-defs);
;;;   *1*  -- (oneify-cltl-code mode def stobj-flag wrld) of that def,
;;; and, where ACL2 installed them from its own source files (a boot-strap
;;; function reclassified to :logic, the *1* of a Common Lisp primitive, an
;;; ACL2 runtime variable), the top-level form read from that file, located by
;;; name, with the file's SHA-256 and the line recorded.  Every form is fully
;;; macroexpanded by THIS image's SBCL (sb-cltl2:macroexpand-all) and printed
;;; readably under a fixed package (no package accessible), uninterned symbols
;;; renamed by first occurrence.  Nothing is translated.
;;;
;;; The names the forms call that are neither extracted nor Common Lisp are
;;; exactly the host runtime: the names clruntime.lisp defines.  A name that is
;;; none of the three is a REAL GAP and the export fails naming it (X2).
;;;
;;; defs.lisp is a sequence of UNIT blocks, each headed by a line
;;;   ;;;; UNIT <id>
;;; and holding the unit's forms, one per line.  manifest.tsv lists every
;;; unit's id, the SHA-256 of its block text and its origin.  xt-verify-defs
;;; re-derives every unit from the world and the sources and compares: the
;;; ids present, the block text and the re-derived text must all agree
;;; (X1); any difference refuses by unit name.
;;;
;;; A table an emitted form reads by name ((table-alist 'T ...), ACL2's own
;;; code included: get-check-invariant-risk reads acl2-defaults-table) is not
;;; a unit.  xt-fe-export leaves the closure's tables in the state global
;;; XT-FE-TABLES, and xt-core-export (core-export.lisp), run after it, carries
;;; exactly those (and the host's install tables) in the world snapshot with
;;; a digest per row (X3).  This walk is the one discovery of carried tables.
(in-package "ACL2")
(require :sb-cltl2)

;;; ------------------------------------------------------------------------
;;; SHA-256 (FIPS 180-4) over a string of Latin-1 characters.  Checked against
;;; hashlib in tests/test_extract_forms.py.
(defvar *fe-k256*
  #(#x428a2f98 #x71374491 #xb5c0fbcf #xe9b5dba5 #x3956c25b #x59f111f1 #x923f82a4 #xab1c5ed5
    #xd807aa98 #x12835b01 #x243185be #x550c7dc3 #x72be5d74 #x80deb1fe #x9bdc06a7 #xc19bf174
    #xe49b69c1 #xefbe4786 #x0fc19dc6 #x240ca1cc #x2de92c6f #x4a7484aa #x5cb0a9dc #x76f988da
    #x983e5152 #xa831c66d #xb00327c8 #xbf597fc7 #xc6e00bf3 #xd5a79147 #x06ca6351 #x14292967
    #x27b70a85 #x2e1b2138 #x4d2c6dfc #x53380d13 #x650a7354 #x766a0abb #x81c2c92e #x92722c85
    #xa2bfe8a1 #xa81a664b #xc24b8b70 #xc76c51a3 #xd192e819 #xd6990624 #xf40e3585 #x106aa070
    #x19a4c116 #x1e376c08 #x2748774c #x34b0bcb5 #x391c0cb3 #x4ed8aa4a #x5b9cca4f #x682e6ff3
    #x748f82ee #x78a5636f #x84c87814 #x8cc70208 #x90befffa #xa4506ceb #xbef9a3f7 #xc67178f2))

(defun fe-sha256-hex (string)
  (let* ((n (length string))
         (bytes (make-array (* 64 (ceiling (+ n 9) 64)) :element-type '(unsigned-byte 8) :initial-element 0))
         (h (make-array 8 :initial-contents '(#x6a09e667 #xbb67ae85 #x3c6ef372 #xa54ff53a
                                              #x510e527f #x9b05688c #x1f83d9ab #x5be0cd19)))
         (w (make-array 64)))
    (dotimes (i n)
      (let ((c (char-code (char string i))))
        (when (> c 255) (error "fe-sha256: non-Latin-1 character in a hashed unit: ~s" (char string i)))
        (setf (aref bytes i) c)))
    (setf (aref bytes n) #x80)
    (let ((bits (* 8 n)) (len (length bytes)))
      (dotimes (i 8) (setf (aref bytes (- len 1 i)) (ldb (byte 8 (* 8 i)) bits))))
    (flet ((rotr (x k) (logior (ldb (byte 32 0) (ash x (- k))) (ldb (byte 32 0) (ash x (- 32 k)))))
           (add (&rest xs) (ldb (byte 32 0) (apply #'+ xs))))
      (loop for off from 0 below (length bytes) by 64
            do (dotimes (i 16)
                 (setf (aref w i) (logior (ash (aref bytes (+ off (* 4 i))) 24) (ash (aref bytes (+ off (* 4 i) 1)) 16)
                                          (ash (aref bytes (+ off (* 4 i) 2)) 8) (aref bytes (+ off (* 4 i) 3)))))
               (loop for i from 16 below 64
                     do (let* ((w15 (aref w (- i 15))) (w2 (aref w (- i 2)))
                               (s0 (logxor (rotr w15 7) (rotr w15 18) (ash w15 -3)))
                               (s1 (logxor (rotr w2 17) (rotr w2 19) (ash w2 -10))))
                          (setf (aref w i) (add (aref w (- i 16)) s0 (aref w (- i 7)) s1))))
               (let ((a (aref h 0)) (b (aref h 1)) (c (aref h 2)) (d (aref h 3))
                     (e (aref h 4)) (f (aref h 5)) (g (aref h 6)) (hh (aref h 7)))
                 (dotimes (i 64)
                   (let* ((s1 (logxor (rotr e 6) (rotr e 11) (rotr e 25)))
                          (ch (logxor (logand e f) (logand (ldb (byte 32 0) (lognot e)) g)))
                          (t1 (add hh s1 ch (aref *fe-k256* i) (aref w i)))
                          (s0 (logxor (rotr a 2) (rotr a 13) (rotr a 22)))
                          (maj (logxor (logand a b) (logand a c) (logand b c)))
                          (t2 (add s0 maj)))
                     (setq hh g g f f e e (add d t1) d c c b b a a (add t1 t2))))
                 (setf (aref h 0) (add (aref h 0) a) (aref h 1) (add (aref h 1) b)
                       (aref h 2) (add (aref h 2) c) (aref h 3) (add (aref h 3) d)
                       (aref h 4) (add (aref h 4) e) (aref h 5) (add (aref h 5) f)
                       (aref h 6) (add (aref h 6) g) (aref h 7) (add (aref h 7) hh)))))
    (format nil "~(~{~8,'0x~}~)" (coerce h 'list))))

;;; ------------------------------------------------------------------------
;;; canonical printing
(defvar *fe-dummy-pkg* (or (find-package "XT-FE-DUMMY") (make-package "XT-FE-DUMMY" :use nil)))

(defun fe-canon (x)
  "X with each uninterned symbol replaced by one fresh G<n>, numbered by first occurrence."
  (let ((map (make-hash-table :test 'eq)) (n 0))
    (labels ((go-x (x)
               (cond ((and (symbolp x) x (null (symbol-package x)))
                      (or (gethash x map) (setf (gethash x map) (make-symbol (format nil "G~d" (incf n))))))
                     ;; oneify-cltl-code's local function names come from acl2-gentemp's global counter
                     ;; (gentemp)'s T<n> names (interface-raw.lisp:2635) likewise
                     ((and (symbolp x) x (eq (symbol-package x) (find-package "ACL2"))
                           (> (length (symbol-name x)) 1) (char= (char (symbol-name x) 0) #\T)
                           (every #'digit-char-p (subseq (symbol-name x) 1)))
                      (or (gethash x map) (setf (gethash x map) (intern (format nil "XTGT~d" (incf n)) "ACL2"))))
                     ((and (symbolp x) x (eq (symbol-package x) (find-package "ACL2"))
                           (> (length (symbol-name x)) 6) (string= "ONEIFY" (symbol-name x) :end2 6)
                           (every #'digit-char-p (subseq (symbol-name x) 6)))
                      (or (gethash x map) (setf (gethash x map) (intern (format nil "ONEIFY~d" (incf n)) "ACL2"))))
                     ((consp x) (cons (go-x (car x)) (go-x (cdr x))))
                     (t x))))
      (go-x x))))

(defun fe-text (x)
  (let ((*package* *fe-dummy-pkg*) (*print-circle* t) (*print-readably* t) (*print-pretty* nil)
        (*print-case* :upcase) (*print-length* nil) (*print-level* nil)
        (*read-default-float-format* 'single-float) (*print-base* 10) (*print-radix* nil))
    (prin1-to-string (fe-canon x))))

;;; ------------------------------------------------------------------------
;;; the world's raw installations (interface-raw.lisp add-trip)
(defvar *fe-w* nil)
(defvar *fe-defs* nil)       ; f -> (mode ignorep def)
(defvar *fe-stobj-raw* nil)  ; f -> (kind stobj def)   kind :raw-defun :raw-abbrev :abs-macro
(defvar *fe-stobj-ax* nil)   ; f -> (stobj def)
(defvar *fe-stobj-cmds* nil) ; newest first
(defvar *fe-consts* nil)     ; name -> defconst cmd
(defvar *fe-attach* nil)     ; f -> attachment cltl entry
(defvar *fe-macros* nil)
(defvar *fe-stobj-live* nil) ; the live variable symbols of the stobjs (defined by their stobj: units)     ; name -> defmacro cltl cmd

(defun fe-index-world ()
  (setq *fe-w* (w *the-live-state*)
        *fe-defs* (make-hash-table :test 'eq) *fe-stobj-raw* (make-hash-table :test 'eq)
        *fe-stobj-ax* (make-hash-table :test 'eq) *fe-stobj-cmds* nil
        *fe-consts* (make-hash-table :test 'eq) *fe-attach* (make-hash-table :test 'eq)
        *fe-macros* (make-hash-table :test 'eq))
  (dolist (trip *fe-w*)
    (when (and (eq (car trip) 'cltl-command) (eq (cadr trip) 'global-value) (consp (cddr trip)))
      (let ((cmd (cddr trip)))
        (case (car cmd)
          (defuns (dolist (def (cdddr cmd))
                    (unless (gethash (car def) *fe-defs*)
                      (setf (gethash (car def) *fe-defs*) (list (cadr cmd) (caddr cmd) def)))))
          ((defstobj defabsstobj) (push cmd *fe-stobj-cmds*))
          (defconst (unless (gethash (cadr cmd) *fe-consts*) (setf (gethash (cadr cmd) *fe-consts*) cmd)))
          (defmacro (unless (gethash (cadr cmd) *fe-macros*) (setf (gethash (cadr cmd) *fe-macros*) cmd)))
          (attachment (dolist (x (cdr cmd))
                        (let ((n (if (symbolp x) x (car x))))
                          (unless (or (gethash n *fe-attach*) (eq n *special-cltl-cmd-attachment-mark-name*))
                            (setf (gethash n *fe-attach*) x)))))))))
  (setq *fe-stobj-live* (make-hash-table :test 'eq))
  (setq *fe-stobj-cmds* (nreverse *fe-stobj-cmds*))   ; newest first, as walked
  (setq *fe-stobj-cmds* (nreverse *fe-stobj-cmds*))
  (dolist (cmd *fe-stobj-cmds*)
    (setf (gethash (nth 2 cmd) *fe-stobj-live*) t)
    (let ((absp (eq (car cmd) 'defabsstobj)) (name (nth 1 cmd)))
      (dolist (d (nth 4 cmd))
        (unless (gethash (car d) *fe-stobj-raw*)
          (setf (gethash (car d) *fe-stobj-raw*)
                (list (cond (absp :abs-macro) ((member-equal *stobj-inline-declare* d) :raw-abbrev) (t :raw-defun))
                      name d))))
      (dolist (d (nth 6 cmd))
        (unless (gethash (car d) *fe-stobj-ax*) (setf (gethash (car d) *fe-stobj-ax*) (list name d)))))))

(defun fe-qq-expand (form)
  "FORM with every SB-INT:QUASIQUOTE outside a quote macroexpanded: this SBCL's macroexpand-all leaves
quasiquote (and the macros inside its commas) alone."
  (cond ((atom form) form)
        ((eq (car form) 'quote) form)
        ((eq (car form) 'sb-int:quasiquote) (fe-qq-expand (macroexpand-1 form)))
        (t (let ((a (fe-qq-expand (car form))) (d (fe-qq-expand (cdr form))))
             (if (and (eq a (car form)) (eq d (cdr form))) form (cons a d))))))

(defun fe-expand-def (def)
  "(defun NAME FORMALS . BODY) with BODY macroexpanded by this image's SBCL; DEF is (NAME FORMALS . BODY)."
  (let* ((e (sb-cltl2:macroexpand-all (fe-qq-expand `(lambda ,(cadr def) ,@(cddr def)))))
         (lam (if (eq (car e) 'function) (cadr e) e)))
    (list* 'defun (car def) (cadr lam) (cddr lam))))

(defun fe-expand-body-form (form) (sb-cltl2:macroexpand-all (fe-qq-expand form)))

;;; ------------------------------------------------------------------------
;;; ACL2's source files: the forms ACL2 compiled where the world holds none
(defvar *fe-src* nil)        ; symbol -> (kind symbol form file line)
(defvar *fe-src-sha* nil)    ; file name -> sha256 of the file's bytes (Latin-1)

(defun fe-file-string (path)
  (with-open-file (s path :external-format :latin-1)
    (let* ((n (file-length s)) (str (make-string n)) (m (read-sequence str s))) (subseq str 0 m))))

(defparameter *fe-no-expand-heads*
  '(defthm defthmd defstobj defabsstobj defabsstobj-missing-events defpkg in-package declaim
    deflabel defaxiom defchoose defattach defstub defproxy defmacro defun defvar defparameter
    defconstant defg proclaim include-book value-triple local skip-proofs
    defrec in-theory deftheory encapsulate table verify-termination-boot-strap
    verify-guards defdoc))

(defun fe-struct-names (form)
  "The function names a (defstruct NAME-or-(NAME . OPTS) . SLOTS) form defines (default conc-name/constructor/predicate/copier)."
  (let* ((spec (cadr form)) (name (if (consp spec) (car spec) spec)) (opts (if (consp spec) (cdr spec) nil))
         (conc (let ((o (find-if (lambda (o) (and (consp o) (eq (car o) :conc-name))) opts)))
                 (if o (and (cadr o) (string (cadr o))) (format nil "~a-" (symbol-name name)))))
         (slots (mapcar (lambda (x) (if (consp x) (car x) x))
                        (remove-if #'stringp (cddr form))))
         (ctor (let ((o (find-if (lambda (o) (and (consp o) (eq (car o) :constructor))) opts)))
                 (if (and o (cadr o)) (cadr o) (intern (format nil "MAKE-~a" (symbol-name name)) (symbol-package name)))))
         (out (list ctor (intern (format nil "~a-P" (symbol-name name)) (symbol-package name))
                    (intern (format nil "COPY-~a" (symbol-name name)) (symbol-package name)))))
    (dolist (sl slots) (push (intern (format nil "~a~a" (or conc "") (symbol-name sl)) (symbol-package name)) out))
    out))

(defun fe-harvest (form file line acc depth &aux (start (car line)) (end (cdr line)))
  "Record in (car ACC) the defuns and variables a top-level FORM of FILE installs."
  (when (consp form)
    (let ((op (car form)))
      (cond ((eq op 'progn) (dolist (f (cdr form)) (fe-harvest f file line acc depth)))
            ((eq op 'eval-when) (dolist (f (cddr form)) (fe-harvest f file line acc depth)))
            ((eq op 'encapsulate) (dolist (f (cddr form)) (fe-harvest f file line acc depth)))
            ((eq op 'defstruct)
             (let* ((spec (cadr form)) (name (if (consp spec) (car spec) spec)))
               (push (list :struct name form file (fe-locate-line name start end)) (car acc))
               (dolist (g (fe-struct-names form))
                 (push (list :struct-member g form file (fe-locate-line name start end) name) (car acc)))))
            ((eq op 'mutual-recursion) (dolist (f (cdr form)) (fe-harvest f file line acc depth)))
            ((eq op 'defun) (push (list :defun (cadr form) form file (fe-locate-line (cadr form) start end)) (car acc)))
            ((member op '(defvar defparameter defconstant defg))
             (push (list :var (cadr form) form file (fe-locate-line (cadr form) start end)) (car acc)))
            ((and (symbolp op) op (< depth 5) (macro-function op) (not (member op *fe-no-expand-heads*)))
             (let ((exp (ignore-errors (macroexpand-1 form))))
               (when (and exp (not (eq exp form)))
                 (fe-harvest exp file line acc (1+ depth)))))))))

(defun fe-line-of (starts pos)
  (let ((lo 0) (hi (1- (length starts))))
    (loop while (< lo hi)
          do (let ((mid (ceiling (+ lo hi) 2))) (if (<= (aref starts mid) pos) (setq lo mid) (setq hi (1- mid)))))
    (1+ lo)))

(defvar *fe-read-errors* nil)
(defvar *fe-text* nil)
(defvar *fe-starts* nil)
(defun fe-locate-line (sym start end)
  "Line of the first (defun|defstruct|defvar|... SYM inside [START,END) of the current file text; the form's own line else."
  (let* ((n (symbol-name sym)) (best nil))
    (dolist (head '("defun" "defun-one-output" "defstruct" "defvar" "defparameter" "defconstant" "defg" "defn"))
      (dolist (pre '("(" "((" "( (" "(("))
        (let ((p (search (if (string= pre "( (") (format nil "(~a (~a" head (string-downcase n)) (format nil "~a~a ~a" pre head (string-downcase n))) *fe-text* :start2 start :end2 (min end (length *fe-text*)) :test #'char-equal)))
          (when (and p (or (null best) (< p best))) (setq best p)))))
    (fe-line-of *fe-starts* (or best start))))
(defun fe-form-start (text pos end form)
  "POS is where the reader began; when a #+/#- expression was skipped, FORM starts later: the first
column-0 open paren in [POS,END) from which the reader yields FORM."
  (if (char/= (char text pos) #\#) pos
      (loop for i from pos below end
            do (when (and (char= (char text i) #\() (or (= i 0) (char= (char text (1- i)) #\Newline)))
                 (let ((f (ignore-errors (let ((*package* (find-package "ACL2")) (*read-eval* t)
                                                (*read-default-float-format* 'single-float))
                                            (values (read-from-string text t nil :start i))))))
                   (when (equal f form) (return i))))
            finally (return pos))))
(defun fe-read-file-forms (path)
  "Top-level forms of PATH read under this image's reader (its *features*): list of (form start end), character offsets;
sets *fe-text* and *fe-starts*."
  (let* ((text (fe-file-string path)) (starts (make-array 1 :adjustable t :fill-pointer 1 :initial-element 0)) (out nil))
    (dotimes (i (length text)) (when (char= (char text i) #\Newline) (vector-push-extend (1+ i) starts)))
    (setq *fe-text* text *fe-starts* starts)
    (with-input-from-string (s text)
      (let ((*package* (find-package "ACL2")) (*readtable* (copy-readtable nil)) (*read-eval* t)
            (*read-default-float-format* 'single-float))
        (loop
          (let ((c (peek-char t s nil :eof)))
            (cond ((eq c :eof) (return))
                  ((char= c #\;) (read-line s nil))
                  (t (let* ((pos (file-position s))
                            (form (handler-case (read s nil :eof) (error (e) (push (list path (fe-line-of starts pos) (princ-to-string e)) *fe-read-errors*) :read-error))))
                       (when (eq form :eof) (return))
                       (unless (eq form :read-error)
                         (let ((st (fe-form-start text pos (file-position s) form)))
                           (push (list form st (file-position s)) out))))))))))
    (nreverse out)))

(defun fe-index-sources (dir)
  (setq *fe-src* (make-hash-table :test 'eq) *fe-src-sha* (make-hash-table :test 'equal))
  ;; acl2-fns is loaded before the *acl2-files* (acl2.lisp), the raw-Lisp files after them
  (dolist (name (append '("acl2" "acl2-fns" "acl2-init") (symbol-value 'acl2::*acl2-files*) '("float-raw" "multi-threading-raw")))
    (let ((path (format nil "~a/~a.lisp" dir name)))
      (when (probe-file path)
        (setf (gethash name *fe-src-sha*) (fe-sha256-hex (fe-file-string path)))
        (dolist (fl (fe-read-file-forms path))
          (let ((acc (list nil)))
            (fe-harvest (car fl) name (cons (cadr fl) (caddr fl)) acc 0)
            (dolist (e (reverse (car acc)))
              (setf (gethash (cadr e) *fe-src*) e))))))))   ; later files load later and win

(defun fe-src-origin (e)
  (format nil "src:~a.lisp:~d:~a" (fourth e) (fifth e) (gethash (fourth e) *fe-src-sha*)))

;;; ------------------------------------------------------------------------
;;; the host runtime: the names clruntime.lisp defines
(defvar *fe-rt* nil)         ; name -> :function / :variable / :macro

(defun fe-read-runtime (path)
  (setq *fe-rt* (make-hash-table :test 'eq))
  (with-open-file (s path :external-format :utf-8)
    (let ((*package* (find-package "ACL2")) (*read-eval* nil))
      (loop for form = (read s nil :eof) until (eq form :eof)
            do (when (consp form)
                 (case (car form)
                   (defun (setf (gethash (cadr form) *fe-rt*) :function))
                   (defmacro (setf (gethash (cadr form) *fe-rt*) :macro))
                   ((defvar defparameter defconstant) (setf (gethash (cadr form) *fe-rt*) :variable))))))))

;;; ------------------------------------------------------------------------
;;; free names of an expanded form
(defun fe-world-function-p (s)
  "S names a function of the extraction world: the raw symbol, or a *1* symbol of one."
  (let ((f (if (fe-star1-p s) (fe-star1-of s) s)))
    (and (symbolp f) (or (gethash f *fe-defs*) (getpropc f 'formals nil *fe-w*)) t)))

(defun fe-calls (form fns vars)
  "Record the function names a macroexpanded FORM calls in FNS, and in VARS every symbol atom outside quote and
every special variable a let, let* or lambda binds."
  (labels ((walk (x locals)
             (cond ((symbolp x) (when (and x (not (eq x t))) (setf (gethash x vars) t)))
                   ((atom x) nil)
                   (t (let ((op (car x)))
                        (case op
                          (quote nil)
                          (function (cond ((symbolp (cadr x)) (note (cadr x) locals))
                                          ((and (consp (cadr x)) (eq (car (cadr x)) 'lambda)) (walk (cadr x) locals))))
                          (lambda (bound-specials (cadr x)) (walk-body (cddr x) locals))
                          ((let let*) (bound-specials (mapcar (lambda (b) (if (consp b) (car b) b)) (cadr x)))
                           (dolist (b (cadr x)) (when (consp b) (walk (cadr b) locals)))
                           (walk-body (cddr x) locals))
                          ((flet labels)
                           (let ((l2 (append (mapcar #'car (cadr x)) locals)))
                             (dolist (f (cadr x)) (walk-body (cddr f) (if (eq op 'flet) locals l2)))
                             (walk-body (cddr x) l2)))
                          (block (walk-body (cddr x) locals))
                          (return-from (walk (caddr x) locals))
                          (the (walk (caddr x) locals))
                          (tagbody (dolist (y (cdr x)) (when (consp y) (walk y locals))))
                          (go nil)
                          (declare nil)
                          (load-time-value (walk (cadr x) locals))
                          (eval-when (walk-body (cddr x) locals))
                          (progv (walk (cadr x) locals) (walk (caddr x) locals) (walk-body (cdddr x) locals))
                          ;; (funcall 'F ...) / (apply 'F ...): ACL2's ec-call expands to these over a *1*
                          ;; symbol, so F is called though only quoted.  Counted when F names a function of the
                          ;; world (ec-call also tries F$INLINE behind fboundp, which may name nothing).
                          ((funcall apply)
                           (let ((f (cadr x)))
                             (when (and (consp f) (eq (car f) 'quote) (symbolp (cadr f)) (fe-world-function-p (cadr f)))
                               (note (cadr f) locals)))
                           (dolist (y (cdr x)) (walk y locals)))
                          (t (cond ((member op '(if progn setq catch throw unwind-protect multiple-value-prog1
                                                 multiple-value-call locally))
                                    (dolist (y (cdr x)) (walk y locals)))
                                   (t (if (symbolp op) (note op locals) (walk op locals))
                                      (dolist (y (cdr x)) (walk y locals))))))))))
           (walk-body (b locals) (dolist (y b) (walk y locals)))
           ;; a binding of a special variable is a reference to it: without the variable's declaration
           ;; bare SBCL compiles the binding as lexical, invisible to the functions that read it
           (bound-specials (names)
             (dolist (v names)
               (when (and (symbolp v) v (not (member v lambda-list-keywords))
                          (eq (sb-int:info :variable :kind v) :special))
                 (setf (gethash v vars) t))))
           (note (s locals) (unless (member s locals) (setf (gethash s fns) t))))
    (walk form nil)))

(defun fe-walkable (form)
  "The part of a top-level FORM whose symbols are references: a defun/defmacro is its lambda (the name and
lambda list are bindings, not calls); a variable definition is its value form; a declaim has none."
  (case (car form)
    ((defun defmacro) `(lambda ,@(cddr form)))
    ((defparameter defvar defconstant sb-ext:defglobal) (if (cddr form) (caddr form) nil))
    ((declaim defstruct) nil)
    (t form)))

(defun fe-pkg (s) (and (symbolp s) (symbol-package s) (package-name (symbol-package s))))
(defun fe-star1-p (s)
  (let ((p (fe-pkg s))) (and p (> (length p) 9) (string= (subseq p 0 9) "ACL2_*1*_"))))
(defun fe-star1-of (s)   ; *1* symbol -> original function symbol
  (intern (symbol-name s) (subseq (fe-pkg s) 9)))
(defun fe-cl-or-sb-p (s)
  (let ((p (fe-pkg s))) (and p (or (string= p "COMMON-LISP") (string= p "KEYWORD")
                                   (and (> (length p) 3) (string= (subseq p 0 3) "SB-"))))))
(defun fe-earmuffed-p (s)
  (let ((n (symbol-name s))) (and (> (length n) 2) (char= (char n 0) #\*) (char= (char n (1- (length n))) #\*))))

;;; ------------------------------------------------------------------------
;;; units: an id, the forms, an origin
(defvar *fe-phase* "start")
(defvar *fe-last-unit* nil)
(defvar *fe-deadline-timer* nil)
(defun fe-arm-deadline (seconds)
  "Fail closed after SECONDS: print the phase and the last unit emitted, then exit 124.  The export is
measured at about 80 s on hbox (index 5 s, closure 60 s, write 10 s); core.sh passes 900.  xt-fe-export
disarms it when it returns, so it bounds this export and not the xt-core-export that follows."
  (when (and seconds (plusp seconds))
    (let ((main sb-thread:*current-thread*))
      (sb-ext:schedule-timer
       (setq *fe-deadline-timer*
             (sb-ext:make-timer (lambda ()
                                  (format t "~&XT-FE TIMEOUT after ~d s: phase ~a, last unit ~a~%" seconds *fe-phase* *fe-last-unit*)
                                  (finish-output)
                                  (sb-ext:exit :code 124 :abort t))
                                :thread main))
       seconds))))
(defun fe-log (what) (setq *fe-phase* what) (format t "~&XT-FE-LOG ~d ~a~%" (floor (get-internal-real-time) internal-time-units-per-second) what) (finish-output))
(defun fe-id (kind sym) (format nil "~a:~a::~a" (string-downcase (string kind)) (fe-pkg sym) (symbol-name sym)))

(defun fe-id-sym (id)
  "The (kind . symbol) an id like raw:ACL2::F names."
  (let* ((c (position #\: id)) (kind (subseq id 0 c)) (rest (subseq id (1+ c)))
         (cc (search "::" rest)))
    (if cc
        (cons kind (let ((s (find-symbol (subseq rest (+ cc 2)) (subseq rest 0 cc))))
                     (or s (error "xt-verify-defs: unit ~a names no symbol" id))))
        (cons kind nil))))

(defun fe-prologue-forms ()
  ;; acl2.lisp lines 2704-2705; *acl2-optimize-form* (acl2.lisp)
  (list '(in-package "ACL2")   ; defstruct interns its accessors in *package*
        '(declaim (declaration xargs))
        '(declaim (declaration irrelevant))
        '(declaim (optimize (compilation-speed 0) (speed 3) (space 1) (safety 0)))))

(defun fe-derive-raw (f)
  "(forms . origin) of F's raw definition, or NIL."
  (let ((e (gethash f *fe-defs*)) (s (gethash f *fe-stobj-raw*)))
    (cond ((and e (not (cadr e))) (cons (list (fe-expand-def (caddr e))) "world:defuns"))
          ((and s (eq (car s) :abs-macro))
           (cons (list (cons 'defmacro (cdr (fe-expand-def (caddr s))))) (format nil "world:abs-macro:~a" (fe-id :st (cadr s)))))
          ((and s (member (car s) '(:raw-defun :raw-abbrev)))
           (cons (list (fe-expand-def (if (eq (car s) :raw-abbrev) (remove-stobj-inline-declare (caddr s)) (caddr s))))
                 (format nil "world:~a:~a" (if (eq (car s) :raw-abbrev) "stobj-abbrev" "stobj-raw") (fe-id :st (cadr s)))))
          (t (let ((src (gethash f *fe-src*)))
               (when (and src (eq (car src) :defun))
                 (cons (list (fe-expand-def (cdr (third src)))) (fe-src-origin src))))))))

(defun fe-derive-struct (name)
  "The defstruct source form, unexpanded: its expansion is SBCL's own internals, defined identically by this SBCL."
  (let ((src (gethash name *fe-src*)))
    (when (and src (eq (car src) :struct)) (cons (list (third src)) (fe-src-origin src)))))

(defun fe-derive-star1 (f)
  (let ((e (gethash f *fe-defs*)) (ax (gethash f *fe-stobj-ax*)))
    (flet ((oneified (mode def stobj)
             (let ((o (oneify-cltl-code mode def stobj *fe-w*)))
               (list (fe-expand-def o)))))
      (cond (e (cons (oneified (car e) (caddr e) (if (consp (cadr e)) (cdr (cadr e)) nil)) "world:oneify"))
            (ax (cons (oneified :logic (cadr ax) (car ax)) "world:oneify-stobj"))
            (t (let ((src (gethash (*1*-symbol f) *fe-src*)))
                 (when (and src (eq (car src) :defun))
                   (cons (list (fe-expand-def (cdr (third src)))) (fe-src-origin src)))))))))

(defun fe-var-form (head name init)
  (list head name (fe-expand-body-form init)))

(defun fe-derive-var (v)
  (let ((c (gethash v *fe-consts*)) (src (gethash v *fe-src*)))
    (cond (c (let ((form (ifat-defparameter (cadr c) (cadddr c) (caddr c))))
               (cons (list (list (car form) (cadr form) (fe-expand-body-form (caddr form)))) "world:defconst")))
          ((and src (eq (car src) :var))
           (let* ((form (third src)) (head (car form)))
             (cons (list (cond ((eq head 'defg) (list 'sb-ext:defglobal (cadr form) (fe-expand-body-form (caddr form))))
                               ((cddr form) (fe-var-form head (cadr form) (caddr form)))
                               (t (list head (cadr form))))) (fe-src-origin src)))))))

(defun fe-derive-attach (f)
  (let ((x (gethash f *fe-attach*)))
    (when x
      (let ((form (if (symbolp x) (set-attachment-symbol-form x nil) (set-attachment-symbol-form (car x) (cdr x)))))
        (cons (list (if (eq (car form) 'defparameter)
                        (list 'defparameter (cadr form) (fe-expand-body-form (caddr form)))
                      (fe-expand-body-form form)))
              "world:attachment")))))

(defun fe-derive-stobj (name)
  (let ((cmd (find name *fe-stobj-cmds* :key #'cadr)))
    (when cmd
      (cons (list (list 'defparameter (nth 2 cmd) (fe-expand-body-form (nth 3 cmd))))
            (format nil "world:~(~a~)" (car cmd))))))

(defun fe-derive-macro (name)
  (let ((cmd (gethash name *fe-macros*)))
    (when cmd
      (let* ((body (cdddr cmd)) (pre nil))
        (loop while (and body (or (stringp (car body)) (and (consp (car body)) (eq (caar body) 'declare))))
              do (push (pop body) pre))
        (cons (list `(defmacro ,name ,(caddr cmd) ,@(reverse pre) ,@(cdr (fe-expand-body-form `(progn ,@body)))))
              "world:defmacro")))))

(defun fe-derive-inline-decls (f)
  "F's inline proclamation as the image's SBCL holds it.  ACL2 proclaims its own: defun-inline's
F$INLINE / F$NOTINLINE names, the ext-gen-barriers, and the built-ins it declaims inline in raw Lisp
(ACL2 8.7 axioms.lisp:1563: ifix, nfix, zp, natp, posp, len, fix, ...), which SBCL records as F's
:inlinep.  Without them every such call in fn-core is a full call, and a caller's declared types no
longer reach the callee's arithmetic (EXTRACTION-PROGRAM-20261007.md, extract-prof)."
  (let* ((n (symbol-name f))
         (sbcl (sb-int:info :function :inlinep f))
         (inline (or (inline-namep n) (eq sbcl 'inline)))
         (notinline (or (notinline-namep n) (eq sbcl 'notinline)
                        (member-eq f (global-val 'ext-gen-barriers *fe-w*)))))
    (cond (notinline (list `(declaim (notinline ,f))))
          (inline (list `(declaim (inline ,f)))))))

(defun fe-registry-forms (stobj-names all-names)
  `((defun xl-make-live-stobjs ()
      (unless *xl-live-stobjs-initialized-p*
        (setq *xl-user-stobj-alist*
              (list ,@(mapcar (lambda (n) `(cons ',n ,(nth 2 (find n *fe-stobj-cmds* :key #'cadr)))) stobj-names)))
        (setq *xl-live-stobjs-initialized-p* t))
      *xl-user-stobj-alist*)
    (xl-register-stobj-names ',all-names)))

(defun fe-specials-from-ids (ids)
  "The special variables the var: and stobj: units among IDS define (declared before any function is compiled)."
  (let ((out nil))
    (dolist (id ids)
      (cond ((or (eql 0 (search "var:" id)) (eql 0 (search "global:" id))) (push (cdr (fe-id-sym id)) out))
            ((eql 0 (search "attach:" id)) (push (*1*-symbol (cdr (fe-id-sym id))) out))
            ((eql 0 (search "stobj:" id)) (let ((c (find (cdr (fe-id-sym id)) *fe-stobj-cmds* :key #'cadr))) (when c (push (nth 2 c) out))))))
    (sort (remove-duplicates out) #'string< :key (lambda (s) (format nil "~a::~a" (fe-pkg s) (symbol-name s))))))

(defun fe-star1-var-refs (forms-lists)
  "The *1* symbols emitted forms use as variables (throw-or-attach reads a constrained function's *1* cell)."
  (let ((out nil))
    (dolist (forms forms-lists)
      (let ((fns (make-hash-table :test 'eq)) (vars (make-hash-table :test 'eq)))
        (dolist (f forms) (fe-calls (fe-walkable f) fns vars))
        (maphash (lambda (s v) (declare (ignore v)) (when (fe-star1-p s) (pushnew s out))) vars)))
    out))

(defun fe-derive-unit (id &optional stobj-names specials)
  "(forms . origin) of unit ID; the single point both the export and xt-verify-defs derive through."
  (let* ((ks (fe-id-sym id)) (kind (car ks)) (sym (cdr ks)))
    (cond ((string= kind "raw") (fe-derive-raw sym))
          ((string= kind "star1") (fe-derive-star1 sym))
          ((string= kind "var") (fe-derive-var sym))
          ((string= kind "struct") (fe-derive-struct sym))
          ((string= kind "attach") (fe-derive-attach sym))
          ((string= kind "stobj") (fe-derive-stobj sym))
          ((string= kind "macro") (fe-derive-macro sym))
          ((string= kind "decl") (cond ((string= id "decl:specials")
                                        (cons (append
                                                (mapcar (lambda (v)
                                                          (let ((d (fe-derive-var v)))
                                                            (if (and d (eq (car (car (car d))) 'sb-ext:defglobal))
                                                                `(declaim (sb-ext:global ,v))
                                                                `(declaim (special ,v)))))
                                                        (sort (remove-duplicates specials) #'string< :key (lambda (v) (format nil "~a::~a" (fe-pkg v) (symbol-name v)))))
                                                ;; defstobj's (or (boundp var) (eval `(defg ,var nil))), var = (st-lst name)
                                                (mapcar (lambda (n) (fe-expand-body-form `(defg ,(st-lst n) nil))) stobj-names))
                                              "world:defconst,source:defvar"))
                                       ((string= id "decl:prologue") (cons (fe-prologue-forms) "acl2.lisp:2704-2705,*acl2-optimize-form*"))
                                       (t (cons (fe-derive-inline-decls sym) "world:inlinep"))))
          ((string= kind "global")
           ;; the cell's value in the extraction world's session, as the image's LD has it at its
           ;; :return-from-lp form.  A global the session has not bound (the host binds fn's own at
           ;; run time) is declared and left unbound, as in the image.  The world itself is a gap.
           (let ((g (fe-global-of sym)))
             (cond ((eq g 'current-acl2-world) nil)
                   ((boundp-global g *the-live-state*)
                    (cons (list `(defparameter ,sym ',(f-get-global g *the-live-state*))) "world:state-global"))
                   (t (cons (list `(defvar ,sym)) "world:state-global-unbound")))))
          ((string= kind "guard")
           ;; the guard ACL2 prints when a primitive's *1* finds its guard false (guard-raw,
           ;; translate.lisp:7616), untranslated here in the world; clruntime.lisp's guard-raw reads it
           (cons (list `(setf (gethash ',sym *xl-guard-raw*) ',(guard-raw sym *fe-w*))) "world:guard-raw"))
          ((string= kind "registry")
           (cons (fe-registry-forms stobj-names (fe-all-stobj-names)) "world:defstobj-registry"))
          (t (error "unknown unit kind in ~a" id)))))

(defun fe-all-stobj-names ()
  (let ((out nil)) (dolist (c *fe-stobj-cmds*) (pushnew (cadr c) out)) (sort out #'string< :key #'symbol-name)))

(defun fe-unit-text (forms)
  (with-output-to-string (o)
    (dolist (f forms) (write-string (fe-text f) o) (terpri o))))

(defun fe-header (id) (format nil ";;;; UNIT ~a~%" id))

;;; ------------------------------------------------------------------------
;;; the closure
(defstruct (fe-run (:conc-name fr-)) units order gaps rt-refs stobjs edges tables)

(defun fe-stobj-closure (names)
  "NAMES plus the foundations of abstract stobjs and nested stobj field types (frontend.lisp)."
  (xt-stobj-closure-1 names nil *fe-w*))

(defun fe-global-symbol-p (s)
  "S is a state global's cell, X's name in ACL2_GLOBAL_<pkg> (acl2-fns.lisp:75 global-symbol)."
  (let ((p (fe-pkg s))) (and p (> (length p) 12) (string= (subseq p 0 12) "ACL2_GLOBAL_"))))

(defun fe-global-of (s)
  "The state global whose cell S is."
  (intern (symbol-name s) (subseq (fe-pkg s) 12)))

(defun fe-table-subjects (form fn)
  "Call FN on T for each (table-alist (quote T) ...) inside FORM."
  (cond ((atom form) nil)
        ((and (eq (car form) 'table-alist) (consp (cdr form)) (consp (cadr form))
              (eq (car (cadr form)) 'quote) (symbolp (cadr (cadr form))))
         (funcall fn (cadr (cadr form))))
        (t (loop for x on form while (consp x) do (fe-table-subjects (car x) fn)))))

(defun fe-guard-raw-subjects (form fn)
  "Call FN on F for each (guard-raw (quote F) ...) inside FORM."
  (cond ((atom form) nil)
        ((and (eq (car form) 'guard-raw) (consp (cdr form)) (consp (cadr form))
              (eq (car (cadr form)) 'quote) (symbolp (cadr (cadr form))))
         (funcall fn (cadr (cadr form))))
        (t (loop for x on form while (consp x) do (fe-guard-raw-subjects (car x) fn)))))

(defun fe-closure (roots stobj-names macro-names)
  "Walk from ROOTS (raw and *1* of each), the named stobjs and macros; return an fe-run."
  (let ((units (make-hash-table :test 'equal)) (order nil) (queue nil)
        (gaps (make-hash-table :test 'equal)) (rt-refs (make-hash-table :test 'eq)) (stobj-set nil)
        (edges (make-hash-table :test 'equal))    ; unit id -> the unit ids its forms reference (edges.tsv)
        (tables nil))   ; every table an emitted form reads by name: the snapshot carries them (core-export.lisp)
    (labels ((enqueue (kind sym why) (push (list kind sym why) queue))
             (edge (why tid) (when (stringp why) (pushnew tid (gethash why edges) :test #'string=)))
             (add-unit (id forms origin)
               (unless (gethash id units)
                 (setq *fe-last-unit* id)
                 (when (zerop (mod (hash-table-count units) 500)) (fe-log (format nil "units ~d queue ~d" (hash-table-count units) (length queue))))
                 (setf (gethash id units) (list forms origin)) (push id order)
                 (let ((fns (make-hash-table :test 'eq)) (vars (make-hash-table :test 'eq)))
                   (dolist (f forms) (fe-calls (fe-walkable f) fns vars))
                   (maphash (lambda (s v) (declare (ignore v)) (ref-fn s id)) fns)
                   (maphash (lambda (s v) (declare (ignore v)) (ref-var s id)) vars)
                   (dolist (f forms) (fe-table-subjects f (lambda (tb) (edge id (fe-id :table tb))
                                                                (pushnew tb tables))))
                   (dolist (f forms) (fe-guard-raw-subjects f (lambda (g) (edge id (fe-id :guard g))
                                                                    (unless (gethash (fe-id :guard g) units)
                                                                      (enqueue "guard" g id)))))
                   (dolist (f forms)    ; attachments name their implementation as quoted data
                     (when (and (eq (car f) 'defparameter) (fe-star1-p (cadr f)) (consp (caddr f))
                                (eq (car (caddr f)) 'quote) (symbolp (cadr (caddr f))))
                       (let ((impl (cadr (caddr f))))
                         (ref-fn impl id) (ref-fn (*1*-symbol impl) id)))))))
             (ref-fn (s why)
               (cond ((null s) nil)
                     ((gethash s *fe-rt*) (setf (gethash s rt-refs) t) (edge why (fe-id :rt s)))
                     ((fe-star1-p s) (let ((b (fe-star1-of s)))
                                       (edge why (fe-id :star1 b))
                                       (unless (gethash (fe-id :star1 b) units) (enqueue "star1" b why))))
                     ((fe-cl-or-sb-p s) nil)
                     (t (let ((src (gethash s *fe-src*)))
                          (if (and src (eq (car src) :struct-member))
                              (progn (edge why (fe-id :struct (sixth src)))
                                     (unless (gethash (fe-id :struct (sixth src)) units) (enqueue "struct" (sixth src) why)))
                              (progn (edge why (fe-id :raw s))
                                     (unless (gethash (fe-id :raw s) units) (enqueue "raw" s why))))))))
             (ref-var (s why)
               (cond ((or (null s) (eq s t) (keywordp s)) nil)
                     ((gethash s *fe-rt*) (setf (gethash s rt-refs) t) (edge why (fe-id :rt s)))
                     ;; a state global's cell: carried with the extraction session's value (global: units)
                     ((fe-global-symbol-p s)
                      (edge why (fe-id :global s))
                      (unless (gethash (fe-id :global s) units) (enqueue "global" s why)))
                     ((fe-cl-or-sb-p s) nil)
                     ((and (fe-earmuffed-p s) (or (gethash s *fe-consts*) (gethash s *fe-src*)))
                      (edge why (fe-id :var s))
                      (unless (gethash (fe-id :var s) units) (enqueue "var" s why)))
                     ((and (fe-earmuffed-p s) (not (fe-star1-p s)) (not (gethash s *fe-stobj-live*)))
                      (setf (gethash (fe-id :var s) gaps) why))))
             (drain ()
               (loop while queue
                     do (destructuring-bind (kind sym why) (pop queue)
                          (let ((id (fe-id kind sym)))
                            (unless (gethash id units)
                              (let ((d (fe-derive-unit id)))
                                (cond (d (add-unit id (car d) (cdr d))
                                         (when (string= kind "raw")
                                           (let ((dd (fe-derive-inline-decls sym)))
                                             (when dd (add-unit (fe-id :decl sym) dd "world:inlinep")))
                                           (dolist (s (stobjs-in sym *fe-w*))
                                             (when (and s (not (eq s 'state))) (pushnew s stobj-set)))
                                           (let ((a (fe-derive-attach sym)))
                                             (when a (add-unit (fe-id :attach sym) (car a) (cdr a))))))
                                      ((fe-cl-or-sb-p sym) nil)
                                      (t (setf (gethash id gaps) why))))))))))
      ;; a *1* exists only for a function of the world; a raw-only root (an extra root from ACL2's
      ;; sources, setup-standard-io) has none
      (dolist (r roots) (enqueue "raw" r :root) (when (fe-world-function-p r) (enqueue "star1" r :root)))
      (dolist (m macro-names) (enqueue "macro" m :root))
      (dolist (st stobj-names) (pushnew st stobj-set))
      (drain)
      (fe-log (format nil "drained: units ~d stobj-set ~d" (hash-table-count units) (length stobj-set)))
      (loop
        (let ((all (remove-if-not (lambda (n) (find n *fe-stobj-cmds* :key #'cadr))
                                  (fe-stobj-closure stobj-set)))
              (grew nil))
          (dolist (n all)
            (unless (gethash (fe-id :stobj n) units) (setq grew t) (enqueue "stobj" n :stobj)))
          (setq stobj-set (union stobj-set all))
          (fe-log (format nil "stobj round: all ~d grew ~a" (length all) grew))
          (unless grew (return))
          (drain)))
      (let ((names (sort (remove-if-not (lambda (n) (gethash (fe-id :stobj n) units)) (copy-list stobj-set))
                         #'string< :key #'symbol-name)))
        (let ((d (fe-derive-unit "registry:" names)))
          (add-unit "registry:" (car d) (cdr d)))
        (make-fe-run :units units :order order :gaps gaps :rt-refs rt-refs :stobjs names :edges edges
                     :tables (sort tables #'string< :key (lambda (s) (format nil "~a::~a" (fe-pkg s) (symbol-name s)))))))))

;;; ------------------------------------------------------------------------
;;; ordering and files
(defun fe-unit-rank (id)
  (cond ((string= id "decl:prologue") 0)
        ((string= id "decl:specials") 0)
        ((eql 0 (search "decl:" id)) 1)
        ((eql 0 (search "struct:" id)) 2)
        ((eql 0 (search "macro:" id)) 3)
        ((or (eql 0 (search "raw:" id)) (eql 0 (search "star1:" id))) 4)
        ((eql 0 (search "var:" id)) 5)
        ((eql 0 (search "global:" id)) 5)
        ((eql 0 (search "stobj:" id)) 5)
        ((eql 0 (search "attach:" id)) 6)
        (t 7)))

(defun fe-inline-raw-ids (run)
  "The raw: ids of the functions a decl: unit proclaims inline.  SBCL records an inline expansion only
when the declaim precedes the defun, and a caller compiled before that defun keeps a full call, so these
definitions are emitted ahead of every other function (measured: with alphabetical order IFIX and ZP
stayed full calls inside FN-B3-ADD although declaimed inline)."
  (let ((out (make-hash-table :test 'equal)))
    (maphash (lambda (id u)
               (when (and (eql 0 (search "decl:" id))
                          (some (lambda (f) (and (consp f) (eq (car f) 'declaim)
                                                 (consp (cadr f)) (eq (car (cadr f)) 'inline)))
                                (car u)))
                 (setf (gethash (concatenate 'string "raw:" (subseq id 5)) out) t)))
             (fr-units run))
    out))

(defun fe-sorted-ids (run)
  (let ((ids (loop for k being the hash-keys of (fr-units run) collect k))
        (inline (fe-inline-raw-ids run)))
    (stable-sort (sort ids #'string<) #'<
                 :key (lambda (id) (if (gethash id inline) 7/2 (fe-unit-rank id))))))

(defun fe-write-file (path string)
  (with-open-file (o path :direction :output :if-exists :supersede :external-format :latin-1)
    (write-string string o)))

(defun fe-block-text (id forms) (concatenate 'string (fe-header id) (fe-unit-text forms)))

(defun fe-packages-text (all-text)
  "packages.lisp: every package a printed symbol lives in, with the image's imports (as cl.py did)."
  (let ((pkgs (make-hash-table :test 'equal)) (known (known-package-alist *the-live-state*)) (out nil))
    ;; the symbols are in the printed text as PKG::NAME / PKG:NAME; find packages by reading it back
    (with-input-from-string (s all-text)
      (let ((*package* *fe-dummy-pkg*) (*read-eval* nil))
        (labels ((note (x) (cond ((and (symbolp x) x (symbol-package x)) (setf (gethash (package-name (symbol-package x)) pkgs) t))
                                 ((consp x) (note (car x)) (note (cdr x)))
                                 ((vectorp x) (unless (stringp x) (map nil #'note x))))))
          (loop for form = (read s nil :eof) until (eq form :eof) do (note form)))))
    (setf (gethash "ACL2" pkgs) t (gethash "ACL2_INVISIBLE" pkgs) t)
    (let ((names (sort (loop for k being the hash-keys of pkgs
                             unless (member k '("COMMON-LISP" "KEYWORD") :test #'equal) collect k)
                       #'string<)))
      (push ";;; generated by tools/extract/forms-export.lisp from the image's packages; do not edit" out)
      (dolist (p (cons "ACL2" (remove "ACL2" names :test #'equal)))
        (unless (and (> (length p) 3) (string= (subseq p 0 3) "SB-"))
          (push (format nil "(unless (find-package ~s) (make-package ~s :use nil))" p p) out)))
      (dolist (p (cons "ACL2" (remove "ACL2" names :test #'equal)))
        (let ((e (find p known :key (lambda (e) (package-entry-name e)) :test #'equal)))
          (when e
            (dolist (s (package-entry-imports e))
              (push (format nil "(import (list (intern ~s ~s)) ~s)" (symbol-name s) (symbol-package-name s) p) out)))))
      (format nil "~{~a~%~}" (nreverse out)))))

(defun fe-root-p (s)
  (and (symbolp s) s (not (fe-cl-or-sb-p s)) (not (gethash s *fe-rt*))
       (not (eq (getpropc s 'formals :none *fe-w*) :none))))

(defun fe-roots-from-tokens (tokens)
  (let ((out nil) (seen (make-hash-table :test 'eq)))
    (dolist (tk tokens)
      (let ((s (intern-in-package-of-symbol tk 'fe-root-p)))
        (when (and (fe-root-p s) (not (gethash s seen))) (setf (gethash s seen) t) (push s out))))
    (nreverse out)))

(defun fe-token-syms (tokens) (mapcar (lambda (tk) (intern-in-package-of-symbol tk 'fe-root-p)) tokens))

(defun xt-fe-export (tokens out-dir src-dir rt-path world-key &key extra-roots deadline)
  "Write OUT-DIR/defs.lisp, packages.lisp, manifest.tsv, runtime.tsv, edges.tsv, gaps.txt; set the state
global XT-FE-TABLES to the tables the closure reads (for xt-core-export); return (values n-units n-gaps)."
  (fe-arm-deadline deadline)
  (fe-log "index-world") (fe-index-world)
  (fe-log "index-sources") (fe-index-sources src-dir)
  (fe-log "read-runtime") (fe-read-runtime rt-path)
  (fe-log "closure")
  (let* ((syms (fe-token-syms tokens))
         (roots (union (fe-roots-from-tokens tokens) extra-roots))
         (stobjs (remove-if-not (lambda (s) (and s (symbolp s) (getpropc s 'stobj nil *fe-w*))) syms))
         (macros (remove-if-not (lambda (s) (and (gethash s *fe-macros*) (let ((n (symbol-name s))) (and (> (length n) 3) (string= (subseq n 0 3) "FN-")))))
                                syms))
         (run (fe-closure (sort (copy-list roots) #'string< :key #'symbol-name) stobjs macros))
         (ids (progn (setf (gethash "decl:prologue" (fr-units run)) (list (fe-prologue-forms) "acl2.lisp:2704-2705,*acl2-optimize-form*"))
                     (let ((d (fe-derive-unit "decl:specials" (fr-stobjs run)
                                              (append (fe-specials-from-ids (loop for k being the hash-keys of (fr-units run) collect k))
                                                      (fe-star1-var-refs (loop for v being the hash-values of (fr-units run) collect (car v)))))))
                       (setf (gethash "decl:specials" (fr-units run)) (list (car d) (cdr d))))
                     (fe-sorted-ids run)))
         (defs (make-string-output-stream)) (man (make-string-output-stream)) (all (make-string-output-stream)))
    (format man "#world_key~c~a~%#roots~c~d~%" #\Tab world-key #\Tab (length roots))
    (let ((files (make-hash-table :test 'equal)))
      (dolist (id ids)
        (let* ((u (gethash id (fr-units run))) (text (fe-block-text id (car u))) (origin (cadr u)))
          (write-string text defs) (write-string text all)
          (format man "~a~c~a~c~a~%" id #\Tab (fe-sha256-hex text) #\Tab origin)
          (when (eql 0 (search "src:" origin))
            (let* ((c1 (position #\: origin :start 4)) (c2 (position #\: origin :start (1+ c1))) (f (subseq origin 4 c1)))
              (declare (ignore c2))
              (setf (gethash f files) (gethash (subseq f 0 (- (length f) 5)) *fe-src-sha*))))))
      (maphash (lambda (f sha) (format man "#file~c~a~c~a~%" #\Tab f #\Tab sha)) files))
    (fe-write-file (format nil "~a/defs.lisp" out-dir) (get-output-stream-string defs))
    (fe-write-file (format nil "~a/manifest.tsv" out-dir) (get-output-stream-string man))
    (fe-write-file (format nil "~a/packages.lisp" out-dir) (fe-packages-text (get-output-stream-string all)))
    (let ((rt (sort (loop for k being the hash-keys of (fr-rt-refs run) collect k) #'string< :key (lambda (s) (format nil "~a::~a" (fe-pkg s) (symbol-name s))))))
      (fe-write-file (format nil "~a/runtime.tsv" out-dir)
                     (format nil "~{~a~%~}"
                             (mapcar (lambda (s)
                                       (let ((src (or (gethash s *fe-src*) (gethash (*1*-symbol s) *fe-src*))))
                                         (format nil "~a::~a~c~a~c~a" (fe-pkg s) (symbol-name s) #\Tab (gethash s *fe-rt*) #\Tab
                                                 (cond (src (fe-src-origin src)) ((gethash s *fe-defs*) "world:defuns") (t "host-only")))))
                                     rt))))
    ; the reference graph, one line per unit: ID TAB the unit ids its forms reference (tools/extract/closure_why.py)
    (fe-write-file (format nil "~a/edges.tsv" out-dir)
                   (format nil "~{#root~c~a~%~}~{~a~%~}"
                           (loop for r in (sort (copy-list roots) #'string< :key #'symbol-name)
                                 append (list #\Tab (fe-id :raw r)))
                           (loop for id in ids
                                 collect (format nil "~a~c~{~a~^ ~}" id #\Tab
                                                 (sort (copy-list (gethash id (fr-edges run))) #'string<)))))
    (let ((gaps (sort (loop for k being the hash-keys of (fr-gaps run) using (hash-value v) collect (format nil "~a~c~a" k #\Tab v)) #'string<)))
      (fe-write-file (format nil "~a/gaps.txt" out-dir) (format nil "~{~a~%~}" gaps))
      (when *fe-deadline-timer* (sb-ext:unschedule-timer *fe-deadline-timer*) (setq *fe-deadline-timer* nil))
      (f-put-global 'xt-fe-tables (fr-tables run) *the-live-state*)
      (format t "~&XT-FE units ~d roots ~d stobjs ~d macros ~d runtime-refs ~d tables ~d gaps ~d~%"
              (length ids) (length roots) (length (fr-stobjs run)) (length macros) (hash-table-count (fr-rt-refs run))
              (length (fr-tables run)) (length gaps))
      (values (length ids) (length gaps)))))

;;; ------------------------------------------------------------------------
;;; X1: the checker.  The pure comparison (fe-verify-core) takes the manifest,
;;; the defs.lisp text and a function giving the block text a unit re-derives
;;; to; it is separate from the world so tests can run it on synthetic data.
(defun fe-split-lines (text)
  (let ((out nil) (start 0))
    (loop for p = (position #\Newline text :start start)
          do (push (subseq text start (or p (length text))) out)
             (if p (setq start (1+ p)) (return)))
    (when (and out (string= (car out) "")) (pop out))   ; the text's final newline ends the last line
    (nreverse out)))

(defun fe-split-tabs (line)
  (let ((out nil) (start 0))
    (loop for p = (position #\Tab line :start start)
          do (push (subseq line start (or p (length line))) out)
             (if p (setq start (1+ p)) (return)))
    (nreverse out)))

(defun fe-parse-defs (text)
  "defs.lisp text -> list of (id . block-text), in file order; text before the first header is refused."
  (let ((blocks nil) (cur nil) (buf nil) (head ";;;; UNIT "))
    (dolist (line (fe-split-lines text))
      (cond ((and (>= (length line) (length head)) (string= head (subseq line 0 (length head))))
             (when cur (push (cons cur (format nil "~{~a~%~}" (reverse buf))) blocks))
             (setq cur (subseq line (length head)) buf (list line)))
            ((null cur) (when (plusp (length line)) (error "xt-verify-defs REFUSED: defs.lisp has text before the first UNIT header: ~a" (subseq line 0 (min 60 (length line))))))
            (t (push line buf))))
    (when cur (push (cons cur (format nil "~{~a~%~}" (reverse buf))) blocks))
    (nreverse blocks)))

(defun fe-parse-manifest (text)
  "-> (values world-key units files): units = list of (id sha origin), files = list of (file sha)."
  (let ((key nil) (units nil) (files nil))
    (dolist (line (fe-split-lines text))
      (when (plusp (length line))
        (let ((f (fe-split-tabs line)))
          (cond ((string= (car f) "#world_key") (setq key (cadr f)))
                ((string= (car f) "#roots") nil)
                ((string= (car f) "#file") (push (list (cadr f) (caddr f)) files))
                (t (push f units))))))
    (values key (nreverse units) (nreverse files))))

(defun fe-verify-core (manifest-text defs-text rederive expected-key)
  "Return a list of refusal strings (empty when the defs are exactly what the manifest and the world derive).
REDERIVE: unit id -> the block text it re-derives to, or NIL when it no longer derives."
  (let ((refusals nil))
    (multiple-value-bind (key units) (fe-parse-manifest manifest-text)
      (unless (equal key expected-key)
        (push (format nil "manifest is bound to world ~a, not ~a" key expected-key) refusals))
      (let ((blocks (fe-parse-defs defs-text)) (in-manifest (make-hash-table :test 'equal)) (in-defs (make-hash-table :test 'equal)))
        (dolist (b blocks) (setf (gethash (car b) in-defs) (cdr b)))
        (dolist (u units)
          (let* ((id (car u)) (sha (cadr u)) (block-text (gethash id in-defs)) (re (funcall rederive id)))
            (setf (gethash id in-manifest) t)
            (cond ((null block-text) (push (format nil "unit ~a is in the manifest but not in defs.lisp" id) refusals))
                  ((not (string= (fe-sha256-hex block-text) sha))
                   (push (format nil "unit ~a: the defs.lisp text does not match the manifest digest" id) refusals))
                  ((null re) (push (format nil "unit ~a no longer derives from the world or the sources" id) refusals))
                  ((not (string= re block-text))
                   (let ((k (or (mismatch re block-text) 0)))
                     (push (format nil "unit ~a: the text differs from what the world derives at character ~d: defs has ~s, world derives ~s"
                                   id k (subseq block-text k (min (length block-text) (+ k 70))) (subseq re k (min (length re) (+ k 70))))
                           refusals))))))
        (dolist (b blocks)
          (unless (gethash (car b) in-manifest)
            (push (format nil "unit ~a is in defs.lisp but not in the manifest" (car b)) refusals)))))
    (nreverse refusals)))

;;; X2: every symbol an emitted form calls is a unit, a runtime entry or Common Lisp / SBCL.
(defun fe-check-closure (blocks rt-names)
  "BLOCKS: list of (id . forms-list); RT-NAMES: hash of symbols the runtime defines.  Returns a list of
\"UNIT references NAME\" refusals for each called name that is none of extracted, runtime, CL/SB-."
  (let ((defined (make-hash-table :test 'eq)) (refusals nil))
    (dolist (b blocks)
      (dolist (f (cdr b))
        (when (and (consp f) (member (car f) '(defun defmacro)) (symbolp (cadr f))) (setf (gethash (cadr f) defined) t))
        (when (and (consp f) (member (car f) '(defparameter defvar defconstant sb-ext:defglobal)) (symbolp (cadr f))) (setf (gethash (cadr f) defined) t))
        (when (and (consp f) (eq (car f) 'defstruct))
          (dolist (g (fe-struct-names f)) (setf (gethash g defined) t))
          (setf (gethash (if (consp (cadr f)) (car (cadr f)) (cadr f)) defined) t))))
    (dolist (b blocks)
      (let ((fns (make-hash-table :test 'eq)) (vars (make-hash-table :test 'eq)))
        (dolist (f (cdr b)) (fe-calls (fe-walkable f) fns vars))
        (flet ((chk (s kind)
                 (unless (or (null s) (eq s t) (keywordp s) (fe-cl-or-sb-p s) (gethash s defined) (gethash s rt-names))
                   (when (or (eq kind :fn) (fe-earmuffed-p s))
                     (push (format nil "~a references ~a ~a::~a, which is not extracted, not a runtime entry and not Common Lisp"
                                   (car b) (if (eq kind :fn) "function" "variable") (fe-pkg s) (symbol-name s))
                           refusals)))))
          (maphash (lambda (s v) (declare (ignore v)) (chk s :fn)) fns)
          (maphash (lambda (s v) (declare (ignore v)) (chk s :var)) vars))))
    (sort refusals #'string<)))

(defun fe-read-block-forms (block-text)
  (let ((*package* *fe-dummy-pkg*) (*read-eval* nil) (*read-default-float-format* 'single-float) (out nil))
    (with-input-from-string (s block-text)
      (loop for form = (read s nil :eof) until (eq form :eof) do (push form out)))
    (nreverse out)))

(defun xt-verify-defs (out-dir src-dir rt-path world-key)
  "Re-derive every unit in OUT-DIR/manifest.tsv from this image's world and the ACL2 sources, compare with
the manifest and with OUT-DIR/defs.lisp, and check the closure.  Signals a refusal naming each failing unit."
  (fe-index-world) (fe-index-sources src-dir) (fe-read-runtime rt-path)
  (let* ((mtext (fe-file-string (format nil "~a/manifest.tsv" out-dir)))
         (dtext (fe-file-string (format nil "~a/defs.lisp" out-dir)))
         (stobj-names (multiple-value-bind (key units) (fe-parse-manifest mtext)
                        (declare (ignore key))
                        (loop for u in units
                              when (eql 0 (search "stobj:" (car u))) collect (cdr (fe-id-sym (car u))))))
         (blocks0 (mapcar (lambda (b) (cons (car b) (fe-read-block-forms (cdr b)))) (fe-parse-defs dtext)))
         (specials (append (fe-specials-from-ids (mapcar #'car (nth-value 1 (fe-parse-manifest mtext))))
                           (fe-star1-var-refs (mapcar #'cdr (remove "decl:specials" blocks0 :key #'car :test #'string=)))))
         (rederive (lambda (id)
                     (handler-case
                         (let ((d (if (string= id "decl:prologue")
                                      (cons (fe-prologue-forms) "prologue")
                                      (fe-derive-unit id stobj-names specials))))
                           (and d (fe-block-text id (car d))))
                       (error (e) (format nil "<derivation error: ~a>" e)))))
         (refusals (fe-verify-core mtext dtext rederive world-key))
         (blocks blocks0))
    (setq refusals (append refusals (fe-check-closure blocks *fe-rt*)))
    (if refusals
        (progn (format t "~&XT-VERIFY-DEFS REFUSED ~d~%~{  ~a~%~}" (length refusals) (subseq refusals 0 (min 40 (length refusals))))
               (error "xt-verify-defs REFUSED: ~d unit(s); first: ~a" (length refusals) (car refusals)))
        (format t "~&XT-VERIFY-DEFS OK ~d units, world ~a~%" (length blocks) world-key))
    t))
