; tools/image_anatomy/ia-anatomy.lisp -- what is in a saved native image, by
; kind and by owner, and which of it a running node touched (lane
; image-anatomy, 2026-09-26).  Loaded into the image's core in place of its
; `(acl2::sbcl-restart)' (tools/image_anatomy/anatomy.sh), so ACL2 never
; starts and nothing is saved.  A measurement only: it decides nothing a node
; does.
;
; Every allocated object of every space is given one owner:
;   world:<origin>:<property>   reachable from a world triple, first by the
;                               oldest triple (origin: ground-zero, the
;                               community books, the fn books, top-level);
;   plist-index                 the property alists ACL2 installs on symbols
;                               (the world's fast index, getprop's read path);
;   code:<origin>               a code component, its debug info and its
;                               non-symbol constants, by the source file it
;                               was compiled from (sbcl, acl2:<file>, books,
;                               fn-books, fn-books-*1*, host-native, ...);
;   sym:<package class>         a symbol, its name, value, function cell and
;                               the rest of its plist;
;   other                       anything not reached from those roots.
; Output lines start IA-; tools/image_anatomy/ia_report.py reads them with
; the residency snapshots ia_node.py wrote.
(in-package "ACL2")

(defvar *ia-seen* (make-hash-table :test 'eq :size 8000000))
(defvar *ia-owner-ids* (make-hash-table :test 'equal))
(defvar *ia-owner-names* (make-array 0 :adjustable t :fill-pointer t))

(defun ia-owner-id (name)
  (or (gethash name *ia-owner-ids*)
      (setf (gethash name *ia-owner-ids*)
            (vector-push-extend name *ia-owner-names*))))

(defun ia-immediate-p (o)
  (or (typep o 'fixnum) (characterp o) (typep o 'single-float)
      (sb-int:unbound-marker-p o)
      (not (sb-vm:is-lisp-pointer (sb-kernel:get-lisp-obj-address o)))))

(defun ia-boundary-p (o)
  (or (symbolp o) (packagep o) (sb-kernel:code-component-p o)
      (sb-kernel:simple-fun-p o) (typep o 'sb-kernel:fdefn)
      (typep o 'sb-kernel:layout)))

; Mark everything newly reachable from ROOT (ROOT itself even when it is a
; boundary object) as OWNER.
(defun ia-walk (root owner)
  (let ((stack (list root)) (first t) (total 0))
    (loop while stack do
      (let ((o (pop stack)))
        (unless (or (ia-immediate-p o) (gethash o *ia-seen*)
                    (and (not first) (ia-boundary-p o)))
          (setf (gethash o *ia-seen*) owner)
          (incf total (sb-ext:primitive-object-size o))
          (sb-vm:do-referenced-object (o (lambda (x) (push x stack)))))
        (setq first nil)))
    total))

; The largest roots of an owner class, for the record.
(defvar *ia-tops* (make-hash-table :test 'equal))
(defun ia-note-top (class what bytes)
  (push (cons bytes what) (gethash class *ia-tops*)))
(defun ia-print-tops (n)
  (maphash (lambda (class rows)
             (let* ((n (length rows)) (sum (reduce #'+ rows :key #'car))
                    (sorted (sort (copy-list rows) #'> :key #'car)))
               (format t "~&IA-TOPSUM ~a roots=~d bytes=~d~%" class n sum)
               (loop for (bytes . what) in sorted repeat n
                     do (format t "~&IA-TOP ~a ~d ~a~%" class bytes what))))
           *ia-tops*))

; The world, oldest triple first.
(defun ia-book-class (path)
  (let ((s (cond ((stringp path) path)
                 ((and (fboundp 'sysfile-p) (funcall 'sysfile-p path))
                  (concatenate 'string "[books]/" (funcall 'sysfile-filename path)))
                 (t (format nil "~a" path)))))
    (cond ((or (search "[books]/" s) (search "/acl2-8.7/books/" s)) "community-books")
          ((search "/books/" s) "fn-books")
          (t "other-book"))))

(defun ia-walk-world ()
  (let* ((wrld (w *the-live-state*))
         (origin "ground-zero")
         (book nil)
         (by-book (make-hash-table :test 'equal)))
    (dolist (triple (reverse wrld))
      (when (and (eq (car triple) 'boot-strap-flg) (eq (cadr triple) 'global-value)
                 (null (cddr triple)))
        (setq origin "top-level"))
      (when (and (eq (car triple) 'include-book-path) (eq (cadr triple) 'global-value)
                 (not (equal origin "ground-zero")))
        (setq book (car (cddr triple))))
      (let* ((o (cond ((equal origin "ground-zero") origin)
                      (book (ia-book-class book))
                      (t "top-level")))
             (owner (ia-owner-id (format nil "world:~a:~a" o (cadr triple))))
             (before (hash-table-count *ia-seen*)))
        (declare (ignorable before))
        (ia-walk triple owner)
        (when (and book (equal o "fn-books"))
          (setf (gethash book by-book) t))))
    ; The world list's own spine.
    (let ((spine (ia-owner-id "world:spine")))
      (loop for tail on wrld do
        (unless (gethash tail *ia-seen*) (setf (gethash tail *ia-seen*) spine))))
    (format t "~&IA-NOTE world triples=~d fn-books=~d~%" (length wrld)
            (hash-table-count by-book))))

; Code components by the file they were compiled from.
(defun ia-code-debug-info (code)
  (let ((di (ignore-errors (sb-kernel:%code-debug-info code))))
    (and (typep di 'sb-c::compiled-debug-info) di)))

(defun ia-code-source (code)
  (let* ((di (ia-code-debug-info code))
         (src (and di (ignore-errors (sb-c::debug-info-source di)))))
    (and (typep src 'sb-c::debug-source)
         (ignore-errors (sb-c::debug-source-namestring src)))))

; The component's name is its first function's name, or a (TOPLEVEL-FORM ...)
; description; a *1* component names a symbol of ACL2_*1*_ACL2.
(defun ia-code-star1-p (code)
  (let* ((di (ia-code-debug-info code))
         (name (and di (ignore-errors (sb-c::compiled-debug-info-name di)))))
    (labels ((star (x) (cond ((symbolp x)
                              (and (symbol-package x)
                                   (equal (package-name (symbol-package x)) "ACL2_*1*_ACL2")))
                             ((consp x) (some #'star (if (listp (cdr x)) x (list (car x)))))
                             (t nil))))
      (star name))))

(defun ia-code-class (code)
  (let ((s (ia-code-source code)) (star (ia-code-star1-p code)))
    (cond ((null s) (if star "code:none-*1*" "code:none"))
          ((eql 0 (search "SYS:" s)) "code:sbcl")
          ((search "/acl2-8.7/books/" s) (if star "code:community-books-*1*" "code:community-books"))
          ((search "/acl2-8.7/" s)
           (let* ((slash (position #\/ s :from-end t))
                  (file (subseq s (1+ slash))))
             (format nil "code:acl2~a:~a" (if star "-*1*" "") file)))
          ((search "/host/native/" s) "code:host-native")
          ((search "/host/" s) (if star "code:host-wrappers-*1*" "code:host-wrappers"))
          ((search "/books/" s) (if star "code:fn-books-*1*" "code:fn-books"))
          (t (if star "code:elsewhere-*1*" "code:elsewhere")))))

(defun ia-walk-code ()
  (let ((codes nil))
    (sb-vm:map-allocated-objects
     (lambda (o w s) (declare (ignore s))
       (when (= w sb-vm:code-header-widetag) (push o codes)))
     :all)
    (dolist (c codes)
      (let* ((class (ia-code-class c))
             (bytes (ia-walk c (ia-owner-id class))))
        (when (or (member class '("code:none" "code:none-*1*" "code:elsewhere") :test #'equal)
                  (> bytes 200000))
          (let* ((di (ia-code-debug-info c))
                 (name (and di (ignore-errors (sb-c::compiled-debug-info-name di))))
                 (base (and (symbolp name) name
                            (find-symbol (symbol-name name) "ACL2")))
                 (sys (and base (fgetprop base 'predefined nil (w *the-live-state*))))
                 (src (ignore-errors (sb-c::debug-info-source di)))
                 (form (and src (typep src 'sb-c::core-debug-source))))
            (ia-note-top (format nil "~a/~a" class (cond (sys "acl2-predefined")
                                                         (base "not-predefined")
                                                         (t "unnamed")))
                         (let ((*print-pretty* nil) (*print-length* 4) (*print-level* 2))
                           (format nil "~s~@[ form-bytes~]" name form))
                         bytes)))))
    (format t "~&IA-NOTE code-components=~d~%" (length codes))))

(defun ia-package-class (p)
  (let ((n (if p (package-name p) "NONE")))
    (cond ((member n '("ACL2" "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL" "ACL2-PC"
                       "ACL2_*1*_ACL2" "ACL2_*1*_COMMON-LISP" "ACL2_GLOBAL_ACL2"
                       "ACL2_GLOBAL_ACL2-PC" "ACL2_*1*_ACL2-PC" "COMMON-LISP" "KEYWORD"
                       "ACL2-USER")
                   :test #'equal)
           (format nil "sym:~a" n))
          ((eql 0 (search "SB-" n)) "sym:sbcl")
          ((eql 0 (search "ACL2_*1*_" n)) "sym:other-*1*")
          ((eql 0 (search "ACL2_GLOBAL_" n)) "sym:other-global")
          (t "sym:other"))))

(defun ia-walk-symbols ()
  (let ((key *current-acl2-world-key*)
        (index (ia-owner-id "plist-index"))
        (syms nil))
    (sb-vm:map-allocated-objects
     (lambda (o w s) (declare (ignore s))
       (when (= w sb-vm:symbol-widetag) (push o syms)))
     :all)
    ; The installed world index first: (get sym key) and its alist spine.
    (dolist (s syms)
      (let ((alist (get s key)))
        (loop for tail on alist do
          (unless (gethash tail *ia-seen*)
            (setf (gethash tail *ia-seen*) index))
          (let ((entry (car tail)))
            (when (and (consp entry) (not (gethash entry *ia-seen*)))
              (setf (gethash entry *ia-seen*) index))))))
    (dolist (s syms)
      (let* ((class (ia-package-class (symbol-package s)))
             (owner (ia-owner-id class))
             (bytes (ia-walk s owner)))
        (when (> bytes 0)
          (ia-note-top class (let ((*print-pretty* nil))
                               (format nil "~s value=~a plist-keys=~s" s
                                       (if (boundp s) (type-of (symbol-value s)) "unbound")
                                       (loop for k in (symbol-plist s) by #'cddr collect k)))
                       bytes))
        (let ((f (and (symbol-package s) (fboundp s) (ignore-errors (sb-int:find-fdefn s)))))
          (when f (ia-walk f owner)))))
    (format t "~&IA-NOTE symbols=~d~%" (length syms))))


(defun ia-type-name (o w)
  (cond ((= w sb-vm:instance-widetag)
         (format nil "instance:~a" (ignore-errors (type-of o))))
        ((consp o) "cons")
        ((stringp o) "string")
        ((simple-vector-p o) "simple-vector")
        ((typep o '(simple-array (unsigned-byte 8) (*))) "octet-vector")
        ((= w sb-vm:code-header-widetag) "code")
        ((= w sb-vm:symbol-widetag) "symbol")
        (t (let ((ty (ignore-errors (type-of o))))
             (cond ((and (consp ty) (eq (car ty) 'simple-array))
                    (format nil "~a" (list (first ty) (second ty))))
                   (ty (format nil "~a" (if (consp ty) (car ty) ty)))
                   (t (format nil "W~d" w)))))))

; The residency files ia_node.py wrote: F/R lines of page runs.
(defun ia-read-pages (path)
  (let ((file (make-hash-table)) (priv (make-hash-table)))
    (with-open-file (in path)
      (loop for line = (read-line in nil nil) while line do
        (when (and (> (length line) 2) (member (char line 0) '(#\F #\R)))
          (with-input-from-string (s (subseq line 2))
            (let ((lo (read s)) (hi (read s))
                  (table (if (char= (char line 0) #\F) file priv)))
              (loop for p from (floor lo 4096) below (floor hi 4096)
                    do (setf (gethash p table) t)))))))
    (cons file priv)))

(defun ia-object-base (o)
  (logandc2 (sb-kernel:get-lisp-obj-address o) sb-vm:lowtag-mask))

; Octets of [BASE, BASE+SIZE) on pages resident in TABLE.
(defun ia-resident-octets (base size table)
  (let ((total 0) (end (+ base size)))
    (loop for p from (floor base 4096) to (floor (1- end) 4096) do
      (when (gethash p table)
        (incf total (- (min end (* (1+ p) 4096)) (max base (* p 4096))))))
    total))

(defun ia-report (snapshots)
  (let* ((other (ia-owner-id "other"))
         (sets (mapcar (lambda (p) (cons p (ia-read-pages p))) snapshots))
         (rows (make-hash-table :test 'equal)))
    ; rows: (space owner type) -> #(bytes count file-res-1 priv-res-1 ...)
    (dolist (space '(:dynamic :immobile :read-only :static))
      (sb-vm:map-allocated-objects
       (lambda (o w size)
        (when (or (not (eq space :dynamic))
                  (= (sb-kernel:generation-of o) sb-vm:+pseudo-static-generation+))
         (let* ((owner (aref *ia-owner-names* (gethash o *ia-seen* other)))
                (key (list space owner (ia-type-name o w)))
                (row (or (gethash key rows)
                         (setf (gethash key rows)
                               (make-array (+ 2 (* 2 (length sets))) :initial-element 0))))
                (base (ia-object-base o)))
           (incf (aref row 0) size)
           (incf (aref row 1))
           (loop for (nil . (file . priv)) in sets for i from 2 by 2 do
             (incf (aref row i) (ia-resident-octets base size file))
             (incf (aref row (1+ i)) (ia-resident-octets base size priv))))))
       space))
    (format t "~&IA-COLUMNS space owner type bytes count~{ ~a:file ~:*~a:private~}~%"
            (mapcar #'file-namestring snapshots))
    (maphash (lambda (k row)
               (format t "~&IA-ROW ~(~a~)	~a	~a~{	~d~}~%" (first k) (second k) (third k)
                       (coerce row 'list)))
             rows)))

(defun ia-main (snapshots &aux (*print-pretty* nil))
  (format t "~&IA-SPACES dynamic-usage=~d~%" (sb-kernel:dynamic-usage))
  (format t "~&IA-BOUNDS~{ ~a~}~%"
          (loop for sp in '(:read-only :static :fixed :text)
                collect (format nil "~(~a~)=~{~d~^-~}" sp
                                (ignore-errors (multiple-value-list (sb-vm::%space-bounds sp))))))
  (format t "~&IA-BOUNDS dynamic-start=~d~%" sb-vm:dynamic-space-start)
  (ia-walk-world)
  (ia-walk-code)
  (ia-walk-symbols)
  (format t "~&IA-NOTE seen=~d~%" (hash-table-count *ia-seen*))
  (ia-print-tops 25)
  (ia-report snapshots)
  (format t "~&IA-DONE~%"))
