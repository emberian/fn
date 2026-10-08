;;; Source-level ground counterexample, not an ACL2 proof or certification.
;;; Run from the worktree: timeout 20 sbcl --script planning/evidence/post-art-head-local-counterexample.lisp
;;; Evaluates the selected production DEFUN bodies verbatim. XARGS are ignored
;;; by Common Lisp; NFIX and LEN below suffice for these proper-list inputs.
(declaim (declaration xargs))
(defun nfix (x) (if (and (integerp x) (<= 0 x)) x 0))
(defun zp (x) (not (and (integerp x) (< 0 x))))
(defun len (x) (length x))
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun true-listp (x)
  (if (consp x) (true-listp (cdr x)) (null x)))

(defun load-selected (path names)
  (with-open-file (in path)
    (let ((*read-eval* nil))
      (loop for form = (read in nil :eof) until (eq form :eof)
            when (and (consp form) (member (car form) '(defun defconst))
                      (member (cadr form) names))
              do (eval (if (eq (car form) 'defconst)
                           (cons 'defparameter (cdr form))
                         form))))))

(load-selected "books/injection.lisp"
  '(*fn-inj-crlf* *fn-inj-injection-date-field* *fn-inj-injection-info-field*
    *fn-inj-message-id-field* *fn-inj-date-field* fn-inj-append fn-inj-strip
    fn-inj-take fn-inj-drop fn-inj-message-id-line fn-inj-injection-info-line
    fn-inj-injection-info-line-with))
(load-selected "books/post-header-line.lisp" '(fn-pb-fixed-linep))
(load-selected "books/poster-bytes-source.lisp"
  '(*fn-pb-stamp-line-length* *fn-pb-date-line-length* fn-pb-opensp
    fn-pb-strip-header-line))
(load-selected "books/injection-info-params.lisp"
  '(fn-ipp-at-info fn-ipp-at-date fn-ipp-at-msgid fn-ipp-at-stamp))
(load-selected "books/injection-info-params-reference.lisp"
  '(fn-ipp-at-info-old fn-ipp-at-date-old fn-ipp-at-msgid-old fn-ipp-at-stamp-old))

(let* ((agent '(97)) (msgid '(60 120 64 121 62)) (params '(59 120))
       (info (fn-inj-injection-info-line agent))
       (changed-info (fn-inj-injection-info-line-with agent params))
       (padding (make-list 28 :initial-element 65))
       (body (append padding info))
       (changed-body (append padding changed-info)))
  (dolist (case (list (list 'fn-ipp-at-stamp *fn-inj-injection-date-field* 49)
                     (list 'fn-ipp-at-date *fn-inj-date-field* 39)))
    (let* ((fn (first case))
           (head (append (second case) '(120 13 10 13 10)))
           (x (append head body))
           (edit (if (eq fn 'fn-ipp-at-stamp)
                     (lambda (y) (fn-ipp-at-stamp y agent msgid params))
                   (lambda (y) (fn-ipp-at-date y agent params))))
           (old-edit (if (eq fn 'fn-ipp-at-stamp)
                         (lambda (y) (fn-ipp-at-stamp-old y agent msgid params))
                       (lambda (y) (fn-ipp-at-date-old y agent params))))
           (actual (funcall edit x))
           (old (funcall old-edit x))
           (head-only (append (funcall edit head) body)))
      (assert (= (+ (length head) (length padding)) (third case)))
      (assert (every (lambda (b) (and (integerp b) (<= 0 b 255))) x))
      (assert (equal (last head 4) '(13 10 13 10)))
      (assert (equal old (append head changed-body)))
      (assert (not (equal old head-only)))
      (assert (equal actual x))
      (assert (equal actual head-only))
      ;; Control: a generated-length stamp/date with no early blank line.
      (let* ((line (append (second case) (make-list 31 :initial-element 65)
                           '(13 10)))
             (good-head (append line info '(13 10))))
        (assert (= (length line) (third case)))
        (assert (equal (funcall edit (append good-head body))
                       (funcall old-edit (append good-head body))))
        (assert (equal (funcall edit (append good-head body))
                       (append (funcall edit good-head) body))))
      (format t "~A: old form edits body; hardened form preserves input; control agrees.~%" fn))))
