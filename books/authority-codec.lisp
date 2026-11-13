; Served authority's frames as layouts (layer E; docs/design/AUTHORITY-20261105.md
; section 3). FNCT request kind 29: one opcode octet (the carrier's request
; code, authority-port.lisp), then the verb's fields; reply kind 30: the
; opcode, the port's class, a reason word of at most 64 octets (empty on
; acceptance), then exactly the verb's declared result for that class. Every
; form is a DEFLAYOUT row: the generated codec is the served path, B's list
; codec the specification. No Lisp reader; a failed frame never defaults to
; another verb.
(in-package "ACL2")
(include-book "consumer-codec")
(include-book "authority-port")
(fn2-book-layer :e)

(defconst *fn2-authority-right-layout* '(:enum fn2-authority-right (:consume :read :append)))
(defconst *fn2-authority-scope-layout* '(:enum fn2-authority-scope (:own-consumers :stream)))

;; Requests: (OPCODE VERB FIELDS). Names and operation identities are
;; length-prefixed octets, nonempty, at most 64 (checked by the verb, which
;; answers frame for an empty one).
(defconst *fn2-authority-requests*
  `((4 stream-resolve ((stream-name (:octets16 250))))
    (0 principal-create ((name (:octets16 64))))
    (1 principal-bind ((name (:octets16 64))))
    (2 grant-set ((grantee (:id principal)) (right ,*fn2-authority-right-layout*)
                  (scope ,*fn2-authority-scope-layout*) (target (:id stream)) (enabled :bool)
                  (expected-head (:id grant)) (op (:octets16 64))))
    (3 grant-get ((grantee (:id principal)) (right ,*fn2-authority-right-layout*)
                  (scope ,*fn2-authority-scope-layout*) (target (:id stream))))))

;; Accepted results, field for field the port's :result (grant-get's tail
;; after FOUND occurs iff FOUND = 1: a separate layout, so found = 0 is the
;; two-field form and never a grant).
(defconst *fn2-authority-results*
  '((stream-resolve ((target (:id stream))))
    (principal-create ((principal (:id principal))))
    (principal-bind ((principal (:id principal)) (authority-head (:id grant))))
    (grant-set ((grant (:id grant)) (authority-head (:id grant)) (receipt (:octets16 1024))))
    (grant-get ((found :bool) (authority-head (:id grant))))
    (grant-get-found ((grant (:id grant)) (grantor (:id principal)) (enabled :bool) (previous (:id grant))))))

(defconst *fn2-authority-reply-layout*
  '((code :u8) (class (:enum fn2-fnct-class (:accepted :refused :uncertain :fault))) (reason (:octets16 64))))

;; Which verbs may answer uncertain (the ruling: principal-bind and grant-get
;; never do), as data the arms and the fixtures read.
(defconst *fn2-authority-uncertain-verbs* '(principal-create grant-set))

(defun fn2-authority-codes-ok (rows seen)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (and (natp (caar rows)) (< (caar rows) 256) (not (member (caar rows) seen))
         (equal (fn2-authority-local-binding (cadar rows)) (list *fn2-authority-request-kind* (caar rows)))
         (fn2-layoutp (cons '(code :u8) (caddar rows)))
         (fn2-authority-codes-ok (cdr rows) (cons (caar rows) seen)))))
;; Every opcode is the carrier's binding of its verb, and every verb is bound.
(assert-event (fn2-authority-codes-ok *fn2-authority-requests* nil))
(assert-event (equal (len *fn2-authority-requests*) (len *fn2-authority-local-binds*)))

(defun fn2-authority-deflayout-forms (prefix rows code)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let ((verb (if code (cadar rows) (caar rows)))
          (fields (if code (caddar rows) (cadar rows))))
      (cons `(deflayout ,(intern-in-package-of-symbol
                          (concatenate 'string prefix (symbol-name verb)) 'fn2-authority-requests)
               ',(if code (cons '(code :u8) fields) fields))
            (fn2-authority-deflayout-forms prefix (cdr rows) code)))))
(make-event (value `(progn ,@(fn2-authority-deflayout-forms "FN2-AUTHORITY-REQ-" *fn2-authority-requests* t))))
(make-event (value `(progn ,@(fn2-authority-deflayout-forms "FN2-AUTHORITY-RES-" *fn2-authority-results* nil))))
(deflayout fn2-authority-reply *fn2-authority-reply-layout*)

;; The specification (list form): a request's octets and a reply's octets.
(defun fn2-authority-request-row (verb rows)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil) ((eq (cadar rows) verb) (car rows)) (t (fn2-authority-request-row verb (cdr rows)))))
(defun fn2-authority-request-octets (verb values)
  (declare (xargs :verify-guards nil))
  (let ((row (fn2-authority-request-row verb *fn2-authority-requests*)))
    (and row (fn2-layout-octets (cons '(code :u8) (caddr row)) (cons (car row) values)))))
;; (CLASS REASON RESULT-VALUES [FOUND-VALUES]): the reply's octets.
(defun fn2-authority-reply-octets (verb class reason values found-values)
  (declare (xargs :verify-guards nil))
  (let ((row (fn2-authority-request-row verb *fn2-authority-requests*)))
    (and row
         (append (fn2-layout-octets *fn2-authority-reply-layout*
                                    (list (car row) (fn2-fnct-status-octet class) reason))
                 (and (eq class :accepted)
                      (append (fn2-layout-octets (cadr (assoc-eq verb *fn2-authority-results*)) values)
                              (and (eq verb 'grant-get) (equal (car values) 1)
                                   (fn2-layout-octets (cadr (assoc-eq 'grant-get-found *fn2-authority-results*))
                                                      found-values))))))))
