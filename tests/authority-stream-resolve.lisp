; The served directory's identity is independent of CLI-side enumeration.
(in-package "ACL2")
(include-book "authority-served")

(defun fn2-authority-stream-resolve-positive ()
 (declare (xargs :verify-guards nil))
 (let* ((profile (put-assoc-equal :groups '(("ops.audit" . 71) ("ops.alert" . 19)) *fn2-as-served-profile*))
        (r (fn2-as-served-run profile
             (list (fn2-as-client
               (list (fn2-as-frame 'stream-resolve (list (fn2-as-o "ops.audit")))
                     (fn2-as-frame 'stream-resolve (list (fn2-as-o "ops.alert")))
                     (fn2-as-frame 'stream-resolve (list (fn2-as-o "ops.audi")))
                     (fn2-as-frame 'stream-resolve (list (fn2-as-o "ops.auditx")))
                     (fn2-as-frame 'principal-create (list (fn2-as-o "mini")))))) nil)))
   (and (equal (nth 0 r) :quiet) (equal (nth 1 r) 0)
        (equal (car (nth 2 r))
          (append (fn2-as-accepted 'stream-resolve '(71))
                  (fn2-as-accepted 'stream-resolve '(19))
                  (fn2-as-refused 'stream-resolve "unknown-stream")
                  (fn2-as-refused 'stream-resolve "unknown-stream")
                  (fn2-as-accepted 'principal-create (list *fn2-as-mini-id*)))))))
(assert-event (fn2-authority-stream-resolve-positive))

;; Malformed names are raw wire inputs, so the request encoder cannot normalize
;; away either boundary. A subsequent owner operation checks admin retention.
(assert-event
 (let* ((frames
          (list (fn2-fnct-seal *fn2-authority-request-kind* '(4 0 0))
                (fn2-fnct-seal *fn2-authority-request-kind*
                  (append '(4 0 251) (make-list 251 :initial-element 120)))
                (fn2-as-frame 'principal-create (list (fn2-as-o "mini")))))
        (r (fn2-as-served-run *fn2-as-served-profile*
                             (list (fn2-as-client frames)) nil)))
  (and (equal (nth 0 r) :quiet) (equal (nth 1 r) 0)
       (equal (car (nth 2 r))
         (append (fn2-as-refused 'stream-resolve "frame")
                 (fn2-as-refused 'stream-resolve "frame")
                 (fn2-as-accepted 'principal-create (list *fn2-as-mini-id*)))))))

;; A bound principal cannot query the owner directory. Its own grant-get still
;; succeeds after refusal, while a different grantee remains inaccessible:
;; these observable checks distinguish preserving the binding from resetting it.
(assert-event
 (let* ((frames
          (list (fn2-as-frame 'principal-create (list (fn2-as-o "mini")))
                (fn2-as-bind "mini")
                (fn2-as-frame 'stream-resolve (list (fn2-as-o "ops.audit")))
                (fn2-as-frame 'grant-get (list *fn2-as-mini-id* 0 0 0))
                (fn2-as-frame 'grant-get (list 1 0 0 0))))
        (r (fn2-as-served-run *fn2-as-served-profile*
                             (list (fn2-as-client frames)) nil)))
  (and (equal (nth 0 r) :quiet) (equal (nth 1 r) 0)
       (equal (car (nth 2 r))
         (append (fn2-as-accepted 'principal-create (list *fn2-as-mini-id*))
                 (fn2-as-accepted 'principal-bind (list *fn2-as-mini-id* 0))
                 (fn2-as-refused 'stream-resolve "access")
                 (fn2-as-reply 'grant-get :accepted nil '(0 0) nil)
                 (fn2-as-refused 'grant-get "access"))))))

;; Known malformed bind retains opcode 1 but cannot bind; unknown opcode still
;; reports the protocol's opcode-0 frame refusal. Malformed create never claims
;; a principal, and the following owner create checks the binding stayed admin.
(assert-event
 (let* ((frames
          (list (fn2-as-frame 'principal-create (list (fn2-as-o "mini")))
                (fn2-fnct-seal *fn2-authority-request-kind*
                  (append (fn2-authority-request-octets 'principal-bind
                            (list (fn2-as-o "mini"))) '(0)))
                (fn2-fnct-seal *fn2-authority-request-kind* '(9 0 0))
                (fn2-fnct-seal *fn2-authority-request-kind*
                  (append (fn2-authority-request-octets 'principal-create
                            (list (fn2-as-o "ghost"))) '(0)))
                (fn2-as-frame 'principal-create (list (fn2-as-o "origin")))))
        (r (fn2-as-served-run *fn2-as-served-profile*
                             (list (fn2-as-client frames)) (list "ghost"))))
  (and (equal (nth 0 r) :quiet) (equal (nth 1 r) 0)
       (equal (nth 3 r) '((:absent 0)))
       (equal (car (nth 2 r))
         (append (fn2-as-accepted 'principal-create (list *fn2-as-mini-id*))
                 (fn2-as-refused 'principal-bind "frame")
                 (fn2-as-refused 'principal-create "frame")
                 (fn2-as-refused 'principal-create "frame")
                 (fn2-as-accepted 'principal-create (list *fn2-as-origin-id*)))))))
