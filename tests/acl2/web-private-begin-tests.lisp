; Captured POST/remove begin uses exact old gate/action/output, after the
; owner alone selected/touched the session. Source witnesses: admission pending.
(in-package "ACL2")
(include-book "web-session-tests")
(defun wpbt-compare (request config sessions)
  (declare (xargs :mode :program))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (with-local-stobj fn-web-out
        (mv-let (r fn-web-in fn-web-out)
          (let* ((fn-web-in (fn-octets-from-list request fn-web-in))
                 (event (wsst-begin request 300))
                 (reference-config (append (take 6 config) (list :page-plan)))
                 (private-config (append reference-config (list :private-begin))))
            (mv-let (reference table fn-web-out)
              (fn-web-step reference-config sessions nil event fn-web-in fn-web-out)
              (let* ((bytes (fn-octets-list fn-web-out)) (fn-web-out (fn-octets-clear fn-web-out)))
                (mv-let (staged staged-table fn-web-out)
                  (fn-web-step private-config sessions nil event fn-web-in fn-web-out)
                  (let ((empty (equal (fn-octets-len fn-web-out) 0)))
                    (mv-let (private fn-web-out)
                      (fn-web-private-begin-step private-config staged fn-web-in fn-web-out)
                      (mv (list (fn-web-private-begin-p staged) empty (equal staged-table table)
                                (equal private reference) (equal (fn-octets-list fn-web-out) bytes))
                          fn-web-in fn-web-out)))))))
          (mv r fn-web-in)))
      r)))
(defconst *wpbt-post*
  (wsst-post-req "/post" (concatenate 'string "fnr_session=" (wsst-str *tok*))
    (concatenate 'string "csrf=" (wsst-str *csrf*)
                 "&g=local.general&subject=Hello&body=line+one%0D%0A.%0D%0A.QUIT%0D%0Alast")))
(assert-event (equal (wpbt-compare *wpbt-post* *cfg* *ss*) '(t t t t t)))
(defconst *wpbt-bad-csrf*
  (wsst-post-req "/post" (concatenate 'string "fnr_session=" (wsst-str *tok*))
                 "csrf=wrong&g=local.general&subject=Hello&body=Hello"))
(assert-event (equal (wpbt-compare *wpbt-bad-csrf* *cfg* *ss*) '(t t t t t)))
(defconst *wpbt-remove*
  (wsst-post-req "/remove" (concatenate 'string "fnr_session=" (wsst-str *tok*))
    (concatenate 'string "csrf=" (wsst-str *csrf*) "&g=local.general&id=%3Cm%40fn%3E")))
(assert-event (equal (wpbt-compare *wpbt-remove* *cfg* *ss*) '(t t t t t)))
; Removing the only keystone hypothesis: a reached old BEGIN action is :send,
; not a captured private gate, and private processing refuses it.
(defconst *wpbt-old* (wsst-step *cfg* *ss* nil (wsst-begin *wpbt-post* 300) *wpbt-post*))
(assert-event (and (equal (caar *wpbt-old*) :send)
                   (not (fn-web-private-begin-p (car *wpbt-old*)))))
(defun wpbt-removal (action in)
  (declare (xargs :mode :program))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (with-local-stobj fn-web-out
        (mv-let (r fn-web-in fn-web-out)
          (let ((fn-web-in (fn-octets-from-list in fn-web-in)))
            (mv-let (private fn-web-out)
              (fn-web-private-begin-step *cfg* action fn-web-in fn-web-out)
              (mv-let (reference table fn-web-out)
                (fn-wss-gate (fn-wrq-nth 1 action) (fn-wrq-nth 2 action) *ss*
                             (fn-wrq-nth 3 action) *cfg* fn-web-in fn-web-out)
                (mv (and (not (fn-web-private-begin-p action))
                         (not (equal private reference)) (equal table *ss*)) fn-web-in fn-web-out))))
          (mv r fn-web-in)))
      r)))
(assert-event (wpbt-removal (car *wpbt-old*) *wpbt-post*))
