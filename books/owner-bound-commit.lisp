; fn: file first, structurally, on the bound submission's commit route (PKT-069).
;
; host/native/owner.lisp `fnn-owner-complete-bound-submission' completes an
; ACL2-admitted submission.  Given no commit callback it reaches the Store
; through `fnn-owner-attempt-served', which files first
; (`fnn-owner-attempt-transit' asks `fn-pa-filing-plan').  Given a commit
; callback (today the local signed author, host/native/hybrid-control.lisp)
; it used to call the callback directly: a second route into the Store on
; which filing was the caller's convention (control-c1 record, finding 4).
; Now the host asks this gate, through host/owner-host.lisp
; `fn-owner-bound-commit-gate', and calls the callback only on `:commit':
; the groups the submission commits under must be exactly the filing plan's.
; A caller that did not file (a control article under the groups its
; Newsgroups names) is refused, whatever its callback would have written.

(in-package "ACL2")
(include-book "peer-authored-accept")

;   :commit                     the plan files RECEIVED in exactly GROUPS
;   (:refused REASON)           the plan's own refusal
;   (:refused :not-filed)       the plan files it elsewhere than GROUPS
(defun fn-obc-commit-gate (received groups domain)
  (declare (xargs :guard t))
  (let ((plan (fn-pa-filing-plan received groups domain)))
    (cond ((not (equal (car plan) :file)) plan)
          ((equal (cadr plan) groups) :commit)
          (t (list :refused :not-filed)))))

; KEYSTONE.  The callback runs only under `:commit', and `:commit' means the
; filing plan the host calls for every other ingress files RECEIVED in
; exactly the groups the commit names.
(defthm fn-obc-commit-only-after-filing
  (implies (equal (fn-obc-commit-gate received groups domain) :commit)
           (equal (fn-pa-filing-plan received groups domain)
                  (list :file groups)))
  :hints (("Goal" :in-theory (disable fn-pa-filing-plan))))

; With C1's keystone: a control article commits only in its filing group,
; which is in the operator's domain, never in a group its Newsgroups names.
(defthm fn-obc-control-commits-only-in-its-filing-group
  (implies (and (equal (car (fn-ctl-classify-octets received)) :control)
                (equal (fn-obc-commit-gate received groups domain) :commit))
           (let ((group (fn-ctl-filing-group
                         (cadr (fn-ctl-classify-octets received)))))
             (and (equal groups (list (fn-record-string-octets group)))
                  (fn-ctl-control-group-namep group)
                  (fn-ctl-memberp group domain))))
  :hints (("Goal" :use ((:instance fn-obc-commit-only-after-filing)
                        (:instance fn-ctl-control-article-is-filed-only-in-control))
           :in-theory (disable fn-obc-commit-gate fn-pa-filing-plan
                               fn-ctl-classify-octets fn-record-string-octets
                               fn-obc-commit-only-after-filing
                               fn-ctl-control-article-is-filed-only-in-control))))

(in-theory (disable fn-obc-commit-gate))
