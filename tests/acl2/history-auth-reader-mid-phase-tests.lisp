(in-package "ACL2")
(include-book "../../books/history-auth-reader-source")
; Only actual scalar phase dispatch/fencing; no page-authentication claim.
(defconst *hsrm-source* '(9 (17 2) 1 0))
(defconst *hsrm-begin*
 (mv-let (word cursor binding)
  (fn-hsr-source-begin '(:pgs-commit 1 7 10 0 0) *hsrm-source* 31 :resource)
  (list word cursor binding)))
(assert-event
 (let ((c (cadr *hsrm-begin*)) (b (caddr *hsrm-begin*)))
  (and (equal (car *hsrm-begin*) :idle) (fn-hsr-source-boundp b c)
       (equal (fn-hsr-source-action
                '(:need-byte (9 (17 2) 1 0) :mid-character 0 5 8) b 31 c)
              '(:select 5)))))
(assert-event
 (let ((c (cadr *hsrm-begin*)) (b (caddr *hsrm-begin*)))
  (and (fn-hsr-source-boundp b c)
       (equal (fn-hsr-source-action
                '(:need-byte (9 (17 2) 1 0) :unknown-character 0 5 8) b 31 c)
              '(:refused :source-demand))
       (equal (fn-hsr-source-action
                '(:need-byte (9 (17 2) 1 1) :mid-character 0 5 8) b 31 c)
              '(:refused :source-demand)))))
