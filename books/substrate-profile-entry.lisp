; SUB-008: selected-profile decoding of an actual signed policy carrier.
; This emits evidence candidates, not authority or durable acceptance.
(in-package "ACL2")
(include-book "substrate-commit-profile-resume")

(defun fn-stpe-start (profile group statement)
 (declare (xargs :guard (fn-stmt-p statement)
                 :guard-hints (("Goal" :in-theory (enable fn-stmt-p)))))
 (list :fn-stpe profile group statement
       (fn-stcp-decode-start profile (fn-stmt-payload statement))
       (if (equal (fn-stmt-kind statement) :policy) nil :not-policy)))
(defun fn-stpe-wrap (cursor decoder used)
 (declare (xargs :guard t))
 (let* ((profile (fn-stcp-at 1 cursor))
        (group (fn-stcp-at 2 cursor))
        (statement (fn-stcp-at 3 cursor))
        (why (fn-stcp-at 5 cursor))
        (result (fn-stcp-dec-result decoder))
        (next (list :fn-stpe profile group statement decoder why)))
  (cond (why (mv :refused next (fn-stmt-error why) used))
        ((not (fn-stcp-terminalp decoder)) (mv :yield next nil used))
        ((fn-stmt-okp result)
         (mv :done next
             (list :fn-stpe-envelope profile group statement
                   (fn-stmt-value result)) used))
        (t (mv :refused next result used)))))
(defun fn-stpe-resume (cursor)
 (declare (xargs :guard t))
 (if (fn-stcp-at 5 cursor)
     (fn-stpe-wrap cursor (fn-stcp-at 4 cursor) 0)
  (mv-let (decoder used)
   (fn-stcp-decode-resume-acc (fn-stcp-at 1 cursor) (fn-stcp-at 4 cursor))
   (fn-stpe-wrap cursor decoder used))))
(defun fn-stpe-resume-model (cursor)
 (declare (xargs :guard t))
 (if (fn-stcp-at 5 cursor)
     (fn-stpe-wrap cursor (fn-stcp-at 4 cursor) 0)
  (mv-let (decoder used)
   (fn-stcp-decode-resume (fn-stcp-at 1 cursor) (fn-stcp-at 4 cursor))
   (fn-stpe-wrap cursor decoder used))))
; Complete output/cursor/work correspondence of the execution boundary.
(defthm fn-stpe-resume-refines-model
 (equal (fn-stpe-resume cursor) (fn-stpe-resume-model cursor))
 :hints (("Goal"
  :use ((:instance fn-stcp-decode-resume-acc-is-resume
                  (p (fn-stcp-at 1 cursor)) (c (fn-stcp-at 4 cursor))))
  :in-theory (union-theories (theory 'minimal-theory)
                            '(fn-stpe-resume fn-stpe-resume-model)))))
(defthm fn-stpe-resume-preserves-carrier
 (and (equal (fn-stcp-at 1 (mv-nth 1 (fn-stpe-resume cursor)))
             (fn-stcp-at 1 cursor))
      (equal (fn-stcp-at 2 (mv-nth 1 (fn-stpe-resume cursor)))
             (fn-stcp-at 2 cursor))
      (equal (fn-stcp-at 3 (mv-nth 1 (fn-stpe-resume cursor)))
             (fn-stcp-at 3 cursor)))
 :hints (("Goal" :in-theory
  (union-theories (theory 'minimal-theory)
                 '(fn-stpe-resume fn-stpe-wrap fn-stcp-at mv-nth nth zp
                   fn-cbor-ag-car fn-cbor-ag-cdr car-cons cdr-cons)))))
