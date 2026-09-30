; Actual selected owner callback runtime witnesses. Source WIP until the
; modern coherent root admits. These use no readiness Boolean and do not
; install a native callback. Each test process owns its disposable STATE.
(in-package "ACL2")
(include-book "../../books/owner-connection-callbacks")

(defconst *ocbt-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*)))
; Use the actual observed opener and its three recovery barriers. Merely
; pairing an empty initial Store with generation1 would omit its history.
(defconst *ocbt-opened*
  (fn-cpo-open-observed (list *fn-cfg-default-record*) 0 nil))
(assert-event (fn-sn-open-okp *ocbt-opened*))
(defconst *ocbt-store*
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-open-state *ocbt-opened*)
                        :recovery-barrier :ok)
              :recovery-barrier :ok)
    :recovery-barrier :ok))
(defconst *ocbt-owner*
  (fn-ocfg-make (fn-own-start *ocbt-store* 4) *ocbt-config* nil nil))
(assert-event (fn-ocl-relation *ocbt-owner*))

; Actual guard metadata, not source declarations or runtime installation.
(assert-event
 (and (eq (symbol-class 'fn-owner-callback-open (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-callback-open-peer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-callback-exposure-open (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-callback-close (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-callback-fault (w state)) :common-lisp-compliant)))

(defun ocbt-initialize (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner-reader-views nil state))
         (state (f-put-global 'fn-owner-auth nil state))
         (state (f-put-global 'fn-owner-credits (fn-mca-default 4096) state))
         (state (fn-owner-install-ocfg *ocbt-owner* state)))
    state))

(defun ocbt-open-fault (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (ocbt-initialize state))
         (selected (fn-owner-ocfg state))
         (reference (fn-ocfg-open selected (fn-owner-auth state)))
         (entry-credits (f-get-global 'fn-owner-credits state))
         (opened-view (fn-rov-update (fn-rov-owner-ledger state)
                         (fn-rov-oc-ledger (cdr reference))
                         (fn-owner-obligation-view state)))
         (antecedent (fn-ocl-relation selected)))
    (mv-let (erp id state) (fn-owner-callback-open state)
      (let* ((opened-ok
               (and antecedent (not erp) (equal id 0)
                    (equal (fn-owner-ocfg state) (cdr reference))
                    (equal (f-get-global 'fn-owner-effects state) (car reference))
                    (equal (f-get-global 'fn-owner-output state)
                           (fn-served-reply-octets (car reference)))
                    (equal (f-get-global 'fn-owner-closep state)
                           (fn-served-closingp (car reference)))
                    (equal (f-get-global 'fn-owner-starttlsp state)
                           (if (fn-served-starttlsp (car reference)) t nil))
                    (equal (f-get-global 'fn-owner-submittedp state)
                           (if (fn-served-submission (car reference)) t nil))
                    (equal (f-get-global 'fn-owner-log-line state)
                           (fn-olog-connection-line
                             (fn-ocfg-owner (cdr reference)) id nil))
                    (equal (fn-owner-reader-views state) nil)
                    (equal (fn-owner-obligation-view state) opened-view)
                    (equal (f-get-global 'fn-owner-credits state) entry-credits)
                    (consp (fn-own-find-conn id
                             (fn-own-conns (fn-owner-core state))))))
             (before (fn-owner-ocfg state))
             (credits (fn-owner-credits state))
             (view (fn-owner-obligation-view state))
             (ledger (fn-rov-owner-ledger state))
             (result (fn-ocfg-fault before id)))
        (mv-let (fault-erp word state) (fn-owner-callback-fault id state)
          (let ((checked
                 (and opened-ok (not fault-erp) (eq word :faulted)
                      (equal (fn-owner-ocfg state) (cdr result))
                      (equal (f-get-global 'fn-owner-effects state) (car result))
                      (equal (f-get-global 'fn-owner-output state)
                             (fn-served-reply-octets (car result)))
                      (equal (f-get-global 'fn-owner-closep state)
                             (fn-served-closingp (car result)))
                      (equal (f-get-global 'fn-owner-starttlsp state)
                             (if (fn-served-starttlsp (car result)) t nil))
                      (equal (f-get-global 'fn-owner-submittedp state)
                             (if (fn-served-submission (car result)) t nil))
                      (equal (f-get-global 'fn-owner-credits state)
                             (fn-mca-close credits id))
                      (equal (fn-owner-obligation-view state)
                             (fn-rov-update ledger
                               (fn-rov-oc-ledger (cdr result)) view)))))
            (value checked)))))))

(assert-event (mv-let (erp checked state) (ocbt-open-fault state)
                (mv (and (not erp) checked) state))
              :stobjs-out '(nil state))

(defun ocbt-close (state)
  (declare (xargs :stobjs state :mode :program))
  (with-local-stobj fn-arena
    (mv-let (checked fn-arena state)
      (let* ((state (ocbt-initialize state)))
        (mv-let (open-erp id state) (fn-owner-callback-open state)
          (let* ((before (fn-owner-ocfg state))
                 (next (fn-ocfg-close before id))
                 (credits (fn-owner-credits state))
                 (ledger (fn-rov-owner-ledger state))
                 (view (fn-owner-obligation-view state))
                 (state (f-put-global 'ocbt-unaffected :sentinel state)))
            (mv-let (erp word state) (fn-owner-callback-close id fn-arena state)
              (mv (and (not open-erp) (equal id 0) (not erp) (eq word :closed)
                       (equal (fn-owner-ocfg state) next)
                       (equal (f-get-global 'fn-owner-credits state)
                              (fn-mca-close credits id))
                       (equal (fn-owner-obligation-view state)
                              (fn-rov-update ledger (fn-rov-oc-ledger next) view))
                       (equal (f-get-global 'ocbt-unaffected state) :sentinel)
                       (not (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))))
                  fn-arena state)))))
      (value checked))))

(assert-event (mv-let (erp checked state) (ocbt-close state)
                (mv (and (not erp) checked) state))
              :stobjs-out '(nil state))

; Corrupted-state hypothesis removal for the selected-owner relation only.
; No real transition makes this non-article archive. Runtime guards remain
; satisfied, but the carried reader's projection differs from reference.
(defconst *ocbt-bad-owner*
  (let* ((v (fn-own-view (fn-ocfg-owner *ocbt-owner*)))
         (a (fn-own-view-archive v))
         (bad-a (fn-make-state (fn-state-groups a) (fn-state-nexts a)
                   (cons 'junk (fn-state-articles a))
                   (fn-state-next-txid a) (fn-state-pending a)
                   (fn-state-fenced a))))
    (fn-ocfg-with-view *ocbt-owner* (update-nth 2 bad-a v))))

(defun ocbt-reader-relation-removal (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (ocbt-initialize state))
         (state (fn-owner-install-ocfg *ocbt-bad-owner* state))
         (selected (fn-ocfg-at-reader-view (fn-owner-ocfg state)
                    (fn-owner-reader-views state)))
         (reference (fn-ocfg-open selected (fn-owner-auth state)))
         (remaining (boundp-global 'fn-owner state))
         (omitted (fn-ocl-relation selected)))
    (mv-let (erp id state) (fn-owner-callback-open state)
      (value (and remaining (not omitted) (not erp) (equal id 0)
                  (not (equal (fn-owner-ocfg state) (cdr reference))))))))

(assert-event
 (mv-let (erp checked state) (ocbt-reader-relation-removal state)
   (mv (and (not erp) checked) state))
 :stobjs-out '(nil state))
