; Read-only scalar operator observation; no allocation or settlement authority.
(in-package "ACL2")
(include-book "operation-diagnostics")
(include-book "history-semantic-writer-state")

(defun fn-oor-report (current reason epoch fault budget)
 (declare (xargs :guard (natp budget) :verify-guards nil))
 (let* ((token (fn-prl-nth 0 current))
        (live (fn-apr-livep token current))
        (charge (and live (fn-apr-naturals 5 (fn-prl-nth 1 current))
                     (fn-prl-nth 1 current)))
        (prefix '(111 112 101 114 97 116 105 111 110)))
  (if (< budget 10) (mv :response-budget-unavailable nil)
   (mv-let (word fields)
    (fn-od-fields
     (list
      (cons '(111 98 115 101 114 118 97 116 105 111 110) (if live :observed :unavailable))
      (cons '(114 101 97 115 111 110) reason)
      (cons '(97 100 109 105 115 115 105 111 110 45 110 111 110 99 101) (and live (fn-prl-nth 1 token)))
      (cons '(111 112 101 114 97 116 105 111 110 45 107 105 110 100) (and live (fn-prl-nth 6 token)))
      (cons '(112 104 97 115 101) (and live (fn-prl-nth 2 current)))
      (cons '(101 112 111 99 104) epoch)
      (cons '(116 120 105 100) (and live (fn-prl-nth 5 token)))
      (cons '(104 111 108 100 48) (fn-prl-nth 0 charge))
      (cons '(104 111 108 100 49) (fn-prl-nth 1 charge))
      (cons '(104 111 108 100 50) (fn-prl-nth 2 charge))
      (cons '(104 111 108 100 51) (fn-prl-nth 3 charge))
      (cons '(104 111 108 100 52) (fn-prl-nth 4 charge))
      (cons '(102 97 117 108 116) fault)) (- budget 10))
    (if (eq word :rendered) (mv word (append prefix fields '(10)))
     (mv word nil))))))

(defun fn-owner-operation-report (budget state)
 (declare (xargs :stobjs state :guard (natp budget) :verify-guards nil))
 (let* ((current (fn-apr-owner-current state))
        (token (fn-prl-nth 0 current))
        (fault (and (boundp-global 'fn-owner-history-completion-fault state)
                    (f-get-global 'fn-owner-history-completion-fault state)))
        (reason (cond (fault :recovery-required)
                      ((not current) :operation-not-issued)
                      ((not (fn-apr-livep token current)) :runtime-operation-unavailable)
                      (t (fn-owner-history-writer-gate token state)))))
  (fn-oor-report current reason (fn-owner-canonical-epoch state)
                 (and (symbolp fault) fault) budget)))

(verify-guards fn-oor-report
 :hints (("Goal" :in-theory (disable fn-od-fields fn-apr-livep fn-apr-naturals fn-prl-nth))))
(verify-guards fn-owner-operation-report
 :hints (("Goal" :in-theory (disable fn-oor-report))))
; `fn-od-len-append' is local to books/operation-diagnostics.lisp, so the
; rendered line's length (prefix, fields, newline) needs it again here.
(local
 (defthm fn-oor-len-append
  (equal (len (append x y)) (+ (len x) (len y)))
  :hints (("Goal" :induct (append x y)))))
(local
(defthm fn-oor-fields-budget
 (implies (natp budget)
  (<= (len (mv-nth 1 (fn-od-fields fields budget))) budget))
 :hints (("Goal" :use ((:instance fn-od-fields-within-budget))
                 :in-theory (disable fn-od-fields)))
 :rule-classes :linear))
(defthm fn-oor-report-within-budget
 (implies (natp budget)
  (<= (len (mv-nth 1 (fn-oor-report current reason epoch fault budget))) budget))
 :hints (("Goal" :in-theory (e/d (fn-oor-report) (fn-od-fields fn-apr-livep fn-apr-naturals fn-prl-nth))))
 :rule-classes nil)
