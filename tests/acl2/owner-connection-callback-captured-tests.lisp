; Positive actual capture branch, through the existing capture transition.
; A captured related D satisfies the literal selected-source antecedent.
(in-package "ACL2")
(include-book "owner-connection-callback-tests")

(defun ocbt-captured-reader-complete (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (ocbt-initialize state))
         (working (fn-own-view (fn-owner-core state)))
         (views (fn-ocv-capture nil :start working))
         (state (f-put-global 'fn-owner-reader-views views state))
         (selected (fn-ocfg-at-reader-view (fn-owner-ocfg state) views))
         (antecedent (fn-ocl-relation selected))
         (opened (fn-ocfg-open selected (fn-owner-auth state)))
         (id (fn-own-next-id (fn-ocfg-owner selected)))
         (next (fn-ocfg-with-view (cdr opened) working))
         (entry-view (fn-owner-obligation-view state))
         (credits (f-get-global 'fn-owner-credits state)))
    (mv-let (erp actual-id state) (fn-owner-callback-open state)
      (value
       (and (consp views) antecedent
            (not erp)
            (equal actual-id
                   (if (fn-own-find-conn id
                        (fn-own-conns (fn-ocfg-owner (cdr opened)))) id nil))
            (equal (fn-owner-ocfg state) next)
            (equal (f-get-global 'fn-owner-effects state) (car opened))
            (equal (f-get-global 'fn-owner-output state)
                   (fn-served-reply-octets (car opened)))
            (equal (f-get-global 'fn-owner-closep state)
                   (fn-served-closingp (car opened)))
            (equal (f-get-global 'fn-owner-starttlsp state)
                   (if (fn-served-starttlsp (car opened)) t nil))
            (equal (f-get-global 'fn-owner-submittedp state)
                   (if (fn-served-submission (car opened)) t nil))
            (equal (f-get-global 'fn-owner-log-line state)
                   (fn-olog-connection-line (fn-ocfg-owner (cdr opened)) id nil))
            (equal (fn-owner-reader-views state) views)
            (equal entry-view :ocbt-parked-view)
            (equal (fn-owner-obligation-view state) entry-view)
            (equal (f-get-global 'fn-owner-credits state) credits))))))

(assert-event
 (mv-let (erp checked state) (ocbt-captured-reader-complete state)
   (mv (and (not erp) checked) state))
 :stobjs-out '(nil state))
