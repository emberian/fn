; Actual inner authority finish; original node result and config are borrowed
; from the registered core producer. No external tuple confers source authority.
(in-package "ACL2")
(include-book "consumer-configured-authority-state")
(include-book "consumer-account-config-commit")
(include-book "stx-keyring-records")

(defun fn-cape-authority-finish (s produced next current-config base-row-carry)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((event (fn-cp-nth 0 (fn-cp-nth 15 s)))
        (es (fn-cp-nth 13 s)) (checked (fn-cp-nth 0 produced)))
  (cond
   ((not (or (fn-cac-eventp event) (fn-cab-eventp event)))
    (list :unavailable s :semantic-family-unavailable))
   ((not (equal (fn-cp-nth 1 event) es)) (fn-capr-fault s :event-sequence))
   ((not (eq (fn-stxk-context-kind checked) :ok)) (fn-capr-fault s :identity))
   ((not (eq (fn-cp-nth 2 produced) :carried))
    (list :unavailable s :identity-carries))
   ((not (and (eq (fn-cp-nth 3 produced) :none)
               (null (fn-cp-nth 4 produced)) (null (fn-cp-nth 5 produced))))
    (list :unavailable s :authority-identity-effect))
   (t
    (let* ((full (fn-acj-stage (fn-cp-nth 4 s) (fn-cp-nth 5 s)
                    (fn-cp-nth 6 s) current-config
                    event es base-row-carry))
           (pending (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 full))))
           (beginp (eq (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-begin)))
     (if (not (eq (fn-cp-nth 0 full) :ok)) (fn-capr-fault s full)
      (fn-capr-install s next checked (fn-cp-nth 1 produced) full
        (fn-cp-nth 6 full)
        (if beginp (nfix es) (if pending (fn-cp-nth 8 s) nil))
        (fn-cp-nth 9 s) (fn-cp-nth 10 s) (fn-cp-nth 11 s)
        (fn-cp-nth 12 s) (1+ (nfix es))
        (fn-cp-nth 14 s) (ec-call (cdr (fn-cp-nth 15 s))))))))))

(verify-guards fn-cape-authority-finish)

; Private E preparations never publish their candidate root. The eventual
; typed C transition is the sole account/config authority publication.
(local
 (defthm fn-cape-binding-preparation-results-have-no-root
  (and (equal (fn-cp-nth 2 (fn-bcp-stage prep event)) nil)
       (equal (fn-cp-nth 3 (fn-bcp-stage prep event)) nil)
       (equal (fn-cp-nth 2 (fn-bcp-tick prep rowcarry)) nil)
       (equal (fn-cp-nth 3 (fn-bcp-tick prep rowcarry)) nil)
       (equal (fn-cp-nth 2 (fn-bcp-expect prep login kind)) nil)
       (equal (fn-cp-nth 3 (fn-bcp-expect prep login kind)) nil)
       (equal (fn-cp-nth 2 (fn-bcp-seal prep)) nil)
       (equal (fn-cp-nth 3 (fn-bcp-seal prep)) nil))
  :hints (("Goal" :in-theory
           (e/d (fn-bcp-stage fn-bcp-tick fn-bcp-expect fn-bcp-seal fn-cp-nth)
                (fn-bcp-with fn-bcp-state fn-bcp-intent-lookup fn-cait-put-octets
                 fn-cab-eventp fn-cp-idp fn-aic-intent fn-aic-intent-carry
                 fn-bcp-binding-row fn-bcp-binding-row-carry fn-caac-list-cons))))))

(local
 (defthm fn-cape-stage-has-no-publication
  (implies (equal (fn-cp-nth 0 (fn-acj-stage cp metadata prep config event expected rowcarry)) :ok)
           (and (equal (fn-cp-nth 2 (fn-acj-stage cp metadata prep config event expected rowcarry)) nil)
                (equal (fn-cp-nth 3 (fn-acj-stage cp metadata prep config event expected rowcarry)) nil)))
  :hints (("Goal" :in-theory
           (e/d (fn-acj-stage fn-cp-nth)
                (fn-acj-stage-advance fn-caac-step fn-bcp-stage fn-bcp-tick
                 fn-bcp-expect fn-bcp-begin fn-bcp-seal fn-cab-eventp
                 fn-cac-eventp fn-caa-matching-pendingp fn-acj-metadata5)))))
 )

(defthm fn-cape-authority-finish-preserves-exposed-view-and-root
 (let ((after (fn-cp-nth 1
                         (fn-cape-authority-finish s produced next config rowcarry))))
           (and (equal (fn-cp-nth 9 after) (fn-cp-nth 9 s))
                (equal (fn-cp-nth 10 after) (fn-cp-nth 10 s))
                (equal (fn-cp-nth 11 after) (fn-cp-nth 11 s))
                (equal (fn-cp-nth 2 (fn-cp-nth 7 after))
                       (fn-cp-nth 2 (fn-cp-nth 7 s)))
                (equal (fn-cp-nth 3 (fn-cp-nth 7 after))
                       (fn-cp-nth 3 (fn-cp-nth 7 s)))))
 :hints (("Goal" :in-theory
          (e/d (fn-cape-authority-finish fn-capr-install fn-capr-state
                 fn-capr-publication fn-capr-fault fn-cp-nth)
               (fn-acj-stage fn-stxk-context-kind fn-cac-eventp fn-cab-eventp)))))

(in-theory (disable fn-cape-authority-finish))
