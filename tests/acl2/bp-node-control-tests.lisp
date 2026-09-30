; Teeth for the host-called startup, authority and socket completion machine.
(in-package "ACL2")
(include-book "../../books/bp-node-control")
(defun bpnc-words (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (bpnc-words (cdr words)))
    nil))
(defconst *bpnc-config*
  (append (fn-record-string-octets "[store]") '(10)
          (fn-record-string-octets "path = \"/srv/fn\"") '(10)))
(defconst *bpnc-store* (fn-record-string-octets "/srv/fn"))
(defconst *bpnc-ready* (fn-bpnc-startup *bpnc-config* *bpnc-store*))
; Complete positive witness: actual parsed startup antecedent and conclusion.
(assert-event
 (and (equal (fn-ncfg-nth 0 *bpnc-ready*) :ready)
      (let ((loaded (fn-native-config-load *bpnc-config*)))
        (and (equal (fn-ncfg-nth 0 loaded) :accepted)
             (equal (fn-record-string-octets
                     (fn-native-config-store (fn-ncfg-nth 1 loaded))) *bpnc-store*)))))
; Remove :ready: accepted config retained; mismatched Store conclusion false.
(assert-event
 (let* ((other (fn-record-string-octets "/srv/other"))
        (r (fn-bpnc-startup *bpnc-config* other))
        (loaded (fn-native-config-load *bpnc-config*)))
   (and (not (equal (fn-ncfg-nth 0 r) :ready))
        (equal (fn-ncfg-nth 0 loaded) :accepted)
        (not (equal (fn-record-string-octets
                     (fn-native-config-store (fn-ncfg-nth 1 loaded))) other)))))
(defconst *bpnc-admin*
  (list :admin (bpnc-words '("bp-route" "add" "dtn://fn-b/" "relay" "100"))))
(defconst *bpnc-grant* (fn-bpnc-turn-plan t *bpnc-admin*))
(assert-event
 (and (equal (fn-ncfg-nth 0 *bpnc-grant*) :execute)
      (equal t t)
      (equal (fn-ncfg-nth 0 *bpnc-admin*) :admin)
      (equal (fn-ncfg-nth 1 *bpnc-grant*)
             (fn-native-admin-plan (fn-ncfg-nth 1 *bpnc-admin*)))
      (equal (fn-native-admin-result-status (fn-ncfg-nth 1 *bpnc-grant*)) :accepted)
      (member-equal (fn-native-admin-result-kind (fn-ncfg-nth 1 *bpnc-grant*))
                    '(:set-bp-route :remove-bp-route))))
; Remove :execute: same valid admin parser retained; owner conclusion fails.
(assert-event
 (and (equal (fn-ncfg-nth 0 *bpnc-admin*) :admin)
      (equal (fn-native-admin-result-status
              (fn-native-admin-plan (fn-ncfg-nth 1 *bpnc-admin*))) :accepted)
      (not (equal nil t))
      (not (equal (fn-ncfg-nth 0 (fn-bpnc-turn-plan nil *bpnc-admin*)) :execute))))
; Mutation teeth: bypassing either authority gate would grant these.
(assert-event (equal (fn-bpnc-turn-plan nil *bpnc-admin*) '(:refused :not-owner)))
(assert-event
 (equal (fn-bpnc-turn-plan t (list :admin (bpnc-words '("group" "create" "fn.test"))))
        '(:refused :unsupported-bp-control-operation)))
(assert-event
 (equal (fn-ncfg-nth 0
         (fn-bpnc-turn-plan t (list :admin (bpnc-words '("bp-route" "remove" "dtn://fn-b/" "relay")))))
        :execute))
; Both sides of the complete open protocol, including a bind failure and an
; install failure.  Every literal equivalence is asserted, not just its tag.
(assert-event
 (and (equal (equal (fn-ncfg-nth 0 (fn-bpnc-socket-step
                                (fn-bpnc-socket-step (fn-bpnc-socket-initial *bpnc-ready*)
                                                     '(:bind-result :ok))
                                '(:install-result :ok))) :live)
             (and (equal (fn-ncfg-nth 0 *bpnc-ready*) :ready) (equal :ok :ok) (equal :ok :ok)))
      (equal (equal (fn-ncfg-nth 0 (fn-bpnc-socket-step
                                (fn-bpnc-socket-step (fn-bpnc-socket-initial *bpnc-ready*)
                                                     '(:bind-result :failed))
                                '(:install-result :ok))) :live)
             (and (equal (fn-ncfg-nth 0 *bpnc-ready*) :ready) (equal :failed :ok) (equal :ok :ok)))
      (equal (equal (fn-ncfg-nth 0 (fn-bpnc-socket-step
                                (fn-bpnc-socket-step (fn-bpnc-socket-initial *bpnc-ready*)
                                                     '(:bind-result :ok))
                                '(:install-result :failed))) :live)
             (and (equal (fn-ncfg-nth 0 *bpnc-ready*) :ready) (equal :ok :ok) (equal :failed :ok)))))
(defconst *bpnc-live* (fn-bpnc-socket-step
                                (fn-bpnc-socket-step (fn-bpnc-socket-initial *bpnc-ready*)
                                                     '(:bind-result :ok))
                                '(:install-result :ok)))
(assert-event
 (let* ((retiring (fn-bpnc-socket-step *bpnc-live* '(:stop)))
        (closed (fn-bpnc-socket-step retiring '(:retire-result :ok))))
   (and (member-equal (fn-ncfg-nth 0 *bpnc-live*) '(:prepared :bound :live))
        (equal (fn-ncfg-nth 0 (fn-bpnc-socket-action retiring)) :retire)
        (equal (fn-ncfg-nth 0 closed) (if (equal :ok :ok) :closed :fenced))
        (not (fn-bpnc-socket-action closed)))))
(assert-event
 (let* ((retiring (fn-bpnc-socket-step *bpnc-live* '(:stop)))
        (closed (fn-bpnc-socket-step retiring '(:retire-result :failed))))
   (and (member-equal (fn-ncfg-nth 0 *bpnc-live*) '(:prepared :bound :live))
        (equal (fn-ncfg-nth 0 (fn-bpnc-socket-action retiring)) :retire)
        (equal (fn-ncfg-nth 0 closed) (if (equal :failed :ok) :closed :fenced))
        (not (fn-bpnc-socket-action closed)))))
; Hypothesis removal, corrupted phase: no retained hypotheses.  STOP cannot
; manufacture a retire action from an already closed state.
(assert-event
 (let* ((st '(:closed nil nil 0)) (retiring (fn-bpnc-socket-step st '(:stop))))
   (and (not (member-equal (fn-ncfg-nth 0 st) '(:prepared :bound :live)))
        (not (equal (fn-ncfg-nth 0 (fn-bpnc-socket-action retiring)) :retire)))))

; The interface checker inspects this exact theorem property in the ACL2 world.
; Both actual host subjects must occur, without a :via exemption.
(assert-event
 (and (member-eq 'fn-bpnc-socket-initial
                 (all-fnnames
                  (getpropc 'fn-bpnc-open-run-live-iff-both-completions-succeed
                            'theorem nil (w state))))
      (member-eq 'fn-bpnc-socket-step
                 (all-fnnames
                  (getpropc 'fn-bpnc-open-run-live-iff-both-completions-succeed
                            'theorem nil (w state))))))
