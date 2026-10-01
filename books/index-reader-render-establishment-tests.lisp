(in-package "ACL2")
(include-book "index-reader-render-establishment")

; MODEL: synthetic captured publication/source/claim/receipt seeds. Actual
; query registration and actual intent/install transitions are executed.
(defun-nx ircfinal-setup ()
 (let* ((token '(:index-query 17 1 0 7))
        (publication (fn-ipub-make 7 nil nil 1 19 7 nil 0 11 nil 0 12 nil 13 nil nil 4 1))
        (pin (list :publication-pin '(:index-generation 91 1 0) publication))
        (grant '(:query-grant 17 1 0 7 11 12 1 19 7 4 1))
        (source '(:receiver-source (:receiver-turn 33) :rx-token :provider))
        (effects '((:reply (65 66))))
        (request (list :reader-request :preOC pin publication token nil effects :origin :holder source))
        (actor (list :reader-actor :recipient source :response-owned request :step))
        (receipt (list :index-request-receipt :recipient 17 0 nil nil request :committed :step nil actor))
        (control (fn-ibr-begin 17 7 effects pin grant :origin))
        (row (list :receiver-custody source :recipient :original 0 3 :query-owned token nil
                   (list :reader-response-roots :parser actor) nil nil))
        (capture (fn-ibp-capture-make 7 nil nil 1 19 nil 0 11 nil 0 12))
        (context (list :reader-context :preOC pin publication token :payload effects :origin receipt row))
        (segment (update-fn-ibp-qs-id 1 (create-fn-ibp-query-segment)))
        (registered (mv-list 2 (fn-ibp-slot-register token :range control capture context segment)))
        (segment (update-fn-ibp-qs-admissionsi 0 (list grant '(1 0 0 0 0) :active 1) (nth 1 registered))))
  (list token control segment)))
(defthm ircfinal-actual-intent-install-model-positive
 (let* ((s (ircfinal-setup)) (token (nth 0 s)) (before (nth 2 s))
        (intent (fn-irc-slot-render-intent token before))
        (answer (fn-irc-slot-render-install token (mv-nth 1 intent) (create-fn-render-holder)))
        (qs (mv-nth 1 answer)) (rh (mv-nth 2 answer))
        (row (fn-irc-context-custody (fn-ibp-qs-inputsi 0 qs))))
  (and (fn-ibp-query-slot-livep token before) (fn-irc-slot-sourcep token before)
       (eq (mv-nth 0 intent) :render-intent-recorded)
       (eq (mv-nth 0 answer) :installed)
       (equal (fn-rh-plan rh) (fn-spp-at 4 (fn-ibp-qs-controlsi 0 qs)))
       (eq (fn-omk-at 6 row) :render-owned)
       (equal (fn-omk-at 8 row)
              (list :receiver-render-root (fn-rh-live rh) (fn-rh-plan rh)
                    (fn-rh-pin rh) (fn-rh-query rh) (fn-rh-resource rh) (fn-rh-origin rh)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable ircfinal-setup))))

; MUTATION / unreachable-in-composition: corrupt persisted intent and then
; counterfactually invoke install after intent reports recovery-required.
; The real serialized registered caller stops before that call.
(defthm ircfinal-intent-status-removal-mutation
 (let* ((s (ircfinal-setup)) (token (nth 0 s)) (control (nth 1 s))
        (before (nth 2 s)) (context (fn-ibp-qs-inputsi 0 before))
        (row (fn-irc-context-custody context))
        (old-plan (fn-spp-begin (fn-splan-of-effects '((:reply (99)))) :origin
                    (fn-spp-resource (fn-spp-at 4 control))))
        (old-control (fn-ibr-make 17 7 :position old-plan (fn-spp-at 5 control) nil nil nil))
        (row (update-nth 8 (list :receiver-render-intent token old-control)
               (update-nth 6 :render-install-intent row)))
        (before (update-fn-ibp-qs-inputsi 0 (update-nth 9 row context) before))
        (intent (fn-irc-slot-render-intent token before))
        (answer (fn-irc-slot-render-install token (mv-nth 1 intent) (create-fn-render-holder)))
        (qs (mv-nth 1 answer)) (rh (mv-nth 2 answer))
        (next-row (fn-irc-context-custody (fn-ibp-qs-inputsi 0 qs))))
  (and (fn-irc-slot-sourcep token before)
       (eq (mv-nth 0 intent) :recovery-required)
       (not (eq (mv-nth 0 intent) :render-intent-recorded))
       (eq (mv-nth 0 answer) :installed)
       (not (and (equal (fn-rh-plan rh) (fn-spp-at 4 (fn-ibp-qs-controlsi 0 qs)))
          (eq (fn-omk-at 6 next-row) :render-owned)
          (equal (fn-omk-at 8 next-row)
                 (list :receiver-render-root (fn-rh-live rh) (fn-rh-plan rh)
                       (fn-rh-pin rh) (fn-rh-query rh) (fn-rh-resource rh) (fn-rh-origin rh)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable ircfinal-setup))))
; MUTATION / unreachable-in-composition: preoccupied RH; the outer caller
; checks busy before intent. Low-slot status remains a necessary fence.
(defthm ircfinal-install-status-removal-mutation
 (let* ((s (ircfinal-setup)) (token (nth 0 s)) (control (nth 1 s))
        (before (nth 2 s))
        (old-plan (fn-spp-begin (fn-splan-of-effects '((:reply (99)))) :origin
                    (fn-spp-resource (fn-spp-at 4 control))))
        (occupied (mv-nth 1 (fn-rh-producer-install-positioned old-plan
                    (fn-spp-at 5 control) token (fn-spp-resource old-plan) :origin
                    (create-fn-render-holder))))
        (intent (fn-irc-slot-render-intent token before))
        (answer (fn-irc-slot-render-install token (mv-nth 1 intent) occupied))
        (qs (mv-nth 1 answer)) (rh (mv-nth 2 answer))
        (next-row (fn-irc-context-custody (fn-ibp-qs-inputsi 0 qs))))
  (and (fn-irc-slot-sourcep token before)
       (fn-rh-live occupied)
       (eq (mv-nth 0 intent) :render-intent-recorded)
       (eq (mv-nth 0 answer) :recovery-required)
       (not (eq (mv-nth 0 answer) :installed))
       (not (and (equal (fn-rh-plan rh) (fn-spp-at 4 (fn-ibp-qs-controlsi 0 qs)))
          (eq (fn-omk-at 6 next-row) :render-owned)
          (equal (fn-omk-at 8 next-row)
                 (list :receiver-render-root (fn-rh-live rh) (fn-rh-plan rh)
                       (fn-rh-pin rh) (fn-rh-query rh) (fn-rh-resource rh) (fn-rh-origin rh)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable ircfinal-setup))))
