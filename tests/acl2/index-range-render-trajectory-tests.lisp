(in-package "ACL2")
(include-book "../../books/index-range-render-trajectory")
; Historical MODEL seeds; no actual publication/runtime/storage authority.
; The RH custody acquisition itself uses the actual internal constructor.
(defun-nx ibrtraj-setup ()
 (let* ((token '(:index-query 17 1 0 7))
        (arena '((65 66 67)))
        (publication (fn-ipub-make 7 nil nil 1 19 7 nil 0 11 nil 0 12 nil 13 nil nil 4 1))
        (plan (fn-spp-begin (fn-splan-of-effects '((:ignored 1) (:reply (65 66)) (:later 2)))
                           '(:source 17) '(:resource 18)))
        (control (fn-ibr-make 17 7 :position plan
                   (list :publication-pin '(:generation 7) publication) nil nil nil))
        (custody (list :receiver-custody :ticket :source :original 0 3 :query-owned token nil nil nil nil))
        (installed (mv-list 3 (fn-ibr-registered-render-custody-install control token custody (create-fn-render-holder))))
        (capture (fn-ibp-capture-make 7 nil nil 1 19 nil 0 11 nil 0 12))
        (claim '(:query-grant 17 1 0 7 11 12 1 19 7 4 1))
        (qpg (update-fn-qpg-segment-id 1 (create-fn-query-payload-grants)))
        (acquired (mv-list 3 (fn-qpg-acquire 17 0 7 4 1 claim qpg)))
        (context (list :query-context :saved :step :source :receiver (nth 1 acquired) nil nil nil (nth 1 installed)))
        (segment (update-fn-ibp-qs-id 1 (create-fn-ibp-query-segment)))
        (registered (mv-list 2 (fn-ibp-slot-register token :range control capture context segment)))
        (segment (update-fn-ibp-qs-admissionsi 0 (list claim '(1 0 0 0 0) :active 1) (nth 1 registered))))
  (list token (nth 2 installed) segment (nth 2 acquired) arena (nth 0 installed))))

(defthm ibrtraj-paired-position-reply-full-window-model-positive
 (let* ((s (ibrtraj-setup)) (token (nth 0 s)) (rh (nth 1 s))
        (qs (nth 2 s)) (qpg (nth 3 s)) (arena (nth 4 s))
        (position (fn-ibr-joint-segment-render-one 1 rh qs qpg arena nil))
        (rh1 (mv-nth 1 position)) (qs1 (mv-nth 2 position))
        (reply (fn-ibr-joint-segment-render-one 1 rh1 qs1 qpg arena (mv-nth 3 position)))
        (rh2 (mv-nth 1 reply)) (qs2 (mv-nth 2 reply)) (buffer (mv-nth 3 reply))
        (full (fn-ibr-joint-segment-render-one 1 rh2 qs2 qpg arena buffer)))
  (and (eq (nth 5 s) :installed)
       (fn-rh-live rh) (fn-ibp-query-slot-livep token qs)
       (fn-ibr-dispatch-domain-p rh qs arena)
       (fn-irc-slot-render-ready-p token qs rh)
       (fn-ibr-joint-segment-source-fence-p token qs qpg)
       (eq (mv-nth 0 position) :position)
       (fn-ibr-dispatch-domain-p rh1 qs1 arena)
       (eq (mv-nth 0 reply) :reply-byte) (equal buffer '(65))
       (equal (fn-rh-plan rh2) (fn-spp-at 4 (fn-ibp-qs-controlsi 0 qs2)))
       (equal (fn-ibp-qs-inputsi 0 qs2) (fn-ibp-qs-inputsi 0 qs))
       (equal (fn-rh-query rh2) (fn-rh-query rh))
       (equal (fn-rh-pin rh2) (fn-rh-pin rh))
       (equal (fn-rh-resource rh2) (fn-rh-resource rh))
       (equal (fn-rh-origin rh2) (fn-rh-origin rh))
       (eq (mv-nth 0 full) :output-full)
       (equal (mv-nth 1 full) rh2) (equal (mv-nth 2 full) qs2)
       (equal (mv-nth 3 full) buffer)))
 :rule-classes nil)

; MUTATION: corrupt only evolving RHplan; source/identity roots remain held.
(defthm ibrtraj-paired-plan-carry-removal-mutation
 (let* ((s (ibrtraj-setup)) (token (nth 0 s)) (arena (nth 4 s))
        (position (fn-ibr-joint-segment-render-one 1 (nth 1 s) (nth 2 s) (nth 3 s) arena nil))
        (rh (update-fn-rh-plan '(:bad-current-plan) (mv-nth 1 position)))
        (qs (mv-nth 2 position))
        (answer (fn-ibr-joint-segment-render-one 0 rh qs (nth 3 s) arena nil)))
  (and (fn-rh-live rh) (fn-ibp-query-slot-livep token qs)
       (not (fn-ibr-dispatch-domain-p rh qs arena))
       (not (equal (fn-rh-plan (mv-nth 1 answer))
                   (fn-spp-at 4 (fn-ibp-qs-controlsi
                    (nth 3 (fn-rh-query (mv-nth 1 answer))) (mv-nth 2 answer)))))))
 :rule-classes nil)


; MUTATION: a dead RH carries a corrupted stale plan, not an issued actor.
(defthm ibrtraj-live-premise-removal-mutation
 (let* ((s (ibrtraj-setup)) (token (nth 0 s)) (qs (nth 2 s)) (arena (nth 4 s))
        (rh (update-fn-rh-live nil (update-fn-rh-plan '(:bad-current-plan) (nth 1 s))))
        (answer (fn-ibr-joint-segment-render-one 0 rh qs (nth 3 s) arena nil)))
  (and (not (fn-rh-live rh)) (fn-ibp-query-slot-livep token qs)
       (fn-ibr-dispatch-domain-p rh qs arena)
       (eq (mv-nth 0 answer) :unavailable)
       (not (equal (fn-rh-plan (mv-nth 1 answer))
                   (fn-spp-at 4 (fn-ibp-qs-controlsi
                    (nth 3 (fn-rh-query (mv-nth 1 answer))) (mv-nth 2 answer)))))))
 :rule-classes nil)
; MUTATION: query slot cleared while old RH aliases survive; forbidden by
; the actual eventual all-alias terminal protocol, not a release witness.
(defthm ibrtraj-query-live-premise-removal-mutation
 (let* ((s (ibrtraj-setup)) (token (nth 0 s)) (rh (nth 1 s)) (arena (nth 4 s))
        (qs (update-fn-ibp-qs-controlsi 0 nil
              (update-fn-ibp-qs-ticketsi 0 0 (nth 2 s))))
        (answer (fn-ibr-joint-segment-render-one 0 rh qs (nth 3 s) arena nil)))
  (and (fn-rh-live rh) (not (fn-ibp-query-slot-livep token qs))
       (fn-ibr-dispatch-domain-p rh qs arena)
       (eq (mv-nth 0 answer) :unavailable-render-custody)
       (not (equal (fn-rh-plan (mv-nth 1 answer))
                   (fn-spp-at 4 (fn-ibp-qs-controlsi
                    (nth 3 (fn-rh-query (mv-nth 1 answer))) (mv-nth 2 answer)))))))
 :rule-classes nil)
