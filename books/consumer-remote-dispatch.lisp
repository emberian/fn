; All-eight selected operation dispatcher. It returns proposals/read plans;
; only the actual installed owner entry and durable finish can apply a write.
(in-package "ACL2")
(include-book "consumer-remote-completion")

; A current semantic capture coordinate, not a runtime/custody grant. Actual
; canonical source registration/lifetime/revalidation remains mandatory.
(defun fn-crx-coordinate (ingress cp configured-generation event-count)
 (declare (xargs :guard t))
 (list :remote-current (fn-cp-nth 6 ingress) configured-generation
       (fn-cp-nth 4 ingress) (fn-cp-nth 5 ingress) (fn-cp-nth 3 ingress)
       (fn-cp-nth 3 cp) (fn-cp-nth 4 cp) event-count))

(defun fn-crx-selected-plan (cp ingress cep definition configured-generation)
 (declare (xargs :guard t))
 (let* ((request (fn-cp-nth 1 ingress)) (op (fn-cp-nth 1 request))
        (old (fn-cp-nth 9 cep))
        (route (fn-cre-selected-route ingress old))
        (scope-key (fn-crs-key ingress configured-generation)))
  (cond ((not (eq (fn-cp-nth 0 ingress) :authenticated))
         (if (member-eq (fn-cp-nth 0 ingress) '(:refused :unavailable)) ingress
           '(:refused :authentication)))
        ((or (not (eq (fn-cp-nth 6 cep) :ready))
              (not (equal (fn-cp-nth 1 cep) (fn-cp-nth 4 request))))
         '(:refused :consumer-preparation-incomplete))
        ((not (eq (fn-cp-nth 0 route) :definition-request)) route)
        ((not (eq (fn-cp-nth 3 definition) :ready)) '(:refused :scope-incomplete))
        ((not (equal (fn-cp-nth 1 definition) scope-key)) '(:refused :scope-changed))
        (t
         (case op
          ((:register :rebase) (list :definition-proposal ingress cp cep definition))
          (:position (list :position (fn-cp-scope-cursor cp old)))
          (:status (list :status (fn-cp-nth 7 old) (fn-cp-nth 3 cp)
                         (nfix (- (nfix (fn-cp-nth 3 cp)) (nfix (fn-cp-nth 7 old))))))
          (:unregister (fn-cec-unregister-selected cp (fn-cp-nth 2 ingress)
                                 (fn-cp-nth 4 request) old))
          (:ack
           (let* ((bytes (fn-cp-nth 6 request))
                  (decoded (if (fn-cbor-at-mostp bytes *fn-cp-max-token*)
                                (fn-cp-cursor-decode bytes) '(:error :size))))
            (if (eq (fn-cp-nth 0 decoded) :ok)
                (fn-cec-ack-selected cp (fn-cp-nth 2 ingress)
                           (fn-cp-nth 4 old) (fn-cp-nth 5 ingress)
                           (fn-cp-nth 1 decoded) old) '(:refused :scope))))
          ((:poll :wait)
           (list :scan-request ingress cp old (fn-cp-nth 15 definition)
                 (fn-cp-nth 1 definition)
                 (if (eq op :wait) (fn-cp-nth 7 request) 0)))
          (otherwise '(:refused :operation)))))))

(local
 (defthm fn-crx-route-refusal-tag
  (implies (and (eq (fn-cp-nth 0 ingress) :authenticated)
                 (not (eq (fn-cp-nth 0 (fn-cre-selected-route ingress old)) :definition-request)))
           (equal (fn-cp-nth 0 (fn-cre-selected-route ingress old)) :refused))
  :hints (("Goal" :in-theory (e/d (fn-cre-selected-route fn-cp-nth)
                           (fn-cbor-at-mostp len))))))

(local
 (defthm fn-crx-nth-zero
  (equal (fn-cp-nth 0 xs) (if (consp xs) (car xs) nil))
  :hints (("Goal" :in-theory (enable fn-cp-nth)))))

(defthm fn-crx-selected-existing-plan-is-current-account-scoped
 (implies
  (and (fn-cp-nth 9 cep)
       (member-eq (fn-cp-nth 0 (fn-crx-selected-plan cp ingress cep definition generation))
                   '(:definition-proposal :position :status :write :no-op :scan-request)))
  (let ((old (fn-cp-nth 9 cep)))
   (and (eq (fn-cp-nth 0 ingress) :authenticated)
        (equal (fn-cp-nth 1 old) (fn-cp-nth 4 (fn-cp-nth 1 ingress)))
        (equal (fn-cp-nth 2 old) (fn-cp-nth 2 ingress))
        (equal (fn-cp-nth 9 old) (fn-cp-nth 3 ingress))
        (eq (fn-cp-nth 3 definition) :ready)
        (equal (fn-cp-nth 1 definition) (fn-crs-key ingress generation)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-cre-selected-existing-route-is-exact-account-and-consumer
                                 (old (fn-cp-nth 9 cep)))
                 (:instance fn-crx-route-refusal-tag (old (fn-cp-nth 9 cep))))
           :in-theory (e/d (fn-crx-selected-plan)
                          (fn-cre-selected-route fn-crs-key fn-cp-nth fn-cec-ack-selected
                           fn-cec-unregister-selected fn-cp-cursor-decode
                           fn-cp-scope-cursor fn-cbor-at-mostp len)))))

(in-theory (disable fn-crx-coordinate fn-crx-selected-plan))
