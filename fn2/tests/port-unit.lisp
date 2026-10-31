; The port form's expansion-time refusals (fn2/docs/e-surface.md section 2):
; each malformed declaration below is refused by the macro, and one
; well-formed carrier over the same port is admitted beside them.
(in-package "ACL2")
(include-book "../books/consumer-port")
(include-book "std/testing/must-fail" :dir :system)

; A durable verb whose lost reply cannot be settled.
(must-fail (defport fn2-bad-port-a :fields ((x :u8)) :reasons ()
             :verbs ((put :request (x) :result () :effect :durable :retry :repeat :grant (:append x)
                          :meter (:requests) :reasons () :spec "test")))
           :expected :hard)
; A verb restating a precondition's word, which the generator adds itself.
(must-fail (defport fn2-bad-port-b :fields ((x :u8)) :reasons ()
             :verbs ((get :request (x) :result () :effect :read :retry :repeat :grant (:read x)
                          :meter (:requests) :reasons (access) :spec "test")))
           :expected :hard)
; A grant over a field the request does not carry.
(must-fail (defport fn2-bad-port-c :fields ((x :u8) (y :u8)) :reasons ()
             :verbs ((get :request (x) :result () :effect :read :retry :repeat :grant (:read y)
                          :meter (:requests) :reasons () :spec "test")))
           :expected :hard)
; Append bound to ARTICLE: ARTICLE has no terminal reply of class uncertain.
(must-fail (defcarrier fn2-bad-carrier-a :port fn2-consumer :grammar fn2-nntp
             :binds ((append article :terminal (:sent :no-msgid)))
             :loses ((read * :not-carried) (register * :not-carried) (rebase * :not-carried)
                     (unregister * :not-carried) (wait * :not-carried) (ack * :not-carried)
                     (position * :not-carried) (status * :not-carried) (fetch * :not-carried))))
; POST's 340 is a continuation: naming it alone leaves refusal and uncertainty unrepresented.
(must-fail (defcarrier fn2-bad-carrier-b :port fn2-consumer :grammar fn2-nntp
             :binds ((append post :terminal (:send)))
             :loses ((read * :not-carried) (register * :not-carried) (rebase * :not-carried)
                     (unregister * :not-carried) (wait * :not-carried) (ack * :not-carried)
                     (position * :not-carried) (status * :not-carried) (fetch * :not-carried))))
; A verb neither bound, refused nor declared not carried.
(must-fail (defcarrier fn2-bad-carrier-c :port fn2-consumer :frame :fnct
             :binds ((register 4 0) (ack 4 1))))
; Two verbs on one request code.
(must-fail (defcarrier fn2-bad-carrier-d :port fn2-consumer :frame :fnct
             :binds ((register 4 0) (ack 4 0) (position 4 2) (unregister 4 3) (read 4 5) (status 4 6)
                     (wait 4 9) (append 4 11) (rebase 4 12) (fetch 4 13))))
; A loss naming a field the verb does not have.
(must-fail (defcarrier fn2-bad-carrier-e :port fn2-consumer :grammar fn2-nntp
             :binds ((append post :terminal (:received :refused-duplicate :uncertain))
                     (fetch article :terminal (:sent :no-msgid)))
             :loses ((append cursor :reply-code-only)
                     (read * :not-carried) (register * :not-carried) (rebase * :not-carried)
                     (unregister * :not-carried) (wait * :not-carried) (ack * :not-carried)
                     (position * :not-carried) (status * :not-carried))))

; The bridge N then R loses exactly N's append losses.
(assert-event (equal (fn2-port-loss-union (fn2-consumer-nntp-loss 'append) (fn2-consumer-remote-loss 'append))
                     (fn2-consumer-nntp-loss 'append)))
(assert-event (equal (fn2-consumer-nntp-loss 'ack) '((* . :not-carried))))
(assert-event (and (fn2-consumer-outcome-p 'append '(:refused conflict :evidence-committed))
                   (not (fn2-consumer-outcome-p 'read '(:uncertain :log-write)))
                   (equal (fn2-consumer-admit 'append nil :ok) '(:refused access))
                   (equal (fn2-consumer-admit 'append t :shared) :park)))
