; Actual retained-source mutation called once by PrepareIntent after preflight.
; Inputs are private aliases read in its SAME owner span, never native arguments.
(in-package "ACL2")
(include-book "snapshot-source-token")
(include-book "state-globals")
(defun fn-owner-admission-retain-prepare-source
 (token epoch count frontier base-store canonical current parent config
        obligation-view reader-view posting-config state)
 (declare (xargs :stobjs state :guard (acl2-numberp frontier)))
 (let* ((state (f-put-global 'fn-owner-canonical-admission-executor
                (list :admission-prepare-intent token epoch count
                      (cons count (1- frontier)) base-store canonical current) state))
        (state (f-put-global 'fn-owner-history-semantic-source
                (list :history-semantic-source token parent config) state))
        (state (f-put-global 'fn-owner-history-semantic-obligation-base
                (list :history-obligation-base token obligation-view) state))
        (state (f-put-global 'fn-owner-history-semantic-reader-base
                (list :history-reader-base token reader-view posting-config) state)))
  state))
(defthm fn-owner-admission-capture-retains-count-base-and-source
 (let* ((next (fn-owner-admission-retain-prepare-source
               token epoch count frontier base-store canonical current parent config
               obligation-view reader-view posting-config state))
        (intent (f-get-global 'fn-owner-canonical-admission-executor next)))
  (and (equal (fn-omk-at 3 intent) count)
       (equal (fn-omk-at 5 intent) base-store)
       (equal (fn-omk-at 7 intent) current)
       (equal (f-get-global 'fn-owner-history-semantic-source next)
              (list :history-semantic-source token parent config))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-owner-admission-retain-prepare-source fn-omk-at))))
