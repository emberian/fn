; Generic node retention mutation preservation used by ordered Store replay.
(in-package "ACL2")
(include-book "node-invariants")
(include-book "retention-invariants")

(local (in-theory (enable fn-retention-invariants-vocabulary)))
(local (in-theory (enable fn-retain-statep fn-retain-admissiblep
                          fn-retain-admit fn-retain-release
                          fn-node-stagep fn-node-statep fn-statep)))

(defun fn-nrt-node-with-retention (node retention)
  (declare (xargs :guard t :verify-guards nil))
  (fn-node-make-state (fn-node-acceptance node) retention
                      (fn-node-stage node) (fn-node-bindings node)))

(defthm fn-nrt-node-with-retention-components
  (and (true-listp (fn-nrt-node-with-retention node r))
       (equal (len (fn-nrt-node-with-retention node r)) 4)
       (equal (fn-node-acceptance (fn-nrt-node-with-retention node r))
              (fn-node-acceptance node))
       (equal (fn-node-retention (fn-nrt-node-with-retention node r)) r)
       (equal (fn-node-stage (fn-nrt-node-with-retention node r))
              (fn-node-stage node))
       (equal (fn-node-bindings (fn-nrt-node-with-retention node r))
              (fn-node-bindings node)))
  :hints (("Goal" :in-theory (enable fn-nrt-node-with-retention
                                      fn-node-make-state fn-node-acceptance
                                      fn-node-retention fn-node-stage
                                      fn-node-bindings))))

(defthm fn-nrt-node-with-retention-is-shaped
  (fn-node-state-shapep (fn-nrt-node-with-retention node r))
  :hints (("Goal" :in-theory (enable fn-nrt-node-with-retention))))

(in-theory (disable fn-node-acceptance fn-node-retention fn-node-stage
                    fn-node-bindings fn-retain-pins fn-retain-releases
                    fn-nrt-node-with-retention))


(defthm fn-nrt-statep-no-duplicate-pins
  (implies (fn-retain-statep s)
           (fn-retain-no-duplicatesp
            (fn-retain-obligation-ids (fn-retain-pins s))))
  :hints (("Goal" :in-theory (enable fn-retain-statep))))

(defthm fn-nrt-find-id-of-remove-self
  (implies (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))
           (equal (fn-retain-find-id id (fn-retain-remove-id id pins)) nil))
  :hints (("Goal"
           :use ((:instance fn-retain-release-remove-id-members (other id))
                 (:instance fn-retain-find-id-absent
                            (pins (fn-retain-remove-id id pins))))
           :in-theory (disable fn-retain-release-remove-id-members
                               fn-retain-find-id-absent
                               fn-retain-remove-id fn-retain-find-id))))

(defthm fn-nrt-release-pins
  (implies (and (fn-retain-statep s)
                (fn-retain-matching-releasep
                 (fn-retain-find-id id (fn-retain-pins s))
                 id subject kind evidence))
           (equal (fn-retain-pins (fn-retain-release s id subject kind evidence))
                  (fn-retain-remove-id id (fn-retain-pins s))))
  :hints (("Goal" :in-theory (e/d (fn-retain-release fn-retain-make-state
                                                     fn-retain-pins)
                                  (fn-retain-statep fn-retain-find-id
                                                    fn-retain-remove-id
                                                    fn-retain-matching-releasep)))))

(defthm fn-nrt-admit-pins
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (equal (fn-retain-pins
                   (fn-retain-admit s id subject kind evidence charge))
                  (cons (fn-retain-make-obligation id subject kind evidence charge)
                        (fn-retain-pins s))))
  :hints (("Goal" :in-theory (e/d (fn-retain-admit fn-retain-make-state
                                                   fn-retain-pins)
                                  (fn-retain-admissiblep)))))

(defthm fn-nrt-admissible-id-not-pinned
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (not (member-equal id (fn-retain-obligation-ids (fn-retain-pins s)))))
  :hints (("Goal" :in-theory (enable fn-retain-admissiblep fn-retain-known-idp))))

; -----------------------------------------------------------------------------
; Node-level lemmas: bindings and archive pins survive a change to a pin that
; no binding names.

(defthm fn-nrt-subsetp-of-cons
  (implies (fn-subsetp xs ys)
           (fn-subsetp xs (cons a ys)))
  :hints (("Goal" :induct (fn-subsetp xs ys)
           :in-theory (enable fn-subsetp))))

(defthm fn-nrt-subsetp-of-remove
  (implies (and (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))
                (fn-subsetp xs (fn-retain-obligation-ids pins))
                (not (member-equal id xs)))
           (fn-subsetp xs (fn-retain-obligation-ids
                           (fn-retain-remove-id id pins))))
  :hints (("Goal" :induct (fn-subsetp xs (fn-retain-obligation-ids pins))
           :in-theory (e/d (fn-subsetp)
                           (fn-retain-remove-id fn-retain-obligation-ids)))
          ("Subgoal *1/1"
           :use ((:instance fn-retain-release-remove-keeps-other-members
                            (other (car xs)))))))

(defthm fn-nrt-find-binding-id-is-member
  (implies (consp (fn-node-find-binding msgid bindings))
           (member-equal (fn-node-binding-id (fn-node-find-binding msgid bindings))
                         (fn-node-binding-ids bindings)))
  :hints (("Goal" :induct (fn-node-find-binding msgid bindings)
           :in-theory (enable fn-node-find-binding fn-node-binding-ids))))

(defthm fn-nrt-find-id-of-cons-other
  (implies (not (equal id (fn-retain-obligation-id ob)))
           (equal (fn-retain-find-id id (cons ob pins))
                  (fn-retain-find-id id pins)))
  :hints (("Goal" :in-theory (enable fn-retain-find-id))))

(defthm fn-nrt-archive-bindings-after-remove
  (implies (and (fn-node-articles-have-archive-bindingsp articles bindings pins)
                (not (member-equal id (fn-node-binding-ids bindings))))
           (fn-node-articles-have-archive-bindingsp
            articles bindings (fn-retain-remove-id id pins)))
  :hints (("Goal" :induct (fn-node-articles-have-archive-bindingsp
                           articles bindings pins)
           :in-theory (e/d (fn-node-articles-have-archive-bindingsp)
                           (fn-retain-remove-id fn-retain-find-id
                                                fn-retain-matching-releasep
                                                fn-node-find-binding
                                                fn-node-binding-id
                                                fn-article-msgid)))
          ("Subgoal *1/1"
           :use ((:instance fn-nrt-find-binding-id-is-member
                            (msgid (fn-article-msgid (car articles))))
                 (:instance fn-retain-release-remove-keeps-other-pin
                            (other (fn-node-binding-id
                                    (fn-node-find-binding
                                     (fn-article-msgid (car articles))
                                     bindings))))))))

(defthm fn-nrt-archive-bindings-after-cons-pin
  (implies (and (fn-node-articles-have-archive-bindingsp articles bindings pins)
                (not (member-equal id (fn-node-binding-ids bindings))))
           (fn-node-articles-have-archive-bindingsp
            articles bindings
            (cons (fn-retain-make-obligation id subject kind evidence charge)
                  pins)))
  :hints (("Goal" :induct (fn-node-articles-have-archive-bindingsp
                           articles bindings pins)
           :in-theory (e/d (fn-node-articles-have-archive-bindingsp
                            fn-retain-make-obligation fn-retain-obligation-id)
                           (fn-retain-find-id fn-retain-matching-releasep
                                              fn-node-find-binding
                                              fn-node-binding-id
                                              fn-article-msgid)))
          ("Subgoal *1/1"
           :use ((:instance fn-nrt-find-binding-id-is-member
                            (msgid (fn-article-msgid (car articles))))
                 (:instance fn-nrt-find-id-of-cons-other
                            (id (fn-node-binding-id
                                 (fn-node-find-binding
                                  (fn-article-msgid (car articles))
                                  bindings)))
                            (ob (fn-retain-make-obligation id subject kind
                                                           evidence charge)))))))

(defthm fn-nrt-node-statep-retention
  (implies (fn-node-statep node)
           (fn-retain-statep (fn-node-retention node)))
  :hints (("Goal" :in-theory (enable fn-node-statep))))

(defthm fn-nrt-node-statep-binding-ids-subset
  (implies (fn-node-statep node)
           (fn-subsetp (fn-node-binding-ids (fn-node-bindings node))
                       (fn-retain-obligation-ids
                        (fn-retain-pins (fn-node-retention node)))))
  :hints (("Goal" :in-theory (enable fn-node-statep))))

; The two node-level keystones: a release or an admission of a pin that no
; binding names, while no archive transaction is staged, keeps fn-node-statep.
(defthm fn-nrt-node-release-preserves-statep
  (implies (and (fn-node-statep node)
                (null (fn-node-stage node))
                (not (member-equal id (fn-node-binding-ids (fn-node-bindings node))))
                (fn-retain-matching-releasep
                 (fn-retain-find-id id (fn-retain-pins (fn-node-retention node)))
                 id subject kind evidence))
           (fn-node-statep
            (fn-nrt-node-with-retention
             node
             (fn-retain-release (fn-node-retention node) id subject kind evidence))))
  :hints (("Goal"
           :use ((:instance fn-retain-release-preserves-statep
                            (s (fn-node-retention node)))
                 (:instance fn-nrt-release-pins (s (fn-node-retention node)))
                 (:instance fn-nrt-statep-no-duplicate-pins
                            (s (fn-node-retention node)))
                 (:instance fn-nrt-subsetp-of-remove
                            (pins (fn-retain-pins (fn-node-retention node)))
                            (xs (fn-node-binding-ids (fn-node-bindings node))))
                 (:instance fn-nrt-archive-bindings-after-remove
                            (articles (fn-state-articles (fn-node-acceptance node)))
                            (bindings (fn-node-bindings node))
                            (pins (fn-retain-pins (fn-node-retention node)))))
           :in-theory (e/d (fn-node-statep)
                           (fn-retain-release fn-retain-statep fn-statep
                                              fn-node-stagep fn-node-binding-listp
                                              fn-node-articles-have-archive-bindingsp
                                              fn-subsetp fn-retain-remove-id
                                              fn-retain-find-id
                                              fn-retain-matching-releasep
                                              fn-retain-obligation-ids
                                              fn-node-binding-ids
                                              fn-retain-release-preserves-statep
                                              fn-nrt-release-pins
                                              fn-nrt-subsetp-of-remove
                                              fn-nrt-archive-bindings-after-remove)))))

(defthm fn-nrt-node-admit-preserves-statep
  (implies (and (fn-node-statep node)
                (null (fn-node-stage node))
                (fn-retain-admissiblep (fn-node-retention node)
                                       id subject kind evidence charge))
           (fn-node-statep
            (fn-nrt-node-with-retention
             node
             (fn-retain-admit (fn-node-retention node)
                              id subject kind evidence charge))))
  :hints (("Goal"
           :use ((:instance fn-retain-admit-preserves-statep
                            (s (fn-node-retention node)))
                 (:instance fn-nrt-admit-pins (s (fn-node-retention node)))
                 (:instance fn-nrt-admissible-id-not-pinned
                            (s (fn-node-retention node)))
                 (:instance fn-not-member-of-subset
                            (xs (fn-node-binding-ids (fn-node-bindings node)))
                            (ys (fn-retain-obligation-ids
                                 (fn-retain-pins (fn-node-retention node))))
                            (x id))
                 (:instance fn-nrt-subsetp-of-cons
                            (xs (fn-node-binding-ids (fn-node-bindings node)))
                            (ys (fn-retain-obligation-ids
                                 (fn-retain-pins (fn-node-retention node))))
                            (a id))
                 (:instance fn-nrt-archive-bindings-after-cons-pin
                            (articles (fn-state-articles (fn-node-acceptance node)))
                            (bindings (fn-node-bindings node))
                            (pins (fn-retain-pins (fn-node-retention node)))))
           :in-theory (e/d (fn-node-statep fn-retain-obligation-ids
                                           fn-retain-make-obligation
                                           fn-retain-obligation-id)
                           (fn-retain-admit fn-retain-admissiblep
                                            fn-retain-statep fn-statep
                                            fn-node-stagep fn-node-binding-listp
                                            fn-node-articles-have-archive-bindingsp
                                            fn-subsetp fn-retain-find-id
                                            fn-retain-matching-releasep
                                            fn-node-binding-ids
                                            fn-retain-admit-preserves-statep
                                            fn-nrt-admit-pins
                                            fn-nrt-admissible-id-not-pinned
                                            fn-not-member-of-subset
                                            fn-nrt-subsetp-of-cons
                                            fn-nrt-archive-bindings-after-cons-pin)))))
