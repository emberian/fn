; Effect typing for the executed Message-ID trie and historical HDR branch.
(in-package "ACL2")
(include-book "nntp-post")
(include-book "nntp-verdict-effects")
(include-book "group-bucket-invariants")

(local (defthm fn-pinned-effects-projection-is-state
         (implies (fn-nntp-projectionp archive) (fn-statep archive))
         :hints (("Goal" :in-theory (enable fn-nntp-projectionp)))))

(defthm fn-nntp-effects-msgid-retrieval-indexed
  (implies (fn-midx-correspondencep index (fn-state-articles archive))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-msgid-retrieval-indexed session archive index kind token))))
  :hints (("Goal" :use ((:instance fn-nntp-effects-msgid-retrieval))
           :in-theory (disable fn-nntp-effectsp fn-nntp-msgid-retrieval-indexed
                               fn-nntp-msgid-retrieval
                               fn-nntp-effects-msgid-retrieval))))

(defthm fn-nntp-archive-command-pinned-effects-well-formed
  (implies (and (fn-nntp-projectionp archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-gidx-pin-correspondencep index archive))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-archive-command-pinned
              session archive index verdicts env keyword args))))
  :hints (("Goal"
           :use ((:instance fn-nntp-archive-command-effects-well-formed)
                 (:instance fn-gidx-listgroup-command-of-build)
                 (:instance fn-nntp-verdict-hdr-response-effects))
           :in-theory
           (e/d (fn-nntp-archive-command-pinned)
                (fn-nntp-archive-command fn-nntp-msgid-retrieval-indexed
                 fn-gidx-listgroup-command fn-gidx-build
                 fn-nntp-verdict-hdr-response fn-nntp-effectsp
                 fn-nntp-result-effects fn-nntp-projectionp fn-nntp-keywordp
                 fn-midx-correspondencep
                 fn-nntp-archive-command-effects-well-formed
                 fn-nntp-verdict-hdr-response-effects
                 fn-nntp-msgid-retrieval-indexed-refines-scan)))))

(defthm fn-nntp-command-pinned-effects-well-formed
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-gidx-pin-correspondencep index archive))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-command-pinned session archive index verdicts env tokens))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-nntp-command-pinned)
                (fn-nntp-session-command fn-nntp-archive-command-pinned
                 fn-nntp-archive-keywordp fn-nntp-keyword-tokenp
                 fn-nntp-single fn-nntp-projectionp fn-nntp-effectsp
                 fn-nntp-result-effects fn-nntp-session-consistentp))
           :expand ((fn-nntp-session-consistentp session archive)))))

(defthm fn-nntp-step-pinned-effects-well-formed
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-gidx-pin-correspondencep index archive))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-step-pinned session archive index verdicts env wire-event))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-step-pinned)
                (fn-nntp-result-effects fn-nntp-make-result fn-nntp-single
                 fn-nntp-command-pinned fn-nntp-session-consistentp
                 fn-nntp-sessionp fn-nntp-session-openp
                 fn-nntp-command-inputp fn-nntp-tokenize
                 fn-nntp-command-arguments-at-mostp)))))

(defthm fn-post-step-pinned-effects-well-formed
  (implies (and (fn-post-session-consistentp ps archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-gidx-pin-correspondencep index archive))
           (fn-nntp-effectsp
            (fn-post-result-effects
             (fn-nntp-post-step-pinned ps archive index verdicts config
                                       observation injection wire-event))))
  :hints (("Goal"
           :use ((:instance fn-nntp-step-pinned-effects-well-formed
                            (session (fn-post-session-base ps))
                            (env (fn-nntp-env
                                  observation nil
                                  (and (fn-inj-config-allow config) t)))))
           :in-theory
           (e/d (fn-nntp-post-step-pinned fn-post-session-consistentp
                  fn-post-single fn-nntp-effectsp fn-post-refusal-line)
                (fn-nntp-step-pinned-effects-well-formed fn-nntp-step-pinned
                 fn-nntp-session-consistentp fn-nntp-sessionp
                 fn-nntp-projectionp fn-nntp-replyp fn-inj-decide
                 fn-inj-injectedp fn-inj-decision-reason fn-post-offeredp
                 fn-midx-correspondencep)))))

(defthm fn-post-step-pinned-submission-is-an-injected-article
  (implies (fn-post-result-submission
            (fn-nntp-post-step-pinned ps archive index verdicts config
                                      observation injection wire-event))
           (fn-inj-injectedp
            (fn-post-result-submission
             (fn-nntp-post-step-pinned ps archive index verdicts config
                                       observation injection wire-event))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-post-step-pinned)
                (fn-nntp-post-step fn-inj-decide fn-inj-injectedp
                 fn-nntp-step-pinned fn-post-offeredp fn-post-refusal-line
                 fn-post-sessionp)))))
