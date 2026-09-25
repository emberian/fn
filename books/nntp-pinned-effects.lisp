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

(defthm fn-nov-indexed-lines-are-clean
  (fn-nov-clean-line-listp
   (fn-nov-lines-for-numbers-indexed group numbers entries trie))
  :hints (("Goal" :induct (fn-nov-lines-for-numbers-indexed
                            group numbers entries trie)
           :in-theory (e/d (fn-nov-lines-for-numbers-indexed)
                           (fn-nov-overview fn-nov-line)))))

(defthm fn-nntp-indexed-over-block-is-block-text
  (fn-nntp-block-textp
   (fn-nov-lines-for-numbers-indexed group numbers entries trie))
  :hints (("Goal" :use ((:instance fn-nov-indexed-lines-are-clean
                            (entries entries)))
           :in-theory (disable fn-nov-indexed-lines-are-clean
                               fn-nov-lines-for-numbers-indexed))))

(defthm fn-nntp-effects-over-range-indexed
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-over-range-indexed session buckets trie token legacyp)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-indexed)
                                  (fn-nov-lines-for-numbers-indexed
                                   fn-nntp-index-group-range-numbers
                                   fn-nntp-parse-range fn-nntp-single)))))

; LIST COUNTS over the pinned buckets (books/nntp.lisp).  The lines carry the
; same group names and decimal fields as the archive fold's, whatever the
; summary, so no bucket relation is needed for their shape.
(defthm fn-gidx-counts-lines-are-response-text
  (implies (fn-nntp-safe-group-listp groups)
           (fn-nntp-block-textp (fn-gidx-counts-lines archive buckets groups)))
  :hints (("Goal" :induct (fn-gidx-counts-lines archive buckets groups)
           :in-theory (e/d (fn-gidx-counts-lines fn-gidx-counts-line
                            fn-nntp-block-textp fn-nntp-safe-group-listp)
                           (fn-nntp-counts-summary-line)))))

(defthm fn-nntp-effects-gidx-list-counts-command
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-gidx-list-counts-command session archive buckets args))))
  :hints (("Goal" :in-theory (e/d (fn-gidx-list-counts-command)
                                  (fn-nntp-projectionp
                                   fn-statep fn-state-groups
                                   fn-state-articles fn-state-nexts
                                   fn-gidx-counts-lines
                                   fn-nntp-filter-groups-by-wildmat
                                   fn-wildmat-parse)))))

(defthm fn-nntp-control-cleanp-is-clean-field
  (equal (fn-nntp-control-cleanp bytes) (fn-nov-clean-fieldp bytes))
  :hints (("Goal" :in-theory (enable fn-nntp-control-cleanp fn-nov-clean-fieldp
                                     fn-nov-field-octetp))))

(defthm fn-nntp-withdrawn-reply-effects
  (fn-nntp-effectsp (fn-nntp-result-effects (fn-nntp-withdrawn-reply session msgidp)))
  :hints (("Goal" :in-theory (enable fn-nntp-withdrawn-reply))))

(defthm fn-nntp-control-line-is-block-text
  (implies (and (fn-nov-clean-fieldp label) (fn-nov-clean-fieldp item))
           (fn-nntp-block-textp (list (fn-nntp-hdr-line label item))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nntp-hdr-line-is-a-clean-field (content item))
                 (:instance fn-nntp-clean-field-is-response-text
                            (bytes (fn-nntp-hdr-line label item))))
           :in-theory (e/d (fn-nntp-block-textp) (fn-nntp-hdr-line)))))

(defthm fn-nntp-control-hdr-response-effects
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-control-hdr-response session archive index verdicts args)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-control-hdr-response)
                                  (fn-nntp-single fn-nntp-hdr-line
                                   fn-ctl-control-item fn-ctl-served-status
                                   fn-ctl-served-held fn-nntp-string-octets
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-ctl-pin-withdrawn fn-ctl-pin-ws
                                   fn-nntp-token-string fn-ctl-target-octets
                                   fn-octet-listp)))))

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
                 (:instance fn-nntp-effects-over-range-indexed
                            (buckets (fn-gidx-pin-buckets index))
                            (trie (fn-gidx-pin-trie index))
                            (token (car args))
                            (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-nntp-verdict-hdr-response-effects)
                 (:instance fn-nntp-control-hdr-response-effects)
                 (:instance fn-nntp-withdrawn-reply-effects (msgidp nil))
                 (:instance fn-nntp-withdrawn-reply-effects (msgidp t))
                 (:instance fn-nntp-effects-gidx-list-counts-command
                            (buckets (fn-gidx-pin-buckets index))
                            (args (cdr args))))
           :in-theory
           (e/d (fn-nntp-archive-command-pinned)
                (fn-nntp-archive-command fn-nntp-msgid-retrieval-indexed
                 fn-gidx-list-counts-command
                 fn-nntp-effects-gidx-list-counts-command
                 fn-gidx-listgroup-command fn-gidx-build
                 fn-nntp-over-range-indexed
                 fn-nntp-verdict-hdr-response fn-nntp-effectsp
                 fn-nntp-result-effects fn-nntp-projectionp fn-nntp-keywordp
                 fn-midx-correspondencep
                 fn-nntp-archive-command-effects-well-formed
                 fn-nntp-verdict-hdr-response-effects
                 fn-nntp-control-hdr-response-effects fn-nntp-withdrawn-reply-effects
                 fn-nntp-control-hdr-response fn-nntp-withdrawn-reply
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
