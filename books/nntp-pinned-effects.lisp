; Effect typing for the executed Message-ID trie and historical HDR branch.
(in-package "ACL2")
(include-book "nntp-post")
(include-book "nntp-verdict-effects")
(include-book "group-bucket-invariants")
(include-book "nntp-xref-invariants")
; PRF-325: the XFNCATCHUP arm's reply is well formed
; (`fn-cu-serve-reply-effects-well-formed').
(include-book "peer-catchup-effects")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-nntp-index-entry-available)
                          (:definition fn-nntp-index-msgid-okp)
                          (:definition fn-nntp-response-octetp)
                          (:definition fn-nntp-response-textp)
                          (:definition fn-nov-clean-linep)
                          (:definition fn-nov-line-octetp)
                          (:rewrite fn-nntp-message-id-token-is-response-text)
                          (:rewrite fn-nntp-response-text-is-octets))))

(local (defthm fn-pinned-effects-projection-is-state
         (implies (fn-nntp-projectionp archive) (fn-statep archive))
         :hints (("Goal" :in-theory (enable fn-nntp-projectionp)))))

(defthm fn-nntp-effects-msgid-retrieval-indexed
  (implies (fn-midx-correspondencep index (fn-state-articles archive))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-msgid-retrieval-indexed session archive index kind token fn-arena))))
  :hints (("Goal" :use ((:instance fn-nntp-effects-msgid-retrieval))
           :in-theory (disable fn-nntp-effectsp fn-nntp-msgid-retrieval-indexed
                               fn-nntp-msgid-retrieval
                               fn-nntp-effects-msgid-retrieval))))

(defthm fn-nov-indexed-lines-are-clean
  (fn-nov-clean-line-listp
   (fn-nov-lines-for-numbers-indexed group numbers entries trie fn-arena))
  :hints (("Goal" :induct (fn-nov-lines-for-numbers-indexed
                            group numbers entries trie fn-arena)
           :in-theory (e/d (fn-nov-lines-for-numbers-indexed)
                           (fn-nov-overview fn-nov-line)))))

(defthm fn-nntp-indexed-over-block-is-block-text
  (fn-nntp-block-textp
   (fn-nov-lines-for-numbers-indexed group numbers entries trie fn-arena))
  :hints (("Goal" :use ((:instance fn-nov-indexed-lines-are-clean
                            (entries entries)))
           :in-theory (disable fn-nov-indexed-lines-are-clean
                               fn-nov-lines-for-numbers-indexed))))

; The same for the rows the number index finds (over-number-index): the
; renderer is the indexed one's, so its lines are clean whatever the index.
(defthm fn-nov-numbered-lines-are-clean
  (fn-nov-clean-line-listp
   (fn-nov-lines-for-numbers-numbered numbers nidx trie fn-arena))
  :hints (("Goal" :induct (fn-nov-lines-for-numbers-numbered numbers nidx trie fn-arena)
           :in-theory (e/d (fn-nov-lines-for-numbers-numbered)
                           (fn-nov-overview fn-nov-line)))))

(defthm fn-nntp-numbered-over-block-is-block-text
  (fn-nntp-block-textp
   (fn-nov-lines-for-numbers-numbered numbers nidx trie fn-arena))
  :hints (("Goal" :use ((:instance fn-nov-numbered-lines-are-clean))
           :in-theory (disable fn-nov-numbered-lines-are-clean
                               fn-nov-lines-for-numbers-numbered))))

(defthm fn-nntp-effects-over-range-indexed
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-over-range-indexed session buckets trie token legacyp fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-indexed)
                                  (fn-nov-lines-for-numbers-indexed
                                   fn-nov-lines-for-numbers-numbered
                                   fn-nntp-index-group-range-numbers
                                   fn-nntp-parse-range fn-nntp-single)))))

;; R3 (PRF-206): the served OVER/XOVER renderers carrying the Xref field.
;; Their lines are clean (books/nntp-xref-invariants.lisp) whenever the
;; server is absent or a server word, which `fn-nntp-xref-server' always is.
(defthm fn-nntp-served-over-block-is-block-text
  (implies (or (null server) (fn-xref-serverp server))
           (fn-nntp-block-textp
            (fn-nov-served-lines-numbered numbers nidx trie server fn-arena)))
  :hints (("Goal" :use ((:instance fn-nov-served-lines-numbered-are-clean))
           :in-theory (disable fn-nov-served-lines-numbered-are-clean
                               fn-nov-served-lines-numbered fn-xref-serverp))))

(defthm fn-nntp-served-over-one-line-is-block-text
  (implies (and (fn-nov-okp (fn-nov-overview article fn-arena))
                (or (null server) (fn-xref-serverp server)))
           (fn-nntp-block-textp
            (list (fn-nov-served-line number (fn-nov-overview article fn-arena)
                                      server article2))))
  :hints (("Goal" :use ((:instance fn-nov-served-line-is-a-clean-line
                         (over (fn-nov-overview article fn-arena))
                         (article article2))
                        (:instance fn-nov-overview-is-an-overview))
           :in-theory (e/d (fn-nntp-block-textp)
                           (fn-nov-served-line-is-a-clean-line
                            fn-nov-overview-is-an-overview fn-xref-serverp
                            fn-nov-served-line fn-nov-overview fn-nov-overviewp)))))

(defthm fn-nntp-effects-over-range-served
  (implies (or (null server) (fn-xref-serverp server))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-over-range-served session buckets trie token legacyp
                                        server fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-served)
                                  (fn-nov-served-lines-numbered fn-xref-serverp
                                   fn-nntp-index-group-range-numbers
                                   fn-nntp-parse-range fn-nntp-single)))))

(defthm fn-nntp-effects-over-current-served
  (implies (or (null server) (fn-xref-serverp server))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-over-current-served session archive server fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-current-served)
                                  (fn-nov-overview fn-nov-served-line
                                   fn-xref-serverp
                                   fn-nntp-available-article fn-nntp-single)))))

(defthm fn-nntp-effects-over-msgid-served
  (implies (or (null server) (fn-xref-serverp server))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-over-msgid-served session archive token server fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-msgid-served)
                                  (fn-nov-overview fn-nov-served-line
                                   fn-xref-serverp
                                   fn-find-article fn-nntp-single
                                   fn-nntp-token-string)))))

(defthm fn-nntp-effects-list-overview-fmt-served
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-list-overview-fmt-served session)))
  :hints (("Goal" :use fn-nov-fmt-xref-lines-are-clean
           :in-theory (e/d (fn-nntp-list-overview-fmt-served)
                           (fn-nov-fmt-xref-lines-are-clean)))))

(defthm fn-nntp-effects-xref-reply
  (implies (fn-nntp-xref-reply session archive index env keyword args fn-arena)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-xref-reply session archive index env keyword args fn-arena))))
  :hints (("Goal" :use ((:instance fn-nntp-xref-server-is-a-server))
           :in-theory (e/d (fn-nntp-xref-reply)
                           (fn-nntp-xref-server fn-xref-serverp fn-nntp-keywordp
                            fn-nntp-over-range-served fn-nntp-over-current-served
                            fn-nntp-over-msgid-served
                            fn-nntp-list-overview-fmt-served
                            fn-nntp-effectsp fn-nntp-result-effects)))))

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
    (fn-nntp-control-hdr-response session archive index verdicts args fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-control-hdr-response)
                                  (fn-nntp-single fn-nntp-hdr-line
                                   fn-ctl-control-item fn-ctl-served-status
                                   fn-ctl-served-held fn-nntp-string-octets
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-ctl-pin-withdrawn fn-ctl-pin-ws
                                   fn-nntp-token-string fn-ctl-target-octets
                                   fn-octet-listp)))))

; HDR :fn-enrollment (books/nntp-enrollment.lisp): one clean line, its item
; printable by fn-enr-item-is-printable.
(defthm fn-nntp-enrollment-hdr-response-effects
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-enrollment-hdr-response session archive index verdicts args)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-enrollment-hdr-response
                                   fn-nov-decimal-field-is-clean)
                                  (fn-nntp-single fn-nntp-hdr-line
                                   fn-enr-item fn-stx-reader-lookup
                                   fn-midx-lookup
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-nntp-token-string fn-octet-listp)))))

;; PRF-243: the served compatibility arms (books/nntp-reader-compat.lisp).
(defthm fn-rcompat-xref-value-is-clean
  (implies (fn-xref-serverp server)
           (fn-nov-clean-fieldp (fn-rcompat-xref-value server article)))
  :hints (("Goal" :in-theory (e/d (fn-rcompat-xref-value fn-xref-serverp
                                   fn-xref-pairs)
                                  (fn-xref-locations fn-xref-pairs-of))
           :use ((:instance fn-xref-locations-are-clean
                            (pairs (fn-xref-pairs-of
                                    (fn-article-memberships article) article)))
                 (:instance fn-xref-server-octets-are-clean (bytes server))
                 (:instance fn-xref-pairs-of-is-a-pair-list
                            (ms (fn-article-memberships article)))))))

(defthm fn-rcompat-xref-content-is-clean
  (implies (fn-xref-serverp server)
           (fn-nov-clean-fieldp
            (fn-nntp-hdr-octets (fn-rcompat-xref-content server article fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-rcompat-xref-content fn-nntp-hdr-octets)
                                  (fn-rcompat-xref-value fn-xref-serverp)))))

(defthm fn-rcompat-hdr-lines-are-clean
  (implies (fn-xref-serverp server)
           (fn-nntp-hdr-clean-field-listp
            (fn-rcompat-hdr-lines group numbers articles server fn-arena)))
  :hints (("Goal" :induct (fn-rcompat-hdr-lines group numbers articles server fn-arena)
           :in-theory (e/d (fn-nntp-hdr-clean-field-listp)
                           (fn-rcompat-xref-content fn-rcompat-xref-value
                            fn-xref-serverp fn-nntp-available-article
                            fn-nntp-hdr-octets fn-nntp-hdr-okp fn-nntp-hdr-line
                            fn-nntp-decimal-field)))
          ("Subgoal *1/1"
           :use ((:instance fn-nntp-hdr-line-is-a-clean-field
                            (label (fn-nntp-decimal-field (car numbers)))
                            (content (fn-nntp-hdr-octets
                                      (fn-rcompat-xref-content
                                       server (fn-nntp-available-article
                                               group (car numbers) articles) fn-arena))))
                 (:instance fn-rcompat-xref-content-is-clean
                            (article (fn-nntp-available-article
                                      group (car numbers) articles)))))))

(defthm fn-rcompat-one-hdr-line-is-block-text
  (implies (and (fn-nov-clean-fieldp label) (fn-nov-clean-fieldp content))
           (fn-nntp-block-textp (list (fn-nntp-hdr-line label content))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-hdr-clean-field-listp)
                                  (fn-nntp-hdr-line fn-nntp-block-textp
                                   fn-nov-clean-line-listp))
           :use ((:instance fn-nntp-hdr-line-is-a-clean-field)
                 (:instance fn-nntp-hdr-clean-fields-are-clean-lines
                            (lines (list (fn-nntp-hdr-line label content))))
                 (:instance fn-nntp-clean-lines-are-block-text
                            (lines (list (fn-nntp-hdr-line label content))))))))

(defthm fn-rcompat-hdr-lines-are-block-text
  (implies (fn-xref-serverp server)
           (fn-nntp-block-textp
            (fn-rcompat-hdr-lines group numbers articles server fn-arena)))
  :hints (("Goal" :in-theory (disable fn-rcompat-hdr-lines fn-nntp-block-textp
                                      fn-nov-clean-line-listp fn-xref-serverp)
           :use ((:instance fn-rcompat-hdr-lines-are-clean)
                 (:instance fn-nntp-hdr-clean-fields-are-clean-lines
                            (lines (fn-rcompat-hdr-lines group numbers articles
                                                         server fn-arena)))
                 (:instance fn-nntp-clean-lines-are-block-text
                            (lines (fn-rcompat-hdr-lines group numbers articles
                                                         server fn-arena)))))))

(defthm fn-nntp-effects-rcompat-hdr
  (implies (fn-xref-serverp server)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-rcompat-hdr session archive trie args legacyp server fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-rcompat-hdr fn-nntp-hdr-initial)
                                  (fn-rcompat-hdr-lines fn-rcompat-xref-content
                                   fn-nntp-hdr-line fn-nntp-hdr-octets
                                   fn-nntp-hdr-okp fn-xref-serverp
                                   fn-nntp-available-article fn-midx-lookup
                                   fn-nov-scrub fn-nntp-decimal-field
                                   fn-nntp-group-range-numbers fn-nntp-block-textp))
           :use ((:instance fn-rcompat-xref-content-is-clean
                            (article (fn-midx-lookup (fn-nntp-token-string
                                                      (cadr args)) trie)))
                 (:instance fn-rcompat-xref-content-is-clean
                            (article (fn-nntp-available-article
                                      (fn-nntp-session-group session)
                                      (fn-nntp-session-current session)
                                      (fn-state-articles archive))))
                 (:instance fn-nov-scrub-is-clean (bytes (cadr args)))
                 (:instance fn-nov-decimal-field-is-clean
                            (number (fn-nntp-session-current session)))
                 (:instance fn-nov-decimal-field-is-clean (number 0))))))

(defthm fn-rcompat-name-lines-are-block-text
  (fn-nntp-block-textp (fn-rcompat-name-lines names)))

(defthm fn-nntp-effects-rcompat-reply
  (implies (fn-rcompat-reply session archive index env keyword args fn-arena)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-rcompat-reply session archive index env keyword args fn-arena))))
  :hints (("Goal" :use ((:instance fn-nntp-xref-server-is-a-server))
           :in-theory (e/d (fn-rcompat-reply fn-rcompat-newgroups
                            fn-rcompat-active-times fn-rcompat-subscriptions
                            fn-rcompat-retrieval fn-rcompat-article-reply)
                           (fn-rcompat-hdr fn-rcompat-xref-content
                            fn-nntp-xref-server fn-xref-serverp fn-nntp-keywordp
                            fn-nntp-newgroups-response fn-nntp-list-active-times
                            fn-nntp-article-response fn-rcompat-name-lines
                            fn-rcompat-hdr-lines fn-rcompat-xref-value
                            fn-rcompat-served-article fn-nntp-hdr-line
                            fn-nntp-filter-groups-by-wildmat fn-wildmat-parse
                            fn-nntp-available-article fn-nntp-find-group-number
                            fn-midx-lookup)))))

(defthm fn-nntp-archive-command-pinned-effects-well-formed
  (implies (and (fn-nntp-projectionp archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-gidx-pin-correspondencep index archive))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-archive-command-pinned
              session archive index verdicts env keyword args fn-arena))))
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
                 (:instance fn-nntp-enrollment-hdr-response-effects)
                 (:instance fn-nntp-withdrawn-reply-effects (msgidp nil))
                 (:instance fn-nntp-withdrawn-reply-effects (msgidp t))
                 (:instance fn-nntp-effects-gidx-list-counts-command
                            (buckets (fn-gidx-pin-buckets index))
                            (args (cdr args)))
                 (:instance fn-nntp-effects-xref-reply)
                 (:instance fn-nntp-effects-rcompat-reply))
           :in-theory
           (e/d (fn-nntp-archive-command-pinned)
                (fn-nntp-archive-command fn-nntp-msgid-retrieval-indexed
                 fn-gidx-list-counts-command
                 fn-nntp-effects-gidx-list-counts-command
                 fn-gidx-listgroup-command fn-gidx-build
                 fn-nntp-over-range-indexed
                 fn-nntp-over-range-served fn-nntp-over-current-served
                 fn-nntp-over-msgid-served fn-nntp-list-overview-fmt-served
                 fn-nntp-effects-over-range-served
                 fn-nntp-effects-over-current-served
                 fn-nntp-effects-over-msgid-served
                 fn-nntp-effects-list-overview-fmt-served
                 fn-nntp-xref-server fn-xref-serverp
                 fn-nntp-xref-reply fn-nntp-effects-xref-reply
                 fn-rcompat-reply fn-nntp-effects-rcompat-reply
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
             (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))))
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
             (fn-nntp-step-pinned session archive index verdicts env wire-event fn-arena))))
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
                                       observation injection wire-event fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-nntp-step-pinned-effects-well-formed
                            (session (fn-post-session-base ps))
                            (env (fn-post-reader-env config observation))))
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
                                      observation injection wire-event fn-arena))
           (fn-inj-injectedp
            (fn-post-result-submission
             (fn-nntp-post-step-pinned ps archive index verdicts config
                                       observation injection wire-event fn-arena))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-post-step-pinned)
                (fn-nntp-post-step fn-inj-decide fn-inj-injectedp
                 fn-nntp-step-pinned fn-post-offeredp fn-post-refusal-line
                 fn-post-sessionp)))))
