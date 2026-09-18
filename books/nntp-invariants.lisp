; General preservation facts for the fn experimental NNTP reader session.
;
; The archive is immutable to this reader.  These theorems therefore relate a
; session result to the same committed acceptance projection supplied at the
; start of fn-nntp-step; they make no persistence or transport claim.
(in-package "ACL2")
(include-book "nntp")

; A selected group must be one configured in the committed projection.  A NIL
; cursor is permitted even for a nonempty selected group: it represents the
; RFC invalid-current state.  A non-NIL cursor denotes a presently projected
; local article number in that selected group.
(defun fn-nntp-cursor-validp (group current archive)
  (or (null current)
      (consp (fn-nntp-find-group-number
              group current (fn-state-articles archive)))))

(defun fn-nntp-session-consistentp (session archive)
  (and (fn-nntp-sessionp session)
       (or (null (fn-nntp-session-group session))
           (member-equal (fn-nntp-session-group session)
                         (fn-state-groups archive)))
       (or (null (fn-nntp-session-current session))
           (and (not (null (fn-nntp-session-group session)))
                (fn-nntp-cursor-validp
                 (fn-nntp-session-group session)
                 (fn-nntp-session-current session)
                 archive)))))

(defthm fn-nntp-consistent-session-is-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-sessionp session)))

(defthm fn-nntp-initial-session-is-consistent
  (fn-nntp-session-consistentp (fn-nntp-initial-session) archive))

(defthm fn-nntp-set-cursor-sessionp
  (implies (and (fn-nntp-sessionp session)
                (or (equal openp t) (null openp))
                (or (stringp group) (null group))
                (or (posp current) (null current)))
           (fn-nntp-sessionp (fn-nntp-make-session openp group current))))

(defthm fn-nntp-result-session-of-make-result
  (equal (fn-nntp-result-session (fn-nntp-make-result session effects))
         session))

(defthm fn-nntp-single-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-single session text)) session))

(defthm fn-nntp-multi-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-multi session initial lines)) session))

(defthm fn-nntp-multi-octets-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-multi-octets session initial lines)) session))

(defthm fn-nntp-article-response-no-update-preserves-session
  (implies (not updatep)
           (equal (fn-nntp-result-session
                   (fn-nntp-article-response session article number kind updatep group))
                  session))
  :hints (("Goal" :in-theory (enable fn-nntp-article-response))))

(defthm fn-nntp-current-in-group-numbers-is-present
  (implies (and (posp number)
                (member-equal number (fn-nntp-group-numbers group articles)))
           (consp (fn-nntp-find-group-number group number articles)))
  :hints (("Goal" :induct (fn-nntp-group-numbers group articles)
           :in-theory (enable fn-nntp-group-numbers
                              fn-nntp-find-group-number))))

(defthm fn-nntp-group-numbers-are-positive
  (implies (member-equal number (fn-nntp-group-numbers group articles))
           (posp number))
  :hints (("Goal" :induct (fn-nntp-group-numbers group articles)
           :in-theory (enable fn-nntp-group-numbers))))

(defthm fn-nntp-car-is-member
  (implies (consp xs)
           (member-equal (car xs) xs)))

(defthm fn-nntp-string-list-member-is-string
  (implies (and (fn-string-listp strings)
                (member-equal value strings))
           (stringp value))
  :hints (("Goal" :induct (fn-string-listp strings))))

(defthm fn-nntp-string-list-excludes-nil
  (implies (fn-string-listp strings)
           (not (member-equal nil strings)))
  :hints (("Goal" :induct (fn-string-listp strings))))

(defthm fn-nntp-set-cursor-preserves-sessionp
  (implies (and (fn-nntp-sessionp session)
                (stringp group)
                (or (posp current) (null current)))
           (fn-nntp-sessionp (fn-nntp-set-cursor session group current)))
  :hints (("Goal" :in-theory (enable fn-nntp-set-cursor))))

(defthm fn-nntp-single-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-single session text)) archive)))

(defthm fn-nntp-multi-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-multi session initial lines)) archive)))

(defthm fn-nntp-multi-octets-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-multi-octets session initial lines)) archive)))

(defthm fn-nntp-first-group-number-is-present
  (implies (consp (fn-nntp-group-numbers group articles))
           (consp (fn-nntp-find-group-number
                   group (car (fn-nntp-group-numbers group articles)) articles)))
  :hints (("Goal"
           :use ((:instance fn-nntp-current-in-group-numbers-is-present
                 (number (car (fn-nntp-group-numbers group articles))))
                 (:instance fn-nntp-group-numbers-are-positive
                  (number (car (fn-nntp-group-numbers group articles))))
                 (:instance fn-nntp-car-is-member
                  (xs (fn-nntp-group-numbers group articles)))))))

(defthm fn-nntp-first-group-number-is-positive
  (implies (consp (fn-nntp-group-numbers group articles))
           (posp (car (fn-nntp-group-numbers group articles))))
  :hints (("Goal"
           :use ((:instance fn-nntp-group-numbers-are-positive
                  (number (car (fn-nntp-group-numbers group articles))))
                 (:instance fn-nntp-car-is-member
                  (xs (fn-nntp-group-numbers group articles)))))))

(defthm fn-nntp-group-result-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-group-result session archive group))
            archive))
  :hints (("Goal" :in-theory (enable fn-nntp-session-consistentp
                                      fn-nntp-cursor-validp
                                      fn-nntp-group-result))))

(defthm fn-nntp-listgroup-result-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-listgroup-result session archive group range))
            archive))
  :hints (("Goal" :in-theory (enable fn-nntp-session-consistentp
                                      fn-nntp-cursor-validp
                                      fn-nntp-listgroup-result))))

(defthm fn-nntp-article-response-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (or (not updatep)
                    (and (stringp group)
                         (member-equal group (fn-state-groups archive))
                         (posp number)
                         (consp (fn-nntp-find-group-number
                                 group number (fn-state-articles archive))))))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-article-response session article number kind updatep group))
            archive))
  :hints (("Goal" :in-theory (enable fn-nntp-article-response
                                      fn-nntp-session-consistentp
                                      fn-nntp-cursor-validp))))

(defthm fn-nntp-next-number-is-member
  (implies (posp (fn-nntp-next-number current numbers))
           (member-equal (fn-nntp-next-number current numbers) numbers))
  :hints (("Goal" :induct (fn-nntp-next-number current numbers))))

(defthm fn-nntp-last-number-is-member
  (implies (posp (fn-nntp-last-number current numbers))
           (member-equal (fn-nntp-last-number current numbers) numbers))
  :hints (("Goal" :induct (fn-nntp-last-number current numbers))))

(defthm fn-nntp-present-number-is-in-group-numbers
  (implies (and (posp number)
                (consp (fn-nntp-find-group-number group number articles)))
           (member-equal number (fn-nntp-group-numbers group articles)))
  :hints (("Goal" :induct (fn-nntp-find-group-number group number articles)
           :in-theory (enable fn-nntp-find-group-number
                              fn-nntp-group-numbers))))

(defthm fn-nntp-next-or-last-with-article-preserves-consistent-session
  (implies
   (and (fn-nntp-session-consistentp session archive)
        (fn-nntp-projectionp archive)
        (not (null (fn-nntp-session-group session)))
        (not (null (fn-nntp-session-current session)))
        (posp (if (equal direction :next)
                  (fn-nntp-next-number
                   (fn-nntp-session-current session)
                   (fn-nntp-group-numbers
                    (fn-nntp-session-group session) (fn-state-articles archive)))
                (fn-nntp-last-number
                 (fn-nntp-session-current session)
                 (fn-nntp-group-numbers
                  (fn-nntp-session-group session) (fn-state-articles archive))))))
   (fn-nntp-session-consistentp
    (fn-nntp-result-session
     (fn-nntp-next-or-last session archive direction)) archive))
  :hints
  (("Goal"
    :use
    ((:instance fn-nntp-article-response-preserves-consistent-session
      (article
       (fn-nntp-find-group-number
        (fn-nntp-session-group session)
        (if (equal direction :next)
            (fn-nntp-next-number
             (fn-nntp-session-current session)
             (fn-nntp-group-numbers
              (fn-nntp-session-group session) (fn-state-articles archive)))
          (fn-nntp-last-number
           (fn-nntp-session-current session)
           (fn-nntp-group-numbers
            (fn-nntp-session-group session) (fn-state-articles archive))))
        (fn-state-articles archive)))
      (number
       (if (equal direction :next)
           (fn-nntp-next-number
            (fn-nntp-session-current session)
            (fn-nntp-group-numbers
             (fn-nntp-session-group session) (fn-state-articles archive)))
         (fn-nntp-last-number
          (fn-nntp-session-current session)
          (fn-nntp-group-numbers
           (fn-nntp-session-group session) (fn-state-articles archive)))))
      (kind :stat) (updatep t) (group (fn-nntp-session-group session))))
    :in-theory (e/d (fn-nntp-next-or-last)
                     (fn-nntp-article-response)))))

(defthm fn-nntp-next-or-last-without-article-preserves-consistent-session
  (implies
   (and (fn-nntp-session-consistentp session archive)
        (fn-nntp-projectionp archive)
        (not
         (posp (if (equal direction :next)
                   (fn-nntp-next-number
                    (fn-nntp-session-current session)
                    (fn-nntp-group-numbers
                     (fn-nntp-session-group session) (fn-state-articles archive)))
                 (fn-nntp-last-number
                  (fn-nntp-session-current session)
                  (fn-nntp-group-numbers
                   (fn-nntp-session-group session) (fn-state-articles archive)))))))
   (fn-nntp-session-consistentp
    (fn-nntp-result-session
     (fn-nntp-next-or-last session archive direction)) archive))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-next-or-last)
                (fn-nntp-article-response)))))

(defthm fn-nntp-next-or-last-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-next-or-last session archive direction)) archive))
  :hints (("Goal"
           :cases
           ((posp (if (equal direction :next)
                       (fn-nntp-next-number
                        (fn-nntp-session-current session)
                        (fn-nntp-group-numbers
                         (fn-nntp-session-group session) (fn-state-articles archive)))
                     (fn-nntp-last-number
                      (fn-nntp-session-current session)
                      (fn-nntp-group-numbers
                       (fn-nntp-session-group session) (fn-state-articles archive))))))
           :use ((:instance fn-nntp-next-or-last-with-article-preserves-consistent-session)
                 (:instance fn-nntp-next-or-last-without-article-preserves-consistent-session)))))

(defthm fn-nntp-current-retrieval-with-current-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive)
                (not (null (fn-nntp-session-group session)))
                (not (null (fn-nntp-session-current session))))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-current-retrieval session archive kind)) archive))
  :hints (("Goal"
           :use ((:instance fn-nntp-article-response-preserves-consistent-session
                  (article (fn-nntp-find-group-number
                            (fn-nntp-session-group session)
                            (fn-nntp-session-current session)
                            (fn-state-articles archive)))
                  (number (fn-nntp-session-current session))
                  (updatep t)
                  (group (fn-nntp-session-group session))))
           :in-theory (e/d (fn-nntp-current-retrieval)
                            (fn-nntp-article-response)))))

(defthm fn-nntp-current-retrieval-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-current-retrieval session archive kind)) archive))
  :hints (("Goal" :in-theory (enable fn-nntp-current-retrieval))))

(defthm fn-nntp-decimal-value-aux-integer
  (implies (and (integerp accumulator)
                (fn-nntp-decimal-tokenp token))
           (integerp (fn-nntp-decimal-value-aux token accumulator)))
  :hints (("Goal" :induct (fn-nntp-decimal-value-aux token accumulator))))

(defthm fn-nntp-number-token-value-positive
  (implies (fn-nntp-number-tokenp token)
           (posp (fn-nntp-decimal-value token)))
  :hints (("Goal" :in-theory (enable fn-nntp-number-tokenp
                                      fn-nntp-decimal-value))))

(defthm fn-nntp-number-retrieval-with-article-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive)
                (fn-nntp-number-tokenp token)
                (not (null (fn-nntp-session-group session)))
                (consp (fn-nntp-find-group-number
                        (fn-nntp-session-group session)
                        (fn-nntp-decimal-value token)
                        (fn-state-articles archive))))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-number-retrieval session archive kind token)) archive))
  :hints (("Goal"
           :use ((:instance fn-nntp-article-response-preserves-consistent-session
                  (article (fn-nntp-find-group-number
                            (fn-nntp-session-group session)
                            (fn-nntp-decimal-value token)
                            (fn-state-articles archive)))
                  (number (fn-nntp-decimal-value token))
                  (updatep t)
                  (group (fn-nntp-session-group session))))
           :in-theory (e/d (fn-nntp-number-retrieval)
                            (fn-nntp-article-response)))))

(defthm fn-nntp-number-retrieval-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-number-retrieval session archive kind token)) archive))
  :hints (("Goal" :in-theory (enable fn-nntp-number-retrieval))))

(defthm fn-nntp-msgid-retrieval-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-msgid-retrieval session archive kind token)) archive))
  :hints (("Goal" :use fn-nntp-msgid-preserves-session)))

(defthm fn-nntp-retrieval-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-retrieval session archive kind args)) archive))
  :hints (("Goal" :in-theory (e/d (fn-nntp-retrieval)
                                   (fn-nntp-current-retrieval
                                    fn-nntp-number-retrieval
                                    fn-nntp-msgid-retrieval
                                    fn-nntp-result-session
                                    fn-nntp-single
                                    fn-nntp-session-consistentp)))))

(defthm fn-nntp-list-response-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-list-response session archive args))
         session)
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-list-response
                 fn-nntp-list-active-or-newsgroups
                 fn-nntp-list-filtered-response
                 fn-nntp-list-unmaintained-response
                 fn-nntp-list-active
                 fn-nntp-list-newsgroups)
                (fn-wildmat-parse
                 fn-wildmat-result-okp
                 fn-wildmat-result-value
                 fn-nntp-filter-groups-by-wildmat)))))

(defthm fn-nntp-list-response-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-list-response session archive args))
            archive))
  :hints (("Goal" :use fn-nntp-list-response-preserves-session)))

(defthm fn-nntp-listgroup-command-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-listgroup-command session archive args)) archive))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-listgroup-command)
                (fn-nntp-listgroup-result
                 fn-nntp-result-session
                 fn-nntp-single
                 fn-nntp-session-consistentp)))))

(defthm fn-nntp-quit-session-preserves-consistency
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-make-session nil
                                  (fn-nntp-session-group session)
                                  (fn-nntp-session-current session))
            archive))
  :hints (("Goal" :in-theory (enable fn-nntp-session-consistentp))))

(defthm fn-nntp-quit-result-preserves-consistency
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-make-result
              (fn-nntp-make-session nil
                                    (fn-nntp-session-group session)
                                    (fn-nntp-session-current session))
              effects))
            archive))
  :hints (("Goal" :use fn-nntp-quit-session-preserves-consistency)))

(defthm fn-nntp-quit-result-car-preserves-consistency
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (car (fn-nntp-make-result
                  (fn-nntp-make-session nil
                                        (fn-nntp-session-group session)
                                        (fn-nntp-session-current session))
                  effects))
            archive))
  :hints (("Goal" :use fn-nntp-quit-session-preserves-consistency)))

(defthm fn-nntp-quit-list-preserves-consistency
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (list nil (fn-nntp-session-group session)
                  (fn-nntp-session-current session)) archive))
  :hints (("Goal" :use fn-nntp-quit-session-preserves-consistency)))

(defthm fn-nntp-capabilities-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-capabilities session)) session)
  :hints (("Goal" :in-theory (enable fn-nntp-capabilities))))

(defthm fn-nntp-help-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-help session)) session)
  :hints (("Goal" :in-theory (enable fn-nntp-help))))

(defthm fn-nntp-command-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-command session archive tokens))
            archive))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-command)
                (fn-nntp-projectionp
                 fn-nntp-make-session
                 fn-nntp-session-group
                 fn-nntp-session-current
                 fn-nntp-keyword-tokenp
                 fn-nntp-keywordp
                 fn-nntp-capabilities
                 fn-nntp-help
                 fn-nntp-make-result
                 fn-nntp-listgroup-command
                 fn-nntp-list-response
                 fn-nntp-next-or-last
                 fn-nntp-retrieval
                 fn-nntp-group-result
                 fn-nntp-result-session
                 fn-nntp-single
                 fn-nntp-multi
                 fn-nntp-session-consistentp)))))

(defthm fn-nntp-step-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-step session archive wire-event))
            archive))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-step)
                (fn-nntp-make-result
                 fn-nntp-command
                 fn-nntp-projectionp
                 fn-nntp-sessionp
                 fn-nntp-session-openp
                 fn-nntp-command-inputp
                 fn-nntp-tokenize
                 fn-nntp-command-arguments-at-mostp
                 fn-nntp-result-session
                 fn-nntp-single
                 fn-nntp-session-consistentp)))))

; Actual step folding, including malformed events and events after QUIT.  There
; is no event predicate that assumes the result is valid, and no output filter.
(defun fn-nntp-run-session (session archive events)
  (if (consp events)
      (fn-nntp-run-session
       (fn-nntp-result-session (fn-nntp-step session archive (car events)))
       archive (cdr events))
    session))

(defthm fn-nntp-finite-trace-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-run-session session archive events) archive))
  :hints (("Goal" :induct (fn-nntp-run-session session archive events)
           :in-theory (e/d (fn-nntp-run-session)
                            (fn-nntp-step fn-nntp-result-session
                             fn-nntp-session-consistentp fn-nntp-projectionp)))))

(defthm fn-nntp-initialized-finite-trace-is-consistent
  (implies (fn-nntp-projectionp archive)
           (and (fn-nntp-session-consistentp
                 (fn-nntp-run-session (fn-nntp-initial-session) archive events)
                 archive)
                (fn-nntp-sessionp
                 (fn-nntp-run-session (fn-nntp-initial-session) archive events))))
  :hints (("Goal"
           :use ((:instance fn-nntp-initial-session-is-consistent)
                 (:instance fn-nntp-finite-trace-preserves-consistent-session
                  (session (fn-nntp-initial-session)))
                 (:instance fn-nntp-consistent-session-is-session
                  (session (fn-nntp-run-session
                            (fn-nntp-initial-session) archive events))))
           :in-theory (disable fn-nntp-run-session
                               fn-nntp-initial-session
                               fn-nntp-session-consistentp fn-nntp-sessionp
                               fn-nntp-projectionp
                               fn-nntp-initial-session-is-consistent
                               fn-nntp-finite-trace-preserves-consistent-session
                               fn-nntp-consistent-session-is-session))))
