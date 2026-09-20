; Session preservation for the fn experimental NNTP reader session.
;
; The archive is immutable to this reader.  These theorems therefore relate a
; session result to the same committed acceptance projection supplied at the
; start of fn-nntp-step; they make no persistence or transport claim.
;
; Two properties here are about availability rather than about the cursor.
; fn-nntp-step-preserves-carried-projection says the whole-archive recognizer
; verdict a session was opened with is the verdict it keeps, so no command
; recomputes it.  fn-nntp-archive-free-step-ignores-the-archive says no archive
; content whatsoever can change the answer to CAPABILITIES, HELP, QUIT, an
; unrecognized command, or a syntax error.
(in-package "ACL2")
(include-book "nntp-overview")

; This book reasons about the NNTP transitions themselves, so it opens the
; vocabularies the five books of the nntp cluster withdraw at their export
; events (2026-09-19 split of books/nntp.lisp).
(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary fn-nntp-projection-vocabulary fn-nntp-responses-vocabulary fn-nntp-vocabulary)))

; The consp- and true-listp-backchaining rules that made this book's proofs
; fan out (921k of 921k frames of fn-nntp-article-response-keeps-projection
; sat under fn-article-nonempty-true-list-is-consp, and
; fn-nntp-next-or-last-preserves-consistent-session ran past 40M prover steps
; under the five *-true-listp limbs) are no longer enabled on include:
; books/article.lisp withdraws them as fn-article-guard-backchaining and
; books/wildmat.lisp as fn-wildmat-guard-backchaining, and each recognizer's
; shape fact is exported back as a :forward-chaining rule instead
; (fn-article-header-bytes-p-forward-shape and its siblings,
; docs/proof-style.md section 1).  The book-wide withdrawal that used to
; stand here is therefore gone; the one proof that genuinely wants the consp
; rule enables it in its own hint, below.

; -----------------------------------------------------------------------------
; The session relation

; A cursor is valid when it names an article that is available at that number
; in the selected group: present, numbered inside RFC 3977 section 6's range,
; and carrying a renderable Message-ID, which is exactly what a 223 line needs.
(defun fn-nntp-cursor-validp (group current archive)
  (and (posp current)
       (consp (fn-nntp-available-article
               group current (fn-state-articles archive)))))

(defun fn-nntp-group-nonemptyp (group archive)
  (posp (fn-nntp-group-low group (fn-state-articles archive))))

; RFC 3977 sections 6.1.1.2 and 6.1.2.2 make a successful selection set the
; current article number to the first article in the group, and make it invalid
; only when the group is empty.  The relation therefore forbids a NIL cursor
; under a selected nonempty group: a dispatcher that cleared the cursor after
; every command does not satisfy it.
(defun fn-nntp-session-consistentp (session archive)
  (and (fn-nntp-sessionp session)
       (implies (fn-nntp-session-projected session)
                (fn-nntp-projectionp archive))
       (if (null (fn-nntp-session-group session))
           (null (fn-nntp-session-current session))
         (and (member-equal (fn-nntp-session-group session)
                            (fn-state-groups archive))
              (if (fn-nntp-group-nonemptyp (fn-nntp-session-group session) archive)
                  (fn-nntp-cursor-validp (fn-nntp-session-group session)
                                         (fn-nntp-session-current session)
                                         archive)
                (null (fn-nntp-session-current session)))))))

(defthm fn-nntp-consistent-session-is-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-sessionp session)))

(defthm fn-nntp-open-session-is-consistent
  (fn-nntp-session-consistentp (fn-nntp-open-session archive) archive))

(defthm fn-nntp-open-session-records-the-projection
  (equal (fn-nntp-session-projected (fn-nntp-open-session archive))
         (if (fn-nntp-projectionp archive) t nil)))

; -----------------------------------------------------------------------------
; Shape lemmas

(defthm fn-nntp-set-cursor-sessionp
  (implies (and (fn-nntp-sessionp session)
                (or (stringp group) (null group))
                (or (posp current) (null current)))
           (fn-nntp-sessionp (fn-nntp-set-cursor session group current)))
  :hints (("Goal" :in-theory (enable fn-nntp-set-cursor))))

(defthm fn-nntp-set-cursor-keeps-projection
  (equal (fn-nntp-session-projected (fn-nntp-set-cursor session group number))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (enable fn-nntp-set-cursor))))

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

; The membership hypothesis comes first so that it, not the recognizer, binds
; the free variable when this fires on a goal whose recognizer is closed.
(defthm fn-nntp-string-list-member-is-string
  (implies (and (member-equal value strings)
                (fn-string-listp strings))
           (stringp value))
  :hints (("Goal" :induct (fn-string-listp strings))))

(defthm fn-nntp-string-list-excludes-nil
  (implies (fn-string-listp strings)
           (not (member-equal nil strings)))
  :hints (("Goal" :induct (fn-string-listp strings))))

(defthm fn-nntp-projectionp-has-string-groups
  (implies (fn-nntp-projectionp archive)
           (fn-string-listp (fn-state-groups archive)))
  :hints (("Goal" :in-theory (enable fn-nntp-projectionp fn-statep))))

(defthm fn-nntp-projected-group-member-is-string
  (implies (and (member-equal group (fn-state-groups archive))
                (fn-nntp-projectionp archive))
           (stringp group))
  :hints (("Goal" :use ((:instance fn-nntp-string-list-member-is-string
                         (value group) (strings (fn-state-groups archive))))
           :in-theory (disable fn-nntp-string-list-member-is-string
                               fn-nntp-projectionp fn-state-groups))))

(defthm fn-nntp-projected-groups-exclude-nil
  (implies (fn-nntp-projectionp archive)
           (not (member-equal nil (fn-state-groups archive))))
  :hints (("Goal" :use ((:instance fn-nntp-string-list-excludes-nil
                         (strings (fn-state-groups archive))))
           :in-theory (disable fn-nntp-string-list-excludes-nil
                               fn-nntp-projectionp fn-state-groups))))

; An available article is found by raw number too, and a raw match whose
; identifier renders is available.  This is the bridge between the number a
; command names and the cursor the session keeps.
(defthm fn-nntp-article-idp-is-consp
  (implies (fn-nntp-article-idp article) (consp article))
  :hints (("Goal" :in-theory (enable fn-nntp-article-idp fn-article-msgid))))

(defthm fn-nntp-found-article-with-identifier-is-available
  (implies (and (posp number)
                (<= number *fn-nntp-max-article-number*)
                (fn-nntp-article-idp
                 (fn-nntp-find-group-number group number articles)))
           (consp (fn-nntp-available-article group number articles)))
  :hints (("Goal" :induct (fn-nntp-find-group-number group number articles)
           :in-theory (enable fn-nntp-find-group-number
                              fn-nntp-available-article
                              fn-nntp-article-number))))

; -----------------------------------------------------------------------------
; Every command keeps the opened projection verdict

(defthm fn-nntp-single-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-single session text)))
         (fn-nntp-session-projected session)))

(defthm fn-nntp-multi-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-multi session initial lines)))
         (fn-nntp-session-projected session)))

(defthm fn-nntp-multi-octets-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-multi-octets session initial lines)))
         (fn-nntp-session-projected session)))

(defthm fn-nntp-article-response-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session
           (fn-nntp-article-response session article number kind updatep group)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (enable fn-nntp-article-response))))

(defthm fn-nntp-group-result-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-group-result session archive group)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (enable fn-nntp-group-result))))

(defthm fn-nntp-listgroup-result-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session
           (fn-nntp-listgroup-result session archive group range)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (enable fn-nntp-listgroup-result))))

(defthm fn-nntp-listgroup-command-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session
           (fn-nntp-listgroup-command session archive args)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-listgroup-command)
                                  (fn-nntp-listgroup-result fn-nntp-single
                                   fn-nntp-parse-range fn-nntp-token-string
                                   fn-nntp-result-session
                                   fn-nntp-session-projected)))))

(defthm fn-nntp-current-retrieval-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-current-retrieval session archive kind)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-current-retrieval)
                                  (fn-nntp-article-response fn-nntp-single
                                   fn-nntp-result-session
                                   fn-nntp-session-projected)))))

(defthm fn-nntp-number-retrieval-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-number-retrieval session archive kind token)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-number-retrieval)
                                  (fn-nntp-article-response fn-nntp-single
                                   fn-nntp-result-session
                                   fn-nntp-session-projected)))))

(defthm fn-nntp-msgid-retrieval-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-msgid-retrieval session archive kind token)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :use fn-nntp-msgid-preserves-session)))

(defthm fn-nntp-retrieval-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-retrieval session archive kind args)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-retrieval)
                                  (fn-nntp-current-retrieval
                                   fn-nntp-number-retrieval
                                   fn-nntp-msgid-retrieval
                                   fn-nntp-single
                                   fn-nntp-result-session
                                   fn-nntp-session-projected)))))

(defthm fn-nntp-next-or-last-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-next-or-last session archive direction)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-next-or-last)
                                  (fn-nntp-article-response fn-nntp-single
                                   fn-nntp-result-session
                                   fn-nntp-session-projected)))))

; -----------------------------------------------------------------------------
; The reader profile's new commands change no session state
;
; RFC 3977 section 5.3.2 requires MODE READER on a non-mode-switching server
; advertising READER to affect the server state in no way; sections 7.1, 7.3,
; 8.3 and 8.4 define DATE, NEWGROUPS, OVER and LIST OVERVIEW.FMT with no state
; effect either, and in particular OVER does not move the current article.

; The session is untouched by every reader-profile renderer.  Each proof
; opens exactly its renderer with the four cluster vocabularies closed: the
; calendar, the date parsers and fn-nov-overview (which opens
; fn-article-parse) never appear in the session component, and the leaves
; close by fn-nntp-single-preserves-session, fn-nntp-multi-preserves-session,
; fn-nntp-multi-octets-preserves-session and
; fn-nntp-result-session-of-make-result.  Opened, DATE alone ran past 8M
; prover steps in floor/mod (2026-09-19).
(defthm fn-nntp-date-response-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-date-response session env)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-date-response)))))

(defthm fn-nntp-mode-response-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-mode-response session args)) session))

(defthm fn-nntp-newgroups-response-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-newgroups-response session archive env args))
         session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-newgroups-response)))))

(defthm fn-nntp-list-overview-fmt-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-list-overview-fmt session)) session))

(defthm fn-nntp-over-current-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-over-current session archive)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-over-current)))))

(defthm fn-nntp-over-range-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-over-range session archive token))
         session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-over-range)))))

(defthm fn-nntp-over-msgid-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-over-msgid session archive token))
         session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-over-msgid)))))

(defthm fn-nntp-over-response-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-over-response session archive args))
         session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-over-response)))))

; RFC 2980 sections 2.6, 2.8 and 2.1.3 and RFC 3977 sections 8.5 and 8.6:
; the legacy spellings and the two LIST variants they need.  None of them
; touches the session, and each is closed below so the dispatcher theorems
; see one rewrite per command rather than a renderer.
(defthm fn-nntp-list-headers-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-list-headers session)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-list-headers)))))
(defthm fn-nntp-xover-range-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-xover-range session archive token)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-xover-range)))))
(defthm fn-nntp-xover-response-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-xover-response session archive args)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-xover-response)))))
(defthm fn-nntp-hdr-current-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-hdr-current session archive field legacyp)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-hdr-current)))))
(defthm fn-nntp-hdr-range-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-hdr-range session archive field token legacyp)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-hdr-range)))))
(defthm fn-nntp-hdr-msgid-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-hdr-msgid session archive field token legacyp)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-hdr-msgid)))))
(defthm fn-nntp-hdr-command-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-hdr-command session archive args legacyp)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-hdr-command)))))
(defthm fn-nntp-hdr-response-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-hdr-response session archive args)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-hdr-response)))))
(defthm fn-nntp-xhdr-response-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-xhdr-response session archive args)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-xhdr-response)))))
(defthm fn-nntp-list-active-times-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-list-active-times session env args)) session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-list-active-times)))))

(in-theory (disable fn-nntp-date-response fn-nntp-mode-response
                    fn-nntp-newgroups-response fn-nntp-list-overview-fmt
                    fn-nntp-over-current fn-nntp-over-range
                    fn-nntp-over-msgid fn-nntp-over-response
                    fn-nntp-list-headers fn-nntp-xover-range
                    fn-nntp-xover-response fn-nntp-hdr-current
                    fn-nntp-hdr-range fn-nntp-hdr-msgid fn-nntp-hdr-command
                    fn-nntp-hdr-response fn-nntp-xhdr-response
                    fn-nntp-list-active-times))

(defthm fn-nntp-list-response-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-list-response session archive args))
         session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-list-response
                                   fn-nntp-list-active-or-newsgroups
                                   fn-nntp-list-filtered-response
                                   fn-nntp-list-unmaintained-response
                                   fn-nntp-list-active
                                   fn-nntp-list-newsgroups)))))

(defthm fn-nntp-list-command-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-list-command session archive env args))
         session)
  :hints (("Goal" :in-theory (e/d () (fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                                   fn-nntp-projection-vocabulary
                                   fn-nntp-responses-vocabulary)
                                  (fn-nntp-list-command)))))

(in-theory (disable fn-nntp-list-command))

(defthm fn-nntp-capabilities-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-capabilities session)) session)
  :hints (("Goal" :in-theory (enable fn-nntp-capabilities))))

(defthm fn-nntp-help-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-help session)) session)
  :hints (("Goal" :in-theory (enable fn-nntp-help))))

; The dispatcher theorem below keeps the session accessors open for its
; inline QUIT branch, so the closed-form -preserves-session rules for DATE
; and MODE cannot match (car (fn-nntp-date-response ...)).  These two are
; those rules unfolded through fn-nntp-result-session, local, for that one
; proof; nothing exports an accessor equality.
(local (defthm fn-nntp-date-response-result-unfolds
  (equal (car (fn-nntp-date-response session env)) session)
  :hints (("Goal" :use fn-nntp-date-response-preserves-session
           ; the keystone would rewrite its own instance to (equal s s)
           :in-theory (disable fn-nntp-date-response-preserves-session)))))
(local (defthm fn-nntp-mode-response-result-unfolds
  (equal (car (fn-nntp-mode-response session args)) session)
  :hints (("Goal" :use fn-nntp-mode-response-preserves-session
           ; the keystone would rewrite its own instance to (equal s s)
           :in-theory (disable fn-nntp-mode-response-preserves-session)))))

(defthm fn-nntp-session-command-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-session-command session env keyword args)))
         (fn-nntp-session-projected session))
  ; The QUIT branch builds its result inline, so the session accessors stay
  ; open here; the theorem itself is in the closed form later proofs use.
  :hints (("Goal" :in-theory (enable fn-nntp-session-command
                                     fn-nntp-capabilities fn-nntp-help
                                     fn-nntp-multi fn-nntp-single))))

(defthm fn-nntp-archive-command-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-archive-command session archive env keyword args)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-archive-command)
                                  (fn-nntp-group-result fn-nntp-listgroup-command
                                   fn-nntp-list-response fn-nntp-next-or-last
                                   fn-nntp-retrieval fn-nntp-single
                                   fn-nntp-keywordp
                                   fn-nntp-result-session
                                   fn-nntp-session-projected)))))

(defthm fn-nntp-command-keeps-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-command session archive env tokens)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-command)
                                  (fn-nntp-session-command fn-nntp-archive-command
                                   fn-nntp-single fn-nntp-keyword-tokenp
                                   fn-nntp-archive-keywordp
                                   fn-nntp-result-session
                                   fn-nntp-session-projected)))))

; The keystone for D3(a): the verdict fn-nntp-open-session computed is the
; verdict every later step has.  No served command reruns fn-nntp-projectionp.
(defthm fn-nntp-step-preserves-carried-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-step session archive env wire-event)))
         (fn-nntp-session-projected session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-step)
                                  (fn-nntp-command fn-nntp-single
                                   fn-nntp-make-result fn-nntp-sessionp
                                   fn-nntp-command-inputp fn-nntp-tokenize
                                   fn-nntp-command-arguments-at-mostp
                                   fn-nntp-result-session
                                   fn-nntp-session-projected)))))

; -----------------------------------------------------------------------------
; No archive content can deny an archive-free command

; The keystone for D3's availability symptom: a committed article the reader
; cannot project used to answer 503 to CAPABILITIES and QUIT.  These commands
; now do not read the archive at all, so no archive can change their answer.
(defthm fn-nntp-archive-free-step-ignores-the-archive
  (implies (not (fn-nntp-archive-keywordp (car (fn-nntp-tokenize line))))
           (equal (fn-nntp-step session archive env (list :command line))
                  (fn-nntp-step session other env (list :command line))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-step fn-nntp-command)
                                  (fn-nntp-session-command fn-nntp-archive-command
                                   fn-nntp-archive-keywordp fn-nntp-keyword-tokenp
                                   fn-nntp-single fn-nntp-tokenize
                                   fn-nntp-command-inputp
                                   fn-nntp-command-arguments-at-mostp))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Selection sets the cursor to the group's first available article

(defthm fn-nntp-group-selects-the-first-available-article
  (implies (and (member-equal group (fn-state-groups archive))
                (fn-nntp-group-nonemptyp group archive))
           (and (equal (fn-nntp-session-group
                        (fn-nntp-result-session
                         (fn-nntp-group-result session archive group)))
                       group)
                (equal (fn-nntp-session-current
                        (fn-nntp-result-session
                         (fn-nntp-group-result session archive group)))
                       (fn-nntp-group-low group (fn-state-articles archive)))
                (fn-nntp-cursor-validp
                 group (fn-nntp-group-low group (fn-state-articles archive))
                 archive)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-group-result
                                   fn-nntp-group-nonemptyp
                                   fn-nntp-cursor-validp
                                   fn-nntp-set-cursor)
                                  (fn-nntp-group-initial fn-nntp-crlf
                                   fn-nntp-decimal-field
                                   fn-nntp-available-article
                                   fn-nntp-group-low)))))

(defthm fn-nntp-group-on-empty-group-invalidates-the-cursor
  (implies (and (member-equal group (fn-state-groups archive))
                (not (fn-nntp-group-nonemptyp group archive)))
           (null (fn-nntp-session-current
                  (fn-nntp-result-session
                   (fn-nntp-group-result session archive group)))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-group-result
                                   fn-nntp-group-nonemptyp
                                   fn-nntp-set-cursor)
                                  (fn-nntp-group-initial fn-nntp-crlf
                                   fn-nntp-decimal-field
                                   fn-nntp-group-low)))))

; RFC 3977 section 6.1.2.2: LISTGROUP resets the cursor to the group's first
; article even when that article is outside the requested range.
(defthm fn-nntp-listgroup-selects-the-first-available-article
  (implies (and (member-equal group (fn-state-groups archive))
                (fn-nntp-group-nonemptyp group archive))
           (and (equal (fn-nntp-session-group
                        (fn-nntp-result-session
                         (fn-nntp-listgroup-result session archive group range)))
                       group)
                (equal (fn-nntp-session-current
                        (fn-nntp-result-session
                         (fn-nntp-listgroup-result session archive group range)))
                       (fn-nntp-group-low group (fn-state-articles archive)))
                (fn-nntp-cursor-validp
                 group (fn-nntp-group-low group (fn-state-articles archive))
                 archive)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-listgroup-result
                                   fn-nntp-group-nonemptyp
                                   fn-nntp-cursor-validp
                                   fn-nntp-set-cursor)
                                  (fn-nntp-listgroup-initial fn-nntp-crlf
                                   fn-nntp-stuff-lines fn-nntp-number-lines
                                   fn-nntp-group-range-numbers
                                   fn-nntp-decimal-field
                                   fn-nntp-available-article
                                   fn-nntp-group-low)))))

(defthm fn-nntp-unknown-group-keeps-the-session
  (implies (not (member-equal group (fn-state-groups archive)))
           (and (equal (fn-nntp-result-session
                        (fn-nntp-group-result session archive group))
                       session)
                (equal (fn-nntp-result-session
                        (fn-nntp-listgroup-result session archive group range))
                       session))))

; -----------------------------------------------------------------------------
; Preservation, command by command

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

(defthm fn-nntp-group-result-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-group-result session archive group))
            archive))
  :hints (("Goal" :in-theory (e/d (fn-nntp-session-consistentp
                                   fn-nntp-cursor-validp
                                   fn-nntp-group-nonemptyp
                                   fn-nntp-set-cursor
                                   fn-nntp-group-result)
                                  (fn-nntp-group-initial fn-nntp-crlf
                                   fn-nntp-decimal-field
                                   fn-nntp-projectionp
                                   fn-nntp-available-article
                                   fn-nntp-group-low
                                   fn-state-groups fn-state-articles
                                   fn-state-nexts)))))

(defthm fn-nntp-listgroup-result-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-listgroup-result session archive group range))
            archive))
  :hints (("Goal" :in-theory (e/d (fn-nntp-session-consistentp
                                   fn-nntp-cursor-validp
                                   fn-nntp-group-nonemptyp
                                   fn-nntp-set-cursor
                                   fn-nntp-listgroup-result)
                                  (fn-nntp-listgroup-initial fn-nntp-crlf
                                   fn-nntp-stuff-lines fn-nntp-number-lines
                                   fn-nntp-group-range-numbers
                                   fn-nntp-decimal-field
                                   fn-nntp-projectionp
                                   fn-nntp-available-article
                                   fn-nntp-group-low
                                   fn-state-groups fn-state-articles
                                   fn-state-nexts)))))

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
                 fn-nntp-session-consistentp
                 fn-nntp-projectionp fn-statep)))))

(defthm fn-nntp-available-article-implies-nonempty
  (implies (consp (fn-nntp-available-article group number articles))
           (posp (fn-nntp-group-low group articles)))
  :hints (("Goal" :induct (fn-nntp-available-article group number articles)
           :in-theory (enable fn-nntp-available-article fn-nntp-group-low))))

; The cursor moves only to an available article, and only on success.  The
; response's byte rendering is kept out of this proof entirely; only the
; session component of the result is at issue.
(defthm fn-nntp-article-response-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (or (not updatep)
                    (and (stringp group)
                         (member-equal group (fn-state-groups archive))
                         (posp number)
                         (consp (fn-nntp-available-article
                                 group number (fn-state-articles archive))))))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-article-response session article number kind updatep group))
            archive))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-article-response
                 fn-nntp-session-consistentp
                 fn-nntp-group-nonemptyp
                 fn-nntp-set-cursor
                 fn-nntp-cursor-validp)
                (fn-nntp-article-idp
                 fn-nntp-article-framedp
                 fn-nntp-article-section
                 fn-nntp-retrieval-initial
                 fn-nntp-decimal-field
                 fn-nntp-crlf
                 fn-nntp-stuff-lines
                 fn-nntp-projectionp
                 fn-nntp-available-article
                 fn-nntp-group-low
                 fn-state-groups fn-state-articles
                 fn-state-nexts)))))

(defthm fn-nntp-current-retrieval-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-current-retrieval session archive kind)) archive))
  :hints (("Goal"
           :use ((:instance fn-nntp-article-response-preserves-consistent-session
                  (article (fn-nntp-available-article
                            (fn-nntp-session-group session)
                            (fn-nntp-session-current session)
                            (fn-state-articles archive)))
                  (number (fn-nntp-session-current session))
                  (updatep t)
                  (group (fn-nntp-session-group session))))
           :in-theory (e/d (fn-nntp-current-retrieval)
                           (fn-nntp-article-response
                            fn-nntp-projectionp fn-statep
                            fn-state-groups fn-state-articles fn-state-nexts
                            fn-nntp-available-article fn-nntp-group-low
                            fn-nntp-article-idp fn-nntp-article-framedp
                            fn-nntp-article-section fn-nntp-retrieval-initial
                            fn-nntp-decimal-field fn-nntp-crlf
                            fn-nntp-stuff-lines fn-nntp-group-initial
                            fn-nntp-listgroup-initial fn-nntp-number-lines
                            fn-nntp-group-range-numbers)))))

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

(defthm fn-nntp-number-token-value-bounded
  (implies (fn-nntp-number-tokenp token)
           (<= (fn-nntp-decimal-value token) *fn-nntp-max-article-number*))
  :hints (("Goal" :in-theory (enable fn-nntp-number-tokenp
                                     fn-nntp-decimal-value))))

; A retrieval naming a number whose article cannot be rendered answers 503 and
; leaves the session alone, so the cursor never moves onto it.
(defthm fn-nntp-article-response-without-identifier-preserves-session
  (implies (not (fn-nntp-article-idp article))
           (equal (fn-nntp-result-session
                   (fn-nntp-article-response session article number kind updatep group))
                  session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-article-response)
                                  (fn-nntp-article-idp
                                   fn-nntp-article-framedp
                                   fn-nntp-article-section
                                   fn-nntp-retrieval-initial
                                   fn-nntp-decimal-field
                                   fn-nntp-crlf fn-nntp-stuff-lines)))))

(defthm fn-nntp-number-retrieval-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-number-retrieval session archive kind token)) archive))
  :hints (("Goal"
           :cases ((fn-nntp-article-idp
                    (fn-nntp-find-group-number
                     (fn-nntp-session-group session)
                     (fn-nntp-decimal-value token)
                     (fn-state-articles archive))))
           :use ((:instance fn-nntp-article-response-preserves-consistent-session
                  (article (fn-nntp-find-group-number
                            (fn-nntp-session-group session)
                            (fn-nntp-decimal-value token)
                            (fn-state-articles archive)))
                  (number (fn-nntp-decimal-value token))
                  (updatep t)
                  (group (fn-nntp-session-group session)))
                 (:instance fn-nntp-found-article-with-identifier-is-available
                  (group (fn-nntp-session-group session))
                  (number (fn-nntp-decimal-value token))
                  (articles (fn-state-articles archive))))
           :in-theory (e/d (fn-nntp-number-retrieval)
                           (fn-nntp-article-response
                            fn-nntp-found-article-with-identifier-is-available
                            fn-nntp-find-group-number
                            fn-nntp-result-session
                            fn-nntp-single fn-nntp-make-result
                            fn-nntp-projectionp fn-statep
                            fn-state-groups fn-state-articles fn-state-nexts
                            fn-nntp-available-article fn-nntp-group-low
                            fn-nntp-article-idp fn-nntp-article-framedp
                            fn-nntp-article-section fn-nntp-retrieval-initial
                            fn-nntp-decimal-field fn-nntp-crlf
                            fn-nntp-stuff-lines fn-nntp-group-initial
                            fn-nntp-listgroup-initial fn-nntp-number-lines
                            fn-nntp-group-range-numbers)))))

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
                                   fn-nntp-session-consistentp
                                   fn-nntp-projectionp fn-statep)))))

(defthm fn-nntp-next-or-last-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-next-or-last session archive direction)) archive))
  :hints (("Goal"
           :use ((:instance fn-nntp-article-response-preserves-consistent-session
                  (article (fn-nntp-available-article
                            (fn-nntp-session-group session)
                            (fn-nntp-group-next-number
                             (fn-nntp-session-group session)
                             (fn-nntp-session-current session)
                             (fn-state-articles archive))
                            (fn-state-articles archive)))
                  (number (fn-nntp-group-next-number
                           (fn-nntp-session-group session)
                           (fn-nntp-session-current session)
                           (fn-state-articles archive)))
                  (kind :stat) (updatep t)
                  (group (fn-nntp-session-group session)))
                 (:instance fn-nntp-article-response-preserves-consistent-session
                  (article (fn-nntp-available-article
                            (fn-nntp-session-group session)
                            (fn-nntp-group-last-number
                             (fn-nntp-session-group session)
                             (fn-nntp-session-current session)
                             (fn-state-articles archive))
                            (fn-state-articles archive)))
                  (number (fn-nntp-group-last-number
                           (fn-nntp-session-group session)
                           (fn-nntp-session-current session)
                           (fn-state-articles archive)))
                  (kind :stat) (updatep t)
                  (group (fn-nntp-session-group session))))
           :in-theory (e/d (fn-nntp-next-or-last
                                   ; consp from true-listp inside fn-nntp-sessionp;
                                   ; withdrawn book-wide at the top, needed here
                                   fn-article-nonempty-true-list-is-consp)
                           (fn-nntp-article-response
                            fn-nntp-group-next-number fn-nntp-group-last-number
                            fn-nntp-projectionp fn-statep
                            fn-state-groups fn-state-articles fn-state-nexts
                            fn-nntp-available-article fn-nntp-group-low
                            fn-nntp-article-idp fn-nntp-article-framedp
                            fn-nntp-article-section fn-nntp-retrieval-initial
                            fn-nntp-decimal-field fn-nntp-crlf
                            fn-nntp-stuff-lines fn-nntp-group-initial
                            fn-nntp-listgroup-initial fn-nntp-number-lines
                            fn-nntp-group-range-numbers)))))

; RFC 3977 sections 6.1.3.2 and 6.1.4.2: LAST and NEXT either move the cursor
; to an article that exists in the group or leave the session untouched.
(defthm fn-nntp-next-or-last-moves-only-to-an-available-article
  (implies (fn-nntp-session-consistentp session archive)
           (let ((result (fn-nntp-result-session
                          (fn-nntp-next-or-last session archive direction))))
             (or (equal result session)
                 (and (equal (fn-nntp-session-group result)
                             (fn-nntp-session-group session))
                      (fn-nntp-cursor-validp (fn-nntp-session-group session)
                                             (fn-nntp-session-current result)
                                             archive)))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-next-or-last
                                   fn-nntp-article-response
                                   fn-nntp-cursor-validp
                                   fn-nntp-set-cursor)
                                  (fn-nntp-session-consistentp
                                   fn-nntp-article-idp
                                   fn-nntp-article-framedp
                                   fn-nntp-article-section
                                   fn-nntp-retrieval-initial
                                   fn-nntp-decimal-field
                                   fn-nntp-crlf
                                   fn-nntp-stuff-lines
                                   fn-nntp-available-article
                                   fn-nntp-group-next-number
                                   fn-nntp-group-last-number))))
  :rule-classes nil)

(defthm fn-nntp-list-response-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-list-response session archive args))
            archive))
  :hints (("Goal" :use fn-nntp-list-response-preserves-session)))

(defthm fn-nntp-quit-session-preserves-consistency
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-make-session nil
                                  (fn-nntp-session-group session)
                                  (fn-nntp-session-current session)
                                  (fn-nntp-session-projected session))
            archive))
  :hints (("Goal" :in-theory (enable fn-nntp-session-consistentp))))

(defthm fn-nntp-session-command-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-session-command session env keyword args)) archive))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-session-command)
                (fn-nntp-make-session
                 fn-nntp-session-group
                 fn-nntp-session-current
                 fn-nntp-session-projected
                 fn-nntp-keywordp
                 fn-nntp-keyword-tokenp
                 fn-nntp-capabilities
                 fn-nntp-help
                 fn-nntp-make-result
                 fn-nntp-result-session
                 fn-nntp-single
                 fn-nntp-session-consistentp
                 fn-nntp-projectionp fn-statep)))))

(defthm fn-nntp-archive-command-preserves-consistent-session
  (implies (and (fn-nntp-session-consistentp session archive)
                (fn-nntp-projectionp archive))
           (fn-nntp-session-consistentp
            (fn-nntp-result-session
             (fn-nntp-archive-command session archive env keyword args)) archive))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-archive-command)
                (fn-nntp-projectionp fn-statep
                 fn-nntp-keywordp
                 fn-nntp-listgroup-command
                 fn-nntp-list-response
                 fn-nntp-next-or-last
                 fn-nntp-retrieval
                 fn-nntp-group-result
                 fn-nntp-result-session
                 fn-nntp-single
                 fn-nntp-session-consistentp)))))

(defthm fn-nntp-command-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-command session archive env tokens))
            archive))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-command)
                (fn-nntp-projectionp fn-statep
                 fn-nntp-archive-keywordp
                 fn-nntp-keyword-tokenp
                 fn-nntp-session-command
                 fn-nntp-archive-command
                 fn-nntp-result-session
                 fn-nntp-single
                 fn-nntp-session-consistentp))
           :expand ((fn-nntp-session-consistentp session archive)))))

(defthm fn-nntp-step-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-step session archive env wire-event))
            archive))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-step)
                (fn-nntp-make-result
                 fn-nntp-command
                 fn-nntp-projectionp fn-statep
                 fn-nntp-sessionp
                 fn-nntp-session-openp
                 fn-nntp-command-inputp
                 fn-nntp-tokenize
                 fn-nntp-command-arguments-at-mostp
                 fn-nntp-result-session
                 fn-nntp-single
                 fn-nntp-session-consistentp)))))

; -----------------------------------------------------------------------------
; Finite traces

; Actual step folding, including malformed events and events after QUIT.  There
; is no event predicate that assumes the result is valid, and no output filter.
(defun fn-nntp-run-session (session archive env events)
  (if (consp events)
      (fn-nntp-run-session
       (fn-nntp-result-session (fn-nntp-step session archive env (car events)))
       archive env (cdr events))
    session))

(defthm fn-nntp-finite-trace-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-run-session session archive env events) archive))
  :hints (("Goal" :induct (fn-nntp-run-session session archive env events)
           :in-theory (e/d (fn-nntp-run-session)
                           (fn-nntp-step fn-nntp-result-session
                            fn-nntp-session-consistentp fn-nntp-projectionp)))))

(defthm fn-nntp-finite-trace-preserves-carried-projection
  (equal (fn-nntp-session-projected (fn-nntp-run-session session archive env events))
         (fn-nntp-session-projected session))
  :hints (("Goal" :induct (fn-nntp-run-session session archive env events)
           :in-theory (e/d (fn-nntp-run-session)
                           (fn-nntp-step fn-nntp-result-session
                            fn-nntp-session-projected)))))

(defthm fn-nntp-opened-finite-trace-is-consistent
  (and (fn-nntp-session-consistentp
        (fn-nntp-run-session (fn-nntp-open-session archive) archive env events)
        archive)
       (fn-nntp-sessionp
        (fn-nntp-run-session (fn-nntp-open-session archive) archive env events)))
  :hints (("Goal"
           :use ((:instance fn-nntp-open-session-is-consistent)
                 (:instance fn-nntp-finite-trace-preserves-consistent-session
                  (session (fn-nntp-open-session archive)))
                 (:instance fn-nntp-consistent-session-is-session
                  (session (fn-nntp-run-session
                            (fn-nntp-open-session archive) archive env events))))
           :in-theory (disable fn-nntp-run-session
                               fn-nntp-open-session
                               fn-nntp-session-consistentp fn-nntp-sessionp
                               fn-nntp-projectionp
                               fn-nntp-open-session-is-consistent
                               fn-nntp-finite-trace-preserves-consistent-session
                               fn-nntp-consistent-session-is-session))))
