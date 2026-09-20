; Expected transcripts for the selected reader profile: DATE (RFC 3977
; section 7.1), NEWGROUPS (section 7.3), MODE READER (section 5.3), OVER
; (section 8.3) and LIST OVERVIEW.FMT (section 8.4), plus the section 6.2
; argument forms and error precedence.
;
; Every expected reply below is an independent octet string written from the
; RFC, not obtained by running the reader and recording what it said.  The two
; NEWGROUPS block comparisons are the one exception and are deliberate: RFC
; 3977 section 7.3.2 requires the NEWGROUPS block to be in the same format as
; LIST ACTIVE, so the test compares the two commands against each other.
(in-package "ACL2")
(include-book "../../books/nntp-effects")
(include-book "std/testing/must-fail" :dir :system)

; This book reasons about the NNTP transitions themselves, so it opens the
; vocabularies the five books of the nntp cluster withdraw at their export
; events (2026-09-19 split of books/nntp.lisp).
(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary fn-nntp-projection-vocabulary fn-nntp-responses-vocabulary fn-nntp-vocabulary)))

(defconst *rp-groups* '("fn.letters" "fn.empty"))
(defconst *rp-id* "<Case@Id.invalid>")
(defconst *rp-payload* '(77 101 115 115 97 103 101 45 73 68 58 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 13 10 83 117 98 106 101 99 116 58 32 84 101 115 116 13 10 13 10 72 101 108 108 111 13 10 46 100 111 116 13 10))
(defconst *rp-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *rp-groups*) 1 *rp-id* *rp-payload*
                      '("fn.letters"))
   0 1 :durable))
(defconst *rp-session0* (fn-nntp-open-session *rp-archive*))
(assert-event (fn-nntp-projectionp *rp-archive*))

; 2026-09-19T12:34:56Z expressed as RFC 9171 section 4.2.6 DTN milliseconds,
; and a group creation fact dated 2025-09-21T00:00:00Z.
(defconst *rp-obs* (fn-clock-observation 1000 843136496000 1000 t))
(defconst *rp-blind-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *rp-facts*
  (list (fn-nntp-group-fact "fn.letters" 0 *rp-blind-obs*)
        (fn-nntp-group-fact "fn.empty" 811728000000 *rp-blind-obs*)))
(defconst *rp-env* (fn-nntp-env *rp-obs* *rp-facts*))
(defconst *rp-blind-env* (fn-nntp-env *rp-blind-obs* *rp-facts*))
(assert-event (fn-nntp-envp *rp-env*))
(assert-event (fn-nntp-envp *rp-blind-env*))

; A macro, so each transcript below writes its command line as a bare octet
; list; every use in this book is a literal.
(defmacro rp-reply (session archive env line)
  `(fn-nntp-result-effects
    (fn-nntp-step ,session ,archive ,env (list :command ',line))))

; -----------------------------------------------------------------------------
; The calendar conversion, pinned at boundaries an off-by-one would move

(assert-event (equal (fn-nntp-civil-from-days 10957) '(2000 1 1)))
(assert-event (equal (fn-nntp-civil-from-days 0) '(1970 1 1)))
; 11016 days after 1970-01-01 is 2000-02-29 (30 years with seven leap days
; is 10957 days to 2000-01-01, then 31 + 28); the earlier 11015 was typed.
(assert-event (equal (fn-nntp-civil-from-days 11016) '(2000 2 29)))
(assert-event (equal (fn-nntp-days-from-civil 2000 2 29) 11016))
(assert-event (equal (fn-nntp-dtn-civil 843136496000) '(2026 9 19 12 34 56)))
(assert-event (equal (fn-nntp-dtn-civil 0) '(2000 1 1 0 0 0)))
(assert-event (equal (fn-nntp-civil-dtn-ms 2000 1 1 0 0 0) 0))
(assert-event (equal (fn-nntp-civil-dtn-ms 2025 9 21 0 0 0) 811728000000))
(assert-event (equal (fn-nntp-civil-dtn-ms 1970 1 1 0 0 0) 0))
(assert-event (equal (fn-nntp-unix-dtn-ms 946684800000) 0))
(assert-event (equal (fn-nntp-unix-dtn-ms 0) 0))

; -----------------------------------------------------------------------------
; DATE (RFC 3977 section 7.1)

(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (68 65 84 69))
        (list (fn-nntp-reply-effect '(49 49 49 32 50 48 50 54 48 57 49 57 49 50 51 52 53 54 13 10)))))

; With no wall reading the reader refuses and says so; it never invents a time.
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-blind-env* (68 65 84 69))
        (list (fn-nntp-reply-effect
               '(53 48 51 32 115 101 114 118 101 114 32 104 111 108 100 115 32 110 111 32 119 97 108 108 32 99 108 111 99 107 32 114 101 97 100 105 110 103 13 10)))))

(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (68 65 84 69 32 78 79 87))
        (list (fn-nntp-reply-effect '(53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))

; -----------------------------------------------------------------------------
; MODE READER (RFC 3977 section 5.3)

(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (77 79 68 69 32 82 69 65 68 69 82))
        (list (fn-nntp-reply-effect '(50 48 49 32 112 111 115 116 105 110 103 32 112 114 111 104 105 98 105 116 101 100 13 10)))))

; Section 5.3.2: the command affects the server state in no way.
(assert-event
 (equal (fn-nntp-result-session
         (fn-nntp-step *rp-session0* *rp-archive* *rp-env*
                       (list :command '(77 79 68 69 32 82 69 65 68 69 82))))
        *rp-session0*))

(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (77 79 68 69 32 83 84 82 69 65 77))
        (list (fn-nntp-reply-effect '(53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (77 79 68 69))
        (list (fn-nntp-reply-effect '(53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))

; -----------------------------------------------------------------------------
; CAPABILITIES (RFC 3977 section 5.2) and LIST OVERVIEW.FMT (section 8.4)

(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (67 65 80 65 66 73 76 73 84 73 69 83))
        (list (fn-nntp-reply-effect
               '(49 48 49 32 99 97 112 97 98 105 108 105 116 121 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 86 69 82 83 73 79 78 32 50 13 10 82 69 65 68 69 82 13 10 79 86 69 82 32 77 83 71 73 68 13 10 76 73 83 84 32 65 67 84 73 86 69 32 78 69 87 83 71 82 79 85 80 83 32 79 86 69 82 86 73 69 87 46 70 77 84 13 10 73 77 80 76 69 77 69 78 84 65 84 73 79 78 32 102 110 45 110 110 116 112 45 108 97 98 13 10 46 13 10)))))

(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env*
                  (76 73 83 84 32 79 86 69 82 86 73 69 87 46 70 77 84))
        (list (fn-nntp-reply-effect
               '(50 49 53 32 111 114 100 101 114 32 111 102 32 102 105 101 108 100 115 32 105 110 32 111 118 101 114 118 105 101 119 32 100 97 116 97 98 97 115 101 13 10 83 117 98 106 101 99 116 58 13 10 70 114 111 109 58 13 10 68 97 116 101 58 13 10 77 101 115 115 97 103 101 45 73 68 58 13 10 82 101 102 101 114 101 110 99 101 115 58 13 10 58 98 121 116 101 115 13 10 58 108 105 110 101 115 13 10 46 13 10)))))

; -----------------------------------------------------------------------------
; The NEWGROUPS date and time grammar (RFC 3977 section 7.3.2)

; Four-digit years need no clock at all.
(assert-event (equal (fn-nntp-newgroups-date-parse '(49 57 57 57 48 54 50 52) 0)
                     '(:ok 1999 6 24)))
(assert-event (equal (fn-nntp-newgroups-date-parse '(50 48 48 48 48 50 50 57) 0)
                     '(:ok 2000 2 29)))
; Month and day ranges are enforced; the year floor is section 7.3.2's 19xx.
(assert-event (equal (car (fn-nntp-newgroups-date-parse '(49 57 57 57 49 51 50 52) 0))
                     :error))
(assert-event (equal (car (fn-nntp-newgroups-date-parse '(49 57 57 57 48 54 51 50) 0))
                     :error))
(assert-event (equal (car (fn-nntp-newgroups-date-parse '(49 56 57 57 48 54 50 52) 0))
                     :error))
; Seven digits is neither form.
(assert-event (equal (fn-nntp-newgroups-date-parse '(49 57 57 57 48 54 50) 0)
                     '(:error :syntax)))
(assert-event (equal (fn-nntp-newgroups-date-parse '(49 57 57 57 45 48 54 45 50 52) 0)
                     '(:error :syntax)))

; The century rule: with the current year 2026, 26 is this century and 27 the
; previous one.  Without a wall reading the two-digit form is refused, not
; resolved against a guess.
(assert-event (equal (fn-nntp-newgroups-date-parse '(50 54 48 54 50 52) 2026)
                     '(:ok 2026 6 24)))
(assert-event (equal (fn-nntp-newgroups-date-parse '(50 55 48 54 50 52) 2026)
                     '(:ok 1927 6 24)))
(assert-event (equal (fn-nntp-newgroups-date-parse '(57 57 48 54 50 52) 2026)
                     '(:ok 1999 6 24)))
(assert-event (equal (fn-nntp-newgroups-date-parse '(50 54 48 54 50 52) 0)
                     '(:error :no-century)))
(assert-event (equal (fn-nntp-observed-year *rp-obs*) 2026))
(assert-event (equal (fn-nntp-observed-year *rp-blind-obs*) 0))

(assert-event (equal (fn-nntp-newgroups-time-parse '(49 50 51 52 53 54))
                     '(:ok 12 34 56)))
; Section 7.3.2 admits second 60 for a leap second, and rejects hour 24.
(assert-event (equal (fn-nntp-newgroups-time-parse '(50 51 53 57 54 48))
                     '(:ok 23 59 60)))
(assert-event (equal (car (fn-nntp-newgroups-time-parse '(50 51 53 57 54 49)))
                     :error))
(assert-event (equal (car (fn-nntp-newgroups-time-parse '(50 52 48 48 48 48)))
                     :error))
(assert-event (equal (car (fn-nntp-newgroups-time-parse '(49 50 51 52 53)))
                     :error))

; -----------------------------------------------------------------------------
; NEWGROUPS transcripts

; Same format as LIST ACTIVE (section 7.3.2), so the blocks must agree.
(defconst *rp-list-active*
  (fn-nntp-result-effects
   (fn-nntp-step *rp-session0* *rp-archive* *rp-env*
                 (list :command '(76 73 83 84 32 65 67 84 73 86 69)))))
(defconst *rp-newgroups-all*
  (fn-nntp-result-effects
   (fn-nntp-step *rp-session0* *rp-archive* *rp-env*
                 (list :command '(78 69 87 71 82 79 85 80 83 32 49 57 55 48 48 49 48 49 32 48 48 48 48 48 48 32 71 77 84)))))
(assert-event
 (equal *rp-newgroups-all*
        (list (fn-nntp-reply-effect
               (append '(50 51 49 32 108 105 115 116 32 111 102 32 110 101 119 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10)
                       (fn-ng-nthcdr 39
                                     (car (cdr (car *rp-list-active*)))))))))

; A threshold after fn.letters was created and before fn.empty was selects
; exactly one group.
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env*
                  (78 69 87 71 82 79 85 80 83 32 50 48 50 53 48 49 48 49 32 48 48 48 48 48 48 32 71 77 84))
        (list (fn-nntp-reply-effect
               (append '(50 51 49 32 108 105 115 116 32 111 102 32 110 101 119 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10)
                       (fn-nntp-stuff-lines
                        (list (fn-nntp-active-line *rp-archive* "fn.empty")))
                       '(46 13 10))))))

; An empty list is a valid response (section 7.3.2).
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env*
                  (78 69 87 71 82 79 85 80 83 32 50 48 57 57 48 49 48 49 32 48 48 48 48 48 48 32 71 77 84))
        (list (fn-nntp-reply-effect
               '(50 51 49 32 108 105 115 116 32 111 102 32 110 101 119 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10 46 13 10)))))

; The GMT token is optional and only in third position.
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env*
                  (78 69 87 71 82 79 85 80 83 32 50 48 57 57 48 49 48 49 32 48 48 48 48 48 48))
        (list (fn-nntp-reply-effect
               '(50 51 49 32 108 105 115 116 32 111 102 32 110 101 119 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10 46 13 10)))))
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env*
                  (78 69 87 71 82 79 85 80 83 32 50 48 57 57 48 49 48 49 32 48 48 48 48 48 48 32 85 84 67))
        (list (fn-nntp-reply-effect '(53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env*
                  (78 69 87 71 82 79 85 80 83 32 50 48 57 57 48 49 48 49))
        (list (fn-nntp-reply-effect '(53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-blind-env*
                  (78 69 87 71 82 79 85 80 83 32 57 57 48 49 48 49 32 48 48 48 48 48 48 32 71 77 84))
        (list (fn-nntp-reply-effect
               '(53 48 51 32 116 119 111 45 100 105 103 105 116 32 121 101 97 114 32 110 101 101 100 115 32 97 32 119 97 108 108 32 99 108 111 99 107 32 114 101 97 100 105 110 103 13 10)))))

; -----------------------------------------------------------------------------
; OVER (RFC 3977 section 8.3)

(defconst *rp-selected*
  (fn-nntp-result-session
   (fn-nntp-step *rp-session0* *rp-archive* *rp-env*
                 (list :command '(71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115)))))

; The eight mandatory fields, TAB separated, in section 8.3.2's order.  From,
; Date and References are absent from the stored article, so those fields are
; empty; :bytes is the retained octet count and :lines the retained body lines.
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env* (79 86 69 82))
        (list (fn-nntp-reply-effect
               '(50 50 52 32 111 118 101 114 118 105 101 119 32 105 110 102 111 114 109 97 116 105 111 110 32 102 111 108 108 111 119 115 13 10 49 9 84 101 115 116 9 9 9 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 9 9 54 49 9 50 13 10 46 13 10)))))

; The message-id form reports article number zero and moves nothing.
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env*
                  (79 86 69 82 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62))
        (list (fn-nntp-reply-effect
               '(50 50 52 32 111 118 101 114 118 105 101 119 32 105 110 102 111 114 109 97 116 105 111 110 32 102 111 108 108 111 119 115 13 10 48 9 84 101 115 116 9 9 9 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 9 9 54 49 9 50 13 10 46 13 10)))))
(assert-event
 (equal (fn-nntp-result-session
         (fn-nntp-step *rp-selected* *rp-archive* *rp-env*
                       (list :command '(79 86 69 82 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62))))
        *rp-selected*))

; A range, an open range, and a range containing nothing.
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env* (79 86 69 82 32 49 45))
        (list (fn-nntp-reply-effect
               '(50 50 52 32 111 118 101 114 118 105 101 119 32 105 110 102 111 114 109 97 116 105 111 110 32 102 111 108 108 111 119 115 13 10 49 9 84 101 115 116 9 9 9 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 9 9 54 49 9 50 13 10 46 13 10)))))
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env* (79 86 69 82 32 49 45 49))
        (list (fn-nntp-reply-effect
               '(50 50 52 32 111 118 101 114 118 105 101 119 32 105 110 102 111 114 109 97 116 105 111 110 32 102 111 108 108 111 119 115 13 10 49 9 84 101 115 116 9 9 9 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 9 9 54 49 9 50 13 10 46 13 10)))))
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env* (79 86 69 82 32 53 45 50))
        (list (fn-nntp-reply-effect '(52 50 51 32 110 111 32 97 114 116 105 99 108 101 115 32 105 110 32 116 104 97 116 32 114 97 110 103 101 13 10)))))
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env* (79 86 69 82 32 55))
        (list (fn-nntp-reply-effect '(52 50 51 32 110 111 32 97 114 116 105 99 108 101 115 32 105 110 32 116 104 97 116 32 114 97 110 103 101 13 10)))))

; Section 8.3.2's error precedence: 412 before 420/423, 430 for an absent id.
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (79 86 69 82))
        (list (fn-nntp-reply-effect '(52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (79 86 69 82 32 49 45))
        (list (fn-nntp-reply-effect '(52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env*
                  (79 86 69 82 32 60 110 111 46 115 117 99 104 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62))
        (list (fn-nntp-reply-effect
               '(52 51 48 32 110 111 32 97 114 116 105 99 108 101 32 119 105 116 104 32 116 104 97 116 32 109 101 115 115 97 103 101 45 105 100 13 10)))))
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env* (79 86 69 82 32 120))
        (list (fn-nntp-reply-effect '(53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env* (79 86 69 82 32 49 32 50))
        (list (fn-nntp-reply-effect '(53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))

; An empty group has an invalid current article, so the third form is 420.
(defconst *rp-empty-selected*
  (fn-nntp-result-session
   (fn-nntp-step *rp-session0* *rp-archive* *rp-env*
                 (list :command '(71 82 79 85 80 32 102 110 46 101 109 112 116 121)))))
(assert-event
 (equal (rp-reply *rp-empty-selected* *rp-archive* *rp-env* (79 86 69 82))
        (list (fn-nntp-reply-effect '(52 50 48 32 110 111 32 99 117 114 114 101 110 116 32 97 114 116 105 99 108 101 13 10)))))

; -----------------------------------------------------------------------------
; The section 8.3.2 transformation, on an article that needs it

(defconst *rp-fold-payload* '(77 101 115 115 97 103 101 45 73 68 58 32 60 70 111 108 100 64 73 100 46 105 110 118 97 108 105 100 62 13 10 83 117 98 106 101 99 116 58 32 79 110 101 9 84 119 111 13 10 9 84 104 114 101 101 13 10 13 10 66 111 100 121 13 10))
(defconst *rp-fold-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *rp-groups*) 1 "<Fold@Id.invalid>"
                      *rp-fold-payload* '("fn.letters"))
   0 1 :durable))
(defconst *rp-fold-over* (fn-nov-overview (car (fn-state-articles *rp-fold-archive*))))
(assert-event (fn-nov-okp *rp-fold-over*))
; Folding is undone and the embedded TAB becomes one space: no TAB survives to
; invent a field boundary, and no CRLF survives to split the line.
(assert-event (equal (fn-nov-subject *rp-fold-over*)
                     '(79 110 101 32 84 119 111 32 84 104 114 101 101)))
(assert-event (fn-nov-clean-fieldp (fn-nov-subject *rp-fold-over*)))
(assert-event (equal (fn-nov-from *rp-fold-over*) nil))
(assert-event (equal (fn-nov-date *rp-fold-over*) nil))
(assert-event (equal (fn-nov-references *rp-fold-over*) nil))
(assert-event (equal (fn-nov-bytes *rp-fold-over*) 65))
(assert-event (equal (fn-nov-lines *rp-fold-over*) 1))

; Teeth for fn-nov-scrub-is-clean: the transformation is what removes these
; octets, and nothing else in the pipeline would.
(assert-event (not (fn-nov-clean-fieldp '(65 9 66))))
(assert-event (not (fn-nov-clean-fieldp '(65 13 10 66))))
(assert-event (not (fn-nov-clean-fieldp '(65 0 66))))
(assert-event (equal (fn-nov-scrub '(65 9 66)) '(65 32 66)))
(assert-event (equal (fn-nov-scrub '(65 13 10 66)) '(65 66)))
(assert-event (equal (fn-nov-scrub '(65 0 66)) '(65 32 66)))
(assert-event (equal (fn-nov-scrub '(65 13 66)) '(65 32 66)))
(assert-event (equal (fn-nov-scrub '(65 10 66)) '(65 32 66)))

; -----------------------------------------------------------------------------
; ARTICLE/HEAD/BODY/STAT completeness (RFC 3977 section 6.2)

(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (65 82 84 73 67 76 69))
        (list (fn-nntp-reply-effect '(52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env* (65 82 84 73 67 76 69 32 49))
        (list (fn-nntp-reply-effect '(52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
(assert-event
 (equal (rp-reply *rp-empty-selected* *rp-archive* *rp-env* (72 69 65 68))
        (list (fn-nntp-reply-effect '(52 50 48 32 110 111 32 99 117 114 114 101 110 116 32 97 114 116 105 99 108 101 13 10)))))
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env* (66 79 68 89 32 57))
        (list (fn-nntp-reply-effect '(52 50 51 32 110 111 32 97 114 116 105 99 108 101 32 119 105 116 104 32 116 104 97 116 32 110 117 109 98 101 114 13 10)))))
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env*
                  (83 84 65 84 32 60 110 111 46 115 117 99 104 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62))
        (list (fn-nntp-reply-effect
               '(52 51 48 32 110 111 32 97 114 116 105 99 108 101 32 119 105 116 104 32 116 104 97 116 32 109 101 115 115 97 103 101 45 105 100 13 10)))))
; The message-id form is answered even with no group selected: section 6.2.1.3
; makes 412 a condition of the numeric and current forms only.
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-env*
                  (83 84 65 84 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62))
        (list (fn-nntp-reply-effect
               '(50 50 51 32 48 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 32 114 101 116 114 105 101 118 101 100 13 10)))))
(assert-event
 (equal (rp-reply *rp-selected* *rp-archive* *rp-env* (83 84 65 84))
        (list (fn-nntp-reply-effect
               '(50 50 51 32 49 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 32 114 101 116 114 105 101 118 101 100 13 10)))))

; -----------------------------------------------------------------------------
; Every new branch keeps the emitted response grammar and the session relation

(assert-event (fn-nntp-session-consistentp *rp-selected* *rp-archive*))
(assert-event
 (fn-nntp-effectsp
  (rp-reply *rp-selected* *rp-archive* *rp-env* (79 86 69 82 32 49 45))))
(assert-event
 (fn-nntp-effectsp
  (rp-reply *rp-session0* *rp-archive* *rp-env* (68 65 84 69))))
(assert-event
 (fn-nntp-effectsp
  (rp-reply *rp-session0* *rp-archive* *rp-env*
            (78 69 87 71 82 79 85 80 83 32 49 57 55 48 48 49 48 49 32 48 48 48 48 48 48 32 71 77 84))))
(assert-event
 (fn-nntp-effectsp
  (rp-reply *rp-session0* *rp-archive* *rp-env* (77 79 68 69 32 82 69 65 68 69 82))))
(assert-event
 (fn-nntp-effectsp
  (rp-reply *rp-session0* *rp-archive* *rp-env*
            (76 73 83 84 32 79 86 69 82 86 73 69 87 46 70 77 84))))

; A forged environment cannot produce a malformed NEWGROUPS reply: the fact
; screen inside fn-nntp-facts-since is what makes the environment recognizer
; unnecessary as a hypothesis of fn-nntp-step-effects-well-formed.
(defconst *rp-forged-env*
  (fn-nntp-env *rp-obs*
               (list (fn-nntp-group-fact "bad name" 0 *rp-blind-obs*)
                     (list :fn-nntp-group-fact "fn.letters" 0 :not-an-observation))))
(assert-event (not (fn-nntp-envp *rp-forged-env*)))
(assert-event
 (fn-nntp-effectsp
  (rp-reply *rp-session0* *rp-archive* *rp-forged-env*
            (78 69 87 71 82 79 85 80 83 32 49 57 55 48 48 49 48 49 32 48 48 48 48 48 48 32 71 77 84))))
(assert-event
 (equal (rp-reply *rp-session0* *rp-archive* *rp-forged-env*
                  (78 69 87 71 82 79 85 80 83 32 49 57 55 48 48 49 48 49 32 48 48 48 48 48 48 32 71 77 84))
        (list (fn-nntp-reply-effect
               '(50 51 49 32 108 105 115 116 32 111 102 32 110 101 119 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10 46 13 10)))))


; fn-nov-fmt-lines-are-clean is stated over *fn-nov-fmt-lines*, not over
; arbitrary texts: a text carrying CR renders the CR, so the general form is
; not a theorem.  The constant, which is all the server renders, is clean.
(assert-event
 (not (fn-nov-clean-line-listp
       (fn-nov-fmt-octet-lines (list (coerce (list (code-char 13)) 'string))))))
(assert-event (fn-nov-clean-line-listp (fn-nov-fmt-octet-lines *fn-nov-fmt-lines*)))
