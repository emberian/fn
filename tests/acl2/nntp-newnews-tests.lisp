; Teeth and transcripts for NEWNEWS (RFC 3977 section 7.4).
;
; The keystones are in books/nntp-newnews.lisp.  This book supplies, for each
; one, a reachable non-degenerate witness and a `must-fail` case per
; hypothesis (with three named exceptions, argued where they are), plus the
; expected octets of the five replies the command can produce: the 230 block,
; the empty 230 block, the 501 syntax refusal and the two 503s.  Every
; expected reply below is written from the RFC and from the block framing of
; section 3.1.1, not obtained by running the reader and recording what it
; said.
;
; The archive is five committed articles over two groups, chosen so that no
; assertion rests on one clause:
;   a1  fn.letters  Injection-Date 2026-09-19T12:00:00Z   reported
;   a2  fn.letters  Injection-Date 2026-01-01T00:00:00Z   too old
;   a3  fn.notes    Injection-Date 2026-09-19T12:00:00Z   wrong group
;   a4  fn.letters  Date only, 13:00:00 -0100 (14:00Z)    reported, by the
;                                                         RFC 5537 fallback
;   a5  fn.letters  no Injection-Date and no Date         unreadable stamp
(in-package "ACL2")
(include-book "../../books/nntp-effects")
(include-book "std/testing/must-fail" :dir :system)

; This book reasons about the NNTP transitions themselves, so it opens the
; vocabularies the books of the nntp cluster withdraw at their export events.
(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary fn-nntp-vocabulary
                          fn-nntp-newnews-vocabulary)))

; -----------------------------------------------------------------------------
; The instants, as RFC 9171 section 4.2.6 DTN milliseconds.  Each is the
; closed-form calendar's own value, pinned here so a drifting conversion is a
; failure and not a silently different answer.
(defconst *nn-midnight* 843091200000)      ; 2026-09-19T00:00:00Z
(defconst *nn-noon* 843134400000)          ; 2026-09-19T12:00:00Z
(defconst *nn-afternoon* 843141600000)     ; 2026-09-19T14:00:00Z
(defconst *nn-january* 820540800000)       ; 2026-01-01T00:00:00Z
(assert-event (equal (fn-nntp-civil-dtn-ms 2026 9 19 0 0 0) *nn-midnight*))
(assert-event (equal (fn-nntp-civil-dtn-ms 2026 9 19 12 0 0) *nn-noon*))
(assert-event (equal (fn-nntp-civil-dtn-ms 2026 9 19 14 0 0) *nn-afternoon*))
(assert-event (equal (fn-nntp-civil-dtn-ms 2026 1 1 0 0 0) *nn-january*))

(defconst *nn-a1-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 97
    49 64 102 110 46 105 110 118 97 108 105 100 62 13
    10 70 114 111 109 58 32 116 64 102 110 46 105 110
    118 97 108 105 100 13 10 83 117 98 106 101 99 116
    58 32 79 110 101 13 10 78 101 119 115 103 114 111
    117 112 115 58 32 102 110 46 108 101 116 116 101 114
    115 13 10 73 110 106 101 99 116 105 111 110 45 68
    97 116 101 58 32 83 97 116 44 32 49 57 32 83
    101 112 32 50 48 50 54 32 49 50 58 48 48 58
    48 48 32 43 48 48 48 48 13 10 13 10 72 101
    108 108 111 13 10))

(defconst *nn-a2-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 97
    50 64 102 110 46 105 110 118 97 108 105 100 62 13
    10 70 114 111 109 58 32 116 64 102 110 46 105 110
    118 97 108 105 100 13 10 83 117 98 106 101 99 116
    58 32 84 119 111 13 10 78 101 119 115 103 114 111
    117 112 115 58 32 102 110 46 108 101 116 116 101 114
    115 13 10 73 110 106 101 99 116 105 111 110 45 68
    97 116 101 58 32 84 104 117 44 32 48 49 32 74
    97 110 32 50 48 50 54 32 48 48 58 48 48 58
    48 48 32 43 48 48 48 48 13 10 13 10 72 101
    108 108 111 13 10))

(defconst *nn-a3-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 97
    51 64 102 110 46 105 110 118 97 108 105 100 62 13
    10 70 114 111 109 58 32 116 64 102 110 46 105 110
    118 97 108 105 100 13 10 83 117 98 106 101 99 116
    58 32 84 104 114 101 101 13 10 78 101 119 115 103
    114 111 117 112 115 58 32 102 110 46 110 111 116 101
    115 13 10 73 110 106 101 99 116 105 111 110 45 68
    97 116 101 58 32 83 97 116 44 32 49 57 32 83
    101 112 32 50 48 50 54 32 49 50 58 48 48 58
    48 48 32 43 48 48 48 48 13 10 13 10 72 101
    108 108 111 13 10))

(defconst *nn-a4-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 97
    52 64 102 110 46 105 110 118 97 108 105 100 62 13
    10 70 114 111 109 58 32 116 64 102 110 46 105 110
    118 97 108 105 100 13 10 83 117 98 106 101 99 116
    58 32 70 111 117 114 13 10 78 101 119 115 103 114
    111 117 112 115 58 32 102 110 46 108 101 116 116 101
    114 115 13 10 68 97 116 101 58 32 83 97 116 44
    32 49 57 32 83 101 112 32 50 48 50 54 32 49
    51 58 48 48 58 48 48 32 45 48 49 48 48 13
    10 13 10 72 101 108 108 111 13 10))

(defconst *nn-a5-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 97
    53 64 102 110 46 105 110 118 97 108 105 100 62 13
    10 70 114 111 109 58 32 116 64 102 110 46 105 110
    118 97 108 105 100 13 10 83 117 98 106 101 99 116
    58 32 70 105 118 101 13 10 78 101 119 115 103 114
    111 117 112 115 58 32 102 110 46 108 101 116 116 101
    114 115 13 10 13 10 72 101 108 108 111 13 10))

(defconst *nn-expected-letters-reply*
  '(50 51 48 32 108 105 115 116 32 111 102 32 110 101
    119 32 97 114 116 105 99 108 101 115 32 98 121 32
    109 101 115 115 97 103 101 45 105 100 32 102 111 108
    108 111 119 115 13 10 60 97 52 64 102 110 46 105
    110 118 97 108 105 100 62 13 10 60 97 49 64 102
    110 46 105 110 118 97 108 105 100 62 13 10 46 13
    10))

(defconst *nn-expected-empty-reply*
  '(50 51 48 32 108 105 115 116 32 111 102 32 110 101
    119 32 97 114 116 105 99 108 101 115 32 98 121 32
    109 101 115 115 97 103 101 45 105 100 32 102 111 108
    108 111 119 115 13 10 46 13 10))

(defconst *nn-expected-both-reply*
  '(50 51 48 32 108 105 115 116 32 111 102 32 110 101
    119 32 97 114 116 105 99 108 101 115 32 98 121 32
    109 101 115 115 97 103 101 45 105 100 32 102 111 108
    108 111 119 115 13 10 60 97 52 64 102 110 46 105
    110 118 97 108 105 100 62 13 10 60 97 51 64 102
    110 46 105 110 118 97 108 105 100 62 13 10 60 97
    49 64 102 110 46 105 110 118 97 108 105 100 62 13
    10 46 13 10))

(defconst *nn-expected-501*
  '(53 48 49 32 115 121 110 116 97 120 32 101 114 114
    111 114 13 10))

(defconst *nn-expected-503-century*
  '(53 48 51 32 116 119 111 45 100 105 103 105 116 32
    121 101 97 114 32 110 101 101 100 115 32 97 32 119
    97 108 108 32 99 108 111 99 107 32 114 101 97 100
    105 110 103 13 10))

(defconst *nn-line-letters* '(78 69 87 78 69 87 83 32 102 110 46 108 101 116 116 101 114 115
    32 50 48 50 54 48 57 49 57 32 48 48 48 48 48 48 32 71
    77 84))
(defconst *nn-line-letters-nogmt* '(78 69 87 78 69 87 83 32 102 110 46 108 101 116 116 101 114 115
    32 50 48 50 54 48 57 49 57 32 48 48 48 48 48 48))
(defconst *nn-line-letters-2digit* '(78 69 87 78 69 87 83 32 102 110 46 108 101 116 116 101 114 115
    32 50 54 48 57 49 57 32 48 48 48 48 48 48 32 71 77 84))
(defconst *nn-line-both* '(78 69 87 78 69 87 83 32 102 110 46 42 32 50 48 50 54 48
    57 49 57 32 48 48 48 48 48 48 32 71 77 84))
(defconst *nn-line-nogroup* '(78 69 87 78 69 87 83 32 102 110 46 110 111 115 117 99 104 32
    50 48 50 54 48 57 49 57 32 48 48 48 48 48 48 32 71 77
    84))
(defconst *nn-line-short* '(78 69 87 78 69 87 83 32 102 110 46 108 101 116 116 101 114 115
    32 50 48 50 54 48 57 49 57))
(defconst *nn-line-badzone* '(78 69 87 78 69 87 83 32 102 110 46 108 101 116 116 101 114 115
    32 50 48 50 54 48 57 49 57 32 48 48 48 48 48 48 32 85
    84 67))
(defconst *nn-line-badwildmat* '(78 69 87 78 69 87 83 32 91 32 50 48 50 54 48 57 49 57
    32 48 48 48 48 48 48 32 71 77 84))
(defconst *nn-line-badtime* '(78 69 87 78 69 87 83 32 102 110 46 108 101 116 116 101 114 115
(defconst *nn-line-newgroups* '(78 69 87 71 82 79 85 80 83 32 50 48 50 54 48 57 49 57 32 48 48 48 48 48 48 32 71 77 84))
    32 50 48 50 54 48 57 49 57 32 50 53 48 48 48 48 32 71
    77 84))

(defconst *nn-dt-plus0000* '(83 97 116 44 32 49 57 32 83 101 112 32 50 48 50 54 32 49
    50 58 48 48 58 48 48 32 43 48 48 48 48))
(defconst *nn-dt-noday* '(49 57 32 83 101 112 32 50 48 50 54 32 49 50 58 48 48 58
    48 48 32 71 77 84))
(defconst *nn-dt-minus0500* '(83 97 116 44 32 49 57 32 83 101 112 32 50 48 50 54 32 48
    55 58 48 48 58 48 48 32 45 48 53 48 48))
(defconst *nn-dt-noseconds* '(83 97 116 44 32 49 57 32 83 101 112 32 50 48 50 54 32 49
    50 58 48 48 32 43 48 48 48 48))
(defconst *nn-dt-est* '(83 97 116 44 32 49 57 32 83 101 112 32 50 48 50 54 32 48
    55 58 48 48 58 48 48 32 69 83 84))
(defconst *nn-dt-comment* '(83 97 116 44 32 49 57 32 83 101 112 32 50 48 50 54 32 49
    50 58 48 48 58 48 48 32 40 117 116 99 41 32 43 48 48 48
    48))
(defconst *nn-dt-nozone* '(83 97 116 44 32 49 57 32 83 101 112 32 50 48 50 54 32 49
    50 58 48 48 58 48 48))
(defconst *nn-dt-badhour* '(83 97 116 44 32 49 57 32 83 101 112 32 50 48 50 54 32 50
    53 58 48 48 58 48 48 32 43 48 48 48 48))
(defconst *nn-dt-badmonth* '(83 97 116 44 32 49 57 32 70 111 111 32 50 48 50 54 32 49
    50 58 48 48 58 48 48 32 43 48 48 48 48))
(defconst *nn-dt-twodigityear* '(83 97 116 44 32 49 57 32 83 101 112 32 50 54 32 49 50 58
    48 48 58 48 48 32 43 48 48 48 48))
(defconst *nn-dt-preepoch* '(49 32 74 97 110 32 49 57 57 57 32 48 48 58 48 48 58 48
    48 32 43 48 48 48 48))
(defconst *nn-dt-unknownzone* '(83 97 116 44 32 49 57 32 83 101 112 32 50 48 50 54 32 49
    50 58 48 48 58 48 48 32 88 89 90))

; -----------------------------------------------------------------------------
; The RFC 5322 section 3.3 date-time decoder
;
; Each line below is an independent reading of the grammar: the same instant
; written five ways must decode to the same millisecond, and the four
; malformed forms must decode to a distinct named error rather than to a
; number the scan would then compare.

(assert-event (equal (fn-nntp-dt-parse *nn-dt-plus0000*) (list :ok *nn-noon*)))
(assert-event (equal (fn-nntp-dt-parse *nn-dt-noday*) (list :ok *nn-noon*)))
(assert-event (equal (fn-nntp-dt-parse *nn-dt-minus0500*) (list :ok *nn-noon*)))
(assert-event (equal (fn-nntp-dt-parse *nn-dt-noseconds*) (list :ok *nn-noon*)))
; RFC 5536 section 3.1.1 requires the deprecated GMT zone to be accepted, and
; RFC 5322 section 4.3 gives EST a real offset and an unrecognized zone none.
(assert-event (equal (fn-nntp-dt-parse *nn-dt-est*) (list :ok *nn-noon*)))
(assert-event (equal (fn-nntp-dt-parse *nn-dt-unknownzone*) (list :ok *nn-noon*)))
; The DTN epoch is the floor, exactly as it is for NEWGROUPS.
(assert-event (equal (fn-nntp-dt-parse *nn-dt-preepoch*) (list :ok 0)))
; The stated limitation: a comment is CFWS this decoder does not take.
(assert-event (equal (fn-nntp-dt-parse *nn-dt-comment*) (list :error :zone)))
(assert-event (equal (fn-nntp-dt-parse *nn-dt-nozone*) (list :error :zone)))
(assert-event (equal (fn-nntp-dt-parse *nn-dt-badhour*) (list :error :range)))
(assert-event (equal (fn-nntp-dt-parse *nn-dt-badmonth*) (list :error :month)))
(assert-event (equal (fn-nntp-dt-parse *nn-dt-twodigityear*)
                     (list :error :year)))
; The control: the decoder is not answering :ok for everything.  An empty
; value and a bare number are refused, so the :ok readings above are decisions.
(assert-event (equal (fn-nntp-dt-parse nil) (list :error :day)))
(assert-event (equal (fn-nntp-dt-parse '(49 50 51)) (list :error :month)))

; -----------------------------------------------------------------------------
; The archive

(defconst *nn-groups* '("fn.letters" "fn.notes"))

; `st`, not `state`: ACL2 reserves that symbol for the live state.
(defun nn-accept (st msgid payload groups stamp)
  (fn-accept-complete
   (fn-accept-prepare st 1 msgid payload groups stamp)
   (fn-state-next-txid st) 1 :durable))

(defconst *nn-archive*
  (nn-accept
   (nn-accept
    (nn-accept
     (nn-accept
      (nn-accept (fn-initial-state *nn-groups*)
                 "<a1@fn.invalid>" *nn-a1-payload* '("fn.letters") 843134400)
      "<a2@fn.invalid>" *nn-a2-payload* '("fn.letters") 820540800)
     "<a3@fn.invalid>" *nn-a3-payload* '("fn.notes") 843134400)
    "<a4@fn.invalid>" *nn-a4-payload* '("fn.letters") 843141600)
   "<a5@fn.invalid>" *nn-a5-payload* '("fn.letters") 820540800)))

(assert-event (equal (len (fn-state-articles *nn-archive*)) 5))
(assert-event (fn-nntp-projectionp *nn-archive*))

(defconst *nn-session* (fn-nntp-open-session *nn-archive*))
(assert-event (fn-nntp-session-projected *nn-session*))

(defconst *nn-obs* (fn-clock-observation 1000 843136496000 1000 t))
(defconst *nn-blind-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *nn-env* (fn-nntp-env *nn-obs* nil nil))
(defconst *nn-blind-env* (fn-nntp-env *nn-blind-obs* nil nil))
(assert-event (fn-nntp-envp *nn-env*))
(assert-event (fn-nntp-envp *nn-blind-env*))

(defconst *nn-articles* (fn-state-articles *nn-archive*))
(defconst *nn-a1-id* (fn-nntp-string-octets "<a1@fn.invalid>"))
(defconst *nn-a3-id* (fn-nntp-string-octets "<a3@fn.invalid>"))
(defconst *nn-a4-id* (fn-nntp-string-octets "<a4@fn.invalid>"))

; -----------------------------------------------------------------------------
; The durable stamp, independent of payload Date and Injection-Date.
(assert-event (equal (fn-article-stamp
                      (fn-find-article "<a1@fn.invalid>" *nn-articles*))
                     843134400))
(assert-event (equal (fn-article-stamp
                      (fn-find-article "<a5@fn.invalid>" *nn-articles*))
                     820540800))

(defun nn-ids (groups threshold horizon)
  (fn-nntp-newnews-scan groups threshold *nn-articles* horizon))

(defconst *nn-a1-article* (fn-find-article "<a1@fn.invalid>" *nn-articles*))
(defconst *nn-a3-article* (fn-find-article "<a3@fn.invalid>" *nn-articles*))
(defconst *nn-a5-article* (fn-find-article "<a5@fn.invalid>" *nn-articles*))
(defconst *nn-a5-id* (fn-nntp-string-octets "<a5@fn.invalid>"))

; At the owner's stamped second the article qualifies; one second later it
; does not.  a5 has no Date header, but its accepted stamp still decides.
(assert-event (equal (nn-ids '("fn.letters") *nn-midnight* :none)
                     (list *nn-a4-id* *nn-a1-id*)))
(assert-event (equal (nn-ids *nn-groups* *nn-midnight* :none)
                     (list *nn-a4-id* *nn-a3-id* *nn-a1-id*)))
(assert-event (equal (fn-nntp-newnews-scan
                      '("fn.letters") *nn-january*
                      (list *nn-a5-article*) :none)
                     (list *nn-a5-id*)))
(assert-event (equal (fn-nntp-newnews-scan
                      '("fn.letters") (+ *nn-january* 1000)
                      (list *nn-a5-article*) :none)
                     nil))
(assert-event (equal (nn-ids '("fn.letters") *nn-afternoon* :none)
                     (list *nn-a4-id*)))
(assert-event (equal (nn-ids '("fn.letters")
                             (fn-nntp-civil-dtn-ms 2026 9 20 0 0 0) :none)
                     nil))
(assert-event (fn-nov-clean-line-listp
               (nn-ids '("fn.letters") *nn-midnight* :none)))

(defun nn-with-stamp (a stamp)
  (fn-make-article (fn-article-msgid a) (fn-article-payload a)
                   (fn-article-groups a) (fn-article-memberships a)
                   (fn-article-pin a) stamp))
(defconst *nn-legacy* (nn-with-stamp *nn-a5-article* :legacy))
; The newest stamped article is outside the matched group but still supplies
; the nearest later-acceptance horizon for this older legacy article.
(defconst *nn-mixed* (list *nn-a3-article* *nn-legacy*))
(assert-event (equal (fn-nntp-newnews-scan
                      '("fn.letters") *nn-noon* *nn-mixed* :none)
                     (list *nn-a5-id*)))
(assert-event (equal (fn-nntp-newnews-scan
                      '("fn.letters") (+ *nn-noon* 1000) *nn-mixed* :none)
                     nil))
; A lone legacy article uses the reader's pinned wall, or stays visible
; without any wall.  The served path does not guess from its payload.
(assert-event (equal (fn-nntp-newnews-reader-horizon *nn-env*) 843136496))
(assert-event (equal (fn-nntp-newnews-reader-horizon *nn-blind-env*) :none))
(assert-event (equal (fn-nntp-newnews-scan
                      '("fn.letters") 843136496000
                      (list *nn-legacy*)
                      (fn-nntp-newnews-reader-horizon *nn-env*))
                     (list *nn-a5-id*)))
(assert-event (equal (fn-nntp-newnews-scan
                      '("fn.letters") 843136497000
                      (list *nn-legacy*)
                      (fn-nntp-newnews-reader-horizon *nn-env*))
                     nil))
(assert-event (equal (fn-nntp-newnews-scan
                      '("fn.letters") 999999999999
                      (list *nn-legacy*)
                      (fn-nntp-newnews-reader-horizon *nn-blind-env*))
                     (list *nn-a5-id*)))

; Both sides of the independent filter equation make real decisions.
(assert-event (equal (fn-nntp-newnews-accepted-since
                      '("fn.letters") *nn-midnight* *nn-articles* nil :none)
                     (nn-ids '("fn.letters") *nn-midnight* :none)))
(assert-event (equal (fn-nntp-newnews-accepted-since
                      '("fn.letters") (+ *nn-noon* 1000)
                      *nn-articles* nil :none)
                     (list *nn-a4-id*)))
(local
 (must-fail
  (defthm nn-teeth-every-article-is-a-candidate
    (fn-nntp-newnews-candidatep '("fn.letters") *nn-a3-article*))))
(local
 (must-fail
  (defthm nn-teeth-every-stamp-is-new
    (equal (nn-ids '("fn.letters") (+ *nn-noon* 1000) :none)
           (nn-ids '("fn.letters") *nn-midnight* :none)))))
(local
 (must-fail
  (defthm nn-teeth-payload-decides-the-answer
    (not (equal
          (fn-nntp-newnews-scan
           '("fn.letters") *nn-midnight*
           (fn-nntp-newnews-without-payload *nn-articles*) :none)
          (nn-ids '("fn.letters") *nn-midnight* :none))))))
(assert-event (equal (fn-nntp-newnews-candidate-count
                      '("fn.letters") *nn-articles*) 4))
(assert-event (equal (len (nn-ids '("fn.letters") *nn-midnight* :none)) 2))
(local
 (must-fail
  (defthm nn-teeth-lines-exceed-candidates
    (< (fn-nntp-newnews-candidate-count
        '("fn.letters") *nn-articles*)
       (len (nn-ids '("fn.letters") *nn-midnight* :none))))))

; -----------------------------------------------------------------------------
; fn-nntp-step-dispatches-newnews-to-the-newnews-response: one ground case
; per hypothesis that changes the answer.  Each is a concrete session, line
; or archive, not a free-variable claim: an open dispatcher over free
; variables splits into thousands of subgoals before it fails, and a tooth
; should say WHICH case separates the two sides.
;
; There is no case for `(consp (fn-nntp-tokenize line))`, for
; `(fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))` or for
; `(fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))`.  All three
; are tests `fn-nntp-step` makes and all three are already implied by the
; hypotheses that remain: a token that upcases to "NEWNEWS" is seven
; letters, so it is an RFC 3977 section 9.8 keyword and the list it heads is
; a cons; and a NEWNEWS line inside section 3.1's 510-octet limit cannot
; carry a 498-octet argument, because the keyword and the two other
; mandatory arguments take 25 octets of it.  Dropping any of the three
; leaves a statement that is TRUE and that this book cannot prove, and a
; `must-fail` on it would record a proof difficulty, not a tooth.

(defconst *nn-closed-session* (fn-nntp-make-session nil "fn.letters" 1 t))
(defconst *nn-unprojected-session* (fn-nntp-make-session t nil nil nil))
(assert-event (fn-nntp-sessionp *nn-closed-session*))
(assert-event (fn-nntp-sessionp *nn-unprojected-session*))
; RFC 3977 section 3.1's limit is 510 octets and `fn-nntp-tokenize` does not
; enforce it, so this line tokenizes into a well-formed NEWNEWS command that
; `fn-nntp-command-inputp` nevertheless refuses.  That is what makes the
; command-input hypothesis separable from the rest.
(defconst *nn-line-too-long*
  '(78 69 87 78 69 87 83 32 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102 102
    102 102 102 102 102 102 102 102 102 102 102 102 32 50 48 50 54 48
    57 49 57 32 48 48 48 48 48 48 32 71 77 84))
(assert-event (equal (len *nn-line-too-long*) 518))
(assert-event (fn-nntp-command-inputp *nn-line-letters*))
(assert-event (not (fn-nntp-command-inputp *nn-line-too-long*)))
(assert-event (fn-nntp-keywordp (car (fn-nntp-tokenize *nn-line-too-long*))
                                "NEWNEWS"))

(defmacro nn-dispatch-claim (session line)
  `(equal (fn-nntp-step ,session *nn-archive* *nn-env* (list :command ,line))
          (fn-nntp-newnews-response ,session *nn-archive* *nn-env*
                                    (cdr (fn-nntp-tokenize ,line)))))

; The witness: with every hypothesis met the two sides are the same object.
(assert-event (nn-dispatch-claim *nn-session* *nn-line-letters*))

(local
 (must-fail
  (defthm nn-teeth-dispatch-without-a-session
    (nn-dispatch-claim :not-a-session *nn-line-letters*))))

(local
 (must-fail
  (defthm nn-teeth-dispatch-on-a-closed-session
    (nn-dispatch-claim *nn-closed-session* *nn-line-letters*))))

(local
 (must-fail
  (defthm nn-teeth-dispatch-without-a-projection
    (nn-dispatch-claim *nn-unprojected-session* *nn-line-letters*))))

(local
 (must-fail
  (defthm nn-teeth-dispatch-without-a-command-line
    (nn-dispatch-claim *nn-session* *nn-line-too-long*))))

(local
 (must-fail
  (defthm nn-teeth-dispatch-of-any-keyword
    (nn-dispatch-claim *nn-session* *nn-line-newgroups*))))

; -----------------------------------------------------------------------------
; The replies, as octets

(defmacro nn-reply (env line)
  `(fn-nntp-result-effects
    (fn-nntp-step *nn-session* *nn-archive* ,env (list :command ,line))))

(defun nn-only-reply (effects)
  (and (consp effects)
       (null (cdr effects))
       (equal (car effects) (fn-nntp-reply-effect (car (cdr (car effects)))))
       (car (cdr (car effects)))))

(assert-event (equal (nn-only-reply (nn-reply *nn-env* *nn-line-letters*))
                     *nn-expected-letters-reply*))
; The GMT token is optional and changes nothing: RFC 3977 section 7.4.1's
; grammar with and without it must give the same block.
(assert-event (equal (nn-only-reply (nn-reply *nn-env* *nn-line-letters-nogmt*))
                     *nn-expected-letters-reply*))
; Section 7.3.2's century rule, inherited by section 7.4.2: with a wall clock
; the two-digit year resolves to the same instant.
(assert-event (equal (nn-only-reply (nn-reply *nn-env* *nn-line-letters-2digit*))
                     *nn-expected-letters-reply*))
; Without one it is 503 and not a guess.  The three outcomes stay distinct:
; 230 answered, 501 refused for syntax, 503 refused for want of information.
(assert-event (equal (nn-only-reply (nn-reply *nn-blind-env*
                                              *nn-line-letters-2digit*))
                     *nn-expected-503-century*))
(assert-event (equal (nn-only-reply (nn-reply *nn-env* *nn-line-both*))
                     *nn-expected-both-reply*))
; Section 7.4.2: an empty list is a valid response.
(assert-event (equal (nn-only-reply (nn-reply *nn-env* *nn-line-nogroup*))
                     *nn-expected-empty-reply*))
(assert-event (equal (nn-only-reply (nn-reply *nn-env* *nn-line-short*))
                     *nn-expected-501*))
(assert-event (equal (nn-only-reply (nn-reply *nn-env* *nn-line-badzone*))
                     *nn-expected-501*))
(assert-event (equal (nn-only-reply (nn-reply *nn-env* *nn-line-badwildmat*))
                     *nn-expected-501*))
(assert-event (equal (nn-only-reply (nn-reply *nn-env* *nn-line-badtime*))
                     *nn-expected-501*))
; Every reply above is a well-formed effect list, which is what
; books/nntp-effects.lisp's fn-nntp-step-effects-well-formed claims of them.
(assert-event (fn-nntp-effectsp (nn-reply *nn-env* *nn-line-letters*)))
(assert-event (fn-nntp-effectsp (nn-reply *nn-env* *nn-line-badwildmat*)))
; RFC 3977 section 7.4.2 assigns NEWNEWS no state change, and it makes none.
(assert-event (equal (fn-nntp-result-session
                      (fn-nntp-step *nn-session* *nn-archive* *nn-env*
                                    (list :command *nn-line-letters*)))
                     *nn-session*))

; -----------------------------------------------------------------------------
 ; A candidate-free list of 300 articles has a complete empty answer.  No
; parser, size budget or partial-response 503 remains on this command.
(defun nn-repeat-other (article n)
  (declare (xargs :measure (nfix n)))
  (if (posp n)
      (cons article (nn-repeat-other article (- n 1)))
    nil))
(defconst *nn-bulk-other* (nn-repeat-other *nn-a3-article* 300))
(assert-event (equal (len *nn-bulk-other*) 300))
(assert-event (equal (fn-nntp-newnews-candidate-count
                      '("fn.letters") *nn-bulk-other*) 0))
(assert-event (equal (fn-nntp-newnews-scan
                      '("fn.letters") *nn-midnight* *nn-bulk-other* :none)
                     nil))
