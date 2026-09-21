; Executable boundary traces for the bounded NNTP wire framing model, and the
; teeth for the wire keystones: each hypothesis of a keystone gets a concrete
; input for which the conclusion fails without it.
(in-package "ACL2")
(include-book "../../books/wire-invariants")

(defconst *fn-wire-empty* (fn-wire-initial-state 32 64))
(assert-event (fn-wire-statep *fn-wire-empty*))

; A command CRLF may be split at every byte boundary.
(defconst *fn-wire-command-split-a*
  (fn-wire-feed *fn-wire-empty* '(72 69 76 80 13)))
(assert-event (equal (fn-wire-result-events *fn-wire-command-split-a*) nil))
(defconst *fn-wire-command-split-b*
  (fn-wire-feed (fn-wire-result-state *fn-wire-command-split-a*) '(10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-command-split-b*)
        '((:command (72 69 76 80)))))

; -----------------------------------------------------------------------------
; Entering article mode is an explicit accept-or-refuse decision.

(defconst *fn-wire-article-start-result* (fn-wire-begin-article *fn-wire-empty*))
(defconst *fn-wire-article-start*
  (fn-wire-result-state *fn-wire-article-start-result*))
(assert-event (not (fn-wire-begin-article-refusedp *fn-wire-article-start-result*)))
(assert-event (equal (fn-wire-state-mode *fn-wire-article-start*) :article))
(assert-event (fn-wire-statep *fn-wire-article-start*))

; Teeth for fn-wire-begin-article-acceptance-enters-empty-article-mode: one
; refused input per conjunct of fn-wire-begin-article-admissiblep, each with
; the unchanged state and the explicit reject event, and none of them entering
; article mode.
(defconst *fn-wire-partial-command*
  (fn-wire-result-state (fn-wire-feed *fn-wire-empty* '(72 69))))
(defconst *fn-wire-pending-cr*
  (fn-wire-result-state (fn-wire-feed *fn-wire-empty* '(13))))

; mode is not :command
(assert-event
 (fn-wire-begin-article-refusedp
  (fn-wire-begin-article *fn-wire-article-start*)))
(assert-event
 (equal (fn-wire-result-state (fn-wire-begin-article *fn-wire-article-start*))
        *fn-wire-article-start*))
; line-rev is not empty
(assert-event (fn-wire-statep *fn-wire-partial-command*))
(assert-event (not (null (fn-wire-state-line-rev *fn-wire-partial-command*))))
(assert-event
 (fn-wire-begin-article-refusedp
  (fn-wire-begin-article *fn-wire-partial-command*)))
(assert-event
 (equal (fn-wire-result-state (fn-wire-begin-article *fn-wire-partial-command*))
        *fn-wire-partial-command*))
(assert-event
 (equal (fn-wire-result-events (fn-wire-begin-article *fn-wire-partial-command*))
        '((:reject :begin-article-unquiesced))))

; Command and article physical-line profiles are separate.  The 510-octet
; command content ceiling stays on the opening state; after a complete command
; the article transition selects body-limit-plus-one, enough for any retained
; article source line and one leading-dot stuffing byte.
(defconst *fn-wire-article-profile-start*
  (let ((wire (fn-wire-initial-state 510 8192)))
    (fn-wire-begin-article-with-line-limit
     wire (fn-wire-article-line-limit wire))))
(assert-event
 (equal (fn-wire-state-line-limit
         (fn-wire-result-state *fn-wire-article-profile-start*))
        8193))
(assert-event
 (equal (fn-wire-state-mode
         (fn-wire-result-state *fn-wire-article-profile-start*))
        :article))
; A positive physical profile is necessary: accepting zero would produce a
; malformed state and the next byte would have no coherent capacity meaning.
(assert-event
 (equal (fn-wire-result-events
         (fn-wire-begin-article-with-line-limit
          (fn-wire-initial-state 510 8192) 0))
        '((:reject :begin-article-bad-line-limit))))
(assert-event
 (not (equal (fn-wire-state-mode
              (fn-wire-result-state
               (fn-wire-begin-article *fn-wire-partial-command*)))
             :article)))
; pending-crp is set
(assert-event (fn-wire-statep *fn-wire-pending-cr*))
(assert-event (equal (fn-wire-state-pending-crp *fn-wire-pending-cr*) t))
(assert-event
 (fn-wire-begin-article-refusedp (fn-wire-begin-article *fn-wire-pending-cr*)))
(assert-event
 (not (equal (fn-wire-state-mode
              (fn-wire-result-state
               (fn-wire-begin-article *fn-wire-pending-cr*)))
             :article)))
; the supplied value is not a wire state at all
(assert-event (not (fn-wire-statep '(:command nil 0 nil nil 0 32))))
(assert-event
 (fn-wire-begin-article-refusedp
  (fn-wire-begin-article '(:command nil 0 nil nil 0 32))))
(assert-event
 (equal (fn-wire-result-state
         (fn-wire-begin-article '(:command nil 0 nil nil 0 32)))
        '(:command nil 0 nil nil 0 32)))

; -----------------------------------------------------------------------------
; Framing traces.

; A dot-stuffed line is data and a terminator split across chunks ends one body.
(defconst *fn-wire-article-part-a*
  (fn-wire-feed *fn-wire-article-start* '(46 46 102 105 114 115 116 13 10 46 13)))
(assert-event (equal (fn-wire-result-events *fn-wire-article-part-a*) nil))
(defconst *fn-wire-article-part-b*
  (fn-wire-feed (fn-wire-result-state *fn-wire-article-part-a*) '(10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-article-part-b*)
        '((:article ((46 102 105 114 115 116))))))

; The empty article is distinct from malformed input and completes on dot CRLF.
(defconst *fn-wire-empty-article*
  (fn-wire-feed *fn-wire-article-start* '(46 13 10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-empty-article*) '((:article nil))))

; A line over limit closes the connection.  Its apparent CRLF and a command
; after it are discarded, so rejected article tails never become commands.
(defconst *fn-wire-tiny-article*
  (fn-wire-result-state
   (fn-wire-begin-article (fn-wire-initial-state 3 64))))
(defconst *fn-wire-overlong*
  (fn-wire-feed *fn-wire-tiny-article*
                '(97 98 99 100 13 10 72 69 76 80 13 10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-overlong*) '((:reject :line-overlimit))))
(assert-event
 (equal (fn-wire-state-mode (fn-wire-result-state *fn-wire-overlong*)) :closed))
(assert-event
 (equal (fn-wire-result-events
         (fn-wire-feed (fn-wire-result-state *fn-wire-overlong*) '(81 13 10)))
        nil))

; A closed input state is an immediate no-op even when handed an arbitrary
; suffix.  This checks that rejection does not cause unbounded tail traversal.
(assert-event
 (equal (fn-wire-feed (fn-wire-result-state *fn-wire-overlong*)
                      '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16))
        (fn-wire-make-result (fn-wire-result-state *fn-wire-overlong*) nil)))

; Bare LF and CR followed by a non-LF are malformed and close rather than
; resynchronizing to a body or command boundary.
(defconst *fn-wire-bare-lf* (fn-wire-feed *fn-wire-empty* '(72 10 73 13 10)))
(assert-event (equal (fn-wire-result-events *fn-wire-bare-lf*) '((:reject :malformed))))
(defconst *fn-wire-bad-cr* (fn-wire-feed *fn-wire-empty* '(72 13 73 13 10)))
(assert-event (equal (fn-wire-result-events *fn-wire-bad-cr*) '((:reject :malformed))))

; Total retained body bytes are bounded, after dot unstuffing and with CRLF
; accounted for.  The second line is rejected before it becomes an article.
(defconst *fn-wire-small-body*
  (fn-wire-result-state
   (fn-wire-begin-article (fn-wire-initial-state 16 3))))
(defconst *fn-wire-body-overlimit*
  (fn-wire-feed *fn-wire-small-body* '(97 98 13 10 46 13 10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-body-overlimit*) '((:reject :body-overlimit))))

; The carried counters are the measurements they stand for, at a nondegenerate
; retained state: four retained line octets and two retained body lines.
(defconst *fn-wire-carry-state*
  (fn-wire-result-state
   (fn-wire-feed *fn-wire-article-start*
                 '(97 98 13 10 99 100 13 10 101 102 103 104))))
(assert-event (fn-wire-statep *fn-wire-carry-state*))
(assert-event (equal (fn-wire-state-line-len *fn-wire-carry-state*) 4))
(assert-event (equal (fn-wire-state-line-len *fn-wire-carry-state*)
                     (len (fn-wire-state-line-rev *fn-wire-carry-state*))))
(assert-event (equal (fn-wire-state-body-size *fn-wire-carry-state*) 8))
(assert-event (equal (fn-wire-state-body-size *fn-wire-carry-state*)
                     (fn-wire-lines-size
                      (fn-wire-state-body-rev *fn-wire-carry-state*))))

; The executable partition law is exercised with an article split inside its
; CRLF and a separately chunked continuation.
(defconst *fn-wire-partition-whole*
  (fn-wire-feed *fn-wire-article-start* '(120 13 10 46 13 10)))
(defconst *fn-wire-partition-split*
  (fn-wire-continue
   (fn-wire-feed *fn-wire-article-start* '(120 13))
   '(10 46 13 10)))
(assert-event (equal *fn-wire-partition-whole* *fn-wire-partition-split*))

; -----------------------------------------------------------------------------
; The served path: fn-wire-next, the adapter loop, and the reference.

; A pull caller can stop after POST, change framing mode, and resume on the
; unconsumed bytes of that exact socket chunk.  Thus POST's following article
; cannot be misread as ordinary command text merely because both arrived at
; once.  (POST itself remains outside this reader-only wire model.)
(defconst *fn-wire-post-and-article*
  '(80 79 83 84 13 10 72 105 13 10 46 13 10))
(defconst *fn-wire-post-whole*
  (fn-wire-next *fn-wire-empty* *fn-wire-post-and-article*))
(assert-event (equal (fn-wire-next-event *fn-wire-post-whole*)
                     '(:command (80 79 83 84))))
(defconst *fn-wire-post-article-whole*
  (fn-wire-next (fn-wire-result-state
                 (fn-wire-begin-article (fn-wire-next-state *fn-wire-post-whole*)))
                (fn-wire-next-unconsumed *fn-wire-post-whole*)))
(defconst *fn-wire-post-split*
  (fn-wire-next *fn-wire-empty* '(80 79 83 84 13 10)))
(defconst *fn-wire-post-article-split*
  (fn-wire-next (fn-wire-result-state
                 (fn-wire-begin-article (fn-wire-next-state *fn-wire-post-split*)))
                '(72 105 13 10 46 13 10)))
(assert-event (equal *fn-wire-post-article-whole* *fn-wire-post-article-split*))

; A coalesced complete article produces one explicit article event, leaves no
; socket remainder for the pull caller, and returns command framing mode.
(defconst *fn-wire-coalesced-article*
  (fn-wire-next *fn-wire-article-start* '(72 105 13 10 46 13 10)))
(assert-event (equal (fn-wire-next-event *fn-wire-coalesced-article*)
                     '(:article ((72 105)))))
(assert-event (equal (fn-wire-next-unconsumed *fn-wire-coalesced-article*) nil))
(assert-event (equal (fn-wire-state-mode
                      (fn-wire-next-state *fn-wire-coalesced-article*))
                     :command))

; The public full-chunk API rejects improper ACL2 list structure rather than
; treating it as a completed socket chunk.  The pull API rejects when it reaches
; the improper tail and never presents that atom as an octet command suffix.
(assert-event
 (equal (fn-wire-result-events (fn-wire-feed *fn-wire-empty* '(72 . 105)))
        '((:reject :malformed))))
(assert-event
 (equal (fn-wire-next-event (fn-wire-next *fn-wire-empty* '(72 . 105)))
        '(:reject :malformed)))

; The constant-work served path agrees with the recomputing reference on a
; nondegenerate article chunk: two body lines, a partial third line, and a
; dot-stuffed line.
(defconst *fn-wire-reference-chunk*
  '(46 46 97 13 10 98 99 13 10 100))
(assert-event
 (equal (fn-wire-next *fn-wire-article-start* *fn-wire-reference-chunk*)
        (fn-wire-next-reference *fn-wire-article-start*
                                *fn-wire-reference-chunk*)))
(assert-event
 (equal (fn-wire-next *fn-wire-empty* *fn-wire-post-and-article*)
        (fn-wire-next-reference *fn-wire-empty* *fn-wire-post-and-article*)))

; Teeth for fn-wire-feed-byte-matches-reference and its lifted forms: the
; fn-wire-statep hypothesis is doing work.  This eight-field value has the
; right shape but a carried line length that does not measure its retained
; line, so the constant-work step and the recomputing reference disagree.
(defconst *fn-wire-drifted-counter* '(:command (65 66) 0 nil nil 0 32 64))
(assert-event (not (fn-wire-statep *fn-wire-drifted-counter*)))

(defthm fn-wire-feed-byte-needs-statep-to-match-reference
  (not (equal (fn-wire-feed-byte '(:command (65 66) 0 nil nil 0 32 64) 67)
              (fn-wire-feed-byte-reference '(:command (65 66) 0 nil nil 0 32 64)
                                           67)))
  :rule-classes nil)

(defthm fn-wire-next-loop-needs-statep-to-match-reference
  (not (equal (fn-wire-next-loop '(:command (65 66) 0 nil nil 0 32 64) '(67))
              (fn-wire-next-reference '(:command (65 66) 0 nil nil 0 32 64)
                                      '(67))))
  :rule-classes nil)

; Teeth for fn-wire-drive-is-feed-proper: without fn-wire-statep the adapter
; loop refuses the state and the fixed-mode helper does not.
(defthm fn-wire-drive-needs-statep-to-be-feed-proper
  (not (equal (fn-wire-drive '(:command (65 66) 0 nil nil 0 32 64) '(67 13 10))
              (fn-wire-feed-proper '(:command (65 66) 0 nil nil 0 32 64)
                                   '(67 13 10))))
  :rule-classes nil)

; The adapter loop drains a whole chunk into its event sequence, and splitting
; the chunk anywhere yields the same events and the same final state.  This is
; the executable witness for fn-wire-drive-partition-independence.
(defconst *fn-wire-drive-whole*
  (fn-wire-drive *fn-wire-empty* '(72 69 76 80 13 10 81 85 73 84 13 10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-drive-whole*)
        '((:command (72 69 76 80)) (:command (81 85 73 84)))))
(defconst *fn-wire-drive-left*
  (fn-wire-drive *fn-wire-empty* '(72 69 76 80 13)))
(defconst *fn-wire-drive-right*
  (fn-wire-drive (fn-wire-result-state *fn-wire-drive-left*)
                 '(10 81 85 73 84 13 10)))
(assert-event
 (equal *fn-wire-drive-whole*
        (fn-wire-make-result
         (fn-wire-result-state *fn-wire-drive-right*)
         (append (fn-wire-result-events *fn-wire-drive-left*)
                 (fn-wire-result-events *fn-wire-drive-right*)))))

; Teeth for the fn-wire-octet-listp hypotheses of the partition theorem: an
; improper left chunk is dropped by append, so the concatenated drive frames a
; command while the split drive rejects the chunk as malformed.
(defthm fn-wire-drive-partition-needs-proper-left-chunk
  (not (equal (fn-wire-drive (fn-wire-initial-state 32 64)
                             (append '(65 . 66) '(13 10)))
              (fn-wire-make-result
               (fn-wire-result-state
                (fn-wire-drive
                 (fn-wire-result-state
                  (fn-wire-drive (fn-wire-initial-state 32 64) '(65 . 66)))
                 '(13 10)))
               (append
                (fn-wire-result-events
                 (fn-wire-drive (fn-wire-initial-state 32 64) '(65 . 66)))
                (fn-wire-result-events
                 (fn-wire-drive
                  (fn-wire-result-state
                   (fn-wire-drive (fn-wire-initial-state 32 64) '(65 . 66)))
                  '(13 10)))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Outbound RFC 3977 section 3.1.1 rendering.  `fn-owner-feed-command' is the
; host-called projection of fn-wire-render-feed-command (owner-host.lisp), so
; these traces exercise the same renderer, not a Python counterpart.

(defconst *fn-wire-outbound-source*
  '(83 117 98 106 101 99 116 58 32 116 13 10 13 10
    46 108 105 116 101 114 97 108 13 10 46 13 10
    98 111 100 121 13 10 13 10 13 10))
(defconst *fn-wire-outbound-rendered*
  (fn-wire-render-block *fn-wire-outbound-source* 64))
(assert-event (fn-wire-outbound-okp *fn-wire-outbound-rendered*))
; All source CRLFs survive, including both final blank lines; only the two
; source line-leading dots gain one octet, and the final dot CRLF is framing.
(assert-event
 (equal (fn-wire-outbound-octets *fn-wire-outbound-rendered*)
        '(83 117 98 106 101 99 116 58 32 116 13 10 13 10
          46 46 108 105 116 101 114 97 108 13 10 46 46 13 10
          98 111 100 121 13 10 13 10 13 10 46 13 10)))

; This is the complete, bounded receiver composition for the output of the
; actual renderer above.  It calls fn-wire-drive, which is the reader-host
; framing loop, after the normal article-mode transition.  The yielded article
; has exactly the retained source lines: two final empty lines, a literal
; dot-leading line, and a dot-only line all survive the physical round trip.
(defconst *fn-wire-outbound-roundtrip*
  (fn-wire-drive *fn-wire-article-start*
                (fn-wire-outbound-octets *fn-wire-outbound-rendered*)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-outbound-roundtrip*)
        '((:article ((83 117 98 106 101 99 116 58 32 116)
                     nil
                     (46 108 105 116 101 114 97 108)
                     (46)
                     (98 111 100 121)
                     nil
                     nil)))))
(assert-event
 (equal (fn-wire-state-mode
         (fn-wire-result-state *fn-wire-outbound-roundtrip*))
        :command))

; Teeth for fn-wire-after-line-unstuffs-rendered-source-line.  A dot-only
; source becomes two dots on the wire and is retained as one literal dot;
; removing the body-bound hypothesis instead reaches the real close branch.
(assert-event
 (equal (fn-wire-after-line *fn-wire-article-start* '(46 46))
        (fn-wire-make-result
         (fn-wire-make-state :article nil 0 '((46)) nil 3 32 64)
         nil)))
(assert-event
 (not (equal
       (fn-wire-after-line
        (fn-wire-result-state
         (fn-wire-begin-article (fn-wire-initial-state 32 2)))
        '(97))
       (fn-wire-make-result
        (fn-wire-make-state :article nil 0 '((97)) nil 3 32 2)
        nil))))

; Empty source is a valid empty NNTP block, and is distinct from malformed
; source.  It is the zero-line article accepted by the inbound wire machine.
(assert-event
 (equal (fn-wire-render-block nil 0) '(:ok (46 13 10))))
(assert-event
 (equal (fn-wire-render-block '(13 10) 2) '(:ok (13 10 46 13 10))))

; Teeth for the renderer's source hypotheses: no newline repair and no
; unbounded walk.  Each source differs materially from the accepted witness.
(assert-event
 (equal (fn-wire-outbound-reason
         (fn-wire-render-block '(83 10) 8))
        :bare-lf))
(assert-event
 (equal (fn-wire-outbound-reason
         (fn-wire-render-block '(83 13 88) 8))
        :malformed-cr))
(assert-event
 (equal (fn-wire-outbound-reason
         (fn-wire-render-block '(83 13 10) 2))
        :overlimit))
(assert-event
 (equal (fn-wire-outbound-reason
         (fn-wire-render-block '(83 . 13) 8))
        :malformed-list))

; The composed feed command keeps an ACL2-issued CHECK verbatim, and renders
; the body after an ACL2-issued TAKETHIS line as one complete block.  A CHECK
; with an article suffix is refused rather than silently sent as a block.
(assert-event
 (equal (fn-wire-render-feed-command
         '(67 72 69 67 75 32 60 105 64 110 62 13 10) 32 64)
        '(:ok (67 72 69 67 75 32 60 105 64 110 62 13 10))))
(assert-event
 (equal (fn-wire-render-feed-command
         '(84 65 75 69 84 72 73 83 32 60 105 64 110 62 13 10
           46 13 10) 32 64)
        '(:ok (84 65 75 69 84 72 73 83 32 60 105 64 110 62 13 10
               46 46 13 10 46 13 10))))
(assert-event
 (equal (fn-wire-outbound-reason
         (fn-wire-render-feed-command
          '(67 72 69 67 75 32 60 105 64 110 62 13 10 120 13 10) 32 64))
        :offer-has-body))
